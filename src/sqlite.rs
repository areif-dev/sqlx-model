use std::fmt::Debug;

use async_trait::async_trait;
use serde::{ser::Error, Serialize};
use sqlx::{sqlite::SqliteRow, FromRow, SqlitePool};

use crate::{sanitize_name, BasicType};

fn bind_values<'q, T>(
    query_str: &'q str,
    vals: &'q [serde_json::Value],
) -> Option<sqlx::query::QueryAs<'q, sqlx::Sqlite, T, sqlx::sqlite::SqliteArguments<'q>>>
where
    T: Send + 'q + for<'r> FromRow<'r, sqlx::sqlite::SqliteRow>,
{
    let mut query = sqlx::query_as(query_str);
    for val in vals {
        query = match val_to_basic_type(val)? {
            BasicType::Null => query.bind(Option::<String>::None),
            BasicType::Real(f) => query.bind(f),
            BasicType::Text(s) => query.bind(s),
            BasicType::Blob(v) => query.bind(v),
            BasicType::Integer(i) => query.bind(i),
        };
    }
    Some(query)
}

fn val_to_basic_type(val: &serde_json::Value) -> Option<BasicType> {
    match val {
        serde_json::Value::Null => Some(BasicType::Null),
        serde_json::Value::Bool(b) => Some(BasicType::Integer(if *b { 1 } else { 0 })),
        serde_json::Value::Number(_) => val_to_basic_num(val),
        serde_json::Value::String(s) => Some(BasicType::Text(s.to_string())),
        serde_json::Value::Array(a) => Some(BasicType::Blob(val_to_blob(a)?)),
        _ => None,
    }
}

fn val_to_blob(arr: &Vec<serde_json::Value>) -> Option<Vec<u8>> {
    let mut blob = Vec::new();
    for el in arr {
        let basic = val_to_basic_num(el)?;
        match basic {
            BasicType::Integer(i) => blob.push(u8::try_from(i).ok()?),
            _ => return None,
        }
    }
    Some(blob)
}

fn val_to_basic_num(val: &serde_json::Value) -> Option<BasicType> {
    if let serde_json::Value::Number(num) = val {
        if let Some(n) = num.as_i64() {
            return Some(BasicType::Integer(n));
        }
        if let Some(n) = num.as_f64() {
            return Some(BasicType::Real(n));
        }
        return None;
    }
    None
}

#[derive(Debug)]
pub struct QueryBuilder<M: SqliteModel> {
    base_clause: String,
    where_clause: String,
    vals: Vec<serde_json::Value>,
}

fn build_where_clause(col: &str, op: &str) -> String {
    format!(" where {} {} ?", sanitize_name(col), op,)
}

impl<M> QueryBuilder<M>
where
    M: SqliteModel + for<'r> FromRow<'r, SqliteRow> + Send + Unpin + Clone,
{
    pub fn eq(self, col: &str, val: serde_json::Value) -> QueryBuilder<M> {
        let mut new_vals = self.vals.to_vec();
        new_vals.push(val);
        QueryBuilder {
            where_clause: build_where_clause(col, "="),
            ..self
        }
    }

    pub async fn fetch_one(self, pool: &SqlitePool) -> Result<M, M::Error> {
        let all = self.fetch_limit(pool, Some(1)).await?;
        Ok(all.get(0).ok_or(sqlx::Error::RowNotFound)?.clone())
    }

    pub async fn fetch_limit(
        self,
        pool: &SqlitePool,
        limit: Option<usize>,
    ) -> Result<Vec<M>, M::Error> {
        let limit = limit.map_or("".to_string(), |l| format!(" limit {}", l));
        let query_str = format!("{}{}{};", self.base_clause, self.where_clause, limit);
        let query =
            bind_values(&query_str, &self.vals).ok_or(serde_json::Error::custom(format!(
                "QueryBuilder::limit: cannot parse values of {:?} for query {}",
                &self.vals, &query_str
            )))?;
        Ok(query.fetch_all(pool).await?)
    }
}

#[async_trait]
pub trait SqliteModel {
    /// Custom error type for the model, which must implement the standard Error trait and be convertible from sqlx::Error
    type Error: From<sqlx::Error> + From<serde_json::Error>;

    /// The name of this type in the database
    ///
    /// # Errors
    /// The default implementation parses `std::any::type_name`, and will
    /// panic if splitting the value of `std::any::type_name` on "::" returns `None`
    fn table_name() -> String {
        let full_path = std::any::type_name::<Self>();
        full_path
            .split("::")
            .last()
            .expect("Failed to convert type_name to table_name")
            .to_string()
    }

    /// Inserts a new record into the table and returns the newly created model instance.
    ///
    /// # Arguments
    /// - pool: A reference to a sqlx::SqlitePool used for database interaction.
    /// - skip_cols: A list of column names to skip during the insertion. This can be useful for
    /// skipping columns that you would like to be set to their default value by the database. Eg
    /// automatically setting and incrementing the primary key.
    ///
    /// # Returns
    /// - Result<Self, Self::Error>: Returns the newly inserted model instance on success, otherwise returns an error.
    ///
    /// # Errors
    /// - Returns Self::Error if the database operation fails.
    async fn insert(&self, pool: &sqlx::SqlitePool, skip_cols: &[&str]) -> Result<Self, Self::Error>
    where
        Self: Sized + for<'r> FromRow<'r, SqliteRow> + Serialize + Unpin + Send + Debug,
    {
        let mut column_names = Vec::new();
        let mut ordered_vals = Vec::new();
        let mut qmarks = Vec::new();
        let map = match serde_json::to_value(self)? {
            serde_json::Value::Object(m) => m,
            _ => {
                return Err(serde_json::Error::custom(format!(
                    "Failed to serialize {:?} into a map while running an insert query.",
                    &self,
                )))?
            }
        };
        for (col, val) in map {
            if !skip_cols.contains(&col.as_str()) {
                column_names.push(col.to_string());
                ordered_vals.push(val);
                qmarks.push("?");
            }
        }
        let query_str = format!(
            "insert into {} ({}) values ({}) returning *;",
            Self::table_name(),
            column_names.join(","),
            qmarks.join(","),
        );
        let query =
            bind_values(&query_str, &ordered_vals).ok_or(serde_json::Error::custom(format!(
                "Insert query: cannot parse attributes of {:?} into Sqlite compatible types",
                &self
            )))?;
        Ok(query.fetch_one(pool).await?)
    }

    /// Inserts or updates a record in the table depending on whether a conflict occurs on a specific column.
    ///
    /// # Arguments
    /// - pool: A reference to a sqlx::SqlitePool used for database interaction.
    /// - skip_cols: A list of column names to skip during the insertion. This can be useful for
    /// skipping columns that you would like to be set to their default value by the database. Eg
    /// automatically setting and incrementing the primary key.
    /// - conflict_col: The name of the column to check for conflicts (usually the primary key).
    ///
    /// # Returns
    /// - Result<Self, Self::Error>: Returns the upserted model instance on success, otherwise returns an error.
    ///
    /// # Errors
    /// - Returns Self::Error if the database operation fails.
    async fn upsert(
        &self,
        pool: &sqlx::SqlitePool,
        skip_cols: &[&str],
        conflict_col: &str,
    ) -> Result<Self, Self::Error>
    where
        Self: Sized + for<'r> FromRow<'r, SqliteRow> + Serialize + Unpin + Send + Debug,
    {
        let mut column_names = Vec::new();
        let mut ordered_vals = Vec::new();
        let mut qmarks = Vec::new();
        let mut update_clause = Vec::new();
        let map = match serde_json::to_value(self)? {
            serde_json::Value::Object(m) => m,
            _ => {
                return Err(serde_json::Error::custom(format!(
                    "Failed to serialize {:?} into a map while running an upsert query.",
                    &self
                )))?
            }
        };
        for (col, val) in map {
            if !skip_cols.contains(&col.as_str()) {
                column_names.push(col.to_string());
                ordered_vals.push(val);
                qmarks.push("?");
                update_clause.push(format!("{} = ?", col));
            }
        }
        let query_str = format!(
            "insert into {} ({}) values ({}) on conflict({}) do update set {} returning *;",
            Self::table_name(),
            column_names.join(","),
            qmarks.join(","),
            conflict_col,
            update_clause.join(","),
        );

        let mut vals = Vec::new();
        for _ in 0..2 {
            ordered_vals.iter().for_each(|v| vals.push(v.to_owned()));
        }
        let query = bind_values(&query_str, &vals).ok_or(serde_json::Error::custom(format!(
            "Upsert: cannot parse attributes of {:?} into Sqlite compatible types",
            &self
        )))?;
        Ok(query.fetch_one(pool).await?)
    }

    /// Selects a single record from the table based on the specified column and value.
    ///
    /// # Arguments
    /// - pool: A reference to a sqlx::SqlitePool used for database interaction.
    /// - col: The name of the column to filter by.
    /// - val: The value to filter by, wrapped in BasicType.
    ///
    /// # Returns
    /// - Result<Self, Self::Error>: Returns the selected model instance on success, otherwise returns an error.
    ///
    /// # Errors
    /// - Returns Self::Error if the database operation fails or if no record matches the filter
    /// or some other sqlx::Error occurs.
    async fn select() -> QueryBuilder<Self>
    where
        Self: Sized + for<'r> FromRow<'r, SqliteRow> + Unpin + Send,
    {
        QueryBuilder::<Self> {
            base_clause: format!("select * from {}", sanitize_name(Self::table_name())),
            where_clause: "".to_string(),
            vals: Vec::new(),
        }
    }

    /// Deletes a single record from the table based on the specified column and value and returns the deleted model instance.
    ///
    /// # Arguments
    /// - pool: A reference to a sqlx::SqlitePool used for database interaction.
    /// - col: The name of the column to filter by.
    /// - val: The value to filter by, wrapped in BasicType.
    ///
    /// # Returns
    /// - Result<Vec<Self>, Self::Error>: Returns the deleted model instance on success, otherwise returns an error.
    ///
    /// # Errors
    /// - Returns Self::Error if the database operation fails or if no record matches the filter.
    async fn delete(
        pool: &sqlx::SqlitePool,
        col: &str,
        val: serde_json::Value,
    ) -> Result<Vec<Self>, Self::Error>
    where
        Self: Sized + for<'r> FromRow<'r, SqliteRow> + Unpin + Send,
    {
        let query_str = format!(
            "delete from {} where {} = ? returning *;",
            Self::table_name(),
            col
        );
        let vals = vec![val];
        let query = bind_values(&query_str, &vals).ok_or(serde_json::Error::custom(format!(
            "delete: cannot parse {} into Sqlite compatible type",
            &vals.get(0).ok_or(serde_json::Error::custom(
                "delete: vec of vals should have extactly 1 item. Found none"
            ))?
        )))?;
        Ok(query.fetch_all(pool).await?)
    }
}

#[cfg(test)]
mod tests {
    use async_trait::async_trait;
    use serde::Serialize;
    use sqlx::prelude::FromRow;

    use super::SqliteModel;

    #[derive(Debug)]
    enum Error {
        SqlxError(sqlx::Error),
        SerdeJsonError(serde_json::Error),
    }

    impl std::fmt::Display for Error {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl std::error::Error for Error {}

    impl From<sqlx::Error> for Error {
        fn from(value: sqlx::Error) -> Self {
            Error::SqlxError(value)
        }
    }

    impl From<serde_json::Error> for Error {
        fn from(value: serde_json::Error) -> Self {
            Error::SerdeJsonError(value)
        }
    }

    #[derive(Debug, FromRow, Serialize)]
    struct TestModel {
        pub id: i64,
        pub name: String,
        pub passwd: Vec<u8>,
        pub created_at: i64,
    }

    #[async_trait]
    impl SqliteModel for TestModel {
        type Error = Error;
    }

    async fn create_table(pool: &sqlx::SqlitePool) -> Result<(), sqlx::Error> {
        let query_str = format!(
            r"create table if not exists TestModel (
                    id integer primary key, 
                    name text not null, 
                    passwd blob not null,
                    created_at integer not null default (strftime('%s', 'now'))
                );",
        );

        sqlx::query(&query_str).execute(pool).await?;
        Ok(())
    }

    #[tokio::test]
    async fn test_create_table() {
        let pool = sqlx::SqlitePool::connect(":memory:").await.unwrap();
        create_table(&pool).await.unwrap();
    }

    #[tokio::test]
    async fn test_insert() {
        let pool = sqlx::SqlitePool::connect(":memory:").await.unwrap();
        create_table(&pool).await.unwrap();
        let test = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![1, 2, 3, 4],
            created_at: 1,
        };

        test.insert(&pool, &["id"]).await.unwrap();
        let res: TestModel = sqlx::query_as("select * from TestModel")
            .fetch_one(&pool)
            .await
            .unwrap();

        assert_eq!(res.id, 1);
        assert_eq!(res.name, test.name);
        assert_eq!(res.passwd, test.passwd);
        assert_eq!(res.created_at, test.created_at);
    }

    #[tokio::test]
    async fn test_upsert() {
        let pool = sqlx::SqlitePool::connect(":memory:").await.unwrap();
        create_table(&pool).await.unwrap();
        let mut test = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![1, 2, 3, 4],
            created_at: 1,
        };

        test.upsert(&pool, &["id"], "id").await.unwrap();
        let res: TestModel = sqlx::query_as("select * from TestModel")
            .fetch_one(&pool)
            .await
            .unwrap();

        assert_eq!(res.id, 1);
        assert_eq!(res.name, test.name);
        assert_eq!(res.passwd, test.passwd);
        assert_eq!(res.created_at, test.created_at);

        test = TestModel {
            id: 1,
            name: "test".to_string(),
            passwd: vec![4, 3, 2, 1, 0],
            created_at: 2,
        };
        test.upsert(&pool, &[], "id").await.unwrap();
        let res: Vec<TestModel> = sqlx::query_as("select * from TestModel")
            .fetch_all(&pool)
            .await
            .unwrap();

        assert_eq!(res.len(), 1);
        let res = res.get(0).unwrap();
        assert_eq!(res.id, 1);
        assert_eq!(res.name, "test".to_string());
        assert_eq!(res.passwd, vec![4, 3, 2, 1, 0]);
        assert_eq!(res.created_at, 2);

        test = TestModel {
            id: 18,
            name: "another".to_string(),
            passwd: vec![9, 8, 7, 6],
            created_at: 3,
        };
        test.upsert(&pool, &[], "id").await.unwrap();
        let res: Vec<TestModel> = sqlx::query_as("select * from TestModel")
            .fetch_all(&pool)
            .await
            .unwrap();

        assert_eq!(res.len(), 2);
        let (first, sec) = (res.get(0).unwrap(), res.get(1).unwrap());
        assert_eq!(first.id, 1);
        assert_eq!(first.name, "test".to_string());
        assert_eq!(first.passwd, vec![4, 3, 2, 1, 0]);
        assert_eq!(first.created_at, 2);
        assert_eq!(sec.id, 18);
        assert_eq!(sec.name, "another".to_string());
        assert_eq!(sec.passwd, vec![9, 8, 7, 6]);
        assert_eq!(sec.created_at, 3);
    }

    #[tokio::test]
    async fn test_select_one() {
        let pool = sqlx::SqlitePool::connect(":memory:").await.unwrap();
        create_table(&pool).await.unwrap();
        let test = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![1, 2, 3, 4],
            created_at: 1,
        };
        test.upsert(&pool, &["id"], "id").await.unwrap();

        let res = TestModel::select_one(&pool, "id", 1.into()).await.unwrap();
        assert_eq!(res.id, 1);
        assert_eq!(res.name, test.name);
        assert_eq!(res.passwd, test.passwd);
        assert_eq!(res.created_at, test.created_at);
    }

    #[tokio::test]
    async fn test_select_many() {
        let pool = sqlx::SqlitePool::connect(":memory:").await.unwrap();
        create_table(&pool).await.unwrap();
        let test = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![1, 2, 3, 4],
            created_at: 1,
        };
        let test1 = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![4, 3, 2, 1, 0],
            created_at: 2,
        };
        test.upsert(&pool, &["id"], "id").await.unwrap();
        test1.upsert(&pool, &["id"], "id").await.unwrap();

        let res = TestModel::select_many(&pool, "id", 1.into()).await.unwrap();
        assert_eq!(res.len(), 1);
        let res = TestModel::select_many(&pool, "name", "Test".into())
            .await
            .unwrap();

        assert_eq!(res.len(), 2);
        let (res1, res2) = (res.get(0).unwrap(), res.get(1).unwrap());
        assert_eq!(res1.id, 1);
        assert_eq!(res1.name, test.name);
        assert_eq!(res1.passwd, test.passwd);
        assert_eq!(res1.created_at, test.created_at);
        assert_eq!(res2.id, 2);
        assert_eq!(res2.name, test1.name);
        assert_eq!(res2.passwd, test1.passwd);
        assert_eq!(res2.created_at, test1.created_at);
    }

    #[tokio::test]
    async fn test_delete() {
        let pool = sqlx::SqlitePool::connect(":memory:").await.unwrap();
        create_table(&pool).await.unwrap();
        let test = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![1, 2, 3, 4, 5, 6, 7],
            created_at: 1,
        };
        let test1 = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![4, 3, 2, 1, 0],
            created_at: 2,
        };
        test.upsert(&pool, &["id"], "id").await.unwrap();
        test1.upsert(&pool, &["id"], "id").await.unwrap();

        let res = TestModel::delete(&pool, "id", 1.into()).await.unwrap();
        assert_eq!(res.len(), 1);
        let res = res.get(0).unwrap();
        assert_eq!(res.id, 1);
        assert_eq!(res.name, test.name);
        assert_eq!(res.passwd, test.passwd);
        assert_eq!(res.created_at, test.created_at);

        let res: Vec<TestModel> = sqlx::query_as("select * from TestModel")
            .fetch_all(&pool)
            .await
            .unwrap();

        assert_eq!(res.len(), 1);
        let res2 = res.get(0).unwrap();
        assert_eq!(res2.id, 2);
        assert_eq!(res2.name, test1.name);
        assert_eq!(res2.passwd, test1.passwd);
        assert_eq!(res2.created_at, test1.created_at);

        let test2 = TestModel {
            id: 18,
            name: "Test".to_string(),
            passwd: vec![4, 8, 9, 0, 5, 6, 1, 3],
            created_at: 3,
        };
        test2.upsert(&pool, &["id"], "id").await.unwrap();

        let res = TestModel::delete(&pool, "name", "Test".into())
            .await
            .unwrap();
        assert_eq!(res.len(), 2);
        let (res1, res2) = (res.get(0).unwrap(), res.get(1).unwrap());
        assert_eq!(res1.id, 2);
        assert_eq!(res1.name, test1.name);
        assert_eq!(res1.passwd, test1.passwd);
        assert_eq!(res1.created_at, test1.created_at);
        assert_eq!(res2.id, 3);
        assert_eq!(res2.name, test2.name);
        assert_eq!(res2.passwd, test2.passwd);
        assert_eq!(res2.created_at, test2.created_at);

        let res: Vec<TestModel> = sqlx::query_as("select * from TestModel")
            .fetch_all(&pool)
            .await
            .unwrap();
        assert_eq!(res.len(), 0);
    }
}
