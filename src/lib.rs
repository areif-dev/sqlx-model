mod sqlite;

pub use sqlite::SqliteModel;
use sqlx::SqlitePool;

pub fn sanitize_name<S: ToString>(input: S) -> String {
    let input = input.to_string();
    format!(
        "`{}`",
        input
            .chars()
            .filter(|c| c.is_alphanumeric() || *c == '_')
            .collect::<String>()
    )
}

#[derive(Debug, Clone)]
pub enum BasicType {
    Null,
    Integer(i64),
    Real(f64),
    Text(String),
    Blob(Vec<u8>),
}

impl From<bool> for BasicType {
    fn from(value: bool) -> Self {
        match value {
            true => BasicType::Integer(1),
            false => BasicType::Integer(0),
        }
    }
}

impl From<i64> for BasicType {
    fn from(value: i64) -> Self {
        BasicType::Integer(value)
    }
}

impl From<i32> for BasicType {
    fn from(value: i32) -> Self {
        BasicType::Integer(value as i64)
    }
}

impl From<u32> for BasicType {
    fn from(value: u32) -> Self {
        BasicType::Integer(value as i64)
    }
}

impl From<i16> for BasicType {
    fn from(value: i16) -> Self {
        BasicType::Integer(value as i64)
    }
}

impl From<u16> for BasicType {
    fn from(value: u16) -> Self {
        BasicType::Integer(value as i64)
    }
}

impl From<i8> for BasicType {
    fn from(value: i8) -> Self {
        BasicType::Integer(value as i64)
    }
}

impl From<u8> for BasicType {
    fn from(value: u8) -> Self {
        BasicType::Integer(value as i64)
    }
}

impl From<f64> for BasicType {
    fn from(value: f64) -> Self {
        BasicType::Real(value)
    }
}

impl From<String> for BasicType {
    fn from(value: String) -> Self {
        BasicType::Text(value)
    }
}

impl From<&str> for BasicType {
    fn from(value: &str) -> Self {
        BasicType::Text(value.to_string())
    }
}

impl From<Vec<u8>> for BasicType {
    fn from(value: Vec<u8>) -> Self {
        BasicType::Blob(value)
    }
}

impl From<&[u8]> for BasicType {
    fn from(value: &[u8]) -> Self {
        BasicType::Blob(value.to_vec())
    }
}

impl<T> From<Option<T>> for BasicType
where
    T: Into<BasicType>,
{
    fn from(value: Option<T>) -> Self {
        match value {
            Some(v) => v.into(),
            None => BasicType::Null,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sanitize() {
        assert_eq!(&sanitize_name("'; drop table Users;"), "`droptableUsers`");
        assert_eq!(&sanitize_name("ValidName"), "`ValidName`");
        assert_eq!(&sanitize_name("Valid_Name"), "`Valid_Name`");
        assert_eq!(&sanitize_name("; select * from Test;"), "`selectfromtest`");
    }
}
