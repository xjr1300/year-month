//! 年月ライブラリ
//!
//! このクレートは[time](https://crates.io/crates/time)に依存しています。
//!
//! 年は1年から9998年まで対応しています。

/// 年月
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct YearMonth {
    /// 年
    pub year: i32,
    /// 月
    pub month: u8,
}

/// 年月操作エラー
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum YearMonthError {
    #[error("The year is invalid: {0}")]
    InvalidYear(i32),
    #[error("The month is invalid: {0}")]
    InvalidMonth(u8),
    #[error("The string format is invalid: {0}")]
    InvalidFormat(String),
    #[error("The string format of year is invalid: {0}")]
    InvalidYearFormat(String),
    #[error("The string format of month is invalid: {0}")]
    InvalidMonthFormat(String),
}

/// 年月操作結果
pub type YearMonthResult<T> = Result<T, YearMonthError>;

/// 年の最小値
pub const MIN_YEAR: i32 = 1;
/// 年の最大値
pub const MAX_YEAR: i32 = 9998;

impl YearMonth {
    /// コンストラクタ
    ///
    /// # 引数
    ///
    /// * `year` - 年
    /// * `month` - 月
    pub fn new(year: i32, month: u8) -> YearMonthResult<Self> {
        if !(MIN_YEAR..=MAX_YEAR).contains(&year) {
            return Err(YearMonthError::InvalidYear(year));
        }
        if !(1..=12).contains(&month) {
            return Err(YearMonthError::InvalidMonth(month));
        }
        Ok(Self { year, month })
    }
}

impl std::str::FromStr for YearMonth {
    type Err = YearMonthError;

    /// 年と月をハイフンでつなげた文字列から年月を構築する。
    ///
    /// # 引数
    ///
    /// * `s` - 年月を生成する文字列
    ///
    /// # 戻り値
    ///
    /// 年月
    fn from_str(s: &str) -> YearMonthResult<Self> {
        let (year, month) = s
            .split_once('-')
            .ok_or(YearMonthError::InvalidFormat(s.into()))?;
        let year = year
            .parse::<i32>()
            .map_err(|_| YearMonthError::InvalidYearFormat(year.into()))?;
        let month = month
            .parse::<u8>()
            .map_err(|_| YearMonthError::InvalidMonthFormat(month.into()))?;
        Self::new(year, month)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rstest::rstest]
    #[case(1, 1)]
    #[case(9998, 12)]
    #[case(2025, 2)]
    fn year_month_new_ok(#[case] year: i32, #[case] month: u8) {
        let ym = YearMonth::new(year, month);
        assert!(ym.is_ok());
        let ym = ym.unwrap();
        assert_eq!(ym.year, year);
        assert_eq!(ym.month, month);
    }

    #[rstest::rstest]
    #[case(0, 12, YearMonthError::InvalidYear(0))]
    #[case(9999, 1, YearMonthError::InvalidYear(9999))]
    #[case(2025, 0, YearMonthError::InvalidMonth(0))]
    #[case(2025, 13, YearMonthError::InvalidMonth(13))]
    fn year_month_new_err(#[case] year: i32, #[case] month: u8, #[case] expected: YearMonthError) {
        let ym = YearMonth::new(year, month);
        let error = ym.err().unwrap();
        assert_eq!(error, expected);
    }

    #[rstest::rstest]
    #[case("1-1", YearMonth::new(1,1).unwrap())]
    #[case("1-01", YearMonth::new(1,1).unwrap())]
    #[case("2025-02", YearMonth::new(2025,2).unwrap())]
    fn year_month_from_str_ok(#[case] s: &str, #[case] expected: YearMonth) {
        use std::str::FromStr as _;
        assert_eq!(YearMonth::from_str(s).unwrap(), expected);
    }

    #[rstest::rstest]
    #[case("2025", YearMonthError::InvalidFormat("2025".into()))]
    #[case("-1", YearMonthError::InvalidYearFormat("".into()))]
    #[case("xxxx-1", YearMonthError::InvalidYearFormat("xxxx".into()))]
    #[case("2025-", YearMonthError::InvalidMonthFormat("".into()))]
    #[case("2025-xx", YearMonthError::InvalidMonthFormat("xx".into()))]
    fn year_month_from_str_err(#[case] s: &str, #[case] expected: YearMonthError) {
        use std::str::FromStr as _;
        assert_eq!(YearMonth::from_str(s).err().unwrap(), expected);
    }
}
