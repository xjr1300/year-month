//! 年月ライブラリ
//!
//! このクレートは[time](https://crates.io/crates/time)に依存しています。
//!
//! 年は1年から9999年まで対応しています。

use std::cmp::Ordering;

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
    #[error("The year is out of range: {0}")]
    OutOfYearRange(i32),
}

/// 年月操作結果
pub type YearMonthResult<T> = Result<T, YearMonthError>;

/// 年の最小値
pub const MIN_YEAR: i32 = 1;
/// 年の最大値
pub const MAX_YEAR: i32 = 9999;

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

    /// 次の年月を返します。
    ///
    /// # 戻り値
    ///
    /// 次の年月
    pub fn next(&self) -> YearMonthResult<Self> {
        let mut year = self.year;
        let mut month = self.month + 1;
        if month == 13 {
            month = 1;
            year += 1;
        }
        match MAX_YEAR < year {
            true => Err(YearMonthError::OutOfYearRange(year)),
            false => Ok(Self { year, month }),
        }
    }

    /// 前の年月を返します。
    ///
    /// # 戻り値
    ///
    /// 前の年月
    pub fn prev(&self) -> YearMonthResult<Self> {
        let mut year = self.year;
        let mut month = self.month - 1;
        if month == 0 {
            month = 12;
            year -= 1;
        }
        match year < MIN_YEAR {
            true => Err(YearMonthError::OutOfYearRange(year)),
            false => Ok(Self { year, month }),
        }
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

impl std::fmt::Display for YearMonth {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-{:02}", self.year, self.month)
    }
}

impl Ord for YearMonth {
    fn cmp(&self, other: &Self) -> Ordering {
        let result = self.year.cmp(&other.year);
        if result != Ordering::Equal {
            return result;
        }
        self.month.cmp(&other.month)
    }
}

impl PartialOrd for YearMonth {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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
    #[case(10000, 1, YearMonthError::InvalidYear(10000))]
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

    #[rstest::rstest]
    #[case(YearMonth::new(1, 1).unwrap(), "1-01")]
    #[case(YearMonth::new(2025, 12).unwrap(), "2025-12")]
    fn year_month_to_string_ok(#[case] ym: YearMonth, #[case] expected: &str) {
        assert_eq!(ym.to_string(), expected);
    }

    #[rstest::rstest]
    #[case(YearMonth::new(2025, 1).unwrap(), YearMonth::new(2024, 12).unwrap(), Ordering::Greater)]
    #[case(YearMonth::new(2024, 12).unwrap(), YearMonth::new(2025, 1).unwrap(), Ordering::Less)]
    #[case(YearMonth::new(2025, 1).unwrap(), YearMonth::new(2025, 1).unwrap(), Ordering::Equal)]
    fn year_month_ord_ok(
        #[case] lhs: YearMonth,
        #[case] rhs: YearMonth,
        #[case] expected: Ordering,
    ) {
        assert_eq!(
            lhs.cmp(&rhs),
            expected,
            "lhs:{lhs}, rhs:{rhs}, expected:{expected:?}"
        );
    }

    #[rstest::rstest]
    #[case(YearMonth::new(1, 12).unwrap(), YearMonth::new(2, 1).unwrap())]
    #[case(YearMonth::new(2025, 2).unwrap(), YearMonth::new(2025, 3).unwrap())]
    #[case(YearMonth::new(9999, 11).unwrap(), YearMonth::new(9999, 12).unwrap())]
    fn year_month_next_ok(#[case] ym: YearMonth, #[case] expected: YearMonth) {
        assert_eq!(ym.next().unwrap(), expected);
    }

    #[test]
    fn year_month_next_err() {
        let ym = YearMonth::new(9999, 12).unwrap();
        assert_eq!(
            ym.next().err().unwrap(),
            YearMonthError::OutOfYearRange(10000)
        );
    }

    #[rstest::rstest]
    #[case(YearMonth::new(1, 12).unwrap(), YearMonth::new(1, 11).unwrap())]
    #[case(YearMonth::new(2025, 1).unwrap(), YearMonth::new(2024, 12).unwrap())]
    fn year_month_prev_ok(#[case] ym: YearMonth, #[case] expected: YearMonth) {
        assert_eq!(ym.prev().unwrap(), expected);
    }

    #[test]
    fn year_month_prev_err() {
        let ym = YearMonth::new(1, 1).unwrap();
        assert_eq!(ym.prev().err().unwrap(), YearMonthError::OutOfYearRange(0));
    }
}
