//! 年月ライブラリ
//!
//! このクレートは[time](https://crates.io/crates/time)に依存しています。
//!
//! 年は1年から9999年まで対応しています。

use std::cmp::Ordering;

use time::{macros::date, Date, Month};

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
    #[error("The YearMonth specified when constructing an iterator must be greater or equal")]
    DateIteratorError,
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

    /// 年月の日付の数を返します。
    ///
    /// # 戻り値
    ///
    /// 日付の数
    pub fn number_of_days(&self) -> u8 {
        let month = Month::try_from(self.month).unwrap();
        month.length(self.year)
    }

    /// 年月の最初の日付を返します。
    ///
    /// # 戻り値
    ///
    /// 年月の最初の日付
    pub fn first(&self) -> Date {
        Date::from_calendar_date(self.year, Month::try_from(self.month).unwrap(), 1).unwrap()
    }

    /// 年月の最後の日付を返します。
    ///
    /// # 戻り値
    ///
    /// 年月の最後の日付
    pub fn last(&self) -> Date {
        let days = self.number_of_days();
        Date::from_calendar_date(self.year, Month::try_from(self.month).unwrap(), days).unwrap()
    }

    /// TODO: implement the iter method

    /// 年月の日付を走査するイテレータを返します。
    ///
    /// # 戻り値
    ///
    /// 年月の日付を走査するイテレータ
    pub fn dates(&self) -> DateIterator {
        DateIterator::new(self.first(), self.last())
    }

    /// 年月の最初の日付から、引数の年月の最後の日付までを走査するイテレータを返します。
    ///
    /// # 引数
    ///
    /// * `to` - 走査する最後の日付を取得する年月、Noneの場合はイテレーターは`9999-12-31`まで生成
    ///
    /// # 戻り値
    ///
    /// 年月の最初の日付から、日付を走査するイテレーター
    pub fn dates_to_year_month(&self, to: Option<YearMonth>) -> YearMonthResult<DateIterator> {
        // 引数toの年月は、この年月以降の年月でなければならない
        if to.is_some() && to.unwrap() < *self {
            return Err(YearMonthError::DateIteratorError);
        }
        let last = match to {
            Some(to) => to.last(),
            None => date!(9999 - 12 - 31),
        };
        Ok(DateIterator::new(self.first(), last))
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

/// 日付イテレーター
pub struct DateIterator {
    cur: Option<Date>,
    end: Date,
}

impl DateIterator {
    fn new(begin: Date, end: Date) -> Self {
        Self {
            cur: Some(begin),
            end,
        }
    }
}

impl Iterator for DateIterator {
    type Item = Date;

    fn next(&mut self) -> Option<Self::Item> {
        self.cur?;
        match self.cur.unwrap() <= self.end {
            true => {
                let result = self.cur;
                self.cur = self.cur.unwrap().next_day();
                result
            }
            false => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr as _;

    use time::macros::date;

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

    #[rstest::rstest]
    #[case(YearMonth::new(2025, 1).unwrap(), 31)]
    #[case(YearMonth::new(2025, 2).unwrap(), 28)]
    #[case(YearMonth::new(2025, 3).unwrap(), 31)]
    #[case(YearMonth::new(2025, 4).unwrap(), 30)]
    #[case(YearMonth::new(2025, 5).unwrap(), 31)]
    #[case(YearMonth::new(2025, 6).unwrap(), 30)]
    #[case(YearMonth::new(2025, 7).unwrap(), 31)]
    #[case(YearMonth::new(2025, 8).unwrap(), 31)]
    #[case(YearMonth::new(2025, 9).unwrap(), 30)]
    #[case(YearMonth::new(2025, 10).unwrap(), 31)]
    #[case(YearMonth::new(2025, 11).unwrap(), 30)]
    #[case(YearMonth::new(2025, 12).unwrap(), 31)]
    #[case(YearMonth::new(2024, 2).unwrap(), 29)]
    fn year_month_number_of_days(#[case] ym: YearMonth, #[case] expected: u8) {
        assert_eq!(ym.number_of_days(), expected);
    }

    #[test]
    fn year_month_first_ok() {
        let ym = YearMonth::new(2025, 2).unwrap();
        assert_eq!(ym.first(), date!(2025 - 02 - 1));
    }

    #[rstest::rstest]
    #[case(YearMonth::new(2025, 1).unwrap(), date!(2025 - 01 - 31))]
    #[case(YearMonth::new(2025, 2).unwrap(), date!(2025 - 02 - 28))]
    #[case(YearMonth::new(2025, 11).unwrap(), date!(2025 - 11 - 30))]
    #[case(YearMonth::new(2024, 2).unwrap(), date!(2024 - 02 - 29))]
    fn year_month_last_ok(#[case] ym: YearMonth, #[case] expected: Date) {
        assert_eq!(ym.last(), expected);
    }

    #[test]
    fn year_month_dates_ok() {
        let ym = YearMonth::new(2025, 2).unwrap();
        let expected_dates = [
            date!(2025 - 02 - 01),
            date!(2025 - 02 - 02),
            date!(2025 - 02 - 03),
            date!(2025 - 02 - 04),
            date!(2025 - 02 - 05),
            date!(2025 - 02 - 06),
            date!(2025 - 02 - 07),
            date!(2025 - 02 - 08),
            date!(2025 - 02 - 09),
            date!(2025 - 02 - 10),
            date!(2025 - 02 - 11),
            date!(2025 - 02 - 12),
            date!(2025 - 02 - 13),
            date!(2025 - 02 - 14),
            date!(2025 - 02 - 15),
            date!(2025 - 02 - 16),
            date!(2025 - 02 - 17),
            date!(2025 - 02 - 18),
            date!(2025 - 02 - 19),
            date!(2025 - 02 - 20),
            date!(2025 - 02 - 21),
            date!(2025 - 02 - 22),
            date!(2025 - 02 - 23),
            date!(2025 - 02 - 24),
            date!(2025 - 02 - 25),
            date!(2025 - 02 - 26),
            date!(2025 - 02 - 27),
            date!(2025 - 02 - 28),
        ];
        let dates = ym.dates().collect::<Vec<Date>>();
        assert_eq!(dates.len(), expected_dates.len());
        for (date, expected) in dates.iter().zip(expected_dates) {
            assert_eq!(*date, expected);
        }
    }

    #[test]
    fn dates_to_year_month_ok_when_specified_to() {
        let from = YearMonth::new(2023, 12).unwrap();
        let to = YearMonth::new(2024, 2).unwrap();
        let dates = from
            .dates_to_year_month(Some(to))
            .unwrap()
            .collect::<Vec<Date>>();
        // 2023年12月
        let december = dates
            .iter()
            .filter(|d| d.month() == Month::December)
            .collect::<Vec<&Date>>();
        assert_eq!(december.len(), 31);
        // 2023年1月
        let january = dates
            .iter()
            .filter(|d| d.month() == Month::January)
            .collect::<Vec<&Date>>();
        assert_eq!(january.len(), 31);
        // 2023年2月
        let february = dates
            .iter()
            .filter(|d| d.month() == Month::February)
            .collect::<Vec<&Date>>();
        assert_eq!(february.len(), 29);
    }

    #[test]
    fn dates_to_year_month_ok_when_not_specified_to() {
        let from = YearMonth::new(9999, 11).unwrap();
        let dates = from
            .dates_to_year_month(None)
            .unwrap()
            .collect::<Vec<Date>>();
        // 9999年11月
        let november = dates
            .iter()
            .filter(|d| d.month() == Month::November)
            .collect::<Vec<&Date>>();
        assert_eq!(november.len(), 30);
        // 9999年12月
        let december = dates
            .iter()
            .filter(|d| d.month() == Month::December)
            .collect::<Vec<&Date>>();
        assert_eq!(december.len(), 31);
    }

    #[test]
    fn dates_to_year_month_err() {
        let from = YearMonth::new(2025, 2).unwrap();
        let to = YearMonth::new(2025, 1).unwrap();
        assert_eq!(
            from.dates_to_year_month(Some(to)).err().unwrap(),
            YearMonthError::DateIteratorError
        );
    }
}
