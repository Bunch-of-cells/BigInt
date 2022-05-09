use std::{
    cmp::Ordering,
    fmt::{Debug, Display},
    ops::{Add, Mul, Neg, Sub},
    str::FromStr,
};

mod error;
use error::{BigIntConvertionError, ParseBigIntError};

#[derive(Default, Clone)]
pub struct BigInt {
    signed: bool,
    value: Vec<u8>,
}

macro_rules! impl_bigint_from_primitive {
    (+ $($func_name: ident, $type: ty),*) => {
        $(
            impl BigInt {
                pub fn $func_name(value: $type) -> BigInt {
                    let mut digits = vec![];
                    let mut new = value;
                    while new != 0 {
                        digits.push((new % 10).try_into().unwrap());
                        new /= 10;
                    }
                    BigInt {
                        signed: false,
                        value: digits,
                    }
                }
            }

            impl From<$type> for BigInt {
                fn from(value: $type) -> BigInt {
                    BigInt::$func_name(value)
                }
            }

            impl TryInto<$type> for BigInt {
                type Error = BigIntConvertionError;

                fn try_into(self) -> Result<$type, Self::Error> {
                    self.value.into_iter().try_fold(0, |acc: $type, a| {
                        match acc.checked_mul(10).and_then(|acc| acc.checked_add(a.into())) {
                            Some(acc) => Ok(acc),
                            None => Err(BigIntConvertionError::OVERFLOW),
                        }
                    })
                }
            }
        )*
    };

    (- $($func_name: ident, $type: ty),*) => {
        $(
            impl BigInt {
                pub fn $func_name(value: $type) -> BigInt {
                    let mut digits = vec![];
                    let mut new = value;
                    while new != 0 {
                        digits.push((new % 10).abs().try_into().unwrap());
                        new /= 10;
                    }
                    BigInt {
                        signed: value.is_negative(),
                        value: digits,
                    }
                }
            }

            impl From<$type> for BigInt {
                fn from(value: $type) -> BigInt {
                    BigInt::$func_name(value)
                }
            }

            impl TryInto<$type> for BigInt {
                type Error = BigIntConvertionError;

                fn try_into(self) -> Result<$type, Self::Error> {
                    self.value.into_iter().try_fold(0, |acc: $type, a| {
                        match acc.checked_mul(10).and_then(|acc| acc.checked_add(a.try_into().unwrap())) {
                            Some(acc) => Ok(acc),
                            None => Err(if acc.is_negative() { BigIntConvertionError::UNDERFLOW } else { BigIntConvertionError::OVERFLOW }),
                        }
                    }).map(|a| a * if self.signed { -1 } else { 1 })
                }
            }
        )*
    };
}

impl BigInt {
    pub fn new() -> BigInt {
        BigInt {
            signed: false,
            value: vec![],
        }
    }

    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use numbers::BigInt;
    /// assert!(BigInt::from_str("1234").is_ok());
    /// ```
    ///
    /// Passing a non-digit results in failure:
    ///
    /// ```
    /// use numbers::BigInt;
    /// assert!(BigInt::from_str("25sg").is_err());
    /// ```
    pub fn from_str(mut value: &str) -> Result<Self, ParseBigIntError> {
        if value.is_empty() {
            return Err(ParseBigIntError::EMPTY);
        }

        let signed = match value.as_bytes().first() {
            Some(b'+') => Some(false),
            Some(b'-') => Some(true),
            None => return Err(ParseBigIntError::EMPTY),
            Some(c) if !c.is_ascii_digit() => return Err(ParseBigIntError::INVALID),
            _ => None,
        };

        let signed = match signed {
            Some(s) => {
                value = &value[1..];
                s
            }
            None => false,
        };

        let mut new = Vec::new();

        for val in value
            .chars()
            .map(|c| {
                char::to_digit(c, 10)
                    .map(|i| i.try_into().unwrap())
                    .ok_or(ParseBigIntError::INVALID)
            })
            .rev()
        {
            new.push(val?);
        }

        Ok(BigInt { signed, value: new })
    }

    fn unsigned_cmp(&self, other: &BigInt) -> Ordering {
        if self.signed != other.signed {
            return self.signed.cmp(&other.signed);
        }

        if self.value.len() != other.value.len() {
            return self.value.len().cmp(&other.value.len());
        }

        for i in (0..self.value.len()).rev() {
            if self.value[i] != other.value[i] {
                return self.value[i].cmp(&other.value[i]);
            }
        }

        Ordering::Equal
    }
}

impl_bigint_from_primitive!(+
    from_u8, u8, from_u16, u16, from_u32, u32, from_u64, u64, from_u128, u128,
    from_usize, usize
);

impl_bigint_from_primitive!(
    -from_i8, i8, from_i16, i16, from_i32, i32, from_i64, i64, from_i128, i128, from_isize, isize
);

impl FromStr for BigInt {
    type Err = ParseBigIntError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Self::from_str(value)
    }
}

impl Display for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            if self.signed { "-" } else { "" },
            self.value
                .iter()
                .map(|a| (a + b'0') as char)
                .rev()
                .collect::<String>()
        )
    }
}

impl Debug for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Add for BigInt {
    type Output = BigInt;

    fn add(self, other: BigInt) -> BigInt {
        if self.signed != other.signed {
            return self - -other;
        }

        let mut result = vec![];
        let mut carry = 0;

        let (a, b) = if self.value.len() > other.value.len() {
            (self.value, other.value)
        } else {
            (other.value, self.value)
        };

        for i in 0..b.len() {
            let digit = a[i] + b[i] + carry;
            result.push(digit % 10);
            carry = digit / 10;
        }

        for a in a.iter().skip(b.len()) {
            let digit = *a + carry;
            result.push(digit % 10);
            carry = digit / 10;
        }

        if carry > 0 {
            result.push(carry);
        }

        BigInt {
            value: result,
            ..self
        }
    }
}

impl Sub for BigInt {
    type Output = BigInt;

    fn sub(self, other: BigInt) -> BigInt {
        if self.signed != other.signed {
            return self + -other;
        }

        let mut result = vec![];
        let mut borrow = false;

        let mut signed = self < other;

        let (mut a, b) = if self.unsigned_cmp(&other) == Ordering::Greater {
            (self.value, other.value)
        } else {
            (other.value, self.value)
        };

        for i in 0..b.len() {
            if borrow {
                if a[i] == 0 {
                    a[i] = 9;
                } else {
                    a[i] -= 1;
                    borrow = false;
                }
            }
            if b[i] > a[i] {
                borrow = true;
                a[i] += 10;
            }
            let digit = a[i] - b[i];
            result.push(digit);
        }

        for a in a.iter_mut().skip(b.len()) {
            if borrow {
                if *a == 0 {
                    *a = 9;
                } else {
                    *a -= 1;
                    borrow = false;
                }
            }
            let digit = *a;
            result.push(digit);
        }

        result.truncate(
            result
                .iter()
                .rev()
                .position(|&x| x != 0)
                .map(|i| result.len() - i)
                .unwrap_or(0),
        );

        if result.is_empty() {
            signed = false
        }

        BigInt {
            value: result,
            signed,
        }
    }
}

impl Neg for BigInt {
    type Output = BigInt;

    fn neg(self) -> BigInt {
        BigInt {
            signed: !self.signed,
            ..self
        }
    }
}

impl Mul for BigInt {
    type Output = BigInt;

    fn mul(self, other: BigInt) -> BigInt {
        let mut results = vec![];

        let (a, b) = if self.value.len() > other.value.len() {
            (self.value, other.value)
        } else {
            (other.value, self.value)
        };

        for (i, b) in b.iter().enumerate() {
            let mut res = vec![0; i];
            let mut carry = 0;

            for a in &a {
                let digit = a * b + carry;
                res.push(digit % 10);
                carry = digit / 10;
            }

            if carry > 0 {
                res.push(carry);
            }

            results.push(res);
        }

        results.sort_by_key(|b| std::cmp::Reverse(b.len()));

        let mut result = results
            .into_iter()
            .reduce(|a, b| {
                let mut result = vec![];
                let mut carry = 0;

                for i in 0..b.len() {
                    let digit = a[i] + b[i] + carry;
                    result.push(digit % 10);
                    carry = digit / 10;
                }

                for a in a.iter().skip(b.len()) {
                    let digit = *a + carry;
                    result.push(digit % 10);
                    carry = digit / 10;
                }

                if carry > 0 {
                    result.push(carry);
                }

                result
            })
            .unwrap_or_default();

        result.truncate(
            result
                .iter()
                .rev()
                .position(|&x| x != 0)
                .map(|i| result.len() - i)
                .unwrap_or(0),
        );

        let signed = if result.is_empty() {
            false
        } else {
            self.signed ^ other.signed
        };

        BigInt {
            value: result,
            signed,
        }
    }
}

impl PartialEq for BigInt {
    fn eq(&self, other: &BigInt) -> bool {
        if self.signed != other.signed {
            return false;
        }

        if self.value.len() != other.value.len() {
            return false;
        }

        for i in 0..self.value.len() {
            if self.value[i] != other.value[i] {
                return false;
            }
        }

        true
    }
}

impl Eq for BigInt {}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &BigInt) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigInt {
    fn cmp(&self, other: &BigInt) -> Ordering {
        if self.signed != other.signed {
            return self.signed.cmp(&other.signed);
        }

        if self.value.len() != other.value.len() {
            let ord = self.value.len().cmp(&other.value.len());
            if self.signed {
                return ord.reverse();
            }
            return ord;
        }

        for i in (0..self.value.len()).rev() {
            if self.value[i] != other.value[i] {
                let ord = self.value[i].cmp(&other.value[i]);
                if self.signed {
                    return ord.reverse();
                }
                return ord;
            }
        }

        Ordering::Equal
    }
}

impl From<BigInt> for bool {
    fn from(value: BigInt) -> bool {
        value.value.iter().all(|a| *a == 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Signed = i128;
    type Unsigned = u128;

    fn test_random_add_singned() {
        let num1 = rand::random::<Signed>();
        let num2 = rand::random::<Signed>().clamp(
            if num1 > 0 {
                Signed::MIN
            } else {
                Signed::MIN - num1
            },
            if num1 < 0 {
                Signed::MAX
            } else {
                Signed::MAX - num1 - 1
            },
        );

        println!("{} + {}", num1, num2);

        let bigint1 = BigInt::from(num1);
        let bigint2 = BigInt::from(num2);

        assert_eq!(BigInt::from(num1 + num2), bigint1 + bigint2);
    }

    fn test_random_sub_signed() {
        let num1 = rand::random::<Signed>();
        let num2 = rand::random::<Signed>().clamp(
            if num1 < 0 {
                Signed::MIN
            } else {
                Signed::MIN + num1 + 1
            },
            if num1 > 0 {
                Signed::MAX
            } else {
                Signed::MAX + num1
            },
        );

        println!("{} - {}", num1, num2);

        let bigint1 = BigInt::from(num1);
        let bigint2 = BigInt::from(num2);

        assert_eq!(BigInt::from(num1 - num2), bigint1 - bigint2);
    }

    fn test_random_mul_signed() {
        let num1 = rand::random::<Signed>();
        let div = Signed::checked_div(127, num1).unwrap_or(0);
        let num2 = rand::random::<Signed>().clamp(
            if num1 > 0 { -1 } else { 1 } * div,
            if num1 < 0 { -1 } else { 1 } * div,
        );

        let bigint1 = BigInt::from(num1);
        let bigint2 = BigInt::from(num2);

        println!("{} * {}", num1, num2);

        assert_eq!(BigInt::from(num1 * num2), bigint1 * bigint2);
    }

    fn test_random_add_unsingned() {
        let num1 = rand::random::<Unsigned>();
        let num2 = rand::random::<Unsigned>().clamp(0, Unsigned::MAX - num1);

        println!("{} + {}", num1, num2);

        let bigint1 = BigInt::from(num1);
        let bigint2 = BigInt::from(num2);

        assert_eq!(BigInt::from(num1 + num2), bigint1 + bigint2);
    }

    fn test_random_sub_unsigned() {
        let num1 = rand::random::<Unsigned>();
        let num2 = rand::random::<Unsigned>().clamp(0, num1);

        println!("{} - {}", num1, num2);

        let bigint1 = BigInt::from(num1);
        let bigint2 = BigInt::from(num2);

        assert_eq!(BigInt::from(num1 - num2), bigint1 - bigint2);
    }

    fn test_random_mul_unsigned() {
        let num1 = rand::random::<Unsigned>();
        let num2 =
            rand::random::<Unsigned>().clamp(0, Unsigned::MAX.checked_div(num1).unwrap_or(0));

        let bigint1 = BigInt::from(num1);
        let bigint2 = BigInt::from(num2);

        println!("{} * {}", num1, num2);

        assert_eq!(BigInt::from(num1 * num2), bigint1 * bigint2);
    }

    #[test]
    fn test_arith() {
        for _ in 0..1000 {
            test_random_add_singned();
            test_random_sub_signed();
            test_random_mul_signed();
            test_random_add_unsingned();
            test_random_sub_unsigned();
            test_random_mul_unsigned();
        }
    }

    #[test]
    fn from_str() {
        let num = rand::random::<Signed>();
        assert_eq!(BigInt::from_str(&num.to_string()), Ok(BigInt::from(num)));

        let num = rand::random::<Unsigned>();
        assert_eq!(BigInt::from_str(&num.to_string()), Ok(BigInt::from(num)));
    }
}
