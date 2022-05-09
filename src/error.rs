use std::error::Error;
use std::fmt::{Debug, Display};

#[derive(Clone, PartialEq, Eq)]
pub struct ParseBigIntError {
    kind: ParseBigIntErrorKind,
}

impl ParseBigIntError {
    pub(crate) const INVALID: Self = Self {
        kind: ParseBigIntErrorKind::Invalid,
    };

    pub(crate) const EMPTY: Self = Self {
        kind: ParseBigIntErrorKind::Empty,
    };
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ParseBigIntErrorKind {
    Invalid,
    Empty,
}

impl Display for ParseBigIntError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl Debug for ParseBigIntError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl Error for ParseBigIntError {
    fn description(&self) -> &str {
        match self.kind {
            ParseBigIntErrorKind::Invalid => "Invalid character found while parsing",
            ParseBigIntErrorKind::Empty => "Empty string",
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct BigIntConvertionError {
    kind: BigIntConvertionErrorKind,
}

impl BigIntConvertionError {
    pub(crate) const OVERFLOW: Self = Self {
        kind: BigIntConvertionErrorKind::Overflow,
    };

    pub(crate) const UNDERFLOW: Self = Self {
        kind: BigIntConvertionErrorKind::Underflow,
    };
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BigIntConvertionErrorKind {
    Overflow,
    Underflow,
}

impl Display for BigIntConvertionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl Debug for BigIntConvertionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl Error for BigIntConvertionError {
    fn description(&self) -> &str {
        match self.kind {
            BigIntConvertionErrorKind::Overflow => "Value is too big",
            BigIntConvertionErrorKind::Underflow => "Value is too small",
        }
    }
}
