//! Vectors with a length floor, for the places F#'s grammar has one.

/// A vector with at least one element.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Vec1<T>(Vec<T>);

impl<T> Vec1<T> {
    /// `first` followed by `rest`.
    pub fn new(first: T, rest: Vec<T>) -> Self {
        let mut v = Vec::with_capacity(1 + rest.len());
        v.push(first);
        v.extend(rest);
        Vec1(v)
    }

    /// `items`, or `None` if it is empty.
    pub fn from_vec(items: Vec<T>) -> Option<Self> {
        if items.is_empty() {
            None
        } else {
            Some(Vec1(items))
        }
    }

    /// The elements, in order.
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }

    /// The elements, in order.
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

/// A vector with at least two elements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Vec2<T>(Vec<T>);

impl<T> Vec2<T> {
    /// `first`, then `second`, then `rest`.
    pub fn new(first: T, second: T, rest: Vec<T>) -> Self {
        let mut v = Vec::with_capacity(2 + rest.len());
        v.push(first);
        v.push(second);
        v.extend(rest);
        Vec2(v)
    }

    /// `items`, or `None` if it has fewer than two elements.
    pub fn from_vec(items: Vec<T>) -> Option<Self> {
        if items.len() < 2 {
            None
        } else {
            Some(Vec2(items))
        }
    }

    /// The elements, in order.
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }

    /// The elements, in order.
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}
