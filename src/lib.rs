use std::marker::PhantomData;

/// A trait used to mark a certain value of a type as a sentinel.
pub trait Sentinel<T>
where
    T: PartialEq,
{
    /// Produce the sentinel value
    fn sentinel() -> T;

    /// Check if the passed value is the sentinel
    fn is_sentinel(t: &T) -> bool {
        *t == Self::sentinel()
    }
}

/// A compact representation for `Option<T>`, obtained by using a value of `T` as a sentinel.
///
/// Specifically, this type guarantees that `std::mem::size_of::<SentinelOption<T, S>>() == std::mem::size_of::<T>()`.
/// This is achieved by "reserving" a specific value of `T`, the sentinel, to represent the `None` value of the option.
///
/// This representation is solely meant as a means of storing the `Option` more space-efficiently
/// (e.g. before sending on network, saving on disk, keeping in large in-memory structures).
/// Users are expected to use the `Into` trait to convert it back to an `Option` before any actual use of the value.
///
/// # Examples
///
/// To use `SentinelOption<T, S>`, users are expected to define a new struct that implements
/// the `Sentinel<T>` trait:
/// ```rust
/// # use sentinel_option::Sentinel;
/// // Define a new ZST
/// struct U64Max;
///
/// // Implement the Sentinel trait for that type
/// impl Sentinel<u64> for U64Max {
///     fn sentinel() -> u64 {
///         // The sentinel here is the max value of u64
///         u64::max_value()
///     }
/// }
/// ```
///
/// Then the users can instantiate a `SentinelOption`:
///
/// ```rust
/// # use sentinel_option::*;
/// # struct U64Max;
/// # impl Sentinel<u64> for U64Max {
/// #    fn sentinel() -> u64 {
/// #        // The sentinel here is the max value of u64
/// #        u64::max_value()
/// #    }
/// # }
/// // To know the size of our values
/// use std::mem::size_of_val;
///
/// // Convert an option into a SentinelOption
/// type U64MaxSentinelOption = SentinelOption<u64, U64Max>;
/// let sentinel = U64MaxSentinelOption::from(Some(42u64));
///
/// // sentinel is "just an u64"
/// assert_eq!(size_of_val(&sentinel), 8);
///
/// // [...]
///
/// // Convert the sentinel back into an Option
/// let from_sentinel : Option<u64> = sentinel.into();
/// assert_eq!(from_sentinel, Some(42u64));
///
/// // option is bigger because it holds the discriminant
/// assert_eq!(size_of_val(&from_sentinel), 16);
/// ```
pub struct SentinelOption<T, S>
where
    T: PartialEq,
    S: Sentinel<T>,
{
    item: T,
    _phantom: PhantomData<*const S>,
}

impl<T, S> SentinelOption<T, S>
where
    T: PartialEq,
    S: Sentinel<T>,
{
    /// Constructs a new SentinelOption from an Option.
    ///
    /// # Panics
    ///
    /// This function panics if the option contains a Some(t) where t is the sentinel.
    pub fn new(opt: Option<T>) -> Self {
        match opt {
            Some(t) => Self::new_with_some(t),
            None => Self::new_none(),
        }
    }

    /// Constructs a new SentinelOption containing the provided T.
    ///
    /// # Panics
    ///
    /// This function panics if the option contains a Some(t) where t is the sentinel.
    pub fn new_with_some(item: T) -> Self {
        if S::is_sentinel(&item) {
            panic!("Passed sentinel as some!")
        } else {
            Self {
                item,
                _phantom: PhantomData,
            }
        }
    }

    /// Constructs a new SentinelOption containing the sentinel.
    pub fn new_none() -> Self {
        Self {
            item: S::sentinel(),
            _phantom: PhantomData,
        }
    }

    /// Constructs a new SentinelOption from a T without checking the sentinel.
    ///
    /// # Safety
    ///
    /// If using this function to create a SentinelOption, the sentinel will be transformed into a `None` value,
    /// and any other T will be mapped to a `Some` of the passed value.
    pub unsafe fn unchecked_new(item: T) -> Self {
        Self {
            item,
            _phantom: PhantomData,
        }
    }

    /// Returns the raw contained T without checking the sentinel.alloc
    ///
    /// # Safety
    ///
    /// This method returns a T instance that equals the sentinel when the instance contains `None`.
    /// It contains the contained value when the instance contains a different value.
    pub unsafe fn into_unchecked(self) -> T {
        self.item
    }

    /// Returns an `Option` corresponding to the value contained in this instance.
    pub fn into_option(self) -> Option<T> {
        if S::is_sentinel(&self.item) {
            None
        } else {
            Some(self.item)
        }
    }
}

impl<T, S> From<Option<T>> for SentinelOption<T, S>
where
    T: PartialEq,
    S: Sentinel<T>,
{
    fn from(opt: Option<T>) -> Self {
        Self::new(opt)
    }
}

impl<T, S> Into<Option<T>> for SentinelOption<T, S>
where
    T: PartialEq,
    S: Sentinel<T>,
{
    fn into(self) -> Option<T> {
        self.into_option()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    struct U64Max;
    impl Sentinel<u64> for U64Max {
        fn sentinel() -> u64 {
            u64::max_value()
        }
    }

    type U64MaxSentinel = SentinelOption<u64, U64Max>;

    #[test]
    fn is_optimized() {
        use std::mem::size_of;
        assert!(size_of::<u64>() == size_of::<U64MaxSentinel>())
    }

    #[test]
    fn some_value() {
        let x = 42;
        let sentinel = U64MaxSentinel::new_with_some(x);
        let sentinel: Option<u64> = sentinel.into();
        assert!(sentinel.is_some());
        let value = sentinel.unwrap();
        assert_eq!(value, x);
    }

    #[test]
    fn none_value() {
        let sentinel = U64MaxSentinel::new_none();
        let sentinel: Option<u64> = sentinel.into();
        assert!(sentinel.is_none());
    }

    #[test]
    fn using_from_some() {
        let with_value = Some(42u64);
        let sentinel = U64MaxSentinel::from(with_value);
        let from_sentinel: Option<u64> = sentinel.into();
        assert_eq!(from_sentinel, with_value);
    }

    #[test]
    fn using_from_none() {
        let sentinel = U64MaxSentinel::from(None);
        let from_sentinel: Option<u64> = sentinel.into();
        assert_eq!(from_sentinel, None);
    }

    #[test]
    #[should_panic]
    fn some_illegal_value() {
        U64MaxSentinel::new_with_some(u64::max_value());
    }

    #[test]
    #[should_panic]
    fn using_from_illegal_value() {
        let with_value = Some(u64::max_value());
        U64MaxSentinel::from(with_value);
    }

    #[test]
    fn unsafe_value() {
        let x = 42;
        unsafe {
            let sentinel = U64MaxSentinel::unchecked_new(x);
            assert_eq!(sentinel.into_unchecked(), x);
        }
    }
}
