use std::marker::PhantomData;

pub trait Sentinel<T>
where
    T: PartialEq,
{
    fn sentinel() -> T;

    fn is_sentinel(t: &T) -> bool {
        *t == Self::sentinel()
    }
}

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
    pub fn new(opt: Option<T>) -> Self {
        match opt {
            Some(t) => Self::new_with_some(t),
            None => Self::new_none(),
        }
    }

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

    pub fn new_none() -> Self {
        Self {
            item: S::sentinel(),
            _phantom: PhantomData,
        }
    }

    pub unsafe fn unchecked_new(item: T) -> Self {
        Self {
            item,
            _phantom: PhantomData,
        }
    }

    pub unsafe fn into_unchecked(self) -> T {
        self.item
    }

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
