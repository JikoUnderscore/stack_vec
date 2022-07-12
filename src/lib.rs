#![allow(clippy::needless_return)]

//! # stack_vec
//!
//! Based on crate  [stack-vec](https://crates.io/crates/stack-vec).
//!
//! Create a `Vec<T>` like structs of a specific compile-time size on the stack.
//!
//! These structs never allocate on the heap, and expose an API similar to `Vec<T>`.
//!
//! ## Install
//! Add the following line to your Cargo.toml file:
//! ```toml
//! stack_vec = { git = "https://github.com/JikoUnderscore/stack_vec" , branch = "master"}
//! ```
//!
//! ## Usage
//!
//! ``` rust
//! fn main() {
//!     let mut sv = stack_vec::StackVec::<Rect2D, 24>::new();
//!
//!     sv.push(Rect2D { x: 20, y: 30, w: 50, h: 50 });
//!     sv.push(Rect2D { x: 10, y: 50, w: 50, h: 50 });
//!
//!     dbg!(&sv);
//! }
//!
//! #[derive(Debug)]
//! struct Rect2D {
//!     x: u32,
//!     y: u32,
//!     w: u32,
//!     h: u32,
//! }
//! ```
//!
//!
//!
//! # License
//! MIT

pub struct StackVec<T, const SIZE: usize>([std::mem::MaybeUninit<T>; SIZE], usize);

impl<T, const SIZE: usize> StackVec<T, SIZE> {
    /// The max capacity of this `StackVec`
    #[inline]
    pub const fn cap(&self) -> usize {
        SIZE
    }
    /// Create a new empty `StackVec`.
    #[inline]
    pub fn new() -> Self {
        use std::mem::MaybeUninit;
        return unsafe { Self(MaybeUninit::uninit().assume_init(), 0) };
    }
    /// Extend from a slice where `T: Copy`.
    ///
    /// Returns the number of elements copied. If the copy would overflow the capacity the rest is ignored.
    #[inline]
    pub fn extend_from_slice_copy<U: AsRef<[T]>>(&mut self, slice: U) -> usize
        where T: Copy {
        let rest = unsafe { self.rest_mut() };
        let slice = slice.as_ref();
        let len = std::cmp::min(rest.len(), slice.len());
        unsafe {
            std::ptr::copy(slice.as_ptr(),
                           rest.as_mut_ptr() as *mut std::mem::MaybeUninit<T> as *mut T,
                           len);
        }
        self.1 += len;
        return len;
    }
    /// Extend from a slice where `T: Clone`
    ///
    /// Returns the number of elements copied. If the copy would overflow the capacity the rest is ignored.
    pub fn extend_from_slice<U: AsRef<[T]>>(&mut self, slice: U) -> usize
        where T: std::clone::Clone {
        let rest = &mut self.0[self.1..];
        let slice = slice.as_ref();
        let mut wrote = 0;
        for (d, s) in rest.iter_mut().zip(slice.iter()) {
            *d = std::mem::MaybeUninit::new(s.clone());
            self.1 += 1;
            wrote += 1;
        }
        return wrote;
    }
    /// Try to push an element on to the end of the `StackVec`.
    ///
    /// If it is full, return the value as `Err(T)` instead.
    #[inline(always)]
    pub fn try_push(&mut self, value: T) -> Result<(), T> {
        if self.1 < SIZE {
            self.0[self.1] = std::mem::MaybeUninit::new(value);
            self.1 += 1;
            return Ok(());
        } else {
            return Err(value);
        }
    }
    /// Push an element on the the end of the `StackVec`.
    ///
    /// # Panics
    /// If the `StackVec` is full.
    #[inline]
    pub fn push(&mut self, value: T) {
        #[cold]
        fn off_end() -> ! {
            panic!("Tried to push off the end of `StackVec`");
        }
        if self.1 < SIZE {
            self.0[self.1] = std::mem::MaybeUninit::new(value);
            self.1 += 1;
        } else { off_end() }
    }
    /// The number of elements currently in the `StackVec`.
    #[inline]
    pub fn len(&self) -> usize {
        self.1
    }
    /// Returns `true` if the `StackVec` contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// A slice of the elements in the `StackVec`.
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        unsafe { &*(&self.0[..self.1] as *const [std::mem::MaybeUninit<T>] as *const [T]) }
    }
    /// A mutable slice of the elements in the `StackVec`.
    #[inline(always)]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { &mut *(&mut self.0[..self.1] as *mut [std::mem::MaybeUninit<T>] as *mut [T]) }
    }
    /// A mutable slice of the initialised part of the buffer.
    ///
    /// All elements of the returned slice are initialised.
    #[inline(always)]
    pub fn init_buffer_mut(&mut self) -> &mut [std::mem::MaybeUninit<T>] {
        &mut self.0[..self.1]
    }
    /// The initialised part of the buffer.
    ///
    /// All elements of the returned slice are initialised.
    #[inline(always)]
    pub fn init_buffer(&self) -> &[std::mem::MaybeUninit<T>] {
        &self.0[..self.1]
    }
    /// # Safety
    /// A mutable reference to the uninitialised part of the instance.
    ///
    /// No elements of the returned slice are initialised.
    /// # Note
    /// If you initialise some, you must remember to update the length with `set_len()`.
    #[inline(always)]
    pub unsafe fn rest_mut(&mut self) -> &mut [std::mem::MaybeUninit<T>] {
        &mut self.0[self.1..]
    }
    /// The uninitialised part of the instance.
    ///
    /// No elements of the returned slice are initialised.
    #[inline(always)]
    pub fn rest(&self) -> &[std::mem::MaybeUninit<T>] {
        &self.0[self.1..]
    }
    /// # Safety
    /// A mutable reference to the whole capacity buffer.
    ///
    /// `..self.len()` will be initialised, `self.len()..` will be uninitialised.
    ///
    /// # Note
    /// If you initialise or uninitialise some element(s), you must remember to update the length with `set_len()`.
    #[inline]
    pub unsafe fn buffer_mut(&mut self) -> &mut [std::mem::MaybeUninit<T>; SIZE] {
        &mut self.0
    }
    /// A reference to the whole capacity buffer.
    ///
    /// `..self.len()` will be initialised, `self.len()..` will be uninitialised.
    #[inline]
    pub fn buffer(&self) -> &[std::mem::MaybeUninit<T>; SIZE] {
        &self.0
    }
    /// # Safety
    /// Set the internal fill pointer of the `StackVec`.
    ///
    /// This changes how much of the buffer is assumed to be initialised.
    /// Only use this if you have manually initialised some of the uninitialised buffer, as it does no initialising itself.
    #[inline]
    pub unsafe fn set_len(&mut self, len: usize) {
        self.1 = len;
    }
}

impl<T, const SIZE: usize> std::ops::Drop for StackVec<T, SIZE> {
    fn drop(&mut self) {
        if std::mem::needs_drop::<T>() {
            for init in &mut self.0[..self.1] {
                unsafe {
                    drop(std::mem::replace(init, std::mem::MaybeUninit::uninit()).assume_init());
                }
            }
        }
    }
}

impl<T, const SIZE: usize> std::ops::DerefMut for StackVec<T, SIZE> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, const SIZE: usize> std::ops::Deref for StackVec<T, SIZE> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const SIZE: usize> std::convert::AsRef<[T]> for StackVec<T, SIZE> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const SIZE: usize> std::convert::AsMut<[T]> for StackVec<T, SIZE> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const SIZE: usize> std::borrow::Borrow<[T]> for StackVec<T, SIZE> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const SIZE: usize> std::borrow::BorrowMut<[T]> for StackVec<T, SIZE> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const SIZE: usize> std::fmt::Debug for StackVec<T, SIZE> where T: std::fmt::Debug {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}", self.as_slice()))
    }
}

impl<T, const SIZE: usize> PartialEq<Self> for StackVec<T, SIZE> where T: std::cmp::Eq {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<T, const SIZE: usize> std::cmp::Eq for StackVec<T, SIZE> where T: std::cmp::Eq {}

impl<T, const SIZE: usize> PartialOrd<Self> for StackVec<T, SIZE> where T: std::cmp::Ord {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        std::cmp::PartialOrd::partial_cmp(self.as_slice(), other.as_ref())
    }
}

impl<T, const SIZE: usize> std::cmp::Ord for StackVec<T, SIZE> where T: std::cmp::Ord {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        std::cmp::Ord::cmp(self.as_slice(), other.as_slice())
    }
}

impl<T, const SIZE: usize, I: std::slice::SliceIndex<[T]>> std::ops::Index<I> for StackVec<T, SIZE> {
    type Output = I::Output;
    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        std::ops::Index::index(self.as_slice(), index)
    }
}

impl<T, const SIZE: usize, I: std::slice::SliceIndex<[T]>> std::ops::IndexMut<I> for StackVec<T, SIZE> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        std::ops::IndexMut::index_mut(self.as_mut_slice(), index)
    }
}

impl<T, const SIZE: usize> std::clone::Clone for StackVec<T, SIZE> where T: std::clone::Clone {
    fn clone(&self) -> Self {
        let mut emp = Self::new();
        for (d, s) in emp.0.iter_mut().zip(self.iter()) {
            *d = std::mem::MaybeUninit::new(s.clone());
            emp.1 += 1;
        }
        return emp;
    }
}

impl<T, const SIZE: usize> std::convert::From<StackVec<T, SIZE>> for std::vec::Vec<T> {
    #[inline]
    fn from(from: StackVec<T, SIZE>) -> Self {
        from.into_iter().collect()
    }
}

impl<T, const SIZE: usize> std::default::Default for StackVec<T, SIZE> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const SIZE: usize> std::iter::IntoIterator for StackVec<T, SIZE> {
    type Item = T;
    type IntoIter = StackVecIntoIter<T, SIZE>;
    fn into_iter(self) -> Self::IntoIter {
        StackVecIntoIter(self, 0)
    }
}

impl<const SIZE: usize> std::io::Write for StackVec<u8, SIZE> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(self.extend_from_slice_copy(buf))
    }
    #[inline]
    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize> {
        let mut w = 0;
        for buf in bufs { w += self.extend_from_slice_copy(&buf[..]); }
        return Ok(w);
    }
    #[inline]
    fn flush(&mut self) -> std::io::Result<()> { Ok(()) }
    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()> {
        let w = self.extend_from_slice_copy(buf);
        if w != buf.len() {
            return Err(std::io::Error::new(std::io::ErrorKind::Other, "No more space"));
        } else {
            return Ok(());
        }
    }
}

impl<T, const SIZE: usize> std::convert::From<[T; SIZE]> for StackVec<T, SIZE> {
    #[inline]
    fn from(from: [T; SIZE]) -> Self {
        let mut this = Self::new();
        unsafe {
            std::ptr::copy(&from[0] as *const T,
                           &mut this.0[0] as *mut std::mem::MaybeUninit<T> as *mut T,
                           SIZE);
        }
        this.1 = SIZE;
        std::mem::forget(from);
        return this;
    }
}

impl<T, const SIZE: usize> std::iter::FromIterator<T> for StackVec<T, SIZE> {
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let mut output = Self::new();
        for item in iter { output.push(item); }
        return output;
    }
}

/// Consuming iterator type for a `StackVec`
pub struct StackVecIntoIter<T, const SIZE: usize>(StackVec<T, SIZE>, usize);

impl<T, const SIZE: usize> StackVecIntoIter<T, SIZE> {
    #![allow(dead_code)]
    /// The rest of the initialised buffer that has not been consumed yet.
    #[inline]
    pub fn rest(&self) -> &[T] {
        &self.0.as_slice()[self.1..]
    }
    #[inline(always)]
    fn m_rest(&self) -> &[std::mem::MaybeUninit<T>] {
        &self.0.init_buffer()[self.1..]
    }
    /// A mutable reference to the rest of the initialised buffer that has not been consumed yet.
    #[inline]
    pub fn rest_mut(&mut self) -> &mut [T] {
        &mut self.0.as_mut_slice()[self.1..]
    }
    #[inline(always)]
    fn m_rest_mut(&mut self) -> &mut [std::mem::MaybeUninit<T>] {
        &mut self.0.init_buffer_mut()[self.1..]
    }
}

impl<T, const SIZE: usize> std::iter::Iterator for StackVecIntoIter<T, SIZE> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let buf = self.0.init_buffer_mut();
        if self.1 < buf.len() {
            return (unsafe { Some(std::mem::replace(&mut buf[self.1], std::mem::MaybeUninit::uninit()).assume_init()) }, self.1 += 1).0;
        } else {
            return None;
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len(), Some(self.0.len()))
    }
}

impl<T, const SIZE: usize> std::iter::ExactSizeIterator for StackVecIntoIter<T, SIZE> {}

impl<T, const SIZE: usize> std::iter::FusedIterator for StackVecIntoIter<T, SIZE> {}

impl<T, const SIZE: usize> std::ops::Drop for StackVecIntoIter<T, SIZE> {
    fn drop(&mut self) {
        if std::mem::needs_drop::<T>() {
            unsafe {
                for init in self.m_rest_mut() {
                    drop(std::mem::replace(init,
                                           std::mem::MaybeUninit::uninit()).assume_init());
                }
            }
            self.0.1 = 0;
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_and_drop() {
        let mut sv = StackVec::<String, 256>::new();
        sv.push(String::from("Hello"));
        sv.push(String::from(" "));
        sv.push(String::from("world."));
        sv.push(String::from("!!!"));
        sv.push(String::from("owo"));

        assert_eq!(sv.len(), 5);
        assert_eq!("Hello world.", sv.into_iter().take(3).collect::<String>().as_str());
    }

    #[test]
    fn conversions() {
        let mut sv = StackVec::<Vec<usize>, 256>::new();
        assert_eq!(sv.extend_from_slice(&[vec![1usize, 2], vec![3, 4], vec![5, 6]]), 3);

        assert_eq!(sv[1].iter().sum::<usize>(), 7);
        assert_eq!(sv.iter().flat_map(|x| x.iter()).sum::<usize>(), 1 + 2 + 3 + 4 + 5 + 6);

        let v = Vec::from(sv.clone());
        assert_eq!(&v[..], &sv[..]);
        drop(sv);
        assert_eq!(v.iter().flat_map(|x| x.iter()).sum::<usize>(), 1 + 2 + 3 + 4 + 5 + 6);
    }

    #[test]
    fn write() {
        use std::io::Write;
        let mut sv = StackVec::<u8, 256>::new();
        let buf1 = [0u8; 128];
        let buf2 = [1u8; 128];

        sv.write_all(&buf1[..]).expect("Failed to write buf1");
        sv.write_all(&buf2[..]).expect("Failed to write buf2");
        assert!(sv.write_all(&buf1[..]).is_err());

        assert_eq!(&sv[..buf1.len()], &buf1[..]);
        assert_eq!(&sv[buf1.len()..], &buf2[..]);

        assert_eq!(buf1.iter().chain(buf2.iter()).copied().collect::<Vec<_>>(), sv.into_iter().collect::<Vec<_>>());
    }

    #[test]
    fn from_iterator() {
        let sv: StackVec<_, 256> = vec![1, 2, 3, 4, 5, 6].into_iter().collect();
        assert_eq!(sv.into_iter().sum::<i32>(), 6 + 5 + 4 + 3 + 2 + 1i32);

        let nt: StackVec<_, 256> = vec![
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9],
        ].into_iter().collect();
        assert_eq!(nt.iter().flat_map(|x| x.iter()).copied().sum::<i32>(), 9 + 8 + 7 + 6 + 5 + 4 + 3 + 2 + 1);
    }

    #[test]
    #[should_panic]
    fn from_too_big() {
        let _sv: StackVec<_, 256> = vec![vec![String::from("hi")]; 257].into_iter().collect();
    }


    #[test]
    #[should_panic]
    fn add_more() {
        let mut sv = StackVec::<u8, 5>::new();

        sv.push(1);
        sv.push(99);
        sv.push(64);
        sv.push(42);
        sv.push(69);
        sv.push(96);
    }


    // #[test]
    // fn ad_hoc() {
    //     let mut sv = stack![23];
    //
    //     assert_eq!(sv.cap(), 23);
    //
    //     for x in 0..23
    //     {
    //         sv.push(vec![x, x]);
    //     }
    //     assert_eq!(sv.len(), 23);
    //
    //     assert_eq!(sv.into_iter().flat_map(|x| x.into_iter()).sum::<i32>(), (0..23).map(|x| x * 2).sum::<i32>());
    // }
}
