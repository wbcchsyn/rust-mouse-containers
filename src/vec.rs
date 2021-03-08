// Copyright 2021 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0 OR BSD-2-Clause"
//
// This is part of mouse-containers
//
//  mouse-containers is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  mouse-containers is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with mouse-containers.  If not, see <http://www.gnu.org/licenses/>.
//
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//
// Redistribution and use in source and binary forms, with or without modification, are permitted
// provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice, this
//    list of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
// IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
// INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
// NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

use core::alloc::{GlobalAlloc, Layout};
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::iter::IntoIterator;
use core::mem::{size_of, size_of_val, MaybeUninit};
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::slice::{Iter, IterMut, SliceIndex};
use std::alloc::handle_alloc_error;
use std::borrow::{Borrow, BorrowMut};

/// `Vec` behaves like 'std::vec::Vec' except for the followings.
///
/// - `Vec` takes allocator as the parameter.
/// - `Vec` causes a panic if the size will exceed the capacity because it costs O(n) CPU time.
///   Method [`push`] for example, causes a panic if `len` equals to `capacity` .
///   User must call `reserve` in advance if necessary.
/// - `Vec` does not implement some methods that costs O(n) CPU time or more on purpose.
///
/// [`push`]: #method.push
#[derive(Debug)]
pub struct Vec<T, A>
where
    A: GlobalAlloc,
{
    buffer: (*mut T, usize), // (ptr, capacity)
    len_: isize,
    alloc_: A,
}

impl<T, A> Vec<T, A>
where
    A: GlobalAlloc,
{
    const MAX_STACK_CAPACITY: usize = size_of::<(*mut T, usize)>() / size_of::<T>();
}

unsafe impl<T, A> Send for Vec<T, A> where A: Send + GlobalAlloc {}
unsafe impl<T, A> Sync for Vec<T, A> where A: Sync + GlobalAlloc {}

impl<T, A> Drop for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn drop(&mut self) {
        self.clear();

        if self.is_stack() {
            return;
        }

        if self.buffer.0.is_null() {
            return;
        }

        unsafe {
            let layout = Layout::array::<T>(self.capacity()).unwrap();
            self.alloc_.dealloc(self.as_ptr() as *mut u8, layout);
        }
    }
}

impl<T, A> Default for Vec<T, A>
where
    A: Default + GlobalAlloc,
{
    fn default() -> Self {
        Self::from(A::default())
    }
}

impl<T, A> From<A> for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn from(alloc: A) -> Self {
        Self {
            len_: 0,
            buffer: (core::ptr::null_mut(), 0),
            alloc_: alloc,
        }
    }
}

impl<T, A> Vec<T, A>
where
    A: GlobalAlloc,
{
    /// Creates a new empty instance with the specified capacity.
    pub fn with_capacity(capacity: usize, alloc: A) -> Self {
        let mut ret = Self::from(alloc);
        ret.reserve(capacity);
        ret
    }
}

impl<T, A> PartialEq<Self> for Vec<T, A>
where
    T: PartialEq<T>,
    A: GlobalAlloc,
{
    fn eq(&self, other: &Self) -> bool {
        let this: &[T] = self.borrow();
        let other: &[T] = other.borrow();
        this.eq(other)
    }
}

impl<T, A> Eq for Vec<T, A>
where
    T: Eq,
    A: GlobalAlloc,
{
}

impl<T, A> PartialOrd<Self> for Vec<T, A>
where
    T: PartialOrd<T>,
    A: GlobalAlloc,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let this: &[T] = self.borrow();
        let other: &[T] = other.borrow();
        this.partial_cmp(other)
    }
}

impl<T, A> Ord for Vec<T, A>
where
    T: Ord,
    A: GlobalAlloc,
{
    fn cmp(&self, other: &Self) -> Ordering {
        let this: &[T] = self.borrow();
        let other: &[T] = other.borrow();
        this.cmp(other)
    }
}

impl<T, A> Hash for Vec<T, A>
where
    T: Hash,
    A: GlobalAlloc,
{
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        let this: &[T] = self.borrow();
        this.hash(hasher);
    }
}

impl<T, A> AsRef<[T]> for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn as_ref(&self) -> &[T] {
        self.deref()
    }
}

impl<T, A> AsMut<[T]> for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn as_mut(&mut self) -> &mut [T] {
        self.deref_mut()
    }
}

impl<T, A> Borrow<[T]> for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn borrow(&self) -> &[T] {
        self.deref()
    }
}

impl<T, A> BorrowMut<[T]> for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn borrow_mut(&mut self) -> &mut [T] {
        self.deref_mut()
    }
}

impl<T, A> Deref for Vec<T, A>
where
    A: GlobalAlloc,
{
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl<T, A> DerefMut for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl<T, I, A> Index<I> for Vec<T, A>
where
    I: SliceIndex<[T], Output = T>,
    A: GlobalAlloc,
{
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.deref()[index]
    }
}

impl<T, I, A> IndexMut<I> for Vec<T, A>
where
    I: SliceIndex<[T], Output = T>,
    A: GlobalAlloc,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.deref_mut()[index]
    }
}

impl<'a, T, A> IntoIterator for &'a Vec<T, A>
where
    A: GlobalAlloc,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.deref().into_iter()
    }
}

impl<'a, T, A> IntoIterator for &'a mut Vec<T, A>
where
    A: GlobalAlloc,
{
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.deref_mut().into_iter()
    }
}

impl<T, A> Vec<T, A>
where
    A: GlobalAlloc,
{
    /// Returns the number of elements that `self` is holding.
    pub fn len(&self) -> usize {
        if self.is_stack() {
            (self.len_ - isize::MIN) as usize
        } else {
            self.len_ as usize
        }
    }

    /// Forces the length of `self` to `new_len` .
    ///
    /// This is a low-level operation that maintains none of the normal invariants of the type.
    /// Normally changing the length of a vector is done using one of the safe operations instead,
    /// such as truncate, or clear.
    ///
    /// # Safety
    ///
    /// - `new_len` must equal to or be less than the `capacity` .
    /// - The elements at `old_len..new_len` must be initialized.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());
        if self.is_stack() {
            self.len_ = isize::MIN + new_len as isize;
        } else {
            self.len_ = new_len as isize;
        }
    }

    /// Returns the number of elements that `self` can hold without new allocation.
    pub fn capacity(&self) -> usize {
        if self.is_stack() {
            size_of_val(&self.buffer) / size_of::<T>()
        } else {
            self.buffer.1
        }
    }

    /// Returns `ture` if `self` holds no element, or `false` .
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to `alloc` .
    pub fn alloc(&self) -> &A {
        &self.alloc_
    }

    /// Returns a raw pointer to the buffer.
    pub fn as_ptr(&self) -> *const T {
        if self.is_stack() {
            let ptr = &self.buffer as *const (*mut T, usize);
            ptr as *const T
        } else {
            // It seems that 'std::vec::Vec::as_ptr()' returns nonnull pointer.
            // This method follows the way.
            if self.buffer.0.is_null() {
                core::mem::align_of::<T>() as *const T
            } else {
                self.buffer.0
            }
        }
    }

    /// Returns a raw pointer to the buffer.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        if self.is_stack() {
            let ptr = &mut self.buffer as *mut (*mut T, usize);
            ptr as *mut T
        } else {
            // It seems that 'std::vec::Vec::as_mut_ptr()' returns nonnull pointer.
            // This method follows the way.
            if self.buffer.0.is_null() {
                core::mem::align_of::<T>() as *mut T
            } else {
                self.buffer.0
            }
        }
    }

    /// Reserves capacity at least `additional` more elements to be inserted in `self` .
    ///
    /// This method does nothing if the capacity is already sufficient.
    /// After this method is called, the capacity will be greater than or eqaul to `self.len() +
    /// capacity` .
    pub fn reserve(&mut self, additional: usize) {
        if self.len() + additional <= self.capacity() {
            return;
        }

        let ptr = if self.buffer.0.is_null() || self.is_stack() {
            // First allocation
            unsafe {
                let layout = Layout::array::<T>(self.len() + additional).unwrap();
                let ptr = self.alloc_.alloc(layout) as *mut T;
                if ptr.is_null() {
                    handle_alloc_error(layout);
                }

                // Copy holding elements.
                ptr.copy_from_nonoverlapping(self.as_ptr(), self.len());
                // Disable small optimization.
                self.len_ = self.len() as isize;

                ptr
            }
        } else {
            unsafe {
                let layout = Layout::array::<T>(self.capacity()).unwrap();
                let new_size = Layout::array::<T>(self.len() + additional).unwrap().size();
                let old_ptr = self.as_mut_ptr();
                let ptr = self.alloc_.realloc(old_ptr as *mut u8, layout, new_size);

                if ptr.is_null() {
                    let layout = Layout::array::<T>(self.len() + additional).unwrap();
                    handle_alloc_error(layout);
                }

                ptr as *mut T
            }
        };

        self.buffer.0 = ptr;
        self.buffer.1 = self.len() + additional;
    }

    /// Shrinks the capacity to the length as much as possible.
    pub fn shrink_to_fit(&mut self) {
        if self.is_stack() {
            return;
        }

        if self.len() == self.capacity() {
            return;
        }

        let layout = Layout::array::<T>(self.capacity()).unwrap();

        if self.len() == 0 {
            unsafe {
                let old_ptr = self.as_mut_ptr();
                self.alloc_.dealloc(old_ptr as *mut u8, layout);
                self.buffer.0 = core::ptr::null_mut();
            }
        } else {
            unsafe {
                let new_size = core::mem::size_of::<T>() * self.len();
                let old_ptr = self.as_mut_ptr();
                let ptr = self.alloc_.realloc(old_ptr as *mut u8, layout, new_size);
                if ptr.is_null() {
                    let layout = Layout::array::<T>(self.len()).unwrap();
                    handle_alloc_error(layout);
                }

                self.buffer.0 = ptr as *mut T;
            }
        }

        self.buffer.1 = self.len();
    }

    /// Appends `val` to the end of the buffer.
    pub fn push(&mut self, val: T) {
        assert!(self.len() < self.capacity());

        unsafe {
            let ptr = self.as_mut_ptr().add(self.len());
            ptr.write(val);
        }

        let old_len = self.len();
        unsafe { self.set_len(old_len + 1) };
    }

    /// Removes the last element from `self` and returns it if any, or `None` .
    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 {
            None
        } else {
            let old_len = self.len();
            unsafe { self.set_len(old_len - 1) };

            unsafe {
                let mut ret: MaybeUninit<T> = MaybeUninit::uninit();

                let ptr = self.as_mut_ptr().add(self.len());
                ret.as_mut_ptr().copy_from_nonoverlapping(ptr, 1);

                Some(ret.assume_init())
            }
        }
    }

    /// Clears `self` , removing all the elements.
    ///
    /// Note that this method has no effect on the allocated capacity.
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Shortens `self` , keeping the first `len` elements and drops the rest if `len` is less than
    /// the current length; otherwise it does nothing.
    ///
    /// Note that this method has no effect on the allocated capacity.
    pub fn truncate(&mut self, len: usize) {
        if self.len() <= len {
            return;
        }

        unsafe {
            for i in len..self.len() {
                let ptr = self.as_mut_ptr().add(i);
                ptr.drop_in_place();
            }
        }

        unsafe { self.set_len(len) };
    }

    /// Clones and appends all the elements in `other` to the end of `self` .
    ///
    /// # Panics
    ///
    /// Panic if `self.len() + other.len()` is greater than the current capacity.
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        assert!(self.len() + other.len() <= self.capacity());

        unsafe {
            for i in 0..other.len() {
                let ptr = self.as_mut_ptr().add(self.len() + i);
                ptr.write(other[i].clone());
            }
        }

        let old_len = self.len();
        unsafe { self.set_len(old_len + other.len()) };
    }

    fn is_stack(&self) -> bool {
        self.len_ < 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gharial::{GAlloc, GBox};

    #[test]
    fn from() {
        let v: Vec<u8, GAlloc> = Vec::from(GAlloc::default());
        assert_eq!(0, v.len());
        assert_eq!(0, v.capacity());
    }

    #[test]
    fn reserve() {
        let mut v: Vec<usize, GAlloc> = Vec::from(GAlloc::default());

        v.reserve(10);
        assert_eq!(0, v.len());
        assert!(10 <= v.capacity());

        v.reserve(5);
        assert_eq!(0, v.len());
        assert!(5 <= v.capacity());
    }

    #[test]
    fn push() {
        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());

        for i in 0..10 {
            assert_eq!(10, v.capacity());
            assert_eq!(i, v.len());
            v.push(GBox::new(i, alloc.clone()));
        }
    }

    #[test]
    #[should_panic]
    fn push_panic() {
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, GAlloc::default());

        for i in 0..=10 {
            v.push(GBox::from(i));
        }
    }

    #[test]
    fn clear() {
        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());

        for i in 0..10 {
            for j in 0..i {
                v.push(GBox::new(j, alloc.clone()));
            }

            v.clear();
            assert_eq!(10, v.capacity());
            assert_eq!(0, v.len());
        }
    }

    #[test]
    fn is_empty() {
        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());
        assert_eq!(true, v.is_empty());

        for i in 0..10 {
            v.push(GBox::new(i, alloc.clone()));
            assert_eq!(false, v.is_empty());
        }

        v.clear();
        assert_eq!(true, v.is_empty());
    }

    #[test]
    fn extend_from_slice() {
        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());

        let sl = [GBox::new(0, alloc.clone()), GBox::new(1, alloc.clone())];

        assert_eq!(0, v.len());
        assert_eq!(10, v.capacity());
        v.extend_from_slice(&sl);
        assert_eq!(2, v.len());
        assert_eq!(10, v.capacity());
    }

    #[test]
    fn pop() {
        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());
        assert_eq!(None, v.pop());

        for i in 0..10 {
            for j in 0..i {
                v.push(GBox::new(j, alloc.clone()));
            }

            for j in (0..i).rev() {
                assert_eq!(Some(GBox::from(j)), v.pop());
                assert_eq!(j, v.len());
                assert_eq!(10, v.capacity());
            }
        }

        assert_eq!(None, v.pop());
    }

    #[test]
    fn shrink_to_fit() {
        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::from(alloc.clone());

        for i in 0..10 {
            v.reserve(10);

            for j in 0..i {
                v.push(GBox::new(j, alloc.clone()));
            }
            v.shrink_to_fit();
            assert_eq!(v.len(), v.capacity());

            v.clear();
            v.shrink_to_fit();
            assert_eq!(v.len(), v.capacity());
        }
    }

    #[test]
    fn truncate() {
        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());

        for i in 0..15 {
            for j in 0..10 {
                v.push(GBox::new(j, alloc.clone()));
            }

            v.truncate(i);
            assert_eq!(10, v.capacity());
            assert_eq!(usize::min(10, i), v.len());

            v.clear();
        }
    }

    #[test]
    fn deref() {
        let org: &[GBox<usize>] = &[GBox::from(0), GBox::from(1), GBox::from(2), GBox::from(3)];

        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());

        for i in 0..org.len() {
            v.push(org[i].clone());
            assert_eq!(&org[0..=i], v.deref());
        }
    }

    #[test]
    fn deref_mut() {
        let org: &[GBox<usize>] = &[GBox::from(0), GBox::from(1), GBox::from(2), GBox::from(3)];

        let alloc = GAlloc::default();
        let mut v: Vec<GBox<usize>, GAlloc> = Vec::with_capacity(10, alloc.clone());

        for i in 0..org.len() {
            v.push(org[i].clone());
            assert_eq!(&org[0..=i], v.deref_mut());
        }
    }
}
