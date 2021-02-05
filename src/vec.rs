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
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};
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
    ptr: *mut T,
    len_: usize,
    capacity_: usize,
    alloc_: A,
}

impl<T, A> Drop for Vec<T, A>
where
    A: GlobalAlloc,
{
    fn drop(&mut self) {
        if self.ptr.is_null() {
            return;
        }

        self.clear();
        unsafe {
            let layout = Layout::array::<T>(self.capacity_).unwrap();
            self.alloc_.dealloc(self.ptr as *mut u8, layout);
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
            ptr: core::ptr::null_mut(),
            len_: 0,
            capacity_: 0,
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

impl<T, A> Vec<T, A>
where
    A: GlobalAlloc,
{
    /// Returns the number of elements that `self` is holding.
    pub fn len(&self) -> usize {
        self.len_
    }

    /// Returns the number of elements that `self` can hold without new allocation.
    pub fn capacity(&self) -> usize {
        self.capacity_
    }

    /// Returns `ture` if `self` holds no element, or `false` .
    pub fn is_empty(&self) -> bool {
        self.len_ == 0
    }

    /// Returns a reference to `alloc` .
    pub fn alloc(&self) -> &A {
        &self.alloc_
    }

    /// Returns a raw pointer to the buffer.
    pub fn as_ptr(&self) -> *const T {
        // It seems that 'std::vec::Vec::as_ptr()' returns nonnull pointer.
        // This method follows the way.
        if self.ptr.is_null() {
            core::mem::align_of::<T>() as *const T
        } else {
            self.ptr
        }
    }

    /// Returns a raw pointer to the buffer.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        // It seems that 'std::vec::Vec::as_mut_ptr()' returns nonnull pointer.
        // This method follows the way.
        if self.ptr.is_null() {
            core::mem::align_of::<T>() as *mut T
        } else {
            self.ptr
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

        let ptr = if self.ptr.is_null() {
            unsafe {
                let layout = Layout::array::<T>(additional).unwrap();
                let ptr = self.alloc_.alloc(layout);
                if ptr.is_null() {
                    handle_alloc_error(layout);
                }

                ptr
            }
        } else {
            unsafe {
                let layout = Layout::array::<T>(self.capacity_).unwrap();
                let new_size = Layout::array::<T>(self.len() + additional).unwrap().size();
                let ptr = self.alloc_.realloc(self.ptr as *mut u8, layout, new_size);

                if ptr.is_null() {
                    let layout = Layout::array::<T>(self.len() + additional).unwrap();
                    handle_alloc_error(layout);
                }

                ptr
            }
        };

        self.ptr = ptr as *mut T;
        self.capacity_ = self.len() + additional;
    }

    /// Shrinks the capacity to the length as much as possible.
    pub fn shrink_to_fit(&mut self) {
        if self.len_ == self.capacity_ {
            return;
        }

        let layout = Layout::array::<T>(self.capacity_).unwrap();

        if self.len_ == 0 {
            unsafe {
                self.alloc_.dealloc(self.ptr as *mut u8, layout);
                self.ptr = core::ptr::null_mut();
            }
        } else {
            unsafe {
                let new_size = core::mem::size_of::<T>() * self.len_;
                let ptr = self.alloc_.realloc(self.ptr as *mut u8, layout, new_size);
                if ptr.is_null() {
                    let layout = Layout::array::<T>(self.len_).unwrap();
                    handle_alloc_error(layout);
                }

                self.ptr = ptr as *mut T;
            }
        }

        self.capacity_ = self.len_;
    }

    /// Appends `val` to the end of the buffer.
    pub fn push(&mut self, val: T) {
        assert!(self.len_ < self.capacity_);

        unsafe {
            let ptr = self.ptr.add(self.len_);
            ptr.write(val);
        }

        self.len_ += 1;
    }

    /// Removes the last element from `self` and returns it if any, or `None` .
    pub fn pop(&mut self) -> Option<T> {
        if self.len_ == 0 {
            None
        } else {
            self.len_ -= 1;

            unsafe {
                let mut ret: MaybeUninit<T> = MaybeUninit::uninit();

                let ptr = self.ptr.add(self.len_);
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
        if self.len_ <= len {
            return;
        }

        unsafe {
            for i in len..self.len_ {
                let ptr = self.ptr.add(i);
                ptr.drop_in_place();
            }
        }

        self.len_ = len;
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
        assert!(self.len_ + other.len() <= self.capacity_);

        unsafe {
            for i in 0..other.len() {
                let ptr = self.ptr.add(self.len_ + i);
                ptr.write(other[i].clone());
            }
        }

        self.len_ += other.len();
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
