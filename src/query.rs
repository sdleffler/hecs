// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use core::fmt;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;

use crate::archetype::Archetype;
use crate::entities::EntityMeta;
use crate::{Component, Entity, SmartComponent};

/// A collection of component types to fetch from a `World`
pub trait Query<'c, C: Clone + 'c = ()> {
    #[doc(hidden)]
    type Fetch: for<'q> Fetch<'q, 'c, C>;
}

/// Type of values yielded by a query
///
/// Once rust offers generic associated types, this will be moved into `Query`.
pub type QueryItem<'q, 'c, Q, C> = <<Q as Query<'c, C>>::Fetch as Fetch<'q, 'c, C>>::Item;

/// Streaming iterators over contiguous homogeneous ranges of components
pub unsafe trait Fetch<'q, 'c, C: Clone + 'c>: Sized {
    /// Type of value to be fetched
    type Item;

    /// A value on which `get` may never be called
    fn dangling() -> Self;

    /// How this query will access `archetype`, if at all
    fn access(archetype: &Archetype) -> Option<Access>;

    /// Acquire dynamic borrows from `archetype`
    fn borrow(archetype: &Archetype);
    /// Construct a `Fetch` for `archetype` if it should be traversed
    fn new(archetype: &Archetype) -> Option<Self>;
    /// Release dynamic borrows acquired by `borrow`
    fn release(archetype: &Archetype);

    /// Access the `n`th item in this archetype without bounds checking
    ///
    /// # Safety
    /// - Must only be called after `borrow`
    /// - `release` must not be called while `'a` is still live
    /// - Bounds-checking must be performed externally
    /// - Any resulting borrows must be legal (e.g. no &mut to something another iterator might access)
    unsafe fn get(&self, n: usize, id: Entity, ctx: C) -> Self::Item;
}

/// Type of access a `Query` may have to an `Archetype`
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum Access {
    /// Read entity IDs only, no components
    Iterate,
    /// Read components
    Read,
    /// Read and write components
    Write,
}

impl<'a, T: SmartComponent<C>, C: Clone + 'a> Query<'a, C> for &'a T {
    type Fetch = FetchRead<T>;
}

#[doc(hidden)]
pub struct FetchRead<T>(NonNull<T>);

pub struct Ref<'a, T, C> {
    value: &'a T,
    id: Entity,
    context: C,
}

impl<'a, T, C: Clone> Clone for Ref<'a, T, C> {
    fn clone(&self) -> Self {
        Self {
            value: self.value,
            id: self.id,
            context: self.context.clone(),
        }
    }
}

impl<'a, T, C: Copy> Copy for Ref<'a, T, C> {}

impl<'a, T: fmt::Debug, C> fmt::Debug for Ref<'a, T, C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<'a, T: SmartComponent<C>, C: Clone> Deref for Ref<'a, T, C> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value.on_borrow(self.id, self.context.clone());
        self.value
    }
}

unsafe impl<'q, 'c, T: SmartComponent<C>, C: Clone + 'c> Fetch<'q, 'c, C> for FetchRead<T> {
    type Item = Ref<'q, T, C>;

    fn dangling() -> Self {
        Self(NonNull::dangling())
    }

    fn access(archetype: &Archetype) -> Option<Access> {
        if archetype.has::<T>() {
            Some(Access::Read)
        } else {
            None
        }
    }

    fn borrow(archetype: &Archetype) {
        archetype.borrow::<T>();
    }
    fn new(archetype: &Archetype) -> Option<Self> {
        archetype.get::<T>().map(Self)
    }

    fn release(archetype: &Archetype) {
        archetype.release::<T>();
    }

    unsafe fn get(&self, n: usize, id: Entity, context: C) -> Self::Item {
        Ref {
            value: &*self.0.as_ptr().add(n),
            id,
            context,
        }
    }
}

impl<'a, T: SmartComponent<C>, C: Clone + 'a> Query<'a, C> for &'a mut T {
    type Fetch = FetchWrite<T>;
}

#[doc(hidden)]
pub struct FetchWrite<T>(NonNull<T>);

pub struct RefMut<'a, T, C> {
    value: &'a mut T,
    id: Entity,
    context: C,
}

impl<'a, T: fmt::Debug, C> fmt::Debug for RefMut<'a, T, C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<'a, T: SmartComponent<C>, C: Clone + 'a> Deref for RefMut<'a, T, C> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        (&*self.value).on_borrow(self.id, self.context.clone());
        self.value
    }
}

impl<'a, T: SmartComponent<C>, C: Clone + 'a> DerefMut for RefMut<'a, T, C> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value.on_borrow_mut(self.id, self.context.clone());
        self.value
    }
}

unsafe impl<'q, 'c, T: SmartComponent<C>, C: Clone + 'c> Fetch<'q, 'c, C> for FetchWrite<T> {
    type Item = RefMut<'q, T, C>;

    fn dangling() -> Self {
        Self(NonNull::dangling())
    }

    fn access(archetype: &Archetype) -> Option<Access> {
        if archetype.has::<T>() {
            Some(Access::Write)
        } else {
            None
        }
    }

    fn borrow(archetype: &Archetype) {
        archetype.borrow_mut::<T>();
    }
    fn new(archetype: &Archetype) -> Option<Self> {
        archetype.get::<T>().map(Self)
    }

    fn release(archetype: &Archetype) {
        archetype.release_mut::<T>();
    }

    unsafe fn get(&self, n: usize, id: Entity, context: C) -> Self::Item {
        RefMut {
            value: &mut *self.0.as_ptr().add(n),
            id,
            context,
        }
    }
}

impl<'a, T: Query<'a, C>, C: Clone + 'a> Query<'a, C> for Option<T> {
    type Fetch = TryFetch<T::Fetch>;
}

#[doc(hidden)]
pub struct TryFetch<T>(Option<T>);

unsafe impl<'q, 'c, T: Fetch<'q, 'c, C>, C: Clone + 'c> Fetch<'q, 'c, C> for TryFetch<T> {
    type Item = Option<T::Item>;

    fn dangling() -> Self {
        Self(None)
    }

    fn access(archetype: &Archetype) -> Option<Access> {
        Some(T::access(archetype).unwrap_or(Access::Iterate))
    }

    fn borrow(archetype: &Archetype) {
        T::borrow(archetype)
    }
    fn new(archetype: &Archetype) -> Option<Self> {
        Some(Self(T::new(archetype)))
    }

    fn release(archetype: &Archetype) {
        T::release(archetype)
    }

    unsafe fn get(&self, n: usize, id: Entity, context: C) -> Option<T::Item> {
        Some(self.0.as_ref()?.get(n, id, context))
    }
}

/// Query transformer skipping entities that have a `T` component
///
/// See also `QueryBorrow::without`.
///
/// # Example
/// ```
/// # use hecs::*;
/// let mut world = World::new();
/// let a = world.spawn((123, true, "abc"));
/// let b = world.spawn((456, false));
/// let c = world.spawn((42, "def"));
/// let entities = world.query::<Without<bool, &i32>>()
///     .iter()
///     .map(|(e, i)| (e, *i))
///     .collect::<Vec<_>>();
/// assert_eq!(entities, &[(c, 42)]);
/// ```
pub struct Without<T, Q>(PhantomData<(Q, fn(T))>);

impl<'c, T: Component, Q: Query<'c, C>, C: Clone + 'c> Query<'c, C> for Without<T, Q> {
    type Fetch = FetchWithout<T, Q::Fetch>;
}

#[doc(hidden)]
pub struct FetchWithout<T, F>(F, PhantomData<fn(T)>);

unsafe impl<'q, 'c, T: Component, F: Fetch<'q, 'c, C>, C: Clone + 'c> Fetch<'q, 'c, C>
    for FetchWithout<T, F>
{
    type Item = F::Item;

    fn dangling() -> Self {
        Self(F::dangling(), PhantomData)
    }

    fn access(archetype: &Archetype) -> Option<Access> {
        if archetype.has::<T>() {
            None
        } else {
            F::access(archetype)
        }
    }

    fn borrow(archetype: &Archetype) {
        F::borrow(archetype)
    }
    fn new(archetype: &Archetype) -> Option<Self> {
        if archetype.has::<T>() {
            return None;
        }
        Some(Self(F::new(archetype)?, PhantomData))
    }
    fn release(archetype: &Archetype) {
        F::release(archetype)
    }

    unsafe fn get(&self, n: usize, id: Entity, context: C) -> F::Item {
        self.0.get(n, id, context)
    }
}

/// Query transformer skipping entities that do not have a `T` component
///
/// See also `QueryBorrow::with`.
///
/// # Example
/// ```
/// # use hecs::*;
/// let mut world = World::new();
/// let a = world.spawn((123, true, "abc"));
/// let b = world.spawn((456, false));
/// let c = world.spawn((42, "def"));
/// let entities = world.query::<With<bool, &i32>>()
///     .iter()
///     .map(|(e, i)| (e, *i))
///     .collect::<Vec<_>>();
/// assert_eq!(entities.len(), 2);
/// assert!(entities.contains(&(a, 123)));
/// assert!(entities.contains(&(b, 456)));
/// ```
pub struct With<T, Q>(PhantomData<(Q, fn(T))>);

impl<'c, T: Component, Q: Query<'c, C>, C: Clone + 'c> Query<'c, C> for With<T, Q> {
    type Fetch = FetchWith<T, Q::Fetch>;
}

#[doc(hidden)]
pub struct FetchWith<T, F>(F, PhantomData<fn(T)>);

unsafe impl<'q, 'c, T: Component, F: Fetch<'q, 'c, C>, C: Clone + 'c> Fetch<'q, 'c, C>
    for FetchWith<T, F>
{
    type Item = F::Item;

    fn dangling() -> Self {
        Self(F::dangling(), PhantomData)
    }

    fn access(archetype: &Archetype) -> Option<Access> {
        if archetype.has::<T>() {
            F::access(archetype)
        } else {
            None
        }
    }

    fn borrow(archetype: &Archetype) {
        F::borrow(archetype)
    }
    fn new(archetype: &Archetype) -> Option<Self> {
        if !archetype.has::<T>() {
            return None;
        }
        Some(Self(F::new(archetype)?, PhantomData))
    }

    fn release(archetype: &Archetype) {
        F::release(archetype)
    }

    unsafe fn get(&self, n: usize, id: Entity, context: C) -> F::Item {
        self.0.get(n, id, context)
    }
}

/// A borrow of a `World` sufficient to execute the query `Q`
///
/// Note that borrows are not released until this object is dropped.
pub struct QueryBorrow<'c, Q: Query<'c, C>, C: Clone + 'c> {
    meta: &'c [EntityMeta],
    archetypes: &'c [Archetype],
    borrowed: bool,
    context: C,
    _marker: PhantomData<Q>,
}

impl<'c, Q: Query<'c, C>, C: Clone + 'c> QueryBorrow<'c, Q, C> {
    pub(crate) fn new(meta: &'c [EntityMeta], archetypes: &'c [Archetype], context: C) -> Self {
        Self {
            meta,
            archetypes,
            borrowed: false,
            context,
            _marker: PhantomData,
        }
    }

    /// Execute the query
    ///
    /// Must be called only once per query.
    // The lifetime narrowing here is required for soundness.
    pub fn iter(&mut self) -> QueryIter<'_, 'c, Q, C> {
        self.borrow();
        unsafe { QueryIter::new(self.meta, self.archetypes, self.context.clone()) }
    }

    /// Like `iter`, but returns child iterators of at most `batch_size` elements
    ///
    /// Useful for distributing work over a threadpool.
    // The lifetime narrowing here is required for soundness.
    pub fn iter_batched(&mut self, batch_size: u32) -> BatchedIter<'_, 'c, Q, C> {
        self.borrow();
        unsafe { BatchedIter::new(self.meta, self.archetypes, self.context.clone(), batch_size) }
    }

    fn borrow(&mut self) {
        if self.borrowed {
            panic!(
                "called QueryBorrow::iter twice on the same borrow; construct a new query instead"
            );
        }
        for x in self.archetypes {
            // TODO: Release prior borrows on failure?
            if Q::Fetch::access(x) >= Some(Access::Read) {
                Q::Fetch::borrow(x);
            }
        }
        self.borrowed = true;
    }

    /// Transform the query into one that requires a certain component without borrowing it
    ///
    /// This can be useful when the component needs to be borrowed elsewhere and it isn't necessary
    /// for the iterator to expose its data directly.
    ///
    /// Equivalent to using a query type wrapped in `With`.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, true, "abc"));
    /// let b = world.spawn((456, false));
    /// let c = world.spawn((42, "def"));
    /// let entities = world.query::<&i32>()
    ///     .with::<bool>()
    ///     .iter()
    ///     .map(|(e, i)| (e, *i)) // Clone out of the world
    ///     .collect::<Vec<_>>();
    /// assert!(entities.contains(&(a, 123)));
    /// assert!(entities.contains(&(b, 456)));
    /// ```
    pub fn with<T: Component>(self) -> QueryBorrow<'c, With<T, Q>, C> {
        self.transform()
    }

    /// Transform the query into one that skips entities having a certain component
    ///
    /// Equivalent to using a query type wrapped in `Without`.
    ///
    /// # Example
    /// ```
    /// # use hecs::*;
    /// let mut world = World::new();
    /// let a = world.spawn((123, true, "abc"));
    /// let b = world.spawn((456, false));
    /// let c = world.spawn((42, "def"));
    /// let entities = world.query::<&i32>()
    ///     .without::<bool>()
    ///     .iter()
    ///     .map(|(e, i)| (e, *i)) // Clone out of the world
    ///     .collect::<Vec<_>>();
    /// assert_eq!(entities, &[(c, 42)]);
    /// ```
    pub fn without<T: Component>(self) -> QueryBorrow<'c, Without<T, Q>, C> {
        self.transform()
    }

    /// Helper to change the type of the query
    fn transform<R: Query<'c, C>>(mut self) -> QueryBorrow<'c, R, C> {
        let x = QueryBorrow {
            meta: self.meta,
            archetypes: self.archetypes,
            borrowed: self.borrowed,
            context: self.context.clone(),
            _marker: PhantomData,
        };
        // Ensure `Drop` won't fire redundantly
        self.borrowed = false;
        x
    }
}

unsafe impl<'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Send for QueryBorrow<'c, Q, C> {}
unsafe impl<'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Sync for QueryBorrow<'c, Q, C> {}

impl<'c, Q: Query<'c, C>, C: Clone + 'c> Drop for QueryBorrow<'c, Q, C> {
    fn drop(&mut self) {
        if self.borrowed {
            for x in self.archetypes {
                if Q::Fetch::access(x) >= Some(Access::Read) {
                    Q::Fetch::release(x);
                }
            }
        }
    }
}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> IntoIterator for &'q mut QueryBorrow<'c, Q, C> {
    type Item = (Entity, <Q::Fetch as Fetch<'q, 'c, C>>::Item);
    type IntoIter = QueryIter<'q, 'c, Q, C>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over the set of entities with the components in `Q`
pub struct QueryIter<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> {
    meta: &'q [EntityMeta],
    archetypes: &'q [Archetype],
    context: C,
    archetype_index: usize,
    iter: ChunkIter<'c, Q, C>,
}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> QueryIter<'q, 'c, Q, C> {
    /// # Safety
    ///
    /// `'q` must be sufficient to guarantee that `Q` cannot violate borrow safety, either with
    /// dynamic borrow checks or by representing exclusive access to the `World`.
    pub(crate) unsafe fn new(
        meta: &'q [EntityMeta],
        archetypes: &'q [Archetype],
        context: C,
    ) -> Self {
        Self {
            meta,
            archetypes,
            context,
            archetype_index: 0,
            iter: ChunkIter::empty(),
        }
    }
}

unsafe impl<'q, 'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Send for QueryIter<'q, 'c, Q, C> {}
unsafe impl<'q, 'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Sync for QueryIter<'q, 'c, Q, C> {}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> Iterator for QueryIter<'q, 'c, Q, C> {
    type Item = (Entity, <Q::Fetch as Fetch<'q, 'c, C>>::Item);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match unsafe { self.iter.next(self.meta, &self.context) } {
                None => {
                    let archetype = self.archetypes.get(self.archetype_index)?;
                    self.archetype_index += 1;
                    self.iter =
                        Q::Fetch::new(archetype).map_or(ChunkIter::empty(), |fetch| ChunkIter {
                            entities: archetype.entities(),
                            fetch,
                            position: 0,
                            len: archetype.len() as usize,
                            _context: PhantomData,
                        });
                    continue;
                }
                Some(item) => return Some(item),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.len();
        (n, Some(n))
    }
}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> ExactSizeIterator for QueryIter<'q, 'c, Q, C> {
    fn len(&self) -> usize {
        self.archetypes
            .iter()
            .filter(|&x| Q::Fetch::access(x).is_some())
            .map(|x| x.len() as usize)
            .sum()
    }
}

/// A query builder that's convertible directly into an iterator
pub struct QueryMut<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> {
    iter: QueryIter<'q, 'c, Q, C>,
}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> QueryMut<'q, 'c, Q, C> {
    pub(crate) fn new(meta: &'q [EntityMeta], archetypes: &'q mut [Archetype], context: C) -> Self {
        Self {
            iter: unsafe { QueryIter::new(meta, archetypes, context) },
        }
    }

    /// Transform the query into one that requires a certain component without borrowing it
    ///
    /// See `QueryBorrow::with`
    pub fn with<T: Component>(self) -> QueryMut<'q, 'c, With<T, Q>, C> {
        self.transform()
    }

    /// Transform the query into one that skips entities having a certain component
    ///
    /// See `QueryBorrow::without`
    pub fn without<T: Component>(self) -> QueryMut<'q, 'c, Without<T, Q>, C> {
        self.transform()
    }

    /// Helper to change the type of the query
    fn transform<R: Query<'c, C>>(self) -> QueryMut<'q, 'c, R, C> {
        QueryMut {
            iter: unsafe {
                QueryIter::new(self.iter.meta, self.iter.archetypes, self.iter.context)
            },
        }
    }
}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> IntoIterator for QueryMut<'q, 'c, Q, C> {
    type Item = <QueryIter<'q, 'c, Q, C> as Iterator>::Item;
    type IntoIter = QueryIter<'q, 'c, Q, C>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

struct ChunkIter<'c, Q: Query<'c, C>, C: Clone + 'c> {
    entities: NonNull<u32>,
    fetch: Q::Fetch,
    position: usize,
    len: usize,
    _context: PhantomData<*const C>,
}

impl<'c, Q: Query<'c, C>, C: Clone + 'c> ChunkIter<'c, Q, C> {
    fn empty() -> Self {
        Self {
            entities: NonNull::dangling(),
            fetch: Q::Fetch::dangling(),
            position: 0,
            len: 0,
            _context: PhantomData,
        }
    }

    #[inline]
    unsafe fn next<'a>(
        &mut self,
        meta: &[EntityMeta],
        context: &C,
    ) -> Option<(Entity, <Q::Fetch as Fetch<'a, 'c, C>>::Item)> {
        if self.position == self.len {
            return None;
        }
        let index = self.entities.as_ptr().add(self.position);
        let generation = meta.get_unchecked(*index as usize).generation;
        let id = Entity {
            id: *index,
            generation,
        };
        let item = self.fetch.get(self.position, id, context.clone());
        self.position += 1;
        Some((id, item))
    }
}

/// Batched version of `QueryIter`
pub struct BatchedIter<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> {
    _marker: PhantomData<(&'q Q, &'c C)>,
    meta: &'q [EntityMeta],
    archetypes: &'q [Archetype],
    context: C,
    archetype_index: usize,
    batch_size: u32,
    batch: u32,
}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> BatchedIter<'q, 'c, Q, C> {
    /// # Safety
    ///
    /// `'q` must be sufficient to guarantee that `Q` cannot violate borrow safety, either with
    /// dynamic borrow checks or by representing exclusive access to the `World`.
    pub(crate) unsafe fn new(
        meta: &'q [EntityMeta],
        archetypes: &'q [Archetype],
        context: C,
        batch_size: u32,
    ) -> Self {
        Self {
            _marker: PhantomData,
            meta,
            archetypes,
            archetype_index: 0,
            context,
            batch_size,
            batch: 0,
        }
    }
}

unsafe impl<'q, 'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Send for BatchedIter<'q, 'c, Q, C> {}
unsafe impl<'q, 'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Sync for BatchedIter<'q, 'c, Q, C> {}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> Iterator for BatchedIter<'q, 'c, Q, C> {
    type Item = Batch<'q, 'c, Q, C>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let archetype = self.archetypes.get(self.archetype_index)?;
            let offset = self.batch_size * self.batch;
            if offset >= archetype.len() {
                self.archetype_index += 1;
                self.batch = 0;
                continue;
            }
            if let Some(fetch) = Q::Fetch::new(archetype) {
                self.batch += 1;
                return Some(Batch {
                    meta: self.meta,
                    state: ChunkIter {
                        entities: archetype.entities(),
                        fetch,
                        len: (offset + self.batch_size.min(archetype.len() - offset)) as usize,
                        position: offset as usize,
                        _context: PhantomData,
                    },
                    context: self.context.clone(),
                });
            } else {
                self.archetype_index += 1;
                debug_assert_eq!(
                    self.batch, 0,
                    "query fetch should always reject at the first batch or not at all"
                );
                continue;
            }
        }
    }
}

/// A sequence of entities yielded by `BatchedIter`
pub struct Batch<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> {
    meta: &'q [EntityMeta],
    state: ChunkIter<'c, Q, C>,
    context: C,
}

impl<'q, 'c, Q: Query<'c, C>, C: Clone + 'c> Iterator for Batch<'q, 'c, Q, C> {
    type Item = (Entity, <Q::Fetch as Fetch<'q, 'c, C>>::Item);

    fn next(&mut self) -> Option<Self::Item> {
        unsafe { self.state.next(self.meta, &self.context) }
    }
}

unsafe impl<'q, 'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Send for Batch<'q, 'c, Q, C> {}
unsafe impl<'q, 'c, Q: Query<'c, C>, C: Clone + Sync + 'c> Sync for Batch<'q, 'c, Q, C> {}

macro_rules! tuple_impl {
    ($($name: ident),*) => {
        unsafe impl<'a, 'z, Z: Clone + 'z, $($name: Fetch<'a, 'z, Z>),*> Fetch<'a, 'z, Z> for ($($name,)*) {
            type Item = ($($name::Item,)*);

            fn dangling() -> Self {
                ($($name::dangling(),)*)
            }

            #[allow(unused_variables, unused_mut)]
            fn access(archetype: &Archetype) -> Option<Access> {
                let mut access = Access::Iterate;
                $(
                    access = access.max($name::access(archetype)?);
                )*
                Some(access)
            }

            #[allow(unused_variables)]
            fn borrow(archetype: &Archetype) {
                $($name::borrow(archetype);)*
            }

            #[allow(unused_variables)]
            fn new(archetype: &Archetype) -> Option<Self> {
                Some(($($name::new(archetype)?,)*))
            }

            #[allow(unused_variables)]
            fn release(archetype: &Archetype) {
                $($name::release(archetype);)*
            }

            #[allow(unused_variables)]
            unsafe fn get(&self, n: usize, id: Entity, context: Z) -> Self::Item {
                #[allow(non_snake_case)]
                let ($($name,)*) = self;
                ($($name.get(n, id, context.clone()),)*)
            }
        }

        impl<'z, Z: Clone + 'z, $($name: Query<'z, Z>),*> Query<'z, Z> for ($($name,)*) {
            type Fetch = ($($name::Fetch,)*);
        }
    };
}

//smaller_tuples_too!(tuple_impl, B, A);
smaller_tuples_too!(tuple_impl, O, N, M, L, K, J, I, H, G, F, E, D, C, B, A);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn access_order() {
        assert!(Access::Write > Access::Read);
        assert!(Access::Read > Access::Iterate);
        assert!(Some(Access::Iterate) > None);
    }
}
