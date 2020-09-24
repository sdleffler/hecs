use core::marker::PhantomData;

use crate::query::{Fetch, With, Without};
use crate::{Archetype, Component, Entity, Query, QueryItem};

/// A borrow of a `World` sufficient to execute the query `Q` on a single entity
pub struct QueryOne<'c, Q: Query<'c, C>, C: Copy + 'c> {
    archetype: &'c Archetype,
    index: u32,
    borrowed: bool,
    entity: Entity,
    context: C,
    _marker: PhantomData<Q>,
}

impl<'c, Q: Query<'c, C>, C: Copy + 'c> QueryOne<'c, Q, C> {
    /// Construct a query accessing the entity in `archetype` at `index`
    ///
    /// # Safety
    ///
    /// `index` must be in-bounds for `archetype`
    pub(crate) unsafe fn new(
        archetype: &'c Archetype,
        index: u32,
        entity: Entity,
        context: C,
    ) -> Self {
        Self {
            archetype,
            index,
            borrowed: false,
            entity,
            context,
            _marker: PhantomData,
        }
    }

    /// Get the query result, or `None` if the entity does not satisfy the query
    ///
    /// Must be called at most once.
    ///
    /// Panics if called more than once or if it would construct a borrow that clashes with another
    /// pre-existing borrow.
    // Note that this uses self's lifetime, not 'a, for soundness.
    pub fn get(&mut self) -> Option<QueryItem<'_, 'c, Q, C>> {
        if self.borrowed {
            panic!("called QueryOnce::get twice; construct a new query instead");
        }
        unsafe {
            let fetch = Q::Fetch::new(self.archetype)?;
            self.borrowed = true;
            Q::Fetch::borrow(self.archetype);
            Some(fetch.get(self.index as usize, self.entity, self.context))
        }
    }

    /// Transform the query into one that requires a certain component without borrowing it
    ///
    /// See `QueryBorrow::with` for details.
    pub fn with<T: Component>(self) -> QueryOne<'c, With<T, Q>, C> {
        self.transform()
    }

    /// Transform the query into one that skips entities having a certain component
    ///
    /// See `QueryBorrow::without` for details.
    pub fn without<T: Component>(self) -> QueryOne<'c, Without<T, Q>, C> {
        self.transform()
    }

    /// Helper to change the type of the query
    fn transform<R: Query<'c, C>>(mut self) -> QueryOne<'c, R, C> {
        let x = QueryOne {
            archetype: self.archetype,
            index: self.index,
            borrowed: self.borrowed,
            entity: self.entity,
            context: self.context,
            _marker: PhantomData,
        };
        // Ensure `Drop` won't fire redundantly
        self.borrowed = false;
        x
    }
}

impl<'c, Q: Query<'c, C>, C: Copy + 'c> Drop for QueryOne<'c, Q, C> {
    fn drop(&mut self) {
        if self.borrowed {
            Q::Fetch::release(self.archetype);
        }
    }
}

unsafe impl<'c, Q: Query<'c, C>, C: Copy + Sync + 'c> Send for QueryOne<'c, Q, C> {}
unsafe impl<'c, Q: Query<'c, C>, C: Copy + Sync + 'c> Sync for QueryOne<'c, Q, C> {}
