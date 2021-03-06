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

extern crate proc_macro;

mod bundle;
mod query;

use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

/// Implement `Bundle` for a struct
///
/// Bundles can be passed directly to `World::spawn` and `World::insert`, and obtained from
/// `World::remove`. Monomorphic `Bundle` implementations are slightly more efficient than the
/// polymorphic implementations for tuples, and can be convenient when combined with other derives
/// like `serde::Deserialize`.
///
/// # Example
/// ```ignore
/// #[derive(Bundle)]
/// struct Foo {
///     x: i32,
///     y: char,
/// }
///
/// let mut world = World::new();
/// let e = world.spawn(Foo { x: 42, y: 'a' });
/// assert_eq!(*world.get::<i32>(e).unwrap(), 42);
/// ```
#[proc_macro_derive(Bundle)]
pub fn derive_bundle(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match bundle::derive(input) {
        Ok(ts) => ts,
        Err(e) => e.to_compile_error(),
    }
    .into()
}

/// Implement `Query` for a struct
///
/// Queries structs can be passed to the type parameter of `World::query`. They must have exactly
/// one lifetime parameter, and all of their fields must be queries (e.g. references) using that
/// lifetime.
///
/// # Example
/// ```ignore
/// #[derive(Query, Debug, PartialEq)]
/// struct Foo<'a> {
///     x: &'a i32,
///     y: &'a mut bool,
/// }
///
/// let mut world = World::new();
/// let e = world.spawn((42, false));
/// assert_eq!(
///     world.query_one_mut::<Foo>(e).unwrap(),
///     Foo {
///         x: &42,
///         y: &mut false
///     }
/// );
/// ```
#[proc_macro_derive(Query)]
pub fn derive_query(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match query::derive(input) {
        Ok(ts) => ts,
        Err(e) => e.to_compile_error(),
    }
    .into()
}
