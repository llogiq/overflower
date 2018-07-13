# overflower

[![Build Status](https://travis-ci.org/llogiq/overflower.svg)](https://travis-ci.org/llogiq/overflower)
[![Current Version](https://img.shields.io/crates/v/overflower.svg)](https://crates.io/crates/overflower)

This project contains a compiler plugin and supporting library to allow the
programmer to annotate their code to declare how integer overflows should be
dealt with.

# Usage

**Note**: This needs a nightly compiler both for the compiler plugin and the
supporting library, as the latter makes use of specialization, which is
unstable for now.

To use it, you need the following in your Cargo.toml:

```toml
[dependencies]
overflower = "0.4.4"
overflower_support = "0.1.5"
```

You may also make it an optional dependency (`overflower = { version = "0.4.4",
optional = true }`).

Next, in your crate root, you need to add:

```rust
#![feature(plugin)]
#![plugin(overflower)]

extern crate overflower_support;

// Now you can annotate items (up to and including the whole crate)
#[overflow(panic)]
fn panic_on_overflow() { .. }

#[overflow(wrap)]
fn like_you_just_dont_care() { .. }

#[overflow(saturate)]
fn too_much_sunlight() {
    #[overflow(default)]
    fn but_use_standard_ops_here() { .. }
    ..
}
```

In case of an optional dependency, you'd add the following instead:

```rust
#![cfg_attr(feature="overflower", feature(plugin))]
#![cfg_attr(feature="overflower", plugin(overflower))]

#[cfg(feature="overflower")
extern crate overflower_support;

// as well as the following instead of e.g. `#[overflow(wrap)]`
#[cfg_attr(feature="overflower", overflow(wrap))];
```

This is a bit of a work in progress, but most things should already be usable.

License: Apache 2.0
