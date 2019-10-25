# Hangul
> Utilities to manipulate [Hangul Syllables][syllables].

![crates.io version][version] ![crates.io license][license] ![crates.io download][download]

Hangul is a library to manipulate [Hangul Syllables][syllables] in the [Rust] language.

## Overview
Hangul is an [extension trait] implemented for the primitive type [`char`]. Currently it has following methods:

- **Predicate** checks whether given [`char`] is a [Hangul Syllable][syllables]: _is\_syllable()_
- **Predicate** indicates whether the syllable has a jongseong — in other words, [closed]: _is\_open()_, _is\_closed()_
- **Getters** for choseong, jungseong, jongseong, and jamo: _choseong()_, _jungseong()_, _jongseong()_, _to\_jamo()_
- **Iterator** iterates over jamos consisting a syllable: _jamos()_


:warning: **This crate only deals with [Compatibility Jamo]**: If you need [Jamo], file a issue in this repository with your context.

## Usage
Add `hangul` as a dependency in your `Cargo.toml`.

```toml
[dependencies]
hangul = "0.1.1"
```

then import [`HangulExt`](trait.HangulExt.html) trait in your code:

```rust
use hangul::HangulExt;
```

Now you can use methods on [`char`].
```rust
use hangul::{HangulExt};

assert_eq!(
  "첫사랑"
    .chars()
    .flat_map(|c| c.jamos().unwrap())
    .collect::<String>(),
  "ㅊㅓㅅㅅㅏㄹㅏㅇ"
);
```

## Documentation
See [docs.rs][documentation]

## License
Distributed under the MIT license.

[syllables]: https://en.wikipedia.org/wiki/Hangul_Syllables
[version]: https://img.shields.io/crates/v/hangul
[license]: https://img.shields.io/crates/l/hangul
[download]: https://img.shields.io/crates/d/hangul
[Rust]: https://rust-lang.org
[extension trait]: https://github.com/rust-lang/rfcs/blob/master/text/0445-extension-trait-conventions.md
[`char`]: https://doc.rust-lang.org/std/primitive.char.html
[closed]: https://en.wikipedia.org/wiki/Syllable#Open_and_closed
[Compatibility Jamo]: https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo
[Jamo]: https://en.wikipedia.org/wiki/Hangul_Jamo_(Unicode_block)
[documentation]: https://docs.rs/hangul