# Web-Lang

[![Build status](https://github.com/alvra/web-lang/actions/workflows/check.yml/badge.svg?branch=main)](https://github.com/alvra/web-lang/actions/workflows/check.yml)
[![Crates.io](https://img.shields.io/crates/v/web-lang)](https://crates.io/crates/web-lang)
[![Documentation](https://docs.rs/web-lang/badge.svg)](https://docs.rs/web-lang)
![License](https://img.shields.io/crates/l/web-lang)
[![unsafe forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)

Match a languages from the http `Accept-Language` header, urls, or other sources.

Language tags (eg: `"en-au"`) are never validated,
this crate simply tries to make sense of whatever value it is given,
ignoring any input that it cannot understand, and find the best match
based on a few simple rules.

This crate is inspired by Django's translation handling.

## Features

  * No unsafe code (`#[forbid(unsafe_code)]`)
  * No panics
  * Tested; code coverage: 100% (morally)
  * No dependencies

## Example

Simply pass an iterable of language tags and the `Accept-Language` header
to find the best match.

```rust
assert_eq!(
    match_accept(
        ["en", "en-au", "de"],
        "de;q=0.5, en-gb;q=0.9, ja;q=0.2, *;q=0.1"
    ),
    Some("en")
);
```

Complete example with a custom language enum.

```rust
use web_lang::{Language, match_accept};

#[derive(Copy, Clone, PartialEq, Debug)]
enum MyLanguage {
    English,
    AustralianEnglish,
    German,
    Japanese,
}

impl Language for MyLanguage {
    fn tag(&self) -> &str {
        match self {
            Self::English => "en",
            Self::AustralianEnglish => "en-au",
            Self::German => "de",
            Self::Japanese => "ja",
        }
    }
}

const LANGUAGES: &[MyLanguage] = &[
    MyLanguage::English,
    MyLanguage::AustralianEnglish,
    MyLanguage::German,
    MyLanguage::Japanese
];

// Use your own language enum.
assert_eq!(
    match_accept(
        LANGUAGES.iter().copied(),
        "de;q=0.5, en-gb;q=0.9, ja;q=0.2, *;q=0.1"
    ),
    Some(MyLanguage::English)
);
```

## Documentation

[Documentation](https://lib.rs/crates/web-lang)

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
