//! This library provides functions to match a set of available languages
//! to those from the http `Accept-Language` header, urls, or other sources.
//!
//! Language tags (eg: `"en-au"`) are never validated,
//! this crate simply tries to make sense of whatever value it is given,
//! ignoring any input that it cannot understand, and find the best match
//! based on a few simple rules.
//!
//! This crate is inspired by Django's translation handling.
//!
//! # Features
//!
//! - No unsafe code (`#[forbid(unsafe_code)]`)
//! - No panics
//! - Tested; code coverage: 100% (morally)
//! - No dependencies
//!
//! # Examples
//!
//! Simply pass an iterable of language tags to find the best match.
//!
//! ```
//! use web_lang::{match_lang, match_accept};
//!
//! // match a single language tag
//! assert_eq!(
//!     match_lang(
//!         ["en", "en-au", "de"],
//!         "en-gb"
//!     ),
//!     Some("en")
//! );
//!
//! // match a set of language tags,
//! // taken from the http `Accept-Language` header
//! assert_eq!(
//!     match_accept(
//!         ["en", "en-au", "de"],
//!         "de;q=0.5, en-gb;q=0.9, ja;q=0.2, *;q=0.1"
//!     ),
//!     Some("en")
//! );
//! ```
//!
//! Complete example with a custom language enum.
//!
//! ```
//! use web_lang::{Language, match_lang, match_accept};
//!
//! #[derive(Copy, Clone, PartialEq, Debug)]
//! enum MyLanguage {
//!     English,
//!     AustralianEnglish,
//!     German,
//!     Japanese,
//! }
//!
//! impl Language for MyLanguage {
//!     fn tag(&self) -> &str {
//!         match self {
//!             Self::English => "en",
//!             Self::AustralianEnglish => "en-au",
//!             Self::German => "de",
//!             Self::Japanese => "ja",
//!         }
//!     }
//! }
//!
//! const LANGUAGES: &[MyLanguage] = &[
//!     MyLanguage::English,
//!     MyLanguage::AustralianEnglish,
//!     MyLanguage::German,
//!     MyLanguage::Japanese
//! ];
//!
//! // match a single language tag
//! assert_eq!(
//!     match_lang(
//!         LANGUAGES.iter().copied(),
//!         "en-gb"
//!     ),
//!     Some(MyLanguage::English)
//! );
//!
//! // match a set of language tags,
//! // taken from the http `Accept-Language` header
//! assert_eq!(
//!     match_accept(
//!         LANGUAGES.iter().copied(),
//!         "de;q=0.5, en-gb;q=0.9, ja;q=0.2, *;q=0.1"
//!     ),
//!     Some(MyLanguage::English)
//! );
//! ```

#![forbid(unsafe_code)]

/// The "quality" of an accepted language.
///
/// Higher values are preferred.
#[derive(Clone, Copy, Debug)]
struct Quality(f32);

impl Ord for Quality {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl PartialOrd for Quality {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Quality {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for Quality {}

impl PartialEq<f32> for Quality {
    fn eq(&self, other: &f32) -> bool {
        self.0 == *other
    }
}

impl From<Quality> for f32 {
    fn from(q: Quality) -> f32 {
        q.0
    }
}

impl TryFrom<f32> for Quality {
    type Error = ();

    fn try_from(f: f32) -> Result<Quality, ()> {
        if f.is_finite() {
            Ok(Quality(f))
        } else {
            Err(())
        }
    }
}

impl std::str::FromStr for Quality {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value: f32 = s.parse().map_err(|_| ())?;
        if value.is_finite() {
            Ok(Quality(value))
        } else {
            Err(())
        }
    }
}

/// An accepted language with a ["quality"](Quality) indication.
///
/// This type corresponds to a single item from
/// the http `Accept-Language` header, for example: `en;q=0.9`.
#[derive(Clone, PartialEq, Eq, Debug)]
struct AcceptLanguage<'a> {
    /// The language tag; for example `en` or `en-au`.
    ///
    /// This field is [`None`] for wildcard (`*`).
    pub language: Option<&'a str>,
    /// The "quality"; higher values are preferred.
    pub quality: Quality,
}

/// Parse a single language with optional ["quality"](Quality)
/// as found in the http `Accept-Language` header.
///
/// This function always returns a result,
/// even for invalid input.
fn parse_accept_single(accept: &str) -> AcceptLanguage<'_> {
    if let Some((language, quality)) = accept.split_once("q=") {
        let language = language.trim_end();
        if let Some(language) = language.strip_suffix(';') {
            let language = language.trim_end();
            AcceptLanguage {
                language: if language.starts_with('*') {
                    None
                } else {
                    Some(language)
                },
                quality: quality.trim_start().parse().unwrap_or(Quality(0.0)),
            }
        } else {
            // missing ";" separator: "lang-tag-q=1.0"
            // assume the "q" is part of the language
            debug_assert!(accept.len() >= language.len() + 2);
            debug_assert!(&accept[language.len()..(language.len() + 1)] == "q");
            let language = &accept[..(language.len() + 1)];
            AcceptLanguage {
                language: if language.starts_with('*') {
                    None
                } else {
                    Some(language)
                },
                quality: quality.trim_start().parse().unwrap_or(Quality(1.0)),
            }
        }
    } else if accept.is_empty() {
        AcceptLanguage {
            language: None,
            quality: Quality(0.0),
        }
    } else {
        AcceptLanguage {
            language: if accept.starts_with('*') {
                None
            } else {
                Some(accept)
            },
            quality: Quality(1.0),
        }
    }
}

/// Parse a list of languages with optional ["qualities"](Quality)
/// as found in the http `Accept-Language` header.
///
/// This function returns a vector sorted by descending quality.
/// The order of items with identical qualities is preserved.
///
/// Note that languages with a quality lower than the wildcard (`*`)
/// are preserved in the result vector.
fn parse_accept(accept: &str) -> Vec<AcceptLanguage<'_>> {
    let mut languages = accept
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(parse_accept_single)
        .collect::<Vec<_>>();
    languages.sort_by_key(|lang| Quality(-lang.quality.0));
    languages
}

/// Get a fallback language tag.
fn fallback(language: &str) -> Option<&'static str> {
    match language {
        "zh-cn" => Some("zh-hans"),
        "zh-hk" => Some("zh-hant"),
        "zh-mo" => Some("zh-hant"),
        "zh-my" => Some("zh-hans"),
        "zh-sg" => Some("zh-hans"),
        "zh-tw" => Some("zh-hant"),
        _ => None,
    }
}

/// Get a sequence of language prefixes, starting from the language itself.
fn prefixes(language: &str) -> impl Iterator<Item = &str> {
    std::iter::successors(Some(language), |language| {
        language.rsplit_once('-').map(|(prefix, _)| prefix)
    })
}

/// Get a sequence of language alternatives.
///
/// The returned iterator yields the following items.
///   * The first item is the language itself.
///   * The next item is a possible language fallback.
///   * The last items are all other language prefixes,
///     as returned by [`prefixes()`].
///
/// Most languages don't have a fallback, in which case
/// the result is exactly the same as for [`prefixes()`].
fn alternatives(language: &str) -> impl Iterator<Item = &str> {
    std::iter::once(language)
        .chain(fallback(language))
        .chain(prefixes(language).skip(1))
}

/// Interface for a language.
///
/// This trait enables compatibility with your own language enum.
/// Alternatively, you can simply use [`&str`] or [`String`] language tags.
///
/// # Examples
///
/// ```
/// use web_lang::Language;
///
/// enum MyLanguage {
///     English,
///     AustralianEnglish,
///     German,
///     Japanese,
/// }
///
/// impl Language for MyLanguage {
///     fn tag(&self) -> &str {
///         match self {
///             Self::English => "en",
///             Self::AustralianEnglish => "en-au",
///             Self::German => "de",
///             Self::Japanese => "ja",
///         }
///     }
/// }
/// ```
pub trait Language {
    /// The language "tag", for example `en` or `en-au`.
    fn tag(&self) -> &str;
}

impl Language for &str {
    fn tag(&self) -> &str {
        self
    }
}

impl Language for String {
    fn tag(&self) -> &str {
        self
    }
}

/// Tries to match an available language to a single accepted language.
///
/// This function can be used to match a language from
/// a single language tag, for example from a url.
///
/// Languages matching is case-insensitive.
///
/// ```
/// use web_lang::match_lang;
///
/// assert_eq!(
///     match_lang(
///         ["en", "en-au", "de"],
///         "en-gb"
///     ),
///     Some("en")
/// );
/// ```
pub fn match_lang<L: Language>(
    available: impl IntoIterator<Item = L> + Clone,
    accept: &str,
) -> Option<L> {
    for accept_lang in alternatives(accept) {
        for avail in available.clone() {
            if accept_lang.eq_ignore_ascii_case(avail.tag()) {
                return Some(avail);
            }
        }
    }
    None
}

/// Tries to match an available language to a list of accepted languages.
///
/// This function expects the list of accepted languages
/// to be sorted by descending quality.
///
/// Languages matching is case-insensitive.
/// Only accepted languages with positive quality are considered.
fn match_multi<L: Language>(
    available: impl IntoIterator<Item = L> + Clone,
    accepted: &[AcceptLanguage<'_>],
) -> Option<L> {
    for accept in accepted {
        if accept.quality <= Quality(0.0) {
            return None;
        }
        if let Some(accept_lang) = accept.language {
            let r#match = match_lang(available.clone(), accept_lang);
            if let Some(language) = r#match {
                return Some(language);
            }
        } else {
            return None;
        }
    }
    None
}

/// Tries to match an available language to a set of accepted languages.
///
/// This function can be used to match a language from
/// the http `Accept-Language` header.
///
/// Languages matching is case-insensitive.
/// Only accepted languages with positive quality are considered.
///
/// # Examples
///
/// ```
/// use web_lang::match_accept;
///
/// assert_eq!(
///     match_accept(
///         ["en", "en-au", "de"],
///         "de;q=0.5, en-gb;q=0.9, ja;q=0.2, *;q=0.1"
///     ),
///     Some("en")
/// );
/// ```
pub fn match_accept<L: Language>(
    available: impl IntoIterator<Item = L> + Clone,
    accept: &str,
) -> Option<L> {
    match_multi(available, &parse_accept(accept))
}

#[cfg(test)]
mod tests {
    use super::{
        alternatives, match_accept, match_lang, parse_accept,
        parse_accept_single, prefixes, AcceptLanguage, Quality,
    };

    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum Language {
        English,
        German,
        Japanese,
    }

    impl super::Language for Language {
        fn tag(&self) -> &str {
            match self {
                Self::English => "en",
                Self::German => "de",
                Self::Japanese => "ja",
            }
        }
    }

    const LANGUAGES: &[Language] =
        &[Language::English, Language::German, Language::Japanese];

    #[test]
    fn quality_cmp() {
        assert_eq!(Quality(0.5), Quality(0.5));
        assert_ne!(Quality(0.5), Quality(0.6));
        assert!(Quality(0.5) < Quality(0.6));
        assert!(Quality(0.7) > Quality(0.6));
        assert!(Quality(0.5) <= Quality(0.6));
        assert!(Quality(0.7) >= Quality(0.6));
        assert!(Quality(0.5) >= Quality(0.5));
        assert!(Quality(0.5) <= Quality(0.5));
    }

    #[test]
    fn quality_cmp_float() {
        assert_eq!(Quality(0.5), 0.5);
        assert_ne!(Quality(0.5), 0.6);
    }

    #[test]
    fn quality_into_float() {
        assert_eq!(f32::from(Quality(0.5)), 0.5);
    }

    #[test]
    fn quality_from_float() {
        assert_eq!(Quality::try_from(0.5), Ok(Quality(0.5)));
        assert_eq!(Quality::try_from(f32::INFINITY), Err(()));
        assert_eq!(Quality::try_from(f32::NEG_INFINITY), Err(()));
        assert_eq!(Quality::try_from(f32::NAN), Err(()));
    }

    #[test]
    fn test_parse_accept_single() {
        assert_eq!(
            parse_accept_single("en"),
            AcceptLanguage {
                language: Some("en"),
                quality: Quality(1.0),
            }
        );
        assert_eq!(
            parse_accept_single("en;q=0.5"),
            AcceptLanguage {
                language: Some("en"),
                quality: Quality(0.5),
            }
        );
        assert_eq!(
            parse_accept_single("*"),
            AcceptLanguage {
                language: None,
                quality: Quality(1.0),
            }
        );
        assert_eq!(
            parse_accept_single("*x"),
            AcceptLanguage {
                language: None,
                quality: Quality(1.0),
            }
        );
        assert_eq!(
            parse_accept_single("*;q=0.5"),
            AcceptLanguage {
                language: None,
                quality: Quality(0.5),
            }
        );
        assert_eq!(
            parse_accept_single("q=0.5"),
            AcceptLanguage {
                language: Some("q"),
                quality: Quality(0.5),
            }
        );
        assert_eq!(
            parse_accept_single("*q=0.5"),
            AcceptLanguage {
                language: None,
                quality: Quality(0.5),
            }
        );
        assert_eq!(
            parse_accept_single("en;q=x"),
            AcceptLanguage {
                language: Some("en"),
                quality: Quality(0.0),
            }
        );
        assert_eq!(
            parse_accept_single("en;q=inf"),
            AcceptLanguage {
                language: Some("en"),
                quality: Quality(0.0),
            }
        );
        assert_eq!(
            parse_accept_single("en;q=nan"),
            AcceptLanguage {
                language: Some("en"),
                quality: Quality(0.0),
            }
        );
        assert_eq!(
            parse_accept_single(""),
            AcceptLanguage {
                language: None,
                quality: Quality(0.0),
            }
        );
    }

    #[test]
    fn test_parse_accept() {
        assert_eq!(
            parse_accept("en, ja;q=0.2, , de;q=0.5, *;q=0.1"),
            vec![
                AcceptLanguage {
                    language: Some("en"),
                    quality: Quality(1.0),
                },
                AcceptLanguage {
                    language: Some("de"),
                    quality: Quality(0.5),
                },
                AcceptLanguage {
                    language: Some("ja"),
                    quality: Quality(0.2),
                },
                AcceptLanguage {
                    language: None,
                    quality: Quality(0.1),
                },
            ]
        );
    }

    #[test]
    fn test_prefixes() {
        assert_eq!(
            prefixes("a-b-c").collect::<Vec<_>>(),
            vec!["a-b-c", "a-b", "a"],
        )
    }

    #[test]
    fn test_alternatives() {
        assert_eq!(
            alternatives("a-b-c").collect::<Vec<_>>(),
            vec!["a-b-c", "a-b", "a"]
        );
        assert_eq!(
            alternatives("zh-cn").collect::<Vec<_>>(),
            vec!["zh-cn", "zh-hans", "zh"]
        );
    }

    #[test]
    fn test_match_lang() {
        let languages = LANGUAGES.iter().copied();
        assert_eq!(
            match_lang(languages.clone(), "en"),
            Some(Language::English)
        );
        assert_eq!(
            match_lang(languages.clone(), "en-gb"),
            Some(Language::English)
        );
        assert_eq!(match_lang(languages.clone(), "de"), Some(Language::German));
        assert_eq!(
            match_lang(languages.clone(), "de-de"),
            Some(Language::German)
        );
        assert_eq!(
            match_lang(languages.clone(), "ja"),
            Some(Language::Japanese)
        );
        assert_eq!(
            match_lang(languages.clone(), "ja-ja"),
            Some(Language::Japanese)
        );
        assert_eq!(match_lang(languages.clone(), "fi"), None);
        assert_eq!(match_lang(languages.clone(), ""), None);
    }

    #[test]
    fn test_match_lang_case() {
        assert_eq!(match_lang(["DE", "EN", "JA"], "en"), Some("EN"));
    }

    #[test]
    fn test_match_lang_string() {
        assert_eq!(
            match_lang(["de".to_string(), "en".to_string()], "en"),
            Some("en".to_string())
        );
    }

    #[test]
    fn test_match_accept() {
        let languages = LANGUAGES.iter().copied();
        assert_eq!(
            match_accept(languages.clone(), "en"),
            Some(Language::English)
        );
        assert_eq!(
            match_accept(languages.clone(), "en, de, ja"),
            Some(Language::English)
        );
        assert_eq!(
            match_accept(languages.clone(), "en-gb, de, ja"),
            Some(Language::English)
        );
        assert_eq!(
            match_accept(languages.clone(), "de"),
            Some(Language::German)
        );
        assert_eq!(
            match_accept(languages.clone(), "en;q=0.1, de;q=0.9"),
            Some(Language::German)
        );
        assert_eq!(match_accept(languages.clone(), ""), None);
        assert_eq!(match_accept(languages.clone(), "fi"), None);
        assert_eq!(match_accept(languages.clone(), "en;q=-1"), None);
        assert_eq!(match_accept(languages.clone(), "de;q=0.5, *;q=0.8"), None);
    }
}
