const CHOSEONG_TO_JAMO: [u32; 19] = [
  1, 2, 4, 7, 8, 9, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
];

const JUNGSEONG_START: u32 = 0x1161;
const JUNGSEONG_END: u32 = 0x1175;
const JUNGSEONG_COUNT: u32 = JUNGSEONG_END - JUNGSEONG_START + 1;

const JONGSEONG_START: u32 = 0x11A8;
const JONGSEONG_END: u32 = 0x11C2;
const JONGSEONG_COUNT: u32 = JONGSEONG_END - JONGSEONG_START + 2; // + 1 for empty jongseong
const JONGSEONG_TO_JAMO: [u32; 27] = [
  1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 26, 27, 28, 29,
  30,
];

const JAMO_START: u32 = 0x3130;

const SYLLABLE_START: u32 = 0xAC00; // 가
const SYLLABLE_END: u32 = 0xD7A3; // 힣

/// Utilities to handle the [Hangul syllables][syllables].
///
/// This trait extends [`char`][char] with methods including:
///
/// - _Predicate_ checks whether given [`char`][char] is a [Hangul syllable][syllables]
/// - _Predicate_ indicates whether the syllable has a jongseong — in other words, closed
/// - _Getters_ for choseong, jungseong, jongseong, and jamo
/// - _Iterator_ iterates over jamos consisting a syllable
///
/// To use these methods, add this to your `Cargo.toml`:
///
/// ```toml
/// [dependencies]
/// hangul = "0.1.1"
/// ```
///
/// then import [`HangulExt`](trait.HangulExt.html) trait:
///
/// ```
/// use hangul::HangulExt;
/// ```
///
/// Now you can use the methods.
///
/// ```
/// use hangul::HangulExt;
///
/// assert_eq!('京'.is_syllable(), false);
/// assert_eq!('설'.to_jamo(), Ok(( 'ㅅ', 'ㅓ', Some('ㄹ'))));
/// ```
/// [syllables]: https://en.wikipedia.org/wiki/Hangul_Syllables
/// [char]: https://doc.rust-lang.org/std/primitive.char.html
pub trait HangulExt {
  fn is_syllable(self) -> bool;
  fn is_open(self) -> Result<bool, ParseSyllableError>;
  fn is_closed(self) -> Result<bool, ParseSyllableError>;
  fn choseong(self) -> Result<char, ParseSyllableError>;
  fn jungseong(self) -> Result<char, ParseSyllableError>;
  fn jongseong(self) -> Result<Option<char>, ParseSyllableError>;
  fn to_jamo(self) -> Result<(char, char, Option<char>), ParseSyllableError>;
  fn jamos(self) -> Result<Jamos, ParseSyllableError>;
}

/// An error which can be returned when a given [`char`][char] is not in a [Hangul syllables][syllables].
///
/// Unicode Hangul Syllables is a Unicode block range from `U+AC00` to `U+D7AF`. Since [`char`][char] covers much larger range,
/// there's a chance where char is not in a Hangul syllable. In that case, [`ParseSyllableError`](struct.ParseSyllableError.html) is returned.
/// [syllables]: https://en.wikipedia.org/wiki/Hangul_Syllables
/// [char]: https://doc.rust-lang.org/std/primitive.char.html
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct ParseSyllableError;

/// An iterator over the [jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) [`char`][char]s of the [syllable](https://en.wikipedia.org/wiki/Hangul_Syllables).
///
/// This struct is created by the [`jamos`](trait.HangulExt.html#method.jamos) method on [`char`][char] extended with [`HangulExt`] trait. See its documentation for more.
/// [char]: https://doc.rust-lang.org/std/primitive.char.html
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct Jamos {
  value: Vec<char>,
}

impl Iterator for Jamos {
  type Item = char;

  fn next(&mut self) -> Option<char> {
    self.value.pop()
  }
}

impl HangulExt for char {
  /// Tests whether the [`char`][char] is a [Hangul syllable](https://en.wikipedia.org/wiki/Hangul_Syllables).
  ///
  /// # Example
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('냐'.is_syllable(), true);
  /// assert_eq!('猫'.is_syllable(), false); // 猫 is a Chinese character
  /// ```
  /// [char]: https://doc.rust-lang.org/std/primitive.char.html
  fn is_syllable(self) -> bool {
    let cp = self as u32; // cp stands for (Unicode) code point
    cp >= SYLLABLE_START && cp <= SYLLABLE_END
  }

  /// Tests whether [`char`](https://doc.rust-lang.org/std/primitive.char.html) is an [open](https://en.wikipedia.org/wiki/Syllable#Open_and_closed) syllable, i.e., doesn't have jongseong.
  ///
  /// # Errors
  ///
  /// If it's not a syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html).
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('Ж'.is_open(), Err(ParseSyllableError));
  /// ```
  ///
  /// # Example
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('해'.is_open().unwrap(), true); // 해 is open because it doesn't have any jongseong.
  /// assert_eq!('달'.is_open().unwrap(), false); // 달 is open because it has a jongseong ㄹ.
  /// ```
  fn is_open(self) -> Result<bool, ParseSyllableError> {
    self.jongseong().map(|j| j.is_none())
  }

  /// Tests whether [`char`](https://doc.rust-lang.org/std/primitive.char.html) is a [closed](https://en.wikipedia.org/wiki/Syllable#Open_and_closed) syllable, i.e., has jongseong.
  ///
  /// # Errors
  ///
  /// If it's not a syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html).
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('א'.is_closed(), Err(ParseSyllableError));
  /// ```
  ///
  /// # Example
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('물'.is_closed().unwrap(), true); // 물 is closed because it has a jongseong ㄹ.
  /// assert_eq!('무'.is_closed().unwrap(), false); // 무 is open because it doesn't have any jongseong.
  /// ```
  fn is_closed(self) -> Result<bool, ParseSyllableError> {
    self.jongseong().map(|j| j.is_some())
  }

  /// Returns [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) choseong of a given [`char`](https://doc.rust-lang.org/std/primitive.char.html).
  ///
  /// # Errors
  ///
  /// If it's not a syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html).
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('🥑'.choseong(), Err(ParseSyllableError));
  /// ```
  ///
  /// # Examples
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('항'.choseong().unwrap(), 'ㅎ');
  /// ```
  ///
  /// Note that [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) is different from [jamo](https://en.wikipedia.org/wiki/Hangul_Jamo_(Unicode_block)).
  /// This crate only deals with the [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo).
  /// ```
  /// use hangul::HangulExt;
  ///
  /// // Jamo
  /// let p = 'ᄑ';
  /// assert_eq!(p as u32, 0x1111);
  ///
  /// // Compatibility jamo
  /// let p_compat = '푸'.choseong().unwrap();
  /// assert_eq!(p_compat, 'ㅍ');
  /// assert_eq!(p_compat as u32, 0x314D);
  ///
  /// assert_ne!(p_compat, p);
  /// ```
  fn choseong(self) -> Result<char, ParseSyllableError> {
    if self.is_syllable() {
      let choseong_offset = (offset(self) / JONGSEONG_COUNT / JUNGSEONG_COUNT) as usize;
      Ok(std::char::from_u32(JAMO_START + CHOSEONG_TO_JAMO[choseong_offset]).unwrap())
    } else {
      Err(ParseSyllableError)
    }
  }

  /// Returns [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) jungseong of a given [`char`](https://doc.rust-lang.org/std/primitive.char.html).
  ///
  /// # Errors
  ///
  /// If it's not a syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html).
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('L'.jungseong(), Err(ParseSyllableError));
  /// ```
  ///
  /// # Examples
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('괴'.jungseong().unwrap(), 'ㅚ');
  /// ```
  ///
  /// Note that [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) is different from [jamo](https://en.wikipedia.org/wiki/Hangul_Jamo_(Unicode_block)).
  /// This crate only deals with the [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo).
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// // Jamo
  /// let u = 'ᅲ';
  /// assert_eq!(u as u32, 0x1172);
  ///
  /// // Compatibility jamo
  /// let u_compat = '퓨'.jungseong().unwrap();
  /// assert_eq!(u_compat, 'ㅠ');
  /// assert_eq!(u_compat as u32, 0x3160);
  ///
  /// assert_ne!(u_compat, u);
  /// ```
  fn jungseong(self) -> Result<char, ParseSyllableError> {
    if self.is_syllable() {
      let jungseong_offset = (offset(self) / JONGSEONG_COUNT % JUNGSEONG_COUNT) as u32;
      Ok(std::char::from_u32(JAMO_START + jungseong_offset + 31).unwrap())
    } else {
      Err(ParseSyllableError)
    }
  }

  /// Returns [`Option`](https://doc.rust-lang.org/stable/std/option/) of a [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) jongseong of a given [`char`](https://doc.rust-lang.org/std/primitive.char.html).
  ///
  /// # Errors
  ///
  /// If it's not a syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html).
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('か'.jongseong(), Err(ParseSyllableError)); // か is a katakana
  /// ```
  ///
  /// # Examples
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('말'.jongseong().unwrap(), Some('ㄹ'));
  /// assert_eq!('소'.jongseong().unwrap(), None);
  /// ```
  ///
  /// Note that [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) is different from [jamo](https://en.wikipedia.org/wiki/Hangul_Jamo_(Unicode_block)).
  /// This crate only deals with the [compatibility jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo).
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// // Jamo
  /// let rg = 'ᆰ';
  /// assert_eq!(rg as u32, 0x11B0);
  ///
  /// // Compatibility jamo
  /// let rg_compat = '닭'.jongseong().unwrap().unwrap();
  /// assert_eq!(rg_compat, 'ㄺ');
  /// assert_eq!(rg_compat as u32, 0x313A);
  ///
  /// assert_ne!(rg_compat, rg);
  /// ```
  fn jongseong(self) -> Result<Option<char>, ParseSyllableError> {
    if self.is_syllable() {
      let jongseong_offset = (offset(self) % JONGSEONG_COUNT) as usize;
      if jongseong_offset > 0 {
        Ok(std::char::from_u32(
          JAMO_START + JONGSEONG_TO_JAMO[jongseong_offset - 1],
        ))
      } else {
        Ok(None)
      }
    } else {
      Err(ParseSyllableError)
    }
  }

  /// # Examples
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('결'.to_jamo(), Ok(('ㄱ', 'ㅕ', Some('ㄹ'))));
  /// assert_eq!('씨'.to_jamo(), Ok(('ㅆ', 'ㅣ', None)));
  /// assert_eq!('a'.to_jamo(), Err(ParseSyllableError));
  /// ```
  ///
  fn to_jamo(self) -> Result<(char, char, Option<char>), ParseSyllableError> {
    if self.is_syllable() {
      Ok((
        self.choseong().unwrap(),
        self.jungseong().unwrap(),
        self.jongseong().unwrap(),
      ))
    } else {
      Err(ParseSyllableError)
    }
  }

  /// Returns an iterator over the jamos of the syllable.
  ///
  /// # Errors
  ///
  /// If given [`char`](https://doc.rust-lang.org/std/primitive.char.html) is not a syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html).
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('K'.jamos(), Err(ParseSyllableError));
  /// ```
  ///
  /// # Examples
  ///
  /// Basic usage:
  ///
  /// ```
  /// use hangul::{HangulExt};
  ///
  /// let mut jamos = '활'.jamos().unwrap();
  ///
  /// assert_eq!(jamos.next(), Some('ㅎ'));
  /// assert_eq!(jamos.next(), Some('ㅘ'));
  /// assert_eq!(jamos.next(), Some('ㄹ'));
  ///
  /// assert_eq!(jamos.next(), None);
  ///
  /// ```
  ///
  /// You can use it with [`iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) methods like [`flat_map`](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.flat_map) or [`fold`](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.fold) to decompose Hangul String.
  ///
  /// ```
  /// use hangul::{HangulExt};
  ///
  /// assert_eq!(
  ///   "첫사랑"
  ///     .chars()
  ///     .flat_map(|c| c.jamos().unwrap())
  ///     .collect::<String>(),
  ///   "ㅊㅓㅅㅅㅏㄹㅏㅇ"
  /// );
  ///
  /// assert_eq!(
  ///   "첫사랑은 두 번 다시 겪을 수 없다."
  ///     .chars()
  ///     .fold("".to_owned(), |acc, c| acc
  ///       + &c
  ///         .jamos()
  ///         .map(|j| j.collect::<String>())
  ///         .unwrap_or(c.to_string())),
  ///   "ㅊㅓㅅㅅㅏㄹㅏㅇㅇㅡㄴ ㄷㅜ ㅂㅓㄴ ㄷㅏㅅㅣ ㄱㅕㄲㅇㅡㄹ ㅅㅜ ㅇㅓㅄㄷㅏ."
  /// );
  /// ```
  fn jamos(self) -> Result<Jamos, ParseSyllableError> {
    if self.is_syllable() {
      let mut jamos = Jamos { value: Vec::new() };
      if let Ok(Some(jong)) = self.jongseong() {
        jamos.value.push(jong);
      }
      jamos.value.push(self.jungseong().unwrap());
      jamos.value.push(self.choseong().unwrap());

      Ok(jamos)
    } else {
      Err(ParseSyllableError)
    }
  }
}

fn offset(c: char) -> u32 {
  c as u32 - SYLLABLE_START
}
