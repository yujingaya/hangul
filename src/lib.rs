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
/// Utilities to handle [Hangul Syllables][syllables].
///
/// This trait extends [`char`][char] with methods including:
///
/// - _Predicate_ that checks whether given [`char`][char] is a [Hangul Syllable][syllables]
/// - _Getters_ for Choseong, Jungseong, Jongseong, Jamo, and Jamos Iterator
///
/// To use these methods, import the [`HangulExt`](trait.HangulExt.html) crate:
///
/// ```
/// use hangul::HangulExt;
/// ```
///
/// Now you can use the methods:
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
  fn choseong(self) -> Result<char, ParseSyllableError>;
  fn jungseong(self) -> Result<char, ParseSyllableError>;
  fn jongseong(self) -> Result<Option<char>, ParseSyllableError>;
  fn to_jamo(self) -> Result<(char, char, Option<char>), ParseSyllableError>;
  fn jamos(self) -> Result<Jamos, ParseSyllableError>;
}

/// An error which can be returned when a given [`char`][char] is not in a [Hangul Syllables][syllables].
///
/// Unicode Hangul Syllables is a Unicode block range from `U+AC00` to `U+D7AF`. Since [`char`][char] covers much larger range,
/// there's a chance where char is not in a Hangul Syllable. In that case, [`ParseSyllableError`](struct.ParseSyllableError.html) is returned.
/// [syllables]: https://en.wikipedia.org/wiki/Hangul_Syllables
/// [char]: https://doc.rust-lang.org/std/primitive.char.html
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct ParseSyllableError;

/// An iterator over the [Jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) [`char`][char]s of a [Syllable](https://en.wikipedia.org/wiki/Hangul_Syllables).
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
  /// Tests whether the [`char`][char] is a [Hangul Syllable](https://en.wikipedia.org/wiki/Hangul_Syllables).
  ///
  /// # Example
  ///
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('냐'.is_syllable(), true);
  /// assert_eq!('猫'.is_syllable(), false);
  /// ```
  /// [char]: https://doc.rust-lang.org/std/primitive.char.html
  fn is_syllable(self) -> bool {
    let cp = self as u32; // cp stands for (Unicode) code point
    cp >= SYLLABLE_START && cp <= SYLLABLE_END
  }

  /// Returns [Compatibility Jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) Choseong of a given [`char`](https://doc.rust-lang.org/std/primitive.char.html)
  ///
  /// # Errors
  ///
  /// If it's not a Syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html).
  ///
  /// ```
  /// use hangul::{HangulExt, ParseSyllableError};
  ///
  /// assert_eq!('🥑'.choseong(), Err(ParseSyllableError));
  /// ```
  ///
  /// # Examples
  /// ```
  /// use hangul::HangulExt;
  ///
  /// assert_eq!('항'.choseong().unwrap(), 'ㅎ');
  /// ```
  ///
  /// Note that [Compatibility Jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) is different from [Jamo](https://en.wikipedia.org/wiki/Hangul_Jamo_(Unicode_block)).
  /// This crate only deals with the [Compatibility Jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo).
  /// ```
  /// use hangul::HangulExt;
  ///
  /// // Jamo
  /// let p = 'ᄑ';
  /// assert_eq!(p as u32, 0x1111);
  ///
  /// // Compatibility Jamo
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

  /// Returns [Compatibility Jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) Jungseong of a given [`char`](https://doc.rust-lang.org/std/primitive.char.html)
  fn jungseong(self) -> Result<char, ParseSyllableError> {
    if self.is_syllable() {
      let jungseong_offset = (offset(self) / JONGSEONG_COUNT % JUNGSEONG_COUNT) as u32;
      Ok(std::char::from_u32(JAMO_START + jungseong_offset + 31).unwrap())
    } else {
      Err(ParseSyllableError)
    }
  }

  /// Returns [`Option`](https://doc.rust-lang.org/stable/std/option/) of a [Compatibility Jamo](https://en.wikipedia.org/wiki/Hangul_Compatibility_Jamo) Jongseong of a given [`char`](https://doc.rust-lang.org/std/primitive.char.html)
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
  /// assert_eq!('정'.to_jamo(), Ok(('ㅈ', 'ㅓ', Some('ㅇ'))));
  /// assert_eq!('유'.to_jamo(), Ok(('ㅇ', 'ㅠ', None)));
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
  /// If given [`char`](https://doc.rust-lang.org/std/primitive.char.html) is not a Syllable, returns [`ParseSyllableError`](struct.ParseSyllableError.html)
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
  /// You can use it with [`flat_map`](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.flat_map) to decompose Hangul String
  ///
  /// ```
  /// use hangul::{HangulExt};
  ///
  /// assert_eq!(
  ///   "신경쓰지마"
  ///     .chars()
  ///     .flat_map(|c| c.jamos().unwrap())
  ///     .collect::<String>(),
  ///   "ㅅㅣㄴㄱㅕㅇㅆㅡㅈㅣㅁㅏ"
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
