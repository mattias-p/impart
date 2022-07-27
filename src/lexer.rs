use std::str::Utf8Error;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Loc<T> {
    pub line: usize,
    pub col: usize,
    pub inner: T,
}

impl<T> Loc<T> {
    pub fn error<E: AsRef<str>>(&self, message: E) -> String {
        format!("{} at {}:{}", message.as_ref(), self.line, self.col)
    }

    pub fn map<F, U>(self, f: F) -> Loc<U>
    where
        F: FnOnce(T) -> U,
    {
        Loc {
            line: self.line,
            col: self.col,
            inner: f(self.inner),
        }
    }

    pub fn try_map<F, U, E>(self, f: F) -> Result<Loc<U>, E>
    where
        F: FnOnce(T) -> Result<U, E>,
    {
        Ok(f(self.inner)?.loc(self.line, self.col))
    }
}

pub trait LocExt {
    fn loc(self, line: usize, col: usize) -> Loc<Self>
    where
        Self: Sized;
}

impl<T> LocExt for T {
    fn loc(self, line: usize, col: usize) -> Loc<Self>
    where
        Self: Sized,
    {
        Loc {
            line,
            col,
            inner: self,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token<'a> {
    Let,
    Case,
    Else,
    EqualSign,
    LessThan,
    GreaterThan,
    Decimal(&'a str),
    Hexcode(&'a str),
    Ident(&'a str),
    EOF,
}

pub struct Lexer<'a> {
    corpus: &'a [u8],
    pos: usize,
    line_no: usize,
    line_start: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(corpus: &'a [u8]) -> Self {
        Lexer {
            corpus,
            pos: 0,
            line_no: 1,
            line_start: 0,
        }
    }

    pub fn get_str(&self, first: usize, last: usize) -> Result<&'a str, Utf8Error> {
        std::str::from_utf8(&self.corpus[first..=last])
    }

    fn produce(&mut self, inner: Token<'a>, next_offset: usize) -> Loc<Token<'a>> {
        let token = Loc {
            line: self.line_no,
            col: self.pos - self.line_start + 1,
            inner,
        };
        self.pos = next_offset;
        token
    }

    fn error<T: AsRef<str>>(&self, message: T) -> String {
        format!(
            "{} at {}:{}",
            message.as_ref(),
            self.line_no,
            self.pos - self.line_start + 1
        )
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Loc<Token<'a>>, String>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq)]
        enum State {
            Start,
            Slash,
            Comment,
            Bareword(usize),
            Decimal0,
            Decimal1,
            Decimal(usize),
            Hexcode0(u8),
            Hexcode(usize),
        }

        let mut pos = self.pos;
        let mut state = State::Start;
        while let Some(ch) = self.corpus.get(pos) {
            state = match (&state, *ch) {
                // Start state
                (State::Start | State::Comment, b'\n') => {
                    self.pos += 1;
                    self.line_no += 1;
                    self.line_start = self.pos;
                    State::Start
                }
                (State::Start, b' ') => {
                    self.pos += 1;
                    State::Start
                }
                (State::Start, b'/') => State::Slash,
                (State::Start, b'#') => State::Hexcode0(0),
                (State::Start | State::Decimal0, b'0'..=b'9') => State::Decimal0,
                (State::Start, _) => State::Bareword(pos),

                // Comments
                (State::Slash, b'/') => {
                    self.pos += 2;
                    State::Comment
                }
                (State::Comment, _) => {
                    self.pos += 1;
                    State::Comment
                }

                // Whitespace
                (
                    State::Bareword(_) | State::Decimal(_) | State::Hexcode(_) | State::Slash,
                    b' ' | b'\n',
                ) => {
                    break;
                }

                // Barewords
                (State::Bareword(_) | State::Slash, _) => State::Bareword(pos),

                // Hexcodes
                (State::Hexcode0(count), b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F') => {
                    if *count < 5 {
                        State::Hexcode0(count + 1)
                    } else {
                        State::Hexcode(pos)
                    }
                }

                // Decimal numbers
                (State::Decimal0, b'.') => State::Decimal1,
                (State::Decimal1 | State::Decimal(_), b'0'..=b'9') => State::Decimal(pos),
                (
                    State::Decimal0
                    | State::Decimal1
                    | State::Decimal(_)
                    | State::Hexcode0(_)
                    | State::Hexcode(_),
                    ch,
                ) => return Some(Err(self.error(format!("unexpected character '{ch}'")))),
            };
            pos += 1;
        }

        let token = match state {
            State::Start | State::Comment => {
                return Some(Ok(self.produce(Token::EOF, self.pos)));
            }
            State::Bareword(end) => {
                let s = &self.corpus[self.pos..=end];
                let token = match s {
                    b">" => Token::GreaterThan,
                    b"<" => Token::LessThan,
                    b"=" => Token::EqualSign,
                    b"let" => Token::Let,
                    b"case" => Token::Case,
                    b"else" => Token::Else,
                    ident => match std::str::from_utf8(ident) {
                        Ok(ident) => Token::Ident(ident),
                        Err(err) => return Some(Err(self.error(err.to_string()))),
                    },
                };
                self.produce(token, end + 1)
            }
            State::Slash => {
                let s = &self.corpus[self.pos..=self.pos];
                let ident = std::str::from_utf8(s).unwrap();
                let token = Token::Ident(ident);
                self.produce(token, self.pos + 1)
            }
            State::Decimal(end) => {
                let s = self.get_str(self.pos, end).unwrap();
                self.produce(Token::Decimal(s), end + 1)
            }
            State::Hexcode(end) => {
                let s = self.get_str(self.pos + 1, end).unwrap();
                self.produce(Token::Hexcode(s), end + 1)
            }
            State::Decimal0 | State::Decimal1 | State::Hexcode0(_) => {
                return Some(Err(self.error("unexpected EOL")));
            }
        };

        Some(Ok(token))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn next_inner<'a>(lexer: &mut Lexer<'a>) -> Result<Token<'a>, String> {
        Ok(lexer.next().unwrap()?.inner)
    }

    #[test]
    fn lex() {
        let mut lexer = Lexer::new(
            b"
                let
                case
                else
                =
                <
                >
                3.14
                #fc9630
                foobar
            ",
        );

        assert_eq!(next_inner(&mut lexer), Ok(Token::Let));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Case));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Else));
        assert_eq!(next_inner(&mut lexer), Ok(Token::EqualSign));
        assert_eq!(next_inner(&mut lexer), Ok(Token::LessThan));
        assert_eq!(next_inner(&mut lexer), Ok(Token::GreaterThan));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Decimal("3.14")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Hexcode("fc9630")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Ident("foobar")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::EOF));
    }
}
