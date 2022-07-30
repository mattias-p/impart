use std::str::Utf8Error;

#[derive(Clone, Debug, PartialEq)]
pub struct Loc<T> {
    pub line: usize,
    pub col: usize,
    pub inner: T,
}

impl<T> Copy for Loc<T> where T: Copy {}

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
pub enum Op {
    Less,
    Greater,
    Minus,
    Plus,
    Asterisk,
    Solidus,
    Or,
    Xor,
    And,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Var {
    Perlin,
    X,
    Y,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token<'a> {
    Let,
    In,
    If,
    Then,
    Else,
    True,
    False,
    Equal,
    ParenLeft,
    ParenRight,
    Var(Var),
    BraceLeft,
    Colon,
    Semicolon,
    BraceRight,
    Op(Op),
    Decimal(&'a str),
    Hexcode(&'a str),
    Ident(&'a str),
    Eof,
}

pub struct Lexer<'a> {
    lookahead: Option<Result<Loc<Token<'a>>, String>>,
    corpus: &'a [u8],
    pos: usize,
    line_no: usize,
    line_start: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(corpus: &'a [u8]) -> Self {
        Lexer {
            lookahead: None,
            corpus,
            pos: 0,
            line_no: 1,
            line_start: 0,
        }
    }

    pub fn peek(&mut self) -> Option<Result<Loc<Token<'a>>, String>> {
        if self.lookahead.is_none() {
            self.lookahead = self.next();
        }
        self.lookahead.clone()
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
        if let Some(lookahead) = self.lookahead.take() {
            return Some(lookahead);
        }

        #[derive(PartialEq)]
        enum State {
            Start,
            StartCR,
            Solidus,
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
                (State::Start | State::StartCR | State::Comment, b'\r') => {
                    self.pos += 1;
                    self.line_no += 1;
                    self.line_start = self.pos;
                    State::StartCR
                }
                (State::StartCR, b'\n') => {
                    self.pos += 1;
                    self.line_start = self.pos;
                    State::Start
                }
                (State::Start | State::Comment, b'\n') => {
                    self.pos += 1;
                    self.line_no += 1;
                    self.line_start = self.pos;
                    State::Start
                }
                (State::Start | State::StartCR, b' ') => {
                    self.pos += 1;
                    State::Start
                }
                (State::Start | State::StartCR, b'/') => State::Solidus,
                (State::Start | State::StartCR, b'#') => State::Hexcode0(0),
                (State::Start | State::StartCR | State::Decimal0, b'0'..=b'9') => State::Decimal0,
                (State::Start | State::StartCR, _) => State::Bareword(pos),

                // Comments
                (State::Solidus, b'/') => {
                    self.pos += 2;
                    State::Comment
                }
                (State::Comment, _) => {
                    self.pos += 1;
                    State::Comment
                }

                // Whitespace
                (
                    State::Bareword(_) | State::Decimal(_) | State::Hexcode(_) | State::Solidus,
                    b' ' | b'\n' | b'\r',
                ) => {
                    break;
                }

                // Barewords
                (State::Bareword(_) | State::Solidus, _) => State::Bareword(pos),

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
            State::Start | State::StartCR | State::Comment => {
                return Some(Ok(self.produce(Token::Eof, self.pos)));
            }
            State::Bareword(end) => {
                let s = &self.corpus[self.pos..=end];
                let token = match s {
                    b"(" => Token::ParenLeft,
                    b")" => Token::ParenRight,
                    b"-" => Token::Op(Op::Minus),
                    b"+" => Token::Op(Op::Plus),
                    b"*" => Token::Op(Op::Asterisk),
                    b">" => Token::Op(Op::Greater),
                    b"<" => Token::Op(Op::Less),
                    b"not" => Token::Op(Op::Not),
                    b"and" => Token::Op(Op::And),
                    b"xor" => Token::Op(Op::Xor),
                    b"or" => Token::Op(Op::Or),
                    b"=" => Token::Equal,
                    b"let" => Token::Let,
                    b"in" => Token::In,
                    b"if" => Token::If,
                    b"then" => Token::Then,
                    b"else" => Token::Else,
                    b"true" => Token::True,
                    b"false" => Token::False,
                    b"Perlin" => Token::Var(Var::Perlin),
                    b"X" => Token::Var(Var::X),
                    b"Y" => Token::Var(Var::Y),
                    b"{" => Token::BraceLeft,
                    b"}" => Token::BraceRight,
                    b":" => Token::Colon,
                    b";" => Token::Semicolon,
                    ident => match std::str::from_utf8(ident) {
                        Ok(ident) => Token::Ident(ident),
                        Err(err) => return Some(Err(self.error(err.to_string()))),
                    },
                };
                self.produce(token, end + 1)
            }
            State::Solidus => self.produce(Token::Op(Op::Solidus), self.pos + 1),
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
    fn tokens() {
        let mut lexer = Lexer::new(
            b"
                true
                false
                3.14
                #fc9630
                let
                foobar
                =
                in
                if
                then
                else
                Perlin
                X
                Y
                {
                :
                ;
                }
                (
                )
                *
                /
                +
                -
                <
                >
                not
                and
                xor
                or
            ",
        );

        assert_eq!(next_inner(&mut lexer), Ok(Token::True));
        assert_eq!(next_inner(&mut lexer), Ok(Token::False));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Decimal("3.14")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Hexcode("fc9630")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Let));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Ident("foobar")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Equal));
        assert_eq!(next_inner(&mut lexer), Ok(Token::In));
        assert_eq!(next_inner(&mut lexer), Ok(Token::If));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Then));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Else));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Var(Var::Perlin)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Var(Var::X)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Var(Var::Y)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::BraceLeft));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Colon));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Semicolon));
        assert_eq!(next_inner(&mut lexer), Ok(Token::BraceRight));
        assert_eq!(next_inner(&mut lexer), Ok(Token::ParenLeft));
        assert_eq!(next_inner(&mut lexer), Ok(Token::ParenRight));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Asterisk)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Solidus)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Plus)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Minus)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Less)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Greater)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Not)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::And)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Xor)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Op(Op::Or)));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Eof));
    }

    #[test]
    fn positions() {
        let mut lexer = Lexer::new(b"A B C\nD\n  E\n\nF\r\nG\r\n\r\nH\r \nI");

        assert_eq!(lexer.next(), Some(Ok(Token::Ident("A").loc(1, 1))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("B").loc(1, 3))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("C").loc(1, 5))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("D").loc(2, 1))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("E").loc(3, 3))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("F").loc(5, 1))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("G").loc(6, 1))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("H").loc(8, 1))));
        assert_eq!(lexer.next(), Some(Ok(Token::Ident("I").loc(10, 1))));
    }
}
