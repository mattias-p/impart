use std::str::Utf8Error;

#[derive(Debug, PartialEq)]
pub struct AugToken<'a> {
    pub line: usize,
    pub col: usize,
    pub inner: Token<'a>,
}

impl<'a> AugToken<'a> {
    pub fn error<T: AsRef<str>>(&self, message: T) -> String {
        format!("{} at {}:{}", message.as_ref(), self.line, self.col,)
    }
}

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
    Let,
    Case,
    Else,
    Elevation,
    Temperature,
    Humidity,
    EqualSign,
    LessThan,
    GreaterThan,
    Float(&'a str),
    Hexcode(&'a str),
    Quoted(&'a str),
    Ident(&'a str),
    EOF,
}

#[derive(Clone, Copy)]
pub struct LexerContext {
    pos: usize,
    line_no: usize,
    line_start: usize,
}

impl LexerContext {
    pub fn error<T: AsRef<str>>(&self, message: T) -> String {
        format!(
            "{} at {}:{}",
            message.as_ref(),
            self.line_no,
            self.pos - self.line_start + 1
        )
    }
}

pub struct Lexer<'a> {
    corpus: &'a [u8],
    context: LexerContext,
}

impl<'a> Lexer<'a> {
    pub fn new(corpus: &'a [u8]) -> Self {
        Lexer {
            corpus,
            context: LexerContext {
                pos: 0,
                line_no: 1,
                line_start: 0,
            },
        }
    }

    pub fn get_str(&self, first: usize, last: usize) -> Result<&'a str, Utf8Error> {
        std::str::from_utf8(&self.corpus[first..=last])
    }

    fn produce(&mut self, inner: Token<'a>, next_offset: usize) -> AugToken<'a> {
        let token = AugToken {
            line: self.context.line_no,
            col: self.context.pos - self.context.line_start + 1,
            inner,
        };
        self.context.pos = next_offset;
        token
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<AugToken<'a>, String>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq)]
        enum State {
            Start,
            Bareword(usize),
            Float0,
            Float1,
            Float(usize),
            Hexcode0(u8),
            Hexcode(usize),
            Quote0,
            Quote(usize),
        }

        let mut pos = self.context.pos;
        let mut state = State::Start;
        while let Some(ch) = self.corpus.get(pos) {
            state = match (&state, *ch) {
                (State::Start, b'\n') => {
                    self.context.pos += 1;
                    self.context.line_no += 1;
                    self.context.line_start = self.context.pos;
                    State::Start
                }
                (State::Start, b' ') => {
                    self.context.pos += 1;
                    State::Start
                }
                (State::Start, b'"') => State::Quote0,
                (State::Start, b'#') => State::Hexcode0(0),
                (State::Start | State::Float0, b'0'..=b'9') => State::Float0,
                (State::Start, _) => State::Bareword(pos),
                (
                    State::Bareword(_) | State::Float(_) | State::Quote(_) | State::Hexcode(_),
                    b'\n' | b' ',
                ) => {
                    break;
                }
                (State::Quote0, b'"') => State::Quote(pos),
                (State::Quote0, b'\n') => {
                    return Some(Err(self.context.error("unexpected EOL")));
                }
                (State::Hexcode0(count), b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F') => {
                    if *count < 5 {
                        State::Hexcode0(count + 1)
                    } else {
                        State::Hexcode(pos)
                    }
                }
                (State::Float0, b'.') => State::Float1,
                (State::Float1 | State::Float(_), b'0'..=b'9') => State::Float(pos),
                (
                    State::Float0
                    | State::Float1
                    | State::Float(_)
                    | State::Quote(_)
                    | State::Hexcode0(_)
                    | State::Hexcode(_),
                    ch,
                ) => {
                    return Some(Err(self
                        .context
                        .error(format!("unexpected character '{ch}'"))))
                }
                (State::Bareword(_), _) => State::Bareword(pos),
                (State::Quote0, _) => State::Quote0,
            };
            pos += 1;
        }

        let token = match state {
            State::Start => {
                return Some(Ok(self.produce(Token::EOF, self.context.pos)));
            }
            State::Bareword(end) => {
                let s = &self.corpus[self.context.pos..=end];
                let token = match s {
                    b">" => Token::GreaterThan,
                    b"<" => Token::LessThan,
                    b"=" => Token::EqualSign,
                    b"let" => Token::Let,
                    b"case" => Token::Case,
                    b"else" => Token::Else,
                    b"humidity" => Token::Humidity,
                    b"elevation" => Token::Elevation,
                    b"temperature" => Token::Temperature,
                    ident => match std::str::from_utf8(ident) {
                        Ok(ident) => Token::Ident(ident),
                        Err(err) => return Some(Err(self.context.error(err.to_string()))),
                    },
                };
                self.produce(token, end + 1)
            }
            State::Float(end) => {
                let s = self.get_str(self.context.pos, end).unwrap();
                self.produce(Token::Float(s), end + 1)
            }
            State::Hexcode(end) => {
                let s = self.get_str(self.context.pos + 1, end).unwrap();
                self.produce(Token::Hexcode(s), end + 1)
            }
            State::Quote(end) => {
                let s = self.get_str(self.context.pos + 1, end - 1).unwrap();
                self.produce(Token::Quoted(s), end + 1)
            }
            State::Float0 | State::Float1 | State::Hexcode0(_) | State::Quote0 => {
                return Some(Err(self.context.error("unexpected EOL")));
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
            br###"
            let
            case
            else
            elevation
            temperature
            humidity
            =
            <
            >
            3.14
            #fc9630
            "foobar"
            foobar
        "###,
        );

        assert_eq!(next_inner(&mut lexer), Ok(Token::Let));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Case));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Else));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Elevation));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Temperature));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Humidity));
        assert_eq!(next_inner(&mut lexer), Ok(Token::EqualSign));
        assert_eq!(next_inner(&mut lexer), Ok(Token::LessThan));
        assert_eq!(next_inner(&mut lexer), Ok(Token::GreaterThan));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Float("3.14")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Hexcode("fc9630")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Quoted("foobar")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::Ident("foobar")));
        assert_eq!(next_inner(&mut lexer), Ok(Token::EOF));
    }
}
