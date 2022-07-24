#[derive(Debug, PartialEq)]
pub enum Token {
    Case,
    Else,
    Let,
    EqualSign,
    Variable(Variable),
    Comparator(Comparator),
    Ident(String),
    Quoted(String),
    Hexcode(u32),
    Number(f32),
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

    pub fn get_context(&mut self) -> LexerContext {
        while let Some(ch) = self.corpus.get(self.context.pos) {
            match *ch {
                b'\n' => {
                    self.context.pos += 1;
                    self.context.line_no += 1;
                    self.context.line_start = self.context.pos;
                }
                b' ' => {
                    self.context.pos += 1;
                }
                _ => break,
            };
        }
        self.context
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, String>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq)]
        enum State {
            Start,
            Bareword(usize),
            Number(usize),
            Quote,
            Hexcode(usize),
            EndQuote(usize),
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
                (State::Start, b'"') => State::Quote,
                (State::Start, b'#') => State::Hexcode(pos),
                (State::Start, b'0'..=b'9' | b'.') => State::Number(pos),
                (State::Start, _) => State::Bareword(pos),
                (
                    State::Bareword(_) | State::Number(_) | State::EndQuote(_) | State::Hexcode(_),
                    b'\n' | b' ',
                ) => {
                    break;
                }
                (State::Quote, b'"') => State::EndQuote(pos),
                (State::Quote, b'\n') => {
                    return Some(Err(self.context.error("unexpected EOL")));
                }
                (State::Hexcode(_), b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F') => State::Hexcode(pos),
                (State::Number(_), b'0'..=b'9' | b'.') => State::Number(pos),
                (State::Number(_) | State::EndQuote(_) | State::Hexcode(_), ch) => {
                    return Some(Err(self
                        .context
                        .error(format!("unexpected character '{ch}'"))))
                }
                (State::Bareword(_), _) => State::Bareword(pos),
                (State::Quote, _) => State::Quote,
            };
            pos += 1;
        }

        let token = match state {
            State::Start => {
                return None;
            }
            State::Bareword(end) => {
                let s = &self.corpus[self.context.pos..=end];
                let token = match s {
                    b">" => Token::Comparator(Comparator::GreaterThan),
                    b"<" => Token::Comparator(Comparator::LessThan),
                    b"=" => Token::EqualSign,
                    b"let" => Token::Let,
                    b"case" => Token::Case,
                    b"else" => Token::Else,
                    b"humidity" => Token::Variable(Variable::Humidity),
                    b"elevation" => Token::Variable(Variable::Elevation),
                    b"temperature" => Token::Variable(Variable::Temperature),
                    ident => match std::str::from_utf8(ident) {
                        Ok(ident) => Token::Ident(ident.to_string()),
                        Err(err) => return Some(Err(self.context.error(err.to_string()))),
                    },
                };
                self.context.pos = end + 1;
                token
            }
            State::Number(end) => {
                let number = &self.corpus[self.context.pos..=end];
                match std::str::from_utf8(number).unwrap().parse::<f32>() {
                    Ok(number) => {
                        self.context.pos = end + 1;
                        Token::Number(number)
                    }
                    Err(err) => return Some(Err(self.context.error(err.to_string()))),
                }
            }
            State::Hexcode(end) => {
                if self.context.pos + 6 != end {
                    return Some(Err(self.context.error("invalid hexcode")));
                }
                let hexcode = &self.corpus[(self.context.pos + 1)..=end];
                let hexcode = std::str::from_utf8(hexcode).unwrap();
                match u32::from_str_radix(hexcode, 16) {
                    Ok(rgb) => {
                        self.context.pos = end + 1;
                        Token::Hexcode(rgb)
                    }
                    Err(err) => return Some(Err(self.context.error(err.to_string()))),
                }
            }
            State::EndQuote(end) => {
                match std::str::from_utf8(&self.corpus[(self.context.pos + 1)..end]) {
                    Ok(name) => {
                        self.context.pos = end + 1;
                        Token::Quoted(name.to_string())
                    }
                    Err(err) => return Some(Err(self.context.error(err.to_string()))),
                }
            }
            State::Quote => unreachable!(),
        };

        Some(Ok(token))
    }
}

#[derive(Debug, PartialEq)]
pub enum Variable {
    Elevation,
    Temperature,
    Humidity,
}

#[derive(Debug, PartialEq)]
pub enum Comparator {
    LessThan,
    GreaterThan,
}
