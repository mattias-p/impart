use palette::named;
use palette::Srgb;

use crate::generate::Cell;

#[derive(Debug, PartialEq)]
pub enum Token {
    Case,
    Default,
    Variable(Variable),
    Comparator(Comparator),
    Color(Color),
    Number(f32),
    Error(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Color {
    name: String,
    color: Srgb<u8>,
}

impl Color {
    pub fn color(&self) -> Srgb<u8> {
        self.color
    }
}

impl TryFrom<&str> for Color {
    type Error = &'static str;
    fn try_from(name: &str) -> Result<Self, Self::Error> {
        match named::from_str(&name) {
            Some(color) => Ok(Color {
                name: name.to_string(),
                color,
            }),
            None => Err("unrecognized color name"),
        }
    }
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
    fn error(&self, message: &str) -> String {
        format!(
            "{} at {}:{}",
            message,
            self.line_no,
            self.pos - self.line_start + 1
        )
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq)]
        enum State {
            Start,
            Keyword(usize),
            Number(usize),
            Quote,
            EndQuote(usize),
        }

        let mut pos = self.pos;
        let mut state = State::Start;
        while let Some(ch) = self.corpus.get(pos) {
            state = match (&state, *ch) {
                (State::Start, b'\n') => {
                    self.pos += 1;
                    self.line_no += 1;
                    self.line_start = self.pos;
                    State::Start
                }
                (State::Start, b' ') => {
                    self.pos += 1;
                    State::Start
                }
                (State::Start, b'"') => State::Quote,
                (State::Start, b'0'..=b'9' | b'.') => State::Number(pos),
                (State::Start, _) => State::Keyword(pos),
                (State::Keyword(_) | State::Number(_) | State::EndQuote(_), b'\n') => {
                    break;
                }
                (State::Quote, b'\n') => {
                    return Some(Token::Error(self.error("unexpected EOL")));
                }
                (State::Keyword(_) | State::Number(_) | State::EndQuote(_), b' ') => {
                    break;
                }
                (State::Quote, b'"') => State::EndQuote(pos),
                (State::Number(_), b'0'..=b'9' | b'.') => State::Number(pos),
                (State::Number(_) | State::EndQuote(_), ch) => {
                    return Some(Token::Error(
                        self.error(&format!("unexpected character '{ch}'")),
                    ));
                }
                (State::Keyword(_), _) => State::Keyword(pos),
                (State::Quote, _) => State::Quote,
            };
            pos += 1;
        }

        let token = match state {
            State::Start => {
                return None;
            }
            State::Keyword(end) => {
                let s = &self.corpus[self.pos..=end];
                let token = match s {
                    b">" => Token::Comparator(Comparator::GreaterThan),
                    b"<" => Token::Comparator(Comparator::LessThan),
                    b"case" => Token::Case,
                    b"default" => Token::Default,
                    b"humidity" => Token::Variable(Variable::Humidity),
                    b"elevation" => Token::Variable(Variable::Elevation),
                    b"temperature" => Token::Variable(Variable::Temperature),
                    token => {
                        let message = match std::str::from_utf8(token) {
                            Ok(token) => format!("invalid keyword '{token}'"),
                            Err(_) => format!("invalid keyword '{token:?}'"),
                        };
                        return Some(Token::Error(self.error(&message)));
                    }
                };
                self.pos = end + 1;
                token
            }
            State::Number(end) => {
                let number = &self.corpus[self.pos..=end];
                match std::str::from_utf8(number).unwrap().parse::<f32>() {
                    Ok(number) => {
                        self.pos = end + 1;
                        Token::Number(number)
                    }
                    Err(err) => return Some(Token::Error(self.error(&err.to_string()))),
                }
            }
            State::EndQuote(end) => match std::str::from_utf8(&self.corpus[(self.pos + 1)..end]) {
                Ok(name) => match Color::try_from(name) {
                    Ok(color) => {
                        self.pos = end + 1;
                        Token::Color(color)
                    }
                    Err(err) => {
                        return Some(Token::Error(self.error(&format!("{} '{}'", err, name))))
                    }
                },
                Err(err) => return Some(Token::Error(self.error(&err.to_string()))),
            },
            State::Quote => unreachable!(),
        };

        Some(token)
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

#[derive(Debug, PartialEq)]
struct Cond {
    variable: Variable,
    comparator: Comparator,
    number: f32,
}

impl Cond {
    fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let variable = match lexer.next() {
            Some(Token::Variable(var)) => var,
            Some(Token::Error(error)) => Err(error)?,
            Some(token) => Err(lexer.error(&format!("expected variable got {token:?}")))?,
            None => Err(lexer.error("unexpected EOF"))?,
        };
        let comparator = match lexer.next() {
            Some(Token::Comparator(cmp)) => cmp,
            Some(Token::Error(error)) => Err(error)?,
            Some(token) => Err(lexer.error(&format!("expected comparator got {token:?}")))?,
            None => Err(lexer.error("unexpected EOF"))?,
        };
        let number = match lexer.next() {
            Some(Token::Number(number)) => number,
            Some(Token::Error(error)) => Err(error)?,
            Some(token) => Err(lexer.error(&format!("expected number got {token:?}")))?,
            None => Err(lexer.error("unexpected EOF"))?,
        };
        Ok(Cond {
            variable,
            comparator,
            number,
        })
    }

    fn eval(&self, cell: Cell) -> bool {
        let number = match self.variable {
            Variable::Elevation => cell.elevation,
            Variable::Temperature => cell.temperature,
            Variable::Humidity => cell.humidity,
        };
        match self.comparator {
            Comparator::GreaterThan => number > self.number,
            Comparator::LessThan => number < self.number,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Case {
    cond: Cond,
    yes: Box<Expr>,
    no: Box<Expr>,
}

impl Case {
    fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let cond = Cond::parse(lexer)?;
        let yes = Box::new(Expr::parse_inner(lexer)?);
        match lexer.next() {
            Some(Token::Default) => {
                let no = Box::new(Expr::parse_inner(lexer)?);
                Ok(Case { cond, yes, no })
            }
            Some(Token::Case) => {
                let no = Box::new(Expr::Case(Case::parse(lexer)?));
                Ok(Case { cond, yes, no })
            }
            Some(Token::Error(error)) => Err(error)?,
            Some(token) => Err(lexer.error(&format!("expected token 'default' got {token:?}")))?,
            None => Err(lexer.error("unexpected EOF"))?,
        }
    }

    fn eval(&self, cell: Cell) -> Color {
        if self.cond.eval(cell) {
            self.yes.eval(cell)
        } else {
            self.no.eval(cell)
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Color(Color),
    Case(Case),
}

impl Expr {
    fn parse_inner<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        match lexer.next() {
            Some(Token::Color(color)) => Ok(Expr::Color(color)),
            Some(Token::Case) => Ok(Expr::Case(Case::parse(lexer)?)),
            Some(Token::Error(error)) => Err(error)?,
            Some(token) => Err(lexer.error(&format!("unexpected token {token:?}"))),
            None => Err(lexer.error("unexpected EOF")),
        }
    }

    pub fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let expr = Self::parse_inner(lexer)?;
        match lexer.next() {
            None => {}
            Some(Token::Error(error)) => Err(error)?,
            Some(token) => {
                Err(lexer.error(&format!("expected EOF got {token:?}")))?;
            }
        }
        Ok(expr)
    }

    pub fn eval(&self, cell: Cell) -> Color {
        match self {
            Expr::Color(name) => name.clone(),
            Expr::Case(case) => case.eval(cell),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(corpus: &[u8]) -> Result<Expr, String> {
        Expr::parse(&mut Lexer::new(corpus))
    }

    #[test]
    fn parse() {
        //assert_eq!(check(br#""brown""#), Ok(Expr::Color("brown".try_into().unwrap())));
        assert_eq!(
            check(br#" "brown""#),
            Ok(Expr::Color("brown".try_into().unwrap()))
        );
        assert_eq!(
            check(br#"case elevation > 0.5 "brown" default "cyan""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::GreaterThan,
                    number: 0.5,
                },
                yes: Box::new(Expr::Color("brown".try_into().unwrap())),
                no: Box::new(Expr::Color("cyan".try_into().unwrap())),
            }))
        );
        assert_eq!(
            check(b"case xelevation"),
            Err("invalid keyword 'xelevation' at 1:6".to_string())
        );
        assert_eq!(
            check(b"case\nxelevation"),
            Err("invalid keyword 'xelevation' at 2:1".to_string())
        );
        assert_eq!(
            check(br#"case elevation > 0.5 case humidity < 0.31 "sandybrown" default "rosybrown" default "cyan""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::GreaterThan,
                    number: 0.5,
                },
                yes: Box::new(Expr::Case(Case {
                    cond: Cond {
                        variable: Variable::Humidity,
                        comparator: Comparator::LessThan,
                        number: 0.31,
                    },
                    yes: Box::new(Expr::Color("sandybrown".try_into().unwrap())),
                    no: Box::new(Expr::Color("rosybrown".try_into().unwrap())),
                })),
                no: Box::new(Expr::Color("cyan".try_into().unwrap())),
            }))
        );
        assert_eq!(
            check(br#"case elevation < 0.5 "cyan" case humidity < 0.31 "sandybrown" default "rosybrown""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::LessThan,
                    number: 0.5,
                },
                yes: Box::new(Expr::Color("cyan".try_into().unwrap())),
                no: Box::new(Expr::Case(Case {
                    cond: Cond {
                        variable: Variable::Humidity,
                        comparator: Comparator::LessThan,
                        number: 0.31,
                    },
                    yes: Box::new(Expr::Color("sandybrown".try_into().unwrap())),
                    no: Box::new(Expr::Color("rosybrown".try_into().unwrap())),
                })),
            }))
        );
    }
}
