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
            Quote(usize),
            EndQuote(usize, usize),
        }

        let mut pos = self.pos;
        let mut state = State::Start;
        let mut new_lines = 0;
        let mut line_start = self.line_start;
        let mut white_space = 0;
        while let Some(ch) = self.corpus.get(pos) {
            match (&state, *ch) {
                (State::Start, b'\n') => {
                    new_lines += 1;
                    line_start = pos;
                }
                (State::Start, b' ') => {}
                (State::Start, b'"') => {
                    state = State::Quote(pos + 1);
                }
                (State::Start, b'0'..=b'9' | b'.') => {
                    state = State::Number(pos);
                }
                (State::Start, _) => {
                    state = State::Keyword(pos);
                }
                (State::Keyword(_) | State::Number(_) | State::EndQuote(_, _), b'\n') => {
                    pos += 1;
                    white_space = 1;
                    new_lines += 1;
                    line_start = pos;
                    break;
                }
                (State::Quote(_), b'\n') => {
                    return Some(Token::Error(self.error("unexpected EOL")));
                }
                (State::Keyword(_) | State::Number(_) | State::EndQuote(_, _), b' ') => {
                    pos += 1;
                    white_space = 1;
                    break;
                }
                (State::Quote(start), b'"') => {
                    state = State::EndQuote(*start, pos);
                }
                (State::Number(_), b'0'..=b'9' | b'.') => {}
                (State::Number(_) | State::EndQuote(_, _), ch) => {
                    return Some(Token::Error(
                        self.error(&format!("unexpected character '{ch}'")),
                    ));
                }
                (State::Quote(_) | State::Keyword(_), _) => {}
            }
            pos += 1;
        }

        let token = match state {
            State::Start => {
                self.pos = pos;
                self.line_no += new_lines;
                self.line_start = line_start;
                return None;
            }
            State::Keyword(start) => {
                let s = &self.corpus[start..pos - white_space];
                match s {
                    b">" => Token::Comparator(Comparator::GreaterThan),
                    b"<" => Token::Comparator(Comparator::LessThan),
                    b"case" => Token::Case,
                    b"default" => Token::Default,
                    b"humidity" => Token::Variable(Variable::Humidity),
                    b"elevation" => Token::Variable(Variable::Elevation),
                    b"temperature" => Token::Variable(Variable::Temperature),
                    token => {
                        let message = match std::str::from_utf8(token) {
                            Ok(token) => format!("invalid token '{token}'"),
                            Err(_) => format!("invalid token '{token:?}'"),
                        };
                        return Some(Token::Error(self.error(&message)));
                    }
                }
            }
            State::Number(start) => {
                let number = &self.corpus[start..pos - white_space];
                match std::str::from_utf8(number).unwrap().parse::<f32>() {
                    Ok(number) => Token::Number(number),
                    Err(err) => return Some(Token::Error(self.error(&err.to_string()))),
                }
            }
            State::EndQuote(start, end) => {
                match std::str::from_utf8(&self.corpus[start..end]) {
                    Ok(name) => match Color::try_from(name) {
                        Ok(color) => Token::Color(color),
                        Err(err) => Token::Error(self.error(&format!("{} '{}'", err, name))),
                    }
                    Err(err) => return Some(Token::Error(self.error(&err.to_string()))),
                }
            }
            State::Quote(_) => unreachable!(),
        };

        self.pos = pos;
        self.line_no += new_lines;
        self.line_start = line_start;
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
            Variable::Humidity=> cell.humidity,
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
        assert_eq!(check(br#""brown""#), Ok(Expr::Color("brown".try_into().unwrap())));
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
            Err("invalid token 'xelevation' at 1:6".to_string())
        );
        assert_eq!(
            check(b"case\nxelevation"),
            Err("invalid token 'xelevation' at 2:1".to_string())
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
