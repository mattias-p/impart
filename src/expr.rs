use palette::named;
use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::generate::Cell;

#[derive(Debug, PartialEq)]
pub enum Token {
    Case,
    Else,
    Variable(Variable),
    Comparator(Comparator),
    Quoted(String),
    Hexcode(u32),
    Number(f32),
}

pub type Color = Srgb<u8>;

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
    type Item = Result<Token, String>;
    fn next(&mut self) -> Option<Self::Item> {
        #[derive(PartialEq)]
        enum State {
            Start,
            Keyword(usize),
            Number(usize),
            Quote,
            Hexcode(usize),
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
                (State::Start, b'#') => State::Hexcode(pos),
                (State::Start, b'0'..=b'9' | b'.') => State::Number(pos),
                (State::Start, _) => State::Keyword(pos),
                (
                    State::Keyword(_) | State::Number(_) | State::EndQuote(_) | State::Hexcode(_),
                    b'\n' | b' ',
                ) => {
                    break;
                }
                (State::Quote, b'"') => State::EndQuote(pos),
                (State::Quote, b'\n') => {
                    return Some(Err(self.error("unexpected EOL")));
                }
                (State::Hexcode(_), b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F') => State::Hexcode(pos),
                (State::Number(_), b'0'..=b'9' | b'.') => State::Number(pos),
                (State::Number(_) | State::EndQuote(_) | State::Hexcode(_), ch) => {
                    return Some(Err(self.error(format!("unexpected character '{ch}'"))))
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
                    b"else" => Token::Else,
                    b"humidity" => Token::Variable(Variable::Humidity),
                    b"elevation" => Token::Variable(Variable::Elevation),
                    b"temperature" => Token::Variable(Variable::Temperature),
                    token => match std::str::from_utf8(token) {
                        Ok(token) => {
                            return Some(Err(self.error(format!("invalid keyword '{token}'"))))
                        }
                        Err(_) => {
                            return Some(Err(self.error(format!("invalid keyword '{token:?}'"))))
                        }
                    },
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
                    Err(err) => return Some(Err(self.error(err.to_string()))),
                }
            }
            State::Hexcode(end) => {
                if self.pos + 6 != end {
                    return Some(Err(self.error("invalid hexcode")));
                }
                let hexcode = &self.corpus[(self.pos + 1)..=end];
                let hexcode = std::str::from_utf8(hexcode).unwrap();
                match u32::from_str_radix(hexcode, 16) {
                    Ok(rgb) => {
                        self.pos = end + 1;
                        Token::Hexcode(rgb)
                    }
                    Err(err) => return Some(Err(self.error(err.to_string()))),
                }
            }
            State::EndQuote(end) => match std::str::from_utf8(&self.corpus[(self.pos + 1)..end]) {
                Ok(name) => {
                    self.pos = end + 1;
                    Token::Quoted(name.to_string())
                }
                Err(err) => return Some(Err(self.error(err.to_string()))),
            },
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

#[derive(Debug, PartialEq)]
struct Cond {
    variable: Variable,
    comparator: Comparator,
    number: f32,
}

impl Cond {
    fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let variable = match lexer
            .next()
            .unwrap_or_else(|| Err(lexer.error("unexpected EOF")))?
        {
            Token::Variable(var) => var,
            token => Err(lexer.error(&format!("expected variable got {token:?}")))?,
        };

        let comparator = match lexer
            .next()
            .unwrap_or_else(|| Err(lexer.error("unexpected EOF")))?
        {
            Token::Comparator(cmp) => cmp,
            token => Err(lexer.error(&format!("expected comparator got {token:?}")))?,
        };
        let number = match lexer
            .next()
            .unwrap_or_else(|| Err(lexer.error("unexpected EOF")))?
        {
            Token::Number(number) => number,
            token => Err(lexer.error(&format!("expected number got {token:?}")))?,
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
        match lexer
            .next()
            .unwrap_or_else(|| Err(lexer.error("unexpected EOF")))?
        {
            Token::Else => {
                let no = Box::new(Expr::parse_inner(lexer)?);
                Ok(Case { cond, yes, no })
            }
            Token::Case => {
                let no = Box::new(Expr::Case(Case::parse(lexer)?));
                Ok(Case { cond, yes, no })
            }
            token => Err(lexer.error(&format!("expected 'else' got {token:?}")))?,
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
        match lexer
            .next()
            .unwrap_or_else(|| Err(lexer.error("unexpected EOF")))?
        {
            Token::Quoted(name) => match named::from_str(&name) {
                Some(color) => Ok(Expr::Color(color)),
                None => Err(lexer.error("unrecognized color name")),
            },
            Token::Hexcode(rgb) => Ok(Expr::Color(Color::from_u32::<Argb>(rgb))),
            Token::Case => Ok(Expr::Case(Case::parse(lexer)?)),
            token => Err(lexer.error(&format!("unexpected token {token:?}"))),
        }
    }

    pub fn parse<'a>(lexer: &mut Lexer<'a>) -> Result<Self, String> {
        let expr = Self::parse_inner(lexer)?;
        if let Some(token) = lexer.next() {
            let token = token?;
            Err(lexer.error(&format!("expected EOF got {token:?}")))?;
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
    fn named_color(name: &str) -> Expr {
        Expr::Color(named::from_str(name).unwrap())
    }

    #[test]
    fn parse() {
        assert_eq!(check(br#""brown""#), Ok(named_color("brown")));
        assert_eq!(check(br#" "brown""#), Ok(named_color("brown")));
        assert_eq!(
            check(b"#fc9630"),
            Ok(Expr::Color(Srgb::from_u32::<Argb>(0xfc9630)))
        );
        assert_eq!(
            check(br#"case elevation > 0.5 "brown" else "cyan""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::GreaterThan,
                    number: 0.5,
                },
                yes: Box::new(named_color("brown")),
                no: Box::new(named_color("cyan")),
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
            check(br#"case elevation > 0.5 case humidity < 0.31 "sandybrown" else "rosybrown" else "cyan""#),
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
                    yes: Box::new(named_color("sandybrown")),
                    no: Box::new(named_color("rosybrown")),
                })),
                no: Box::new(named_color("cyan")),
            }))
        );
        assert_eq!(
            check(br#"case elevation < 0.5 "cyan" case humidity < 0.31 "sandybrown" else "rosybrown""#),
            Ok(Expr::Case(Case {
                cond: Cond {
                    variable: Variable::Elevation,
                    comparator: Comparator::LessThan,
                    number: 0.5,
                },
                yes: Box::new(named_color("cyan")),
                no: Box::new(Expr::Case(Case {
                    cond: Cond {
                        variable: Variable::Humidity,
                        comparator: Comparator::LessThan,
                        number: 0.31,
                    },
                    yes: Box::new(named_color("sandybrown")),
                    no: Box::new(named_color("rosybrown")),
                })),
            }))
        );
    }
}
