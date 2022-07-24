use palette::named;

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
pub struct Color(String);

impl TryFrom<&str> for Color {
    type Error = &'static str;
    fn try_from(name: &str) -> Result<Self, Self::Error> {
        match named::from_str(&name) {
            Some(_) => Ok(Color(name.to_string())),
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
        enum State {
            Start,
            Number,
            Quote,
            EndQuote,
        }

        let mut pos = self.pos;
        let mut state = State::Start;
        let mut new_line = false;
        let mut white_space = 0;
        while let Some(ch) = self.corpus.get(pos) {
            pos += 1;
            match (&state, *ch) {
                (State::Start | State::Number | State::EndQuote, b'\n') => {
                    white_space = 1;
                    new_line = true;
                    break;
                }
                (State::Start | State::Number | State::EndQuote, b' ') => {
                    white_space = 1;
                    break;
                }
                (State::Quote, b'\n') => {
                    return Some(Token::Error(self.error("unexpected EOL")));
                }
                (State::Start, b'"') => {
                    state = State::Quote;
                }
                (State::Quote, b'"') => {
                    state = State::EndQuote;
                }
                (State::Start | State::Number, digit) if (b'0'..=b'9').contains(&digit) => {
                    state = State::Number;
                }
                (State::Number, b'.') => {}
                (State::Start | State::Quote, _) => {}
                (State::Number | State::EndQuote, ch) => {
                    return Some(Token::Error(
                        self.error(&format!("unexpected character '{ch}'")),
                    ));
                }
            }
        }
        if pos == self.pos {
            return None;
        }
        let s = &self.corpus[self.pos..pos - white_space];

        let token = match (state, s) {
            (State::EndQuote, quoted) => {
                match std::str::from_utf8(&quoted[1..(pos - self.pos - white_space - 1)]) {
                    Ok(name) => match Color::try_from(name) {
                        Ok(color) => Token::Color(color),
                        Err(err) => Token::Error(self.error(err)),
                    }
                    Err(err) => return Some(Token::Error(self.error(&err.to_string()))),
                }
            }
            (State::Number, number) => match std::str::from_utf8(number).unwrap().parse::<f32>() {
                Ok(number) => Token::Number(number),
                Err(err) => return Some(Token::Error(self.error(&err.to_string()))),
            },
            (State::Start, b">") => Token::Comparator(Comparator::GreaterThan),
            (State::Start, b"<") => Token::Comparator(Comparator::LessThan),
            (State::Start, b"case") => Token::Case,
            (State::Start, b"default") => Token::Default,
            (State::Start, b"humidity") => Token::Variable(Variable::Humidity),
            (State::Start, b"elevation") => Token::Variable(Variable::Elevation),
            (State::Start, b"temperature") => Token::Variable(Variable::Temperature),
            (State::Start, token) => {
                let message = match std::str::from_utf8(token) {
                    Ok(token) => format!("invalid token '{token}'"),
                    Err(_) => format!("invalid token '{token:?}'"),
                };
                return Some(Token::Error(self.error(&message)));
            }
            (State::Quote, _) => unreachable!(),
        };
        self.pos = pos;
        if new_line {
            self.line_no += 1;
            self.line_start = pos;
        }
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
            Some(Token::Default) => {}
            Some(Token::Error(error)) => Err(error)?,
            Some(token) => Err(lexer.error(&format!("expected token 'default' got {token:?}")))?,
            None => Err(lexer.error("unexpected EOF"))?,
        };
        let no = Box::new(Expr::parse_inner(lexer)?);
        Ok(Case { cond, yes, no })
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
    }
}
