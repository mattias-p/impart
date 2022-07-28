use std::collections::hash_map::Entry;
use std::collections::HashMap;

use palette::named;
use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::ast;
use crate::generate::Cell;
use crate::lexer::Loc;

pub type Color = Srgb<u8>;

#[derive(Debug)]
pub enum Never {}

pub struct Compiler<'a> {
    defs: HashMap<&'a str, Loc<Immediate<Variable>>>,
}

impl<'a> Compiler<'a> {
    pub fn compile_value(&self, value: &'a ast::Value<'a>) -> Result<Immediate<Variable>, String> {
        match value {
            ast::Value::Hexcode(s) => {
                let argb = u32::from_str_radix(s, 16).unwrap();
                let color = Color::from_u32::<Argb>(argb);
                Ok(Immediate::Color(color))
            }
            ast::Value::Float(s) => {
                let x = s.parse::<f32>().unwrap();
                Ok(Immediate::Float(Float::Const(x)))
            }
            ast::Value::Ident(s) => match *s {
                "elevation" => Ok(Immediate::Float(Float::Variable(Variable::Elevation))),
                "humidity" => Ok(Immediate::Float(Float::Variable(Variable::Humidity))),
                "temperature" => Ok(Immediate::Float(Float::Variable(Variable::Temperature))),
                _ => match self.defs.get(s) {
                    Some(value) => Ok(value.inner),
                    None => match named::from_str(s) {
                        Some(color) => Ok(Immediate::Color(color)),
                        None => Err(format!("use of undeclared identifier")),
                    },
                },
            },
        }
    }

    pub fn compile_expr(&mut self, expr: &Loc<ast::Expr<'a>>) -> Result<Expr<Variable>, String> {
        match expr.inner.clone() {
            ast::Expr::Value(value) => match self.compile_value(&value) {
                Ok(Immediate::Color(color)) => Ok(Expr::Immediate(Immediate::Color(color))),
                Ok(Immediate::Float(_)) => Err(expr.error("expected color got float")),
                Err(e) => Err(expr.error(e.to_string()))?,
            },
            ast::Expr::Let(inner) => {
                let definition = self.compile_value(&inner.definition.inner)?;
                let definition = inner.term.map(|_| definition);
                match self.defs.entry(inner.term.inner) {
                    Entry::Vacant(vacant) => {
                        if named::from_str(inner.term.inner).is_some() {
                            Err(format!(
                                "cannot redefine '{}' at {}:{} (predefined)",
                                inner.term.inner, inner.term.line, inner.term.col
                            ))?;
                        } else {
                            vacant.insert(definition);
                        }
                    }
                    Entry::Occupied(occupied) => {
                        let old_def = occupied.get();
                        Err(format!(
                            "cannot redefine '{}' at {}:{} (first defined at {}:{})",
                            inner.term.inner,
                            inner.term.line,
                            inner.term.col,
                            old_def.line,
                            old_def.col
                        ))?;
                    }
                };
                self.compile_expr(&inner.expr)
            }
            ast::Expr::If(inner) => {
                let left = match self.compile_value(&inner.left.inner) {
                    Ok(Immediate::Float(x)) => x,
                    Ok(Immediate::Color(_)) => Err(inner.left.error("expected float got color"))?,
                    Err(e) => Err(expr.error(e.to_string()))?,
                };

                let right = match self.compile_value(&inner.right.inner) {
                    Ok(Immediate::Float(x)) => x,
                    Ok(Immediate::Color(_)) => Err(inner.right.error("expected float got color"))?,
                    Err(e) => Err(expr.error(e.to_string()))?,
                };

                let branch_true = self.compile_expr(&inner.branch_true)?;
                let branch_false = self.compile_expr(&inner.branch_false)?;

                Ok(Expr::If(Box::new(If {
                    left,
                    comparator: inner.comparator.inner,
                    right,
                    branch_true,
                    branch_false,
                })))
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Variable {
    Elevation,
    Temperature,
    Humidity,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Float<V> {
    Const(f32),
    Variable(V),
}

impl Float<Variable> {
    pub fn eval(&self, cell: Cell) -> Float<Never> {
        match self {
            Float::Const(value) => Float::Const(*value),
            Float::Variable(Variable::Elevation) => Float::Const(cell.elevation),
            Float::Variable(Variable::Temperature) => Float::Const(cell.temperature),
            Float::Variable(Variable::Humidity) => Float::Const(cell.humidity),
        }
    }
}

impl<V> Float<V> {
    pub fn as_const(&self) -> Option<f32> {
        match self {
            Float::Const(value) => Some(*value),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Immediate<V> {
    Float(Float<V>),
    Color(Color),
}

impl Immediate<Variable> {
    pub fn eval(&self, cell: Cell) -> Immediate<Never> {
        match self {
            Immediate::Float(value) => Immediate::Float(value.eval(cell)),
            Immediate::Color(value) => Immediate::Color(*value),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct If<V> {
    left: Float<V>,
    comparator: ast::Comparator,
    right: Float<V>,
    branch_true: Expr<V>,
    branch_false: Expr<V>,
}

impl If<Variable> {
    fn eval(&self, cell: Cell) -> Immediate<Never> {
        let left = self.left.eval(cell).as_const().unwrap();
        let right = self.right.eval(cell).as_const().unwrap();
        let cond = match self.comparator {
            ast::Comparator::GreaterThan => left > right,
            ast::Comparator::LessThan => left < right,
        };

        if cond {
            self.branch_true.eval(cell)
        } else {
            self.branch_false.eval(cell)
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expr<V> {
    Immediate(Immediate<V>),
    If(Box<If<V>>),
}

impl Expr<Variable> {
    pub fn eval(&self, cell: Cell) -> Immediate<Never> {
        match self {
            Expr::Immediate(imm) => imm.eval(cell),
            Expr::If(expr) => expr.eval(cell),
        }
    }
}

pub fn compile<'a>(expr: &Loc<ast::Expr<'a>>) -> Result<Expr<Variable>, String> {
    let mut compiler = Compiler {
        defs: HashMap::new(),
    };
    compiler.compile_expr(expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lexer::Lexer;

    fn check(corpus: &[u8]) -> Result<Expr<Variable>, String> {
        let mut lexer = Lexer::new(corpus);
        let ast = ast::parse(&mut lexer)?;
        compile(&ast)
    }

    fn named_color(name: &str) -> Expr<Variable> {
        Expr::Immediate(Immediate::Color(named::from_str(name).unwrap()))
    }

    #[test]
    fn parse() {
        assert_eq!(check(b"brown"), Ok(named_color("brown")));
        assert_eq!(
            check(b"#fc9630"),
            Ok(Expr::Immediate(Immediate::Color(Srgb::from_u32::<Argb>(
                0xfc9630
            ))))
        );
        assert_eq!(
            check(b"let brown = #123456 in\nbrown"),
            Err("cannot redefine 'brown' at 1:5 (predefined)".to_string())
        );
        assert_eq!(
            check(b"let foo = #123456 in\nlet foo = #654321 in\nfoo"),
            Err("cannot redefine 'foo' at 2:5 (first defined at 1:5)".to_string())
        );
    }
}
