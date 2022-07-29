use std::fmt;

use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::ast;
use crate::generate::Cell;
use crate::lexer::Loc;
use crate::lexer::Op;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Variable {
    Elevation,
    Humidity,
    Temperature,
}

pub enum Source {
    Inline,
    Prelude,
    Def(usize, usize),
}

impl Source {
    pub fn error<S: AsRef<str>>(&self, message: S) -> String {
        let message = message.as_ref();
        match self {
            Source::Inline => format!("{message}"),
            Source::Prelude => format!("{message} (prelude)"),
            Source::Def(line, col) => format!("{message} (defined at {line}:{col})"),
        }
    }
}

pub enum TyKind {
    Bool,
    Float,
    Color,
}

impl fmt::Display for TyKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TyKind::Bool => write!(f, "bool"),
            TyKind::Color => write!(f, "color"),
            TyKind::Float => write!(f, "float"),
        }
    }
}

pub trait Type {
    type Repr: Clone + Copy + fmt::Debug + PartialEq;
    type Op: TypeOp<Repr = Self::Repr>;
}

pub trait TypeOp: Clone + fmt::Debug + PartialEq {
    type Repr;
    fn eval(&self, cell: Cell) -> Self::Repr;
}

#[derive(Clone, Debug, PartialEq)]
pub struct Bool;
impl Type for Bool {
    type Repr = bool;
    type Op = BoolOp;
}
#[derive(Clone, Debug, PartialEq)]
pub enum BoolOp {
    Greater {
        lhs: TyExpr<Float>,
        rhs: TyExpr<Float>,
    },
    Less {
        lhs: TyExpr<Float>,
        rhs: TyExpr<Float>,
    },
    Not {
        rhs: TyExpr<Bool>,
    },
    And {
        lhs: TyExpr<Bool>,
        rhs: TyExpr<Bool>,
    },
    Xor {
        lhs: TyExpr<Bool>,
        rhs: TyExpr<Bool>,
    },
    Or {
        lhs: TyExpr<Bool>,
        rhs: TyExpr<Bool>,
    },
}
impl TypeOp for BoolOp {
    type Repr = bool;
    fn eval(&self, cell: Cell) -> Self::Repr {
        match self {
            BoolOp::Greater { lhs, rhs } => lhs.eval(cell) > rhs.eval(cell),
            BoolOp::Less { lhs, rhs } => lhs.eval(cell) < rhs.eval(cell),
            BoolOp::Not { rhs } => !rhs.eval(cell),
            BoolOp::And { lhs, rhs } => lhs.eval(cell) && rhs.eval(cell),
            BoolOp::Xor { lhs, rhs } => lhs.eval(cell) ^ rhs.eval(cell),
            BoolOp::Or { lhs, rhs } => lhs.eval(cell) || rhs.eval(cell),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Color;
impl Type for Color {
    type Repr = Srgb<u8>;
    type Op = ColorOp;
}
#[derive(Clone, Debug, PartialEq)]
pub enum ColorOp {}
impl TypeOp for ColorOp {
    type Repr = Srgb<u8>;
    fn eval(&self, _cell: Cell) -> Self::Repr {
        unreachable!("ColorOp is a never-type");
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Float;
impl Type for Float {
    type Repr = f32;
    type Op = FloatOp;
}
#[derive(Clone, Debug, PartialEq)]
pub enum FloatOp {
    Variable(Variable),
    Neg {
        rhs: TyExpr<Float>,
    },
    Mul {
        lhs: TyExpr<Float>,
        rhs: TyExpr<Float>,
    },
    Div {
        lhs: TyExpr<Float>,
        rhs: TyExpr<Float>,
    },
    Add {
        lhs: TyExpr<Float>,
        rhs: TyExpr<Float>,
    },
    Sub {
        lhs: TyExpr<Float>,
        rhs: TyExpr<Float>,
    },
}
impl TypeOp for FloatOp {
    type Repr = f32;
    fn eval(&self, cell: Cell) -> Self::Repr {
        match self {
            FloatOp::Variable(Variable::Elevation) => cell.elevation,
            FloatOp::Variable(Variable::Humidity) => cell.humidity,
            FloatOp::Variable(Variable::Temperature) => cell.temperature,
            FloatOp::Neg { rhs } => -rhs.eval(cell),
            FloatOp::Mul { lhs, rhs } => lhs.eval(cell) * rhs.eval(cell),
            FloatOp::Div { lhs, rhs } => lhs.eval(cell) / rhs.eval(cell),
            FloatOp::Add { lhs, rhs } => lhs.eval(cell) + rhs.eval(cell),
            FloatOp::Sub { lhs, rhs } => lhs.eval(cell) - rhs.eval(cell),
        }
    }
}

#[derive(Clone, Debug)]
pub enum AnyExpr {
    Bool(TyExpr<Bool>),
    Color(TyExpr<Color>),
    Float(TyExpr<Float>),
}

impl AnyExpr {
    pub fn get_type(&self) -> TyKind {
        match self {
            AnyExpr::Bool(_) => TyKind::Bool,
            AnyExpr::Color(_) => TyKind::Color,
            AnyExpr::Float(_) => TyKind::Float,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TyExpr<T: Type> {
    Imm(T::Repr),
    IfThenElse(Box<IfThenElse<T>>),
    TypeOp(Box<T::Op>),
}

impl<T: Type> TyExpr<T> {
    pub fn eval(&self, cell: Cell) -> T::Repr {
        match self {
            TyExpr::Imm(value) => *value,
            TyExpr::IfThenElse(if_then_else) => {
                if if_then_else.cond.eval(cell) {
                    if_then_else.if_true.eval(cell)
                } else {
                    if_then_else.if_false.eval(cell)
                }
            }
            TyExpr::TypeOp(op) => op.eval(cell),
        }
    }
}

trait Parser<'a, T: Type> {
    fn typed_ast_atom(&self, value: &'a Loc<ast::Atom<'a>>) -> Result<TyExpr<T>, String>;
    fn typed_ast_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<TyExpr<T>, String>;
}

impl<'a> Parser<'a, Bool> for Compiler<'a> {
    fn typed_ast_atom(&self, value: &'a Loc<ast::Atom<'a>>) -> Result<TyExpr<Bool>, String> {
        let (def, source) = self.untyped_ast_atom(value)?;
        match def {
            AnyExpr::Bool(expr) => Ok(expr),
            AnyExpr::Float(_) => Err(source.error("expected bool got float")),
            AnyExpr::Color(_) => Err(source.error("expected bool got color")),
        }
    }

    fn typed_ast_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<TyExpr<Bool>, String> {
        let (def, source) = self.untyped_ast_expr(value)?;
        match def {
            AnyExpr::Bool(expr) => Ok(expr),
            AnyExpr::Float(_) => Err(source.error("expected bool got float")),
            AnyExpr::Color(_) => Err(source.error("expected bool got color")),
        }
    }
}

impl<'a> Parser<'a, Color> for Compiler<'a> {
    fn typed_ast_atom(&self, value: &'a Loc<ast::Atom<'a>>) -> Result<TyExpr<Color>, String> {
        let (def, source) = self.untyped_ast_atom(value)?;
        match def {
            AnyExpr::Color(expr) => Ok(expr),
            AnyExpr::Bool(_) => Err(source.error("expected color got bool")),
            AnyExpr::Float(_) => Err(source.error("expected color got float")),
        }
    }

    fn typed_ast_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<TyExpr<Color>, String> {
        let (def, source) = self.untyped_ast_expr(value)?;
        match def {
            AnyExpr::Color(expr) => Ok(expr),
            AnyExpr::Bool(_) => Err(source.error("expected color got bool")),
            AnyExpr::Float(_) => Err(source.error("expected color got float")),
        }
    }
}

impl<'a> Parser<'a, Float> for Compiler<'a> {
    fn typed_ast_atom(&self, value: &'a Loc<ast::Atom<'a>>) -> Result<TyExpr<Float>, String> {
        let (def, source) = self.untyped_ast_atom(value)?;
        match def {
            AnyExpr::Float(expr) => Ok(expr),
            AnyExpr::Bool(_) => Err(source.error("expected float got bool")),
            AnyExpr::Color(_) => Err(source.error("expected float got color")),
        }
    }

    fn typed_ast_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<TyExpr<Float>, String> {
        let (def, source) = self.untyped_ast_expr(value)?;
        match def {
            AnyExpr::Float(expr) => Ok(expr),
            AnyExpr::Bool(_) => Err(source.error("expected float got bool")),
            AnyExpr::Color(_) => Err(source.error("expected float got color")),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct IfThenElse<T: Type> {
    pub cond: TyExpr<Bool>,
    pub if_true: TyExpr<T>,
    pub if_false: TyExpr<T>,
}

#[derive(Debug)]
pub struct Compiler<'a> {
    next: Option<(&'a str, Loc<AnyExpr>, &'a Compiler<'a>)>,
}

impl<'a> Compiler<'a> {
    pub fn symbol(&self, sym: &str) -> Option<Loc<AnyExpr>> {
        match &self.next {
            Some((s, def, next)) => {
                if *s == sym {
                    Some(def.clone())
                } else {
                    next.symbol(sym)
                }
            }
            None => None,
        }
    }

    pub fn define(&self, sym: Loc<&'a str>, def: AnyExpr) -> Compiler<'_> {
        Compiler {
            next: Some((sym.inner, sym.map(|_| def), self)),
        }
    }

    pub fn untyped_ast_atom(
        &self,
        value: &Loc<ast::Atom<'a>>,
    ) -> Result<(AnyExpr, Source), String> {
        match value.inner {
            ast::Atom::True => Ok((AnyExpr::Bool(TyExpr::Imm(true)), Source::Inline)),
            ast::Atom::False => Ok((AnyExpr::Bool(TyExpr::Imm(false)), Source::Inline)),
            ast::Atom::Float(s) => {
                let decoded = s.parse::<f32>().unwrap();
                Ok((AnyExpr::Float(TyExpr::Imm(decoded)), Source::Inline))
            }
            ast::Atom::Hexcode(s) => {
                let argb = u32::from_str_radix(s, 16).unwrap();
                Ok((
                    AnyExpr::Color(TyExpr::Imm(Srgb::<u8>::from_u32::<Argb>(argb))),
                    Source::Inline,
                ))
            }
            ast::Atom::Ident(s) => match self.symbol(s) {
                Some(def) => Ok((def.inner.clone(), Source::Def(def.line, def.col))),
                None => match s {
                    "elevation" => Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Variable(
                            Variable::Elevation,
                        )))),
                        Source::Prelude,
                    )),
                    "humidity" => Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Variable(
                            Variable::Humidity,
                        )))),
                        Source::Prelude,
                    )),
                    "temperature" => Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Variable(
                            Variable::Temperature,
                        )))),
                        Source::Prelude,
                    )),
                    _ => Err(value.error(format!("use of undeclared identifier"))),
                },
            },
        }
    }

    pub fn untyped_ast_expr(&self, expr: &Loc<ast::Expr<'a>>) -> Result<(AnyExpr, Source), String> {
        match &expr.inner {
            ast::Expr::Atom(atom) => self.untyped_ast_atom(&expr.clone().map(|_| atom.clone())),
            ast::Expr::LetIn(inner) => {
                let (def, _) = self.untyped_ast_expr(&inner.definition)?;
                let def = inner.term.map(|_| def);
                self.define(inner.term, def.inner)
                    .untyped_ast_expr(&inner.expr)
            }
            ast::Expr::UnOp(inner) => match inner.op {
                Op::Not => {
                    let rhs: TyExpr<Bool> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Bool(TyExpr::TypeOp(Box::new(BoolOp::Not { rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Minus => {
                    let rhs: TyExpr<Float> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Neg { rhs }))),
                        Source::Inline,
                    ))
                }
                _ => unreachable!("no such unary operator"),
            },
            ast::Expr::BinOp(inner) => match inner.op {
                Op::Asterisk => {
                    let lhs: TyExpr<Float> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Float> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Mul { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Solidus => {
                    let lhs: TyExpr<Float> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Float> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Div { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Plus => {
                    let lhs: TyExpr<Float> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Float> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Add { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Minus => {
                    let lhs: TyExpr<Float> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Float> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Float(TyExpr::TypeOp(Box::new(FloatOp::Sub { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Less => {
                    let lhs: TyExpr<Float> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Float> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Bool(TyExpr::TypeOp(Box::new(BoolOp::Less { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Greater => {
                    let lhs: TyExpr<Float> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Float> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Bool(TyExpr::TypeOp(Box::new(BoolOp::Greater { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::And => {
                    let lhs: TyExpr<Bool> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Bool> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Bool(TyExpr::TypeOp(Box::new(BoolOp::And { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Xor => {
                    let lhs: TyExpr<Bool> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Bool> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Bool(TyExpr::TypeOp(Box::new(BoolOp::Xor { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                Op::Or => {
                    let lhs: TyExpr<Bool> = self.typed_ast_expr(&inner.lhs)?;
                    let rhs: TyExpr<Bool> = self.typed_ast_expr(&inner.rhs)?;
                    Ok((
                        AnyExpr::Bool(TyExpr::TypeOp(Box::new(BoolOp::Or { lhs, rhs }))),
                        Source::Inline,
                    ))
                }
                _ => unreachable!("no such binary operator"),
            },
            ast::Expr::IfElse(inner) => {
                let cond = self.typed_ast_expr(&inner.cond)?;
                let (if_true, _) = self.untyped_ast_expr(&inner.if_true)?;
                let (if_false, _) = self.untyped_ast_expr(&inner.if_false)?;
                match (if_true, if_false) {
                    (AnyExpr::Bool(if_true), AnyExpr::Bool(if_false)) => Ok((AnyExpr::Bool(TyExpr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false}))), Source::Inline)),
                    (AnyExpr::Color(if_true), AnyExpr::Color(if_false)) => Ok((AnyExpr::Color(TyExpr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false}))), Source::Inline)),
                    (AnyExpr::Float(if_true), AnyExpr::Float(if_false)) => Ok((AnyExpr::Float(TyExpr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false}))), Source::Inline)),
                    (if_true, if_false) => {
                        Err(format!("expression at {}:{} ({}) has a different type from expression at {}:{} ({})", inner.if_false.line, inner.if_false.col, if_false.get_type()
, inner.if_true.line, inner.if_true.col, if_true.get_type()))
                    }
                }
            }
        }
    }
}

pub fn compile<'a>(expr: &Loc<ast::Expr<'a>>) -> Result<TyExpr<Color>, String> {
    let compiler = Compiler { next: None };
    compiler.typed_ast_expr(expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lexer::Lexer;

    fn check(corpus: &[u8]) -> Result<TyExpr<Color>, String> {
        let mut lexer = Lexer::new(corpus);
        let ast = ast::parse(&mut lexer)?;
        compile(&ast)
    }

    fn color(hexcode: &str) -> Srgb<u8> {
        let hexcode = u32::from_str_radix(hexcode, 16).unwrap();
        Srgb::from_u32::<Argb>(hexcode)
    }

    #[test]
    fn hexcode() {
        assert_eq!(check(b"#fc9630"), Ok(TyExpr::Imm(color("fc9630"))));
    }
    #[test]
    fn let_in() {
        assert_eq!(
            check(b"let brown = #123456 in\nbrown"),
            Ok(TyExpr::Imm(color("123456"))),
        );
    }
    #[test]
    fn let_in_let_in() {
        assert_eq!(
            check(b"let foo = #123456 in\nlet foo = #654321 in\nfoo"),
            Ok(TyExpr::Imm(color("654321"))),
        );
    }
}
