use std::cell::RefCell;
use std::fmt;

use palette::rgb::channels::Argb;
use palette::Srgb;

use crate::ast;
use crate::generate::Cell;
use crate::generate::VarSpec;
use crate::lexer;
use crate::lexer::Loc;
use crate::lexer::Op;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct VarId {
    index: usize,
}

pub enum Source {
    Inline,
    Def(usize, usize),
}

impl Source {
    pub fn error<S: AsRef<str>>(&self, message: S) -> String {
        let message = message.as_ref();
        match self {
            Source::Inline => format!("{message}"),
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
    fn eval(&self, cell: &Cell) -> Self::Repr;
}

#[derive(Clone, Debug, PartialEq)]
pub struct Bool;
impl Type for Bool {
    type Repr = bool;
    type Op = BoolOp;
}
#[derive(Clone, Debug, PartialEq)]
pub enum BoolOp {
    Greater { lhs: Expr<Float>, rhs: Expr<Float> },
    Less { lhs: Expr<Float>, rhs: Expr<Float> },
    Not { rhs: Expr<Bool> },
    And { lhs: Expr<Bool>, rhs: Expr<Bool> },
    Xor { lhs: Expr<Bool>, rhs: Expr<Bool> },
    Or { lhs: Expr<Bool>, rhs: Expr<Bool> },
}
impl TypeOp for BoolOp {
    type Repr = bool;
    fn eval(&self, cell: &Cell) -> Self::Repr {
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
impl BoolOp {
    fn into_anyexpr(self) -> AnyExpr {
        AnyExpr::Bool(Expr::TypeOp(Box::new(self)))
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
    fn eval(&self, _cell: &Cell) -> Self::Repr {
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
    Variable(VarId),
    Neg { rhs: Expr<Float> },
    Mul { lhs: Expr<Float>, rhs: Expr<Float> },
    Div { lhs: Expr<Float>, rhs: Expr<Float> },
    Add { lhs: Expr<Float>, rhs: Expr<Float> },
    Sub { lhs: Expr<Float>, rhs: Expr<Float> },
}
impl TypeOp for FloatOp {
    type Repr = f32;
    fn eval(&self, cell: &Cell) -> Self::Repr {
        match self {
            FloatOp::Variable(var) => cell.vars[var.index],
            FloatOp::Neg { rhs } => -rhs.eval(cell),
            FloatOp::Mul { lhs, rhs } => lhs.eval(cell) * rhs.eval(cell),
            FloatOp::Div { lhs, rhs } => lhs.eval(cell) / rhs.eval(cell),
            FloatOp::Add { lhs, rhs } => lhs.eval(cell) + rhs.eval(cell),
            FloatOp::Sub { lhs, rhs } => lhs.eval(cell) - rhs.eval(cell),
        }
    }
}
impl FloatOp {
    fn into_anyexpr(self) -> AnyExpr {
        AnyExpr::Float(Expr::TypeOp(Box::new(self)))
    }
}

#[derive(Clone, Debug)]
pub enum AnyExpr {
    Bool(Expr<Bool>),
    Color(Expr<Color>),
    Float(Expr<Float>),
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
pub enum Expr<T: Type> {
    Imm(T::Repr),
    IfThenElse(Box<IfThenElse<T>>),
    TypeOp(Box<T::Op>),
}

impl<T: Type> Expr<T> {
    pub fn eval(&self, cell: &Cell) -> T::Repr {
        match self {
            Expr::Imm(value) => *value,
            Expr::IfThenElse(if_then_else) => {
                if if_then_else.cond.eval(cell) {
                    if_then_else.if_true.eval(cell)
                } else {
                    if_then_else.if_false.eval(cell)
                }
            }
            Expr::TypeOp(op) => op.eval(cell),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct IfThenElse<T: Type> {
    pub cond: Expr<Bool>,
    pub if_true: Expr<T>,
    pub if_false: Expr<T>,
}

pub fn float_literal(literal: &Loc<ast::Literal>) -> Result<f32, String> {
    match literal.inner {
        ast::Literal::Decimal(s) => Ok(s.parse::<f32>().unwrap()),
        ast::Literal::True => Err(literal.error("expected number got bool")),
        ast::Literal::False => Err(literal.error("expected number got bool")),
        ast::Literal::Hexcode(_) => Err(literal.error("expected number got color")),
    }
}

const ELEVATION: VarId = VarId { index: 0 };
const HUMIDITY: VarId = VarId { index: 1 };
const TEMPERATURE: VarId = VarId { index: 2 };

#[derive(Debug)]
pub enum SymTable<'a> {
    Vars {
        vars: RefCell<Vec<VarSpec>>,
    },
    Sym {
        sym: &'a str,
        value: Loc<AnyExpr>,
        next: &'a SymTable<'a>,
    },
}

impl<'a> SymTable<'a> {
    pub fn new() -> Self {
        SymTable::Vars {
            vars: RefCell::new(vec![
                VarSpec::Elevation,
                VarSpec::Humidity,
                VarSpec::Temperature,
            ]),
        }
    }

    pub fn get_vars(&self) -> Vec<VarSpec> {
        match self {
            SymTable::Sym { next, .. } => next.get_vars(),
            SymTable::Vars { vars } => vars.borrow().clone(),
        }
    }

    pub fn symbol(&self, name: &str) -> Option<Loc<AnyExpr>> {
        match &*self {
            SymTable::Sym { sym, value, next } => {
                if *sym == name {
                    Some(value.clone())
                } else {
                    next.symbol(name)
                }
            }
            SymTable::Vars { .. } => None,
        }
    }

    pub fn with_def(&'a self, sym: Loc<&'a str>, value: AnyExpr) -> SymTable<'a> {
        SymTable::Sym {
            sym: sym.inner,
            value: sym.map(|_| value),
            next: self,
        }
    }

    pub fn new_variable(&self, spec: VarSpec) -> VarId {
        match self {
            SymTable::Sym { next, .. } => next.new_variable(spec),
            SymTable::Vars { vars } => {
                let mut vars = vars.borrow_mut();
                let index = vars.len();
                vars.push(spec);
                VarId { index }
            }
        }
    }

    pub fn any_expr(&self, expr: &'a Loc<ast::Expr<'a>>) -> Result<(AnyExpr, Source), String> {
        match &expr.inner {
            ast::Expr::Elevation => {
                Ok((FloatOp::Variable(ELEVATION).into_anyexpr(), Source::Inline))
            }
            ast::Expr::Humidity => Ok((FloatOp::Variable(HUMIDITY).into_anyexpr(), Source::Inline)),
            ast::Expr::Temperature => Ok((
                FloatOp::Variable(TEMPERATURE).into_anyexpr(),
                Source::Inline,
            )),
            ast::Expr::True => Ok((AnyExpr::Bool(Expr::Imm(true)), Source::Inline)),
            ast::Expr::False => Ok((AnyExpr::Bool(Expr::Imm(false)), Source::Inline)),
            ast::Expr::Float(s) => {
                let decoded = s.parse::<f32>().unwrap();
                Ok((AnyExpr::Float(Expr::Imm(decoded)), Source::Inline))
            }
            ast::Expr::Hexcode(s) => {
                let argb = u32::from_str_radix(s, 16).unwrap();
                Ok((
                    AnyExpr::Color(Expr::Imm(Srgb::<u8>::from_u32::<Argb>(argb))),
                    Source::Inline,
                ))
            }
            ast::Expr::Ident(s) => match self.symbol(s) {
                Some(def) => Ok((def.inner.clone(), Source::Def(def.line, def.col))),
                None => Err(expr.error(format!("use of undeclared identifier"))),
            },
            ast::Expr::Constructor(inner) => match inner.kind {
                lexer::Var::Perlin => {
                    let mut octaves = None;
                    let mut frequency = None;
                    let mut persistence = None;
                    for attr in &inner.attrs {
                        match attr.name.inner {
                            "octaves" => {
                                if octaves.is_some() {
                                    Err(attr.name.error("octaves already specified"))?;
                                }
                                let value = float_literal(&attr.value)?;
                                if value.fract().abs() > f32::EPSILON {
                                    Err(attr.value.error("octaves must be an integer"))?;
                                }
                                if value.fract() < 1.0 {
                                    Err(attr.value.error("there must be at least one octave"))?;
                                }
                                octaves = Some(value.round());
                            }
                            "frequency" => {
                                if frequency.is_some() {
                                    Err(attr.name.error("frequency already specified"))?;
                                }
                                frequency = Some(float_literal(&attr.value)?);
                            }
                            "persistence" => {
                                if persistence.is_some() {
                                    Err(attr.name.error("persistence already specified"))?;
                                }
                                persistence = Some(float_literal(&attr.value)?);
                            }
                            _ => Err(attr.name.error(format!(
                                "expected 'octaves', 'frequency' or 'persistence' got '{}'",
                                attr.name.inner
                            )))?,
                        }
                    }
                    let octaves =
                        octaves.ok_or_else(|| expr.error("must specify 'octaves'"))? as usize;
                    let frequency =
                        frequency.ok_or_else(|| expr.error("must specify 'frequency'"))?;
                    let persistence =
                        persistence.ok_or_else(|| expr.error("must specify 'persistence'"))?;

                    let variable = self.new_variable(VarSpec::Perlin {
                        octaves,
                        frequency,
                        persistence,
                    });

                    Ok((FloatOp::Variable(variable).into_anyexpr(), Source::Inline))
                }
                lexer::Var::X => {
                    if let Some(attr) = inner.attrs.first() {
                        Err(attr
                            .name
                            .error(format!("expected no attributes got {:?}", attr.name.inner)))?;
                    }
                    let variable = self.new_variable(VarSpec::X);
                    Ok((FloatOp::Variable(variable).into_anyexpr(), Source::Inline))
                }
                lexer::Var::Y => {
                    if let Some(attr) = inner.attrs.first() {
                        Err(attr
                            .name
                            .error(format!("expected no attributes got {:?}", attr.name.inner)))?;
                    }
                    let variable = self.new_variable(VarSpec::Y);
                    Ok((FloatOp::Variable(variable).into_anyexpr(), Source::Inline))
                }
            },
            ast::Expr::LetIn(inner) => {
                let (def, _) = self.any_expr(&inner.definition)?;
                let def = inner.term.map(|_| def);
                self.with_def(inner.term, def.inner).any_expr(&inner.expr)
            }
            ast::Expr::UnOp(inner) => match inner.op {
                Op::Not => {
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok((BoolOp::Not { rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Minus => {
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok((FloatOp::Neg { rhs }.into_anyexpr(), Source::Inline))
                }
                _ => unreachable!("no such unary operator"),
            },
            ast::Expr::BinOp(inner) => match inner.op {
                Op::Asterisk => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok((FloatOp::Mul { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Solidus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok((FloatOp::Div { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Plus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok((FloatOp::Add { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Minus => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok((FloatOp::Sub { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Less => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok((BoolOp::Less { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Greater => {
                    let lhs = self.float_expr(&inner.lhs)?;
                    let rhs = self.float_expr(&inner.rhs)?;
                    Ok((BoolOp::Greater { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::And => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok((BoolOp::And { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Xor => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok((BoolOp::Xor { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                Op::Or => {
                    let lhs = self.bool_expr(&inner.lhs)?;
                    let rhs = self.bool_expr(&inner.rhs)?;
                    Ok((BoolOp::Or { lhs, rhs }.into_anyexpr(), Source::Inline))
                }
                _ => unreachable!("no such binary operator"),
            },
            ast::Expr::IfElse(inner) => {
                let cond = self.bool_expr(&inner.cond)?;
                let (if_true, _) = self.any_expr(&inner.if_true)?;
                let (if_false, _) = self.any_expr(&inner.if_false)?;
                match (if_true, if_false) {
                    (AnyExpr::Bool(if_true), AnyExpr::Bool(if_false)) => Ok((AnyExpr::Bool(Expr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false}))), Source::Inline)),
                    (AnyExpr::Color(if_true), AnyExpr::Color(if_false)) => Ok((AnyExpr::Color(Expr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false}))), Source::Inline)),
                    (AnyExpr::Float(if_true), AnyExpr::Float(if_false)) => Ok((AnyExpr::Float(Expr::IfThenElse(Box::new(IfThenElse{cond, if_true, if_false}))), Source::Inline)),
                    (if_true, if_false) => {
                        Err(format!("expression at {}:{} ({}) has a different type from expression at {}:{} ({})", inner.if_false.line, inner.if_false.col, if_false.get_type()
, inner.if_true.line, inner.if_true.col, if_true.get_type()))
                    }
                }
            }
        }
    }

    fn bool_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<Expr<Bool>, String> {
        let (def, source) = self.any_expr(value)?;
        match def {
            AnyExpr::Bool(expr) => Ok(expr),
            AnyExpr::Float(_) => Err(source.error("expected bool got float")),
            AnyExpr::Color(_) => Err(source.error("expected bool got color")),
        }
    }

    fn color_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<Expr<Color>, String> {
        let (def, source) = self.any_expr(value)?;
        match def {
            AnyExpr::Color(expr) => Ok(expr),
            AnyExpr::Bool(_) => Err(source.error("expected color got bool")),
            AnyExpr::Float(_) => Err(source.error("expected color got float")),
        }
    }

    fn float_expr(&self, value: &'a Loc<ast::Expr<'a>>) -> Result<Expr<Float>, String> {
        let (def, source) = self.any_expr(value)?;
        match def {
            AnyExpr::Float(expr) => Ok(expr),
            AnyExpr::Bool(_) => Err(source.error("expected float got bool")),
            AnyExpr::Color(_) => Err(source.error("expected float got color")),
        }
    }
}

pub fn compile<'a>(expr: &Loc<ast::Expr<'a>>) -> Result<(Expr<Color>, Vec<VarSpec>), String> {
    let symtable = SymTable::new();
    Ok((symtable.color_expr(expr)?, symtable.get_vars()))
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lexer::Lexer;

    fn check(corpus: &[u8]) -> Result<Expr<Color>, String> {
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
        assert_eq!(check(b"#fc9630"), Ok(Expr::Imm(color("fc9630"))));
    }
    #[test]
    fn let_in() {
        assert_eq!(
            check(b"let brown = #123456 in\nbrown"),
            Ok(Expr::Imm(color("123456"))),
        );
    }
    #[test]
    fn let_in_let_in() {
        assert_eq!(
            check(b"let foo = #123456 in\nlet foo = #654321 in\nfoo"),
            Ok(Expr::Imm(color("654321"))),
        );
    }
}
