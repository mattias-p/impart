use std::cell::RefCell;
use std::fmt;
use std::ops;
use std::rc::Rc;

use palette::Srgb;

use crate::generate::Cell;
use crate::generate::VarId;
use crate::lexer::Loc;

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

pub trait Type
where
    Self: Clone,
{
    type Repr: Clone + Copy + fmt::Debug + Default + PartialEq;
    fn eval(&self, cell: &Cell) -> Self::Repr;
    fn eval_static(self) -> Expr<Self>
    where
        Self: Sized + Clone;

    fn reduce_unary<R, F, G>(rhs: Expr<R>, op_immediate: F, op_deferred: G) -> Expr<Self>
    where
        R: Type,
        F: Fn(R::Repr) -> Self::Repr,
        G: Fn(Expr<R>) -> Self,
    {
        let rhs = rhs.eval_static();
        if let Some(rhs) = rhs.as_imm() {
            Expr::Imm(op_immediate(rhs))
        } else {
            Expr::TypeOp(Box::new(op_deferred(rhs)))
        }
    }

    fn reduce_binary<L, R, F, G>(
        lhs: Expr<L>,
        rhs: Expr<R>,
        op_immediate: F,
        op_deferred: G,
    ) -> Expr<Self>
    where
        L: Type,
        R: Type,
        F: Fn(L::Repr, R::Repr) -> Self::Repr,
        G: Fn(Expr<L>, Expr<R>) -> Self,
    {
        let lhs = lhs.eval_static();
        let rhs = rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(op_immediate(lhs, rhs))
        } else {
            Expr::TypeOp(Box::new(op_deferred(lhs, rhs)))
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Bool {
    Not(Expr<Bool>),
    And(Expr<Bool>, Expr<Bool>),
    Xor(Expr<Bool>, Expr<Bool>),
    Or(Expr<Bool>, Expr<Bool>),
    Greater(Expr<Float>, Expr<Float>),
    Less(Expr<Float>, Expr<Float>),
}
impl Type for Bool {
    type Repr = bool;
    fn eval(&self, cell: &Cell) -> Self::Repr {
        match self {
            Bool::Not(rhs) => !rhs.eval(cell),
            Bool::And(lhs, rhs) => lhs.eval(cell) && rhs.eval(cell),
            Bool::Xor(lhs, rhs) => lhs.eval(cell) ^ rhs.eval(cell),
            Bool::Or(lhs, rhs) => lhs.eval(cell) || rhs.eval(cell),
            Bool::Greater(lhs, rhs) => lhs.eval(cell) > rhs.eval(cell),
            Bool::Less(lhs, rhs) => lhs.eval(cell) < rhs.eval(cell),
        }
    }
    fn eval_static(self) -> Expr<Self> {
        match self {
            Bool::Not(rhs) => Self::reduce_unary(rhs, ops::Not::not, Bool::Not),
            Bool::And(lhs, rhs) => Self::reduce_binary(lhs, rhs, ops::BitAnd::bitand, Bool::And),
            Bool::Xor(lhs, rhs) => Self::reduce_binary(lhs, rhs, ops::BitXor::bitxor, Bool::Xor),
            Bool::Or(lhs, rhs) => Self::reduce_binary(lhs, rhs, ops::BitOr::bitor, Bool::Or),
            Bool::Greater(lhs, rhs) => {
                Self::reduce_binary(lhs, rhs, |lhs, rhs| lhs > rhs, Bool::Greater)
            }
            Bool::Less(lhs, rhs) => Self::reduce_binary(lhs, rhs, |lhs, rhs| lhs < rhs, Bool::Less),
        }
    }
}
impl Bool {
    pub fn into_anyexpr(self) -> AnyExpr {
        AnyExpr::Bool(Expr::TypeOp(Box::new(self)))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Color {}
impl Type for Color {
    type Repr = Srgb<u8>;
    fn eval(&self, _cell: &Cell) -> Self::Repr {
        unreachable!("Color does not have any operators");
    }
    fn eval_static(self) -> Expr<Self> {
        unreachable!("Color does not have any operators");
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Float {
    Variable(VarId),
    Neg(Expr<Float>),
    Mul(Expr<Float>, Expr<Float>),
    Div(Expr<Float>, Expr<Float>),
    Add(Expr<Float>, Expr<Float>),
    Sub(Expr<Float>, Expr<Float>),
}
impl Type for Float {
    type Repr = f32;
    fn eval(&self, cell: &Cell) -> Self::Repr {
        match self {
            Float::Variable(var) => cell.get(*var),
            Float::Neg(rhs) => -rhs.eval(cell),
            Float::Mul(lhs, rhs) => lhs.eval(cell) * rhs.eval(cell),
            Float::Div(lhs, rhs) => lhs.eval(cell) / rhs.eval(cell),
            Float::Add(lhs, rhs) => lhs.eval(cell) + rhs.eval(cell),
            Float::Sub(lhs, rhs) => lhs.eval(cell) - rhs.eval(cell),
        }
    }
    fn eval_static(self) -> Expr<Self> {
        match self {
            Float::Variable(_) => Expr::TypeOp(Box::new(self.clone())),
            Float::Neg(rhs) => Self::reduce_unary(rhs, ops::Neg::neg, Float::Neg),
            Float::Mul(lhs, rhs) => Self::reduce_binary(lhs, rhs, ops::Mul::mul, Float::Mul),
            Float::Div(lhs, rhs) => Self::reduce_binary(lhs, rhs, ops::Div::div, Float::Div),
            Float::Add(lhs, rhs) => Self::reduce_binary(lhs, rhs, ops::Add::add, Float::Add),
            Float::Sub(lhs, rhs) => Self::reduce_binary(lhs, rhs, ops::Sub::sub, Float::Sub),
        }
    }
}
impl Float {
    pub fn into_anyexpr(self) -> AnyExpr {
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
pub struct Def<T: Type + Clone> {
    pub inner: Loc<RefCell<Expr<T>>>,
}
impl<T: Type + Clone> Def<T> {
    pub fn eval(&self, cell: &Cell) -> T::Repr {
        self.inner.inner.borrow().eval(cell)
    }
    pub fn eval_static(&self) {
        let tmp = RefCell::new(Expr::Imm(Default::default()));
        self.inner.inner.swap(&tmp);
        let expr = tmp.into_inner().eval_static();
        self.inner.inner.replace(expr);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<T: Type + Clone> {
    Imm(T::Repr),
    TypeOp(Box<T>),
    IfThenElse(Box<IfThenElse<T>>),
    Ref(Rc<Def<T>>),
}

impl<T: Type + Clone> Expr<T> {
    pub fn as_imm(&self) -> Option<T::Repr> {
        if let Expr::Imm(value) = self {
            Some(*value)
        } else {
            None
        }
    }

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
            Expr::Ref(def) => def.eval(cell),
        }
    }

    pub fn eval_static(self) -> Self {
        match self {
            Expr::Imm(_) => self,
            Expr::TypeOp(op) => op.eval_static(),
            Expr::IfThenElse(if_then_else) => {
                let cond = if_then_else.cond.eval_static();
                let if_true = if_then_else.if_true.eval_static();
                let if_false = if_then_else.if_false.eval_static();
                if let Some(cond) = cond.as_imm() {
                    if cond {
                        if_true
                    } else {
                        if_false
                    }
                } else {
                    Expr::IfThenElse(Box::new(IfThenElse {
                        cond,
                        if_true,
                        if_false,
                    }))
                }
            }
            Expr::Ref(ref def) => {
                def.eval_static();
                if (*def.inner.inner.borrow()).as_imm().is_some() {
                    def.inner.inner.borrow().clone()
                } else {
                    self
                }
            }
        }
    }

    pub fn error<S: AsRef<str>>(&self, message: S) -> String {
        let message = message.as_ref();
        match self {
            Expr::Ref(def) => format!(
                "{message} (defined at {}:{})",
                def.inner.line, def.inner.col
            ),
            _ => message.to_string(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct IfThenElse<T: Type + Clone> {
    pub cond: Expr<Bool>,
    pub if_true: Expr<T>,
    pub if_false: Expr<T>,
}

#[cfg(test)]
mod tests {
    use super::*;

    use palette::rgb::channels::Argb;

    fn check(corpus: &[u8]) -> Result<Expr<Color>, String> {
        Ok(parse_source(corpus)?.0)
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
            Ok(Expr::Ref(Rc::new(Def {
                inner: Loc {
                    line: 1,
                    col: 5,
                    inner: RefCell::new(Expr::Imm(color("123456")))
                }
            }))),
        );
    }
    #[test]
    fn let_in_let_in() {
        assert_eq!(
            check(b"let foo = #123456 in\nlet foo = #654321 in\nfoo"),
            Ok(Expr::Ref(Rc::new(Def {
                inner: Loc {
                    line: 2,
                    col: 5,
                    inner: RefCell::new(Expr::Imm(color("654321")))
                }
            }))),
        );
    }
}
