use std::fmt;

use std::cell::RefCell;
use std::rc::Rc;

use crate::generate::Cell;
use crate::lexer::Loc;
use crate::ops::Bool;

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
