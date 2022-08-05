use std::fmt;

use std::cell::RefCell;
use std::rc::Rc;

use crate::generate::Cell;
use crate::lexer::Loc;

pub trait Type
where
    Self: Clone + fmt::Debug + PartialEq,
{
    type Repr: Clone + Copy + fmt::Debug + Default + PartialEq;
    type Cond: Type<Repr = bool, Cond = Self::Cond>;
    fn eval_cell(&self, cell: &Cell) -> Self::Repr;
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
pub struct Def<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub inner: Loc<RefCell<Expr<Output>>>,
}

impl<Output> Def<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub fn eval_cell(&self, cell: &Cell) -> Output::Repr {
        self.inner.inner.borrow().eval_cell(cell)
    }
    pub fn eval_static(&self) {
        let tmp = RefCell::new(Expr::Imm(Default::default()));
        self.inner.inner.swap(&tmp);
        let expr = tmp.into_inner().eval_static();
        self.inner.inner.replace(expr);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    Imm(Output::Repr),
    TypeOp(Box<Output>),
    IfThenElse(Box<IfThenElse<Output>>),
    Ref(Rc<Def<Output>>),
}

impl<Output> Expr<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub fn as_imm(&self) -> Option<Output::Repr> {
        if let Expr::Imm(value) = self {
            Some(*value)
        } else {
            None
        }
    }

    pub fn eval_cell(&self, cell: &Cell) -> Output::Repr {
        match self {
            Expr::Imm(value) => *value,
            Expr::IfThenElse(if_then_else) => if_then_else.eval_cell(cell),
            Expr::TypeOp(op) => op.eval_cell(cell),
            Expr::Ref(def) => def.eval_cell(cell),
        }
    }

    pub fn eval_static(self) -> Self {
        match self {
            Expr::Imm(_) => self,
            Expr::TypeOp(op) => op.eval_static(),
            Expr::IfThenElse(if_then_else) => if_then_else.eval_static(),
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
pub struct IfThenElse<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub cond: Expr<<Output as Type>::Cond>,
    pub if_true: Expr<Output>,
    pub if_false: Expr<Output>,
}

impl<Output> IfThenElse<Output>
where
    Output: Type + Clone,
    <Output as Type>::Cond: Type<Repr = bool, Cond = <Output as Type>::Cond>,
{
    pub fn eval_cell(&self, cell: &Cell) -> <Output as Type>::Repr {
        if self.cond.eval_cell(cell) {
            self.if_true.eval_cell(cell)
        } else {
            self.if_false.eval_cell(cell)
        }
    }
    pub fn eval_static(self) -> Expr<Output> {
        let cond = self.cond.eval_static();
        let if_true = self.if_true.eval_static();
        let if_false = self.if_false.eval_static();
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
}
