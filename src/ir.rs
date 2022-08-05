use std::cell::RefCell;
use std::fmt;
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

pub trait UnaryOp {
    type Rhs: Type;
    type Output: Type;

    fn eval_raw(rhs: <Self::Rhs as Type>::Repr) -> <Self::Output as Type>::Repr;
    fn new(rhs: Expr<Self::Rhs>) -> Self::Output;
    fn operand(&self) -> &Expr<Self::Rhs>;
    fn into_rhs(self) -> Expr<Self::Rhs>;

    fn eval_cell(&self, cell: &Cell) -> <Self::Output as Type>::Repr {
        let rhs = self.operand();
        let rhs = rhs.eval(cell);
        Self::eval_raw(rhs)
    }

    fn eval_static(self) -> Expr<Self::Output>
    where
        Self: Sized,
    {
        let rhs = self.into_rhs().eval_static();
        if let Some(rhs) = rhs.as_imm() {
            Expr::Imm(Self::eval_raw(rhs))
        } else {
            Expr::TypeOp(Box::new(Self::new(rhs)))
        }
    }
}

pub trait BinaryOp {
    type Lhs: Type;
    type Rhs: Type;
    type Output: Type;

    fn eval_raw(
        lhs: <Self::Lhs as Type>::Repr,
        rhs: <Self::Rhs as Type>::Repr,
    ) -> <Self::Output as Type>::Repr;
    fn new(lhs: Expr<Self::Lhs>, rhs: Expr<Self::Rhs>) -> Self::Output;
    fn operands(&self) -> (&Expr<Self::Lhs>, &Expr<Self::Rhs>);
    fn into_operands(self) -> (Expr<Self::Lhs>, Expr<Self::Rhs>);

    fn eval_cell(&self, cell: &Cell) -> <Self::Output as Type>::Repr {
        let (lhs, rhs) = self.operands();
        let lhs = lhs.eval(cell);
        let rhs = rhs.eval(cell);
        Self::eval_raw(lhs, rhs)
    }

    fn eval_static(self) -> Expr<Self::Output>
    where
        Self: Sized,
    {
        let (lhs, rhs) = self.into_operands();
        let lhs = lhs.eval_static();
        let rhs = rhs.eval_static();
        if let (Some(lhs), Some(rhs)) = (lhs.as_imm(), rhs.as_imm()) {
            Expr::Imm(Self::eval_raw(lhs, rhs))
        } else {
            Expr::TypeOp(Box::new(Self::new(lhs, rhs)))
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Not {
    rhs: Expr<Bool>,
}

impl UnaryOp for Not {
    type Rhs = Bool;
    type Output = Bool;
    fn eval_raw(rhs: bool) -> bool {
        !rhs
    }
    fn new(rhs: Expr<Bool>) -> Bool {
        Bool::Not(Self { rhs })
    }
    fn operand(&self) -> &Expr<Bool> {
        &self.rhs
    }
    fn into_rhs(self) -> Expr<Bool> {
        self.rhs
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Neg {
    rhs: Expr<Float>,
}

impl UnaryOp for Neg {
    type Rhs = Float;
    type Output = Float;
    fn eval_raw(rhs: f32) -> f32 {
        -rhs
    }
    fn new(rhs: Expr<Float>) -> Float {
        Float::Neg(Self { rhs })
    }
    fn operand(&self) -> &Expr<Float> {
        &self.rhs
    }
    fn into_rhs(self) -> Expr<Float> {
        self.rhs
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct And {
    lhs: Expr<Bool>,
    rhs: Expr<Bool>,
}

impl BinaryOp for And {
    type Lhs = Bool;
    type Rhs = Bool;
    type Output = Bool;
    fn eval_raw(lhs: bool, rhs: bool) -> bool {
        lhs && rhs
    }
    fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::And(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Bool>, &Expr<Bool>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Bool>, Expr<Bool>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Xor {
    lhs: Expr<Bool>,
    rhs: Expr<Bool>,
}

impl BinaryOp for Xor {
    type Lhs = Bool;
    type Rhs = Bool;
    type Output = Bool;
    fn eval_raw(lhs: bool, rhs: bool) -> bool {
        lhs ^ rhs
    }
    fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::Xor(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Bool>, &Expr<Bool>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Bool>, Expr<Bool>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Or {
    lhs: Expr<Bool>,
    rhs: Expr<Bool>,
}

impl BinaryOp for Or {
    type Lhs = Bool;
    type Rhs = Bool;
    type Output = Bool;
    fn eval_raw(lhs: bool, rhs: bool) -> bool {
        lhs || rhs
    }
    fn new(lhs: Expr<Bool>, rhs: Expr<Bool>) -> Bool {
        Bool::Or(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Bool>, &Expr<Bool>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Bool>, Expr<Bool>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Greater {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl BinaryOp for Greater {
    type Lhs = Float;
    type Rhs = Float;
    type Output = Bool;
    fn eval_raw(lhs: f32, rhs: f32) -> bool {
        lhs > rhs
    }
    fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Bool {
        Bool::Greater(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Float>, &Expr<Float>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Float>, Expr<Float>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Less {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl BinaryOp for Less {
    type Lhs = Float;
    type Rhs = Float;
    type Output = Bool;
    fn eval_raw(lhs: f32, rhs: f32) -> bool {
        lhs < rhs
    }
    fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Bool {
        Bool::Less(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Float>, &Expr<Float>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Float>, Expr<Float>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Mul {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl BinaryOp for Mul {
    type Lhs = Float;
    type Rhs = Float;
    type Output = Float;
    fn eval_raw(lhs: f32, rhs: f32) -> f32 {
        lhs * rhs
    }
    fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Mul(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Float>, &Expr<Float>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Float>, Expr<Float>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Div {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl BinaryOp for Div {
    type Lhs = Float;
    type Rhs = Float;
    type Output = Float;
    fn eval_raw(lhs: f32, rhs: f32) -> f32 {
        lhs / rhs
    }
    fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Div(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Float>, &Expr<Float>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Float>, Expr<Float>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Add {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl BinaryOp for Add {
    type Lhs = Float;
    type Rhs = Float;
    type Output = Float;
    fn eval_raw(lhs: f32, rhs: f32) -> f32 {
        lhs + rhs
    }
    fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Add(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Float>, &Expr<Float>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Float>, Expr<Float>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Sub {
    lhs: Expr<Float>,
    rhs: Expr<Float>,
}

impl BinaryOp for Sub {
    type Lhs = Float;
    type Rhs = Float;
    type Output = Float;
    fn eval_raw(lhs: f32, rhs: f32) -> f32 {
        lhs - rhs
    }
    fn new(lhs: Expr<Float>, rhs: Expr<Float>) -> Float {
        Float::Sub(Self { lhs, rhs })
    }
    fn operands(&self) -> (&Expr<Float>, &Expr<Float>) {
        (&self.lhs, &self.rhs)
    }
    fn into_operands(self) -> (Expr<Float>, Expr<Float>) {
        (self.lhs, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Bool {
    Not(Not),
    And(And),
    Xor(Xor),
    Or(Or),
    Greater(Greater),
    Less(Less),
}
impl Type for Bool {
    type Repr = bool;
    fn eval(&self, cell: &Cell) -> Self::Repr {
        match self {
            Bool::Not(op) => op.eval_cell(cell),
            Bool::And(op) => op.eval_cell(cell),
            Bool::Xor(op) => op.eval_cell(cell),
            Bool::Or(op) => op.eval_cell(cell),
            Bool::Greater(op) => op.eval_cell(cell),
            Bool::Less(op) => op.eval_cell(cell),
        }
    }
    fn eval_static(self) -> Expr<Self> {
        match self {
            Bool::Not(op) => op.eval_static(),
            Bool::And(op) => op.eval_static(),
            Bool::Xor(op) => op.eval_static(),
            Bool::Or(op) => op.eval_static(),
            Bool::Greater(op) => op.eval_static(),
            Bool::Less(op) => op.eval_static(),
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
    Neg(Neg),
    Mul(Mul),
    Div(Div),
    Add(Add),
    Sub(Sub),
}
impl Type for Float {
    type Repr = f32;
    fn eval(&self, cell: &Cell) -> Self::Repr {
        match self {
            Float::Variable(var) => cell.get(*var),
            Float::Neg(op) => op.eval_cell(cell),
            Float::Mul(op) => op.eval_cell(cell),
            Float::Div(op) => op.eval_cell(cell),
            Float::Add(op) => op.eval_cell(cell),
            Float::Sub(op) => op.eval_cell(cell),
        }
    }
    fn eval_static(self) -> Expr<Self> {
        match self {
            Float::Variable(_) => Expr::TypeOp(Box::new(self.clone())),
            Float::Neg(op) => op.eval_static(),
            Float::Mul(op) => op.eval_static(),
            Float::Div(op) => op.eval_static(),
            Float::Add(op) => op.eval_static(),
            Float::Sub(op) => op.eval_static(),
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
