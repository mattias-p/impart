use std::fmt;

use palette::Srgb;

use crate::generate::Cell;
use crate::generate::VarId;
use crate::ir::Expr;
use crate::ir::Type;

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
    type Cond = Self;
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

#[derive(Clone, Debug, PartialEq)]
pub enum Color {}
impl Type for Color {
    type Repr = Srgb<u8>;
    type Cond = Bool;
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
    type Cond = Bool;
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

impl From<Float> for AnyExpr {
    fn from(op: Float) -> Self {
        AnyExpr::Float(Expr::TypeOp(Box::new(op)))
    }
}

impl From<Bool> for AnyExpr {
    fn from(op: Bool) -> Self {
        AnyExpr::Bool(Expr::TypeOp(Box::new(op)))
    }
}
