use palette::Pixel;

use crate::generate::Cell;
use crate::ir::Color;
use crate::ir::TyExpr;

pub struct Renderer {
    expr: TyExpr<Color>,
}

impl Renderer {
    pub fn new(expr: TyExpr<Color>) -> Self {
        Renderer { expr }
    }

    pub fn render(&self, cells: &[Cell]) -> Vec<u8> {
        let mut image: Vec<u8> = Vec::with_capacity(cells.len() * 3);

        for cell in cells {
            let color = self.expr.eval(*cell);
            image.extend(color.into_raw::<[u8; 3]>().into_iter());
        }

        image
    }
}
