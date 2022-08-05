use palette::Pixel;

use crate::expr::Expr;
use crate::generate::Field;
use crate::ops::Color;

pub struct Renderer {
    expr: Expr<Color>,
}

impl Renderer {
    pub fn new(expr: Expr<Color>) -> Self {
        Renderer { expr }
    }

    pub fn render(&self, field: &Field) -> Vec<u8> {
        let mut image: Vec<u8> = Vec::with_capacity(field.size() * 3);

        for cell in field.cells() {
            let color = self.expr.eval_cell(&cell);
            image.extend(color.into_raw::<[u8; 3]>().into_iter());
        }

        image
    }
}
