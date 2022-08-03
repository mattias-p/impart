use noise::Fbm;
use noise::MultiFractal;
use noise::NoiseFn;
use noise::Seedable;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct VarId {
    index: usize,
}
impl VarId {
    pub fn new(index: usize) -> Self {
        VarId { index }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VarSpec {
    X,
    Y,
    Perlin {
        octaves: usize,
        frequency: f32,
        persistence: f32,
    },
}

pub enum Variable {
    Perlin(Fbm),
    X,
    Y,
}

impl Variable {
    fn eval(&self, x: f64, y: f64) -> f32 {
        match self {
            Variable::Perlin(fbm) => fbm.get([x, y]) as f32,
            Variable::X => x as f32,
            Variable::Y => y as f32,
        }
    }
}

/// A Cell describes geographic location
pub struct Cell {
    /// Variables in the range 0.0 - 1.0 inclusive
    pub values: Vec<f32>,
}

impl Cell {
    pub fn get(&self, id: VarId) -> f32 {
        self.values[id.index]
    }
    pub fn as_slice(&self) -> &[f32] {
        &self.values
    }
}

pub struct Field {
    len: usize,
    axes: Vec<Vec<f32>>,
}

impl Field {
    pub fn cells(&self) -> Cells {
        Cells {
            len: self.len,
            index: 0,
            axes: &self.axes,
        }
    }
    pub fn size(&self) -> usize {
        self.len
    }
}

pub struct Cells<'a> {
    len: usize,
    index: usize,
    axes: &'a [Vec<f32>],
}

impl<'a> Iterator for Cells<'a> {
    type Item = Cell;
    fn next(&mut self) -> Option<Cell> {
        if self.index < self.len {
            let values = self.axes.iter().map(|axis| axis[self.index]).collect();
            let cell = Cell { values };
            self.index += 1;
            Some(cell)
        } else {
            None
        }
    }
}

pub struct Generator {
    var_specs: Vec<VarSpec>,
}

impl Generator {
    pub fn new(var_specs: Vec<VarSpec>) -> Self {
        Generator { var_specs }
    }

    pub fn generate(&self, width: u16, height: u16, seed: u32) -> Field {
        let vars: Vec<_> = self
            .var_specs
            .iter()
            .enumerate()
            .map(|(i, spec)| match spec {
                VarSpec::X => Variable::X,
                VarSpec::Y => Variable::Y,
                VarSpec::Perlin {
                    octaves,
                    frequency,
                    persistence,
                } => Variable::Perlin(
                    Fbm::new()
                        .set_seed(seed + i as u32)
                        .set_octaves(*octaves)
                        .set_frequency(*frequency as f64)
                        .set_persistence(*persistence as f64),
                ),
            })
            .collect();

        let len = width as usize * height as usize;
        let mut axes = Vec::with_capacity(self.var_specs.len());

        let step_x = 2.0 / (width - 1) as f64;
        let step_y = 2.0 / (height - 1) as f64;
        for var in &vars {
            let mut axis = Vec::with_capacity(len);
            let mut y = 1.0;
            let mut min = 1.0f32;
            let mut max = -1.0f32;
            for _ in 0..height {
                let mut x = -1.0;
                for _ in 0..width {
                    let value = var.eval(x, y);
                    axis.push(value);
                    min = min.min(value);
                    max = max.max(value);
                    x += step_x;
                }
                y -= step_y;
            }

            let scale = 2.0 / (max - min);
            for v in &mut axis {
                let mut value = *v;
                value = scale * (value - min) - 1.0;
                //value = value.abs().sqrt().copysign(value);
                *v = value;
            }

            axes.push(axis);
        }

        Field { len, axes }
    }
}
