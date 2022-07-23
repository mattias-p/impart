use noise::Fbm;
use noise::NoiseFn;
use noise::Seedable;

/// A Cell describes geographic location
pub struct Cell {
    /// Elevation in the range 0.0 - 1.0 inclusive
    pub elevation: f32,

    /// Humidity in the range 0.0 - 1.0 inclusive
    pub humidity: f32,

    /// Temperature in the range 0.0 - 1.0 inclusive
    pub temperature: f32,
}

pub struct Generator {
    slope: f64,
}

impl Generator {
    pub fn new() -> Self {
        Generator { slope: 0.5 }
    }

    pub fn slope(mut self, value: f64) -> Self {
        self.slope = value;
        self
    }

    pub fn generate(&self, width: u16, height: u16, seed: u32) -> Vec<Cell> {
        let elevation_noise = Fbm::new().set_seed(seed + 0);
        let humidity_noise = Fbm::new().set_seed(seed + 1);
        let temperature_noise = Fbm::new().set_seed(seed + 2);

        let mut cells = Vec::with_capacity(width as usize * height as usize);

        let step_x = 1.0 / (width - 1) as f64;
        let step_y = 1.0 / (height - 1) as f64;
        let mut y = 0.0;
        for _ in 0..height {
            let mut x = 0.0;
            for _ in 0..width {
                let elevation = ((0.5 + self.slope / 2.0)
                    + (0.5 - self.slope / 2.0) * elevation_noise.get([x, y])
                    - self.slope * y) as f32;
                let humidity = (0.5 + 0.5 * humidity_noise.get([x, y])) as f32;
                let temperature = (0.5 + 0.5 * temperature_noise.get([x, y])) as f32;

                cells.push(Cell {
                    elevation,
                    humidity,
                    temperature,
                });

                x += step_x;
            }
            y += step_y;
        }
        cells
    }
}
