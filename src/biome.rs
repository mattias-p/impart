use noise::Fbm;
use noise::NoiseFn;
use noise::Seedable;

use crate::bremm::BREMM;
use crate::partition::Partition;

/// A Cell describes geographic location
pub struct Cell {
    /// Elevation in the range 0.0 - 1.0 inclusive
    elevation: f32,

    /// Humidity in the range 0.0 - 1.0 inclusive
    humidity: f32,

    /// Temperature in the range 0.0 - 1.0 inclusive
    temperature: f32,
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

pub struct Renderer {
    elevation_partition: Option<Partition>,
    humidity_partition: Option<Partition>,
    temperature_partition: Option<Partition>,
}

impl Renderer {
    pub fn new() -> Self {
        Renderer {
            elevation_partition: None,
            humidity_partition: None,
            temperature_partition: None,
        }
    }
    pub fn elevation_partition(mut self, partition: Option<Partition>) -> Self {
        self.elevation_partition = partition;
        self
    }
    pub fn humidity_partition(mut self, partition: Option<Partition>) -> Self {
        self.humidity_partition = partition;
        self
    }
    pub fn temperature_partition(mut self, partition: Option<Partition>) -> Self {
        self.temperature_partition = partition;
        self
    }

    fn normalize_elevation(&self, value: f32) -> f32 {
        if let Some(partition) = &self.elevation_partition {
            partition.project(value)
        } else {
            value
        }
    }
    fn normalize_humidity(&self, value: f32) -> f32 {
        if let Some(partition) = &self.humidity_partition {
            partition.project(value)
        } else {
            value
        }
    }
    fn normalize_temperature(&self, value: f32) -> f32 {
        if let Some(partition) = &self.temperature_partition {
            partition.project(value)
        } else {
            value
        }
    }

    pub fn render(&self, cells: &[Cell]) -> Vec<u8> {
        let mut image: Vec<u8> = Vec::with_capacity(cells.len() * 3);

        for cell in cells {
            let humidity = self.normalize_humidity(cell.humidity);
            let temperature = self.normalize_temperature(cell.temperature);
            let elevation = self.normalize_elevation(cell.elevation);

            image.extend(
                BREMM
                    .get_pixel(humidity, temperature, elevation)
                    .into_iter(),
            );
        }

        image
    }
}
