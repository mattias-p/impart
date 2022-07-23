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

pub fn generate(width: u16, height: u16, seed: u32) -> Vec<Cell> {
    let elevation_noise = Fbm::new().set_seed(seed);
    let humidity_noise = Fbm::new().set_seed(seed + 1);
    let temperature_noise = Fbm::new().set_seed(seed + 2);

    let mut cells = Vec::with_capacity(width as usize * height as usize);

    let step_x = 1.0 / (width - 1) as f64;
    let step_y = 1.0 / (height - 1) as f64;
    let mut y = 0.0;
    for _ in 0..height {
        let mut x = 0.0;
        for _ in 0..width {
            let elevation = (0.75 + 0.25 * elevation_noise.get([x, y]) - 0.5 * y) as f32;
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

pub fn render(cells: &[Cell], partition: &Option<Partition>) -> Vec<u8> {
    let mut image: Vec<u8> = Vec::with_capacity(cells.len() * 3);

    for cell in cells {
        let mut humidity = cell.humidity;
        let mut temperature = cell.temperature;
        let mut elevation = cell.elevation;

        if let Some(ref partition) = partition {
            humidity = partition.project(humidity);
            temperature = partition.project(temperature);
            elevation = partition.project(elevation);
        }

        image.extend(
            BREMM
                .get_pixel(1.0 - humidity, 1.0 - temperature, elevation)
                .into_iter(),
        );
    }

    image
}
