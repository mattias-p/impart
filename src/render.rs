use crate::bremm::BREMM;
use crate::generate::Cell;
use crate::partition::Partition;

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
