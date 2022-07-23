//! An lookup-based implementation of the Bremm et al colormap that is extended to allow lightening
//! and darkening the output color.
//!
//! https://www.researchgate.net/publication/272729717_A_survey_and_task-based_quality_assessment_of_static_2D_colormaps

use palette::convert::FromColorUnclamped;
use palette::white_point::D65;
use palette::Lab;
use palette::Pixel;
use palette::Srgb;
use png::Decoder;
use png::Info;

static BREMM_PNG: &[u8] = include_bytes!("bremm.png");

lazy_static::lazy_static! {
    pub static ref BREMM: Bremm = Bremm::new(BREMM_PNG);
}

pub struct Bremm {
    pub width: usize,
    pub max_x: f32,
    pub max_y: f32,
    buf: Vec<Lab>,
}

impl Bremm {
    pub fn get_pixel(&self, x: f32, y: f32, z: f32) -> [u8; 3] {
        assert!(x >= 0.0);
        assert!(x <= 1.0);
        assert!(y >= 0.0);
        assert!(y <= 1.0);
        assert!(z >= 0.0);
        assert!(z <= 1.0);
        let x: usize = unsafe { (x * self.max_x + 0.5).to_int_unchecked() };
        let y: usize = unsafe { (y * self.max_y + 0.5).to_int_unchecked() };
        let offset = y * self.width + x;
        let color = self.buf[offset];
        let color = color + Lab::new(80.0 * (z - 0.525), 0.0, 0.0);
        let color = Srgb::from_color_unclamped(color);
        color.into_format().into_raw()
    }

    fn new(bremm_png: &[u8]) -> Self {
        let decoder = Decoder::new(bremm_png);
        let mut reader = decoder.read_info().unwrap();
        let mut rgb = vec![0; reader.output_buffer_size()];
        let info = reader.next_frame(&mut rgb).unwrap();
        rgb.truncate(info.buffer_size());
        let Info { width, height, .. } = reader.info();
        let lab: Vec<_> = rgb
            .chunks_exact(3)
            .map(|components| {
                let color: Srgb<f32> =
                    Srgb::new(components[0], components[1], components[2]).into_format();
                Lab::<D65>::from_color_unclamped(color)
            })
            .collect();

        Bremm {
            width: *width as usize,
            max_x: (*width - 1) as f32,
            max_y: (*height - 1) as f32,
            buf: lab,
        }
    }
}
