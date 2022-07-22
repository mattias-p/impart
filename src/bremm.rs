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
    buf: Vec<u8>,
}

impl Bremm {
    pub fn get_pixel(&self, x: f32, y: f32) -> [u8; 3] {
        let x: usize = unsafe { (x * self.max_x + 0.5).to_int_unchecked() };
        let y: usize = unsafe { (y * self.max_y + 0.5).to_int_unchecked() };
        let offset = (y * self.width + x) * 3;
        [
            self.buf[offset + 0],
            self.buf[offset + 1],
            self.buf[offset + 2],
        ]
    }

    fn new(bremm_png: &[u8]) -> Self {
        let decoder = Decoder::new(bremm_png);
        let mut reader = decoder.read_info().unwrap();
        let mut buf = vec![0; reader.output_buffer_size()];
        let info = reader.next_frame(&mut buf).unwrap();
        buf.truncate(info.buffer_size());
        let Info { width, height, .. } = reader.info();
        Bremm {
            width: *width as usize,
            max_x: (*width - 1) as f32,
            max_y: (*height - 1) as f32,
            buf,
        }
    }
}
