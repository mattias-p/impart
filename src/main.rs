mod bremm;

use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;

use clap::Parser;

use crate::bremm::BREMM;

#[derive(Parser)]
#[clap(version, about)]
struct Cli {
    /// Width in modules (x-coordinates)
    #[clap(short, long, default_value_t = 256)]
    width: u16,

    /// Height in modules (z-coordinates)
    #[clap(short, long, default_value_t = 256)]
    height: u16,

    /// Output file
    #[clap(short, long, default_value = "out.png")]
    outfile: PathBuf,
}

fn main() {
    let cli = Cli::parse();

    let file = File::create(cli.outfile).unwrap();
    let ref mut w = BufWriter::new(file);

    let step_x = 1.0 / (cli.width - 1) as f32;
    let step_y = 1.0 / (cli.height - 1) as f32;

    let mut data: Vec<u8> = Vec::with_capacity(cli.width as usize * cli.height as usize * 3);

    let mut y = 0.0;
    for _ in 0..cli.height {
        let mut x = 0.0;
        for _ in 0..cli.width {
            data.extend(BREMM.get_pixel(x, y, (x + y) / 2.0).into_iter());

            x += step_x;
        }
        y += step_y;
    }

    let mut encoder = png::Encoder::new(w, cli.width as u32, cli.height as u32);
    encoder.set_color(png::ColorType::Rgb);
    let mut writer = encoder.write_header().unwrap();
    writer.write_image_data(&data).unwrap();
}
