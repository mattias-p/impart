use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;

use clap::Parser;

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

    let data = vec![127; cli.width as usize * cli.height as usize];

    let encoder = png::Encoder::new(w, cli.width as u32, cli.height as u32);
    let mut writer = encoder.write_header().unwrap();
    writer.write_image_data(&data).unwrap();
}
