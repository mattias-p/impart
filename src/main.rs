mod ast;
mod generate;
mod ir;
mod lexer;
mod render;

use std::fs::File;
use std::io::BufWriter;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use clap::Parser;

use crate::generate::Generator;
use crate::lexer::Lexer;
use crate::render::Renderer;

#[derive(Parser)]
#[clap(version, about)]
struct Cli {
    /// Output file
    #[clap(short, long, default_value = "out.png")]
    outfile: PathBuf,

    /// Source file
    #[clap(short = 'c', long)]
    sourcefile: Option<PathBuf>,

    /// Width in modules (x-coordinates)
    #[clap(short, long, default_value_t = 256)]
    width: u16,

    /// Height in modules (z-coordinates)
    #[clap(short, long, default_value_t = 256)]
    height: u16,

    /// Random seed (0 means pseudo-random)
    #[clap(short, long, default_value_t = 0)]
    seed: u32,

    /// Dump the source
    #[clap(long, action)]
    dump_source: bool,
}

fn main() {
    let cli = Cli::parse();

    let mut buffer = Vec::new();
    let source = if let Some(sourcefile) = cli.sourcefile {
        let mut f = File::open(sourcefile).unwrap();
        f.read_to_end(&mut buffer).unwrap();
        buffer.as_slice()
    } else {
        include_bytes!("default.sbf")
    };

    let file = File::create(cli.outfile).unwrap();
    let ref mut w = BufWriter::new(file);

    let mut lexer = Lexer::new(source);
    let ast = ast::parse(&mut lexer).unwrap();
    let (prog, vars) = ir::compile(&ast).unwrap();
    let renderer = Renderer::new(prog);
    let generator = Generator::new(vars);

    let seed = if cli.seed == 0 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u32
    } else {
        cli.seed
    };

    println!("// seed: {seed}");
    if cli.dump_source {
        std::io::stdout().write(&source).unwrap();
    }

    let cells = generator.generate(cli.width, cli.height, seed);
    let image = renderer.render(&cells);

    let mut encoder = png::Encoder::new(w, cli.width as u32, cli.height as u32);
    encoder.set_color(png::ColorType::Rgb);
    let mut writer = encoder.write_header().unwrap();
    writer.write_image_data(&image).unwrap();
}
