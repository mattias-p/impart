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
}

fn main() {
    let cli = Cli::parse();
    let width = cli.width;
    let height = cli.height;

    println!("width {width}");
    println!("height {height}");
}
