extern crate wasmparser;
extern crate wasmtext;

use std::io;
use std::io::prelude::*;
use std::fs::File;
use std::str;
use std::env;

use wasmparser::WasmDecoder;
use wasmparser::Parser;
use wasmparser::ParserState;
use wasmtext::Writer;

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("Usage: {} in.wasm", args[0]);
        return;
    }

    let stdout = io::stdout();
    let mut handle = stdout.lock();
    let mut writer = Writer::new(&mut handle);

    let ref buf: Vec<u8> = read_wasm(&args[1]).unwrap();
    let mut parser = Parser::new(buf);
    loop {
        let state = parser.read();
        if let ParserState::Error(err) = *state {
            panic!("Unexpected error: {:?}", err);
        }
        writer.write(state).unwrap();
        if let ParserState::EndWasm = *state {
            break;
        }
    }
}

fn read_wasm(file: &str) -> io::Result<Vec<u8>> {
    let mut data = Vec::new();
    let mut f = File::open(file)?;
    f.read_to_end(&mut data)?;
    Ok(data)
}
