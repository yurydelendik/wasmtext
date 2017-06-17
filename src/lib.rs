pub use writer::Writer;

mod writer;

extern crate wasmparser;

#[cfg(test)]
mod tests {
    use std::io::prelude::*;
    use std::fs::{File, read_dir};
    use std::path::PathBuf;
    use wasmparser::Parser;
    use wasmparser::ParserState;
    use writer::Writer;

    fn read_file_data(path: &PathBuf) -> Vec<u8> {
        println!("Reading {:?}", path);
        let mut data = Vec::new();
        let mut f = File::open(path).ok().unwrap();
        f.read_to_end(&mut data).unwrap();
        data
    }

    #[test]
    fn it_works() {
        for entry in read_dir("tests").unwrap() {
            let mut path = entry.unwrap().path();
            if path.extension().unwrap() != "wasm" {
                continue;
            }
            let data = read_file_data(&path);
            let mut parser = Parser::new(data.as_slice());
            let mut out_buffer = Vec::new();
            {
                let mut writer = Writer::new(&mut out_buffer);
                loop {
                    let state = parser.read();
                    if let ParserState::Error(msg) = *state {
                        panic!("Error: {}", msg);
                    }
                    writer.write(state).unwrap();
                    if let ParserState::EndWasm = *state {
                        break;
                    }
                }
            }
            let name = String::from(path.file_name().unwrap().to_str().unwrap()) + ".out";
            path.set_file_name(name);
            let expected = read_file_data(&path);
            if expected != &out_buffer[..] {
                panic!("Test {:?} failed", path.file_name().unwrap().to_str())
            }
        }
    }
}
