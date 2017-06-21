#!/bin/bash
cargo build --example to-wast || exit 1
echo "Updating tests..."
find tests -name "*.wasm" -exec sh -c './target/debug/examples/to-wast {} > {}.out' \;
