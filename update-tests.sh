#!/bin/bash
find tests -name "*.wasm" -exec sh -c 'cargo run --example to-wast {} > {}.out' \;
