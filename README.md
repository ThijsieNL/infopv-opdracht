# GCL Verifier 

This project contains two CLI tools:

- GCL Verifier — a tool to verify properties of GCL programs (e.g., correctness conditions, assertions).
- GCL Benchmarker — a tool to run performance and scalability experiments on the verifier (or other GCL tools) by executing batches of inputs and collecting timing / resource metrics.

This README explains the layout, basic usage, and examples for building and running both tools.

## Repository layout

- /app/ — source code for the gcl-verifier 
- /bench/ - source code for the gcl-benchmarker
- /src/ — source code for the parser and engine (the bulk of the symbolic execution logic)
- /examples/ — sample GCL programs and testcases.
- README.md — this file.

## Prerequisites

The prerequisites are that you have the right cabal and haskell versions installed per the instruction given for the course.

## Build instructions

To build the entire project just run `cabal build`

## GCL Verifier — usage examples

Running the verifier can be done by running `cabal run gcl-verifier -- FILE`.
For all possible options and documentation run `cabal run gcl-verifier -- --help`.

## GCL Benchmarker — usage examples

Running the benchmarker can be done by running `cabal run gcl-benchmarker -- FILE`.
For all possible options and documentation run `cabal run gcl-benchmarker -- --help`.
Note that any combination of options can be passed to the benchmarker and it will bench all combinations.
e.g. `cabal run gcl-benchmarker -- examples/E.gcl -k 5 -k 10 -p 0.0 -p 1.0 -s True` will run four different benchmarks for all combinations of `k` and `p`.
Default k is `[10, 20, 50]` and p is `[0.0, 0.5, 1.0]`.