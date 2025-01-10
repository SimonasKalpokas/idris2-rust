# idris2-rust

**idris2-rust** is a backend for the Idris2 programming language, allowing the compilation of Idris2 code to Rust.

---

## Features

- **Idris2 to Rust Compilation**: Translates a subset of Idris2 code to Rust.
- **Idris2 Subset**: Designed to work with a specific subset of the Idris2 language for simplicity and efficiency.

## Limitations

- **No FFI Support**: Foreign Function Interface is not supported.
- **No Holes**: Idris2 holes are not supported.

---

## Getting Started

### Prerequisites

Ensure you have the following installed on your system:
- [Idris2 with required libraries](https://idris2.readthedocs.io/en/latest/backends/custom.html)
- [Rust](https://www.rust-lang.org/)
- `make`

### Building the Project

To build the project, simply run:
```bash
make build
```

### Running the Backend

Use the following command to compile Idris2 code to Rust:
```bash
./build/exec/idris2-rust <filename> -o <outfile>
```
Create a rust project with the output file as well as support.rs file, found in `/support` directory.

### Example

```bash
./build/exec/idris2-rust testPrograms/Basic.idr -o basic.rs
```

