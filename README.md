Welcome to the repo for the Light progamming language! Light is a nascent, strongly-typed, systems language aimed at the following:
1. High performance
2. Low cognative overhead
3. Native concurrency
4. Memory saftey

These are lofty goals. Right now the language is little more than a toy, but you can create moderately useful programs already.

Immediate next steps are:
- [x] User defined types
- [x] A working module system
- [x] Beginnings of a standard library
- [ ] A first class string type
- [ ] Experimentation with [Hybrid Generational Memory](https://verdagon.dev/blog/hybrid-generational-memory)

# Usage
Only support on Linux currently. With a working Rust toolchain and LLVM >= 14, you should be able to run `cargo build`. Tests should be run via [Insta](https://docs.rs/insta/latest/insta/).
