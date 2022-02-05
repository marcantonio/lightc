use std::{ffi::c_void, io::Write, os::raw::c_char};
extern crate llvm_sys as llvm;

pub extern "C" fn printd(x: u64) -> u64 {
    println!("{}", x);
    x
}

pub extern "C" fn putchard(x: u64) -> u64 {
    print!("{}", x as u8 as char);
    std::io::stdout()
        .flush()
        .expect("Could not flush to standard output.");
    x
}

#[allow(clippy::missing_safety_doc)]
pub unsafe fn add_symbol(name: &str, ptr: *const ()) {
    let name = std::ffi::CString::new(name).unwrap();
    let addr = ptr as *mut c_void;
    llvm::support::LLVMAddSymbol(name.as_ptr() as *const c_char, addr)
}

pub fn load() {
    unsafe {
        add_symbol("printd", printd as *const ());
        add_symbol("putchard", putchard as *const ());
    }
}
