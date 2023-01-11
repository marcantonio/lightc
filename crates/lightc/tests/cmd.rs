use assert_cmd::Command;
use assert_fs::{prelude::*, TempDir};
use predicates::prelude::*;
use serial_test::serial;

/*
| >1 module | -c specified | -o specified |
|-----------|--------------|--------------|-------------|
| no        | no           | no           | `a.out`     |
| no        | no           | yes          | `-o` exec   |
| no        | yes          | no           | mod_name.o  |
| no        | yes          | yes          | `-o` .o     |
| yes       | no           | no           | `a.out`     |
| yes       | no           | yes          | `-o` exec   |
| yes       | yes          | no           | multiple .o |
| yes       | yes          | yes          | `-o` .o     |
*/

#[test]
#[serial]
fn onemod_exec_nooutspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let main_file = tmp_dir.child("main.lt");
    main_file.write_str(
        r#"
module main
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
fn main() {
    printDot()
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg(main_file.path())
        .assert()
        .success();

    assert!(predicate::path::exists().eval(&build_dir));
    assert!(predicate::path::exists().eval(&build_dir.join("main.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.out")));

    let exec_file = tmp_dir.join("a.out");
    assert!(predicate::path::exists().eval(&exec_file));

    Ok(())
}

#[test]
#[serial]
fn onemod_exec_outspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let main_file = tmp_dir.child("main.lt");
    main_file.write_str(
        r#"
module main
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
fn main() {
    printDot()
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    let exec_file = tmp_dir.join("main");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-o")
        .arg(&exec_file)
        .arg(main_file.path())
        .assert()
        .success();

    assert!(predicate::path::exists().eval(&build_dir));
    assert!(predicate::path::exists().eval(&build_dir.join("main.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("main")));

    assert!(predicate::path::exists().eval(&exec_file));

    Ok(())
}

#[test]
#[serial]
fn onemod_obj_nooutspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-c")
        .arg(mod_a_file.path())
        .assert()
        .success();

    assert!(predicate::path::exists().eval(&build_dir));
    assert!(predicate::path::exists().eval(&build_dir.join("a.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.i")));

    let obj_file = tmp_dir.join("a.o");
    assert!(predicate::path::exists().eval(&obj_file));
    assert!(predicate::path::exists().eval(&obj_file.with_extension("i")));

    Ok(())
}

#[test]
#[serial]
fn onemod_obj_outspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    let obj_file = tmp_dir.join("foo.o");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-c")
        .arg("-o")
        .arg(&obj_file)
        .arg(mod_a_file.path())
        .assert()
        .success();

    assert!(predicate::path::exists().eval(&build_dir));
    assert!(predicate::path::exists().eval(&build_dir.join("a.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.i")));

    assert!(predicate::path::exists().eval(&obj_file));
    assert!(predicate::path::exists().eval(&obj_file.with_extension("i")));

    Ok(())
}

#[test]
#[serial]
fn multimod_exec_nooutspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let main_file = tmp_dir.child("main.lt");
    main_file.write_str(
        r#"
module main
use a
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
fn main() {
    printDot()
    a::printBang()
}
"#,
    )?;

    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .args([main_file.path(), mod_a_file.path()])
        .assert()
        .success();

    assert!(predicate::path::exists().eval(&build_dir));
    assert!(predicate::path::exists().eval(&build_dir.join("main.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.out")));

    let exec_file = tmp_dir.join("a.out");
    assert!(predicate::path::exists().eval(&exec_file));

    Ok(())
}

#[test]
#[serial]
fn multimod_exec_outspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let main_file = tmp_dir.child("main.lt");
    main_file.write_str(
        r#"
module main
use a
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
fn main() {
    printDot()
    a::printBang()
}
"#,
    )?;

    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    let exec_file = tmp_dir.join("main");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-o")
        .arg(&exec_file)
        .args([main_file.path(), mod_a_file.path()])
        .assert()
        .success();

    assert!(predicate::path::exists().eval(&build_dir));
    assert!(predicate::path::exists().eval(&build_dir.join("main.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("main")));

    assert!(predicate::path::exists().eval(&exec_file));

    Ok(())
}

#[test]
#[serial]
fn multimod_obj_nooutspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
"#,
    )?;

    let mod_b_file = tmp_dir.child("b.lt");
    mod_b_file.write_str(
        r#"
module b
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-c")
        .args([mod_a_file.path(), mod_b_file.path()])
        .assert()
        .success();

    assert!(predicate::path::exists().eval(&build_dir));

    for file in ["a.o", "a.i", "b.o", "b.i"] {
        assert!(predicate::path::exists().eval(&build_dir.join(file)));
    }

    for file in ["a.o", "a.i", "b.o", "b.i"] {
        assert!(predicate::path::exists().eval(&tmp_dir.join(file)));
    }

    Ok(())
}

#[test]
#[serial]
fn multimod_obj_outspec() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
"#,
    )?;

    let mod_b_file = tmp_dir.child("b.lt");
    mod_b_file.write_str(
        r#"
module b
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");

    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-c")
        .arg("-o")
        .arg("foo.o")
        .args([mod_a_file.path(), mod_b_file.path()])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Argument error: Can't specify `-o` and `-c` for multiple modules"));
    Ok(())
}

#[test]
#[serial]
fn external_mod() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let main_file = tmp_dir.child("main.lt");
    main_file.write_str(
        r#"
module main
use a
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
fn main() {
    printDot()
    a::printBang()
}
"#,
    )?;

    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-c")
        .arg(mod_a_file.path())
        .assert()
        .success();
    assert!(predicate::path::exists().eval(&build_dir.join("a.o")));

    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg(main_file.path())
        .assert()
        .success();
    assert!(predicate::path::exists().eval(&build_dir.join("main.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.out")));

    let exec_file = tmp_dir.join("a.out");
    assert!(predicate::path::exists().eval(&exec_file));

    Ok(())
}

#[test]
#[serial]
fn extern_and_internal_mod() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let main_file = tmp_dir.child("main.lt");
    main_file.write_str(
        r#"
module main
use a
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
fn main() {
    printDot()
    a::printBang()
}
"#,
    )?;

    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let mod_b_file = tmp_dir.child("b.lt");
    mod_b_file.write_str(
        r#"
module b
extern fn putchar(x: int)
fn foo() {}
"#,
    )?;

    let build_dir = tmp_dir.join("build");
    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .arg("-c")
        .arg(mod_b_file.path())
        .assert()
        .success();
    assert!(predicate::path::exists().eval(&build_dir));
    assert!(predicate::path::exists().eval(&build_dir.join("b.o")));

    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .args([main_file.path(), mod_a_file.path()])
        .assert()
        .success();
    assert!(predicate::path::exists().eval(&build_dir.join("a.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("main.o")));
    assert!(predicate::path::exists().eval(&build_dir.join("a.out")));

    let exec_file = tmp_dir.join("a.out");
    assert!(predicate::path::exists().eval(&exec_file));

    Ok(())
}

#[test]
#[serial]
fn exec_no_main_mod() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let mod_a_file = tmp_dir.child("a.lt");
    mod_a_file.write_str(
        r#"
module a
extern fn putchar(x: int)
fn printDot() {
    putchar(46)
    putchar(10)
}
"#,
    )?;

    let mod_b_file = tmp_dir.child("b.lt");
    mod_b_file.write_str(
        r#"
module b
extern fn putchar(x: int)
fn printBang() {
    putchar(33)
    putchar(10)
}
"#,
    )?;

    let build_dir = tmp_dir.join("build");

    Command::cargo_bin("lightc")?
        .current_dir(tmp_dir.path())
        .arg("--build-dir")
        .arg(&build_dir)
        .args([mod_a_file.path(), mod_b_file.path()])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Linking error: no `main` module for executable"));
    Ok(())
}
