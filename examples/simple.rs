extern crate rspec;

use std::io;

pub fn main() {
    let stdout = &mut io::stdout();
    let mut formatter = rspec::formatter::Simple::new(stdout);

    let mut runner = rspec::describe("rspec is a classic BDD testing", (), |ctx| {
        ctx.it("can define tests", |_| true);

        ctx.specify("rspec use results for tests results", |ctx| {
            ctx.it("passes if the return is_ok()", |_| Ok(()) as Result<(),()>);
            ctx.it("fails if the return is_err()", |_| Err(()) as Result<(),()>);
        });

        ctx.specify("rspec can use bools", |ctx| {
            ctx.it("should pass if true", |_| true);
            ctx.it("should fail if false", |_| false);
            ctx.it("is convenient for comparisons", |_| {
                (42 % 37 + 2) > 3
            })
        });

        ctx.specify("rspec can use units", |ctx| {
            ctx.it("should pass if the return is ()", |_| ());
            ctx.it("is convenient for asserts", |_| assert_eq!(1, 1));
        });
    });

    runner.add_event_handler(&mut formatter);
    runner.run_or_exit();
}
