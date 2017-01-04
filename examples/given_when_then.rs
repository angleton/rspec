
extern crate rspec;
use rspec::context::describe;
use std::io;

pub fn main() {
    let stdout = &mut io::stdout();
    let mut formatter = rspec::formatter::Simple::new(stdout);

    let mut runner = describe("rspec allows for Cucumber-style BDD testing", (), |ctx, _| {
        ctx.given("A known state of the subject", (), |ctx, _| {
            ctx.when("a key action is performed", (), |ctx, _| {
                ctx.then("the outputs can be observed", |_| {
                    Err(()) as Result<(),()>
                });
            });
        });
    });

    runner.add_event_handler(&mut formatter);
    runner.run(()).unwrap();
}
