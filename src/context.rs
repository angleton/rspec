//! The Context module holds all the functionality for the test declaration, that is: `describe`,
//! `before_each`, `before_all`, `after_each`, `after_all`, `it` and their variants.
//!
//! A Context can also holds reference to children Contextes, for whom the before closures will be
//! executed after the before closures of the current context. The order of execution of tests
//! respect the order of declaration of theses tests.
//!
//! Running these tests and doing asserts is not the job of the Context, but the Runner, which is
//! a struct returned by the root context declaration.
//!
//! # Examples
//! ```no_run
//! use rspec::context::*;
//!
//! // `rdescribe` instanciate a runner and run it transparently
//! rdescribe("Context", (), |ctx| {
//!     describe("Context::describe", (), |ctx| {
//!         ctx.it("can be nested", |_| Ok(()) as Result<(),()>);
//!         ctx.it("use a `ctx` object", |_| Ok(()) as Result<(),()>)
//!     });
//!
//!     describe("Context::specify", (), |ctx| {
//!         ctx.specify("can be used as a drop-in alternative to `Context::describe`", (), |ctx| {
//!             // ...
//!         });
//!     });
//!
//!     describe("Context::context", (), |ctx| {
//!         ctx.context("can be used as a drop-in alternative to `Context::describe`", (), |ctx| {
//!             // ...
//!         });
//!     });
//!
//!     describe("Context::it", (), |ctx| {
//!         ctx.it("uses a Result returns", |_| Ok(()) as Result<(),()>);
//!         ctx.it("can also use asserts", |_| {
//!             assert_eq!(42, 12 + 30);
//!             Ok(()) as Result<(),()> // don't forget the result type
//!         })
//!     });
//!
//!     describe("Context::given", (), |ctx| {
//!         ctx.describe("can be used for Cucumber-style BDD, like:", (), |ctx| {
//!             ctx.given("A known state of the subject", (), |ctx| {
//!                 ctx.when("a key action is performed", (), |ctx| {
//!                     ctx.then("the outputs can be observed", |_| {
//!                         Ok(()) as Result<(),()>
//!                     });
//!                 });
//!             });
//!         });
//!     });
//! });
//!

use runner::*;
use events::Event;
use example_result::{self, ExampleResult};

pub trait Visitable<T> {
    fn accept(self, visitor: &mut T) -> TestReport;
}

/// The type used for a test result
pub type TestResult = Result<(), ()>;

pub struct Named<T>(String, T);

/// This enum is used to build a tree of named tests and contextes.
pub enum Testable<'a, T>
    where T: 'a
{
    Test(Test<'a, T>),
    Context(Context<'a, T>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TestLabel {
    It,
    Example,
    Then,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TestInfo {
    pub label: TestLabel,
    pub name: String,
}

pub struct Test<'a, T>
    where T: 'a
{
    pub info: TestInfo,
    function: Box<FnMut(T) -> ExampleResult + 'a + Send + Sync>,
}

impl<'a, T> Test<'a, T>
    where T: 'a
{
    pub fn new<F>(info: TestInfo, f: F) -> Self
        where F: FnMut(T) -> ExampleResult + 'a + Send + Sync
    {
        Test {
            info: info,
            function: Box::new(f),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SuiteLabel {
    Describe,
    Suite,
    Given,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SuiteInfo {
    pub label: SuiteLabel,
    pub name: String,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ContextLabel {
    Describe,
    Context,
    Specify,
    Given,
    When,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ContextInfo {
    pub label: ContextLabel,
    pub name: String,
}

pub struct Suite<'a, T>
    where T: 'a
{
    pub info: SuiteInfo,
    root: Context<'a, T>,
}

impl<'a, T> Suite<'a, T>
    where T: 'a
{
    pub fn new(info: SuiteInfo, root: Context<'a, T>) -> Self {
        Suite {
            info: info,
            root: root,
        }
    }
}

impl<'a, T> Visitable<Runner<'a, T>> for Suite<'a, T>
    where T: 'a + Clone
{
    fn accept(self, runner: &mut Runner<'a, T>) -> TestReport {
        runner.broadcast(Event::EnterSuite(self.info.clone()));
        let report = self.root.accept(runner);
        runner.broadcast(Event::ExitSuite(report.clone()));
        report
    }
}

/// A Context holds a collection of tests, a collection of closures to call _before_ running any
/// tests, and a collection of closure to call _after_ all the tests..
///
/// This is effectively the struct we fill when calling `ctx.it()`
pub struct Context<'a, T>
    where T: 'a
{
    info: ContextInfo,
    env: T,
    testables: Vec<Testable<'a, T>>,
    before_each: Vec<Box<FnMut(&mut T) + 'a + Send + Sync>>,
    after_each: Vec<Box<FnMut(&mut T) + 'a + Send + Sync>>,
    before_all: Vec<Box<FnMut(&mut T) + 'a + Send + Sync>>,
    after_all: Vec<Box<FnMut(&mut T) + 'a + Send + Sync>>,
}

impl<'a, T> Context<'a, T>
    where T: 'a
{
    pub fn new(info: ContextInfo, env: T) -> Self {
        Context {
            info: info,
            env: env,
            testables: vec![],
            before_each: vec![],
            after_each: vec![],
            before_all: vec![],
            after_all: vec![],
        }
    }
}

impl<'a, T> Visitable<Runner<'a, T>> for Context<'a, T>
    where T: 'a + Clone
{
    fn accept(self, runner: &mut Runner<'a, T>) -> TestReport {
        let mut report = TestReport::default();

        let Context { mut env,
                      testables,
                      mut before_each,
                      mut after_each,
                      mut before_all,
                      mut after_all,
                      .. } = self;

        for before_all_function in before_all.iter_mut() {
            before_all_function(&mut env);
        }

        for testable in testables {
            let test_res = {
                let mut env = env.clone();
                for before_each_function in before_each.iter_mut() {
                    before_each_function(&mut env);
                }
                let result = match testable {
                    Testable::Test(test) => {
                        let Test { info, mut function } = test;
                        runner.broadcast(Event::EnterTest(info.clone()));
                        use std::panic::{catch_unwind, AssertUnwindSafe};
                        let env = env.clone();
                        let result = catch_unwind(AssertUnwindSafe(move || function(env)));
                        let result = result.unwrap_or_else(|_| example_result::FAILED_RES);
                        runner.broadcast(Event::ExitTest(result));
                        result.into()
                    }
                    Testable::Context(sub_ctx) => {
                        runner.broadcast(Event::EnterContext(sub_ctx.info.clone()));
                        let report = sub_ctx.accept(runner);
                        runner.broadcast(Event::ExitContext(report.clone()));
                        report
                    }
                };
                for after_each_function in after_each.iter_mut() {
                    after_each_function(&mut env);
                }
                result
            };

            report.add(test_res);
        }

        for after_all_function in after_all.iter_mut() {
            after_all_function(&mut env);
        }

        report
    }
}

impl<'a, T> Context<'a, T>
    where T: Clone
{
    /// Open and name a new example group, which will be keeped as a child context of the current
    /// context.
    ///
    /// Note that the order of declaration is respected for running the tests.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use rspec::context::rdescribe;
    ///
    /// // `rdescribe` instanciate a runner and run it transparently
    /// rdescribe("inside this describe, we use the context", (), |ctx| {
    ///
    ///     ctx.it("should run first", |_| Ok(()) as Result<(),()>);
    ///
    ///     ctx.describe("open describe", (), |ctx| {
    ///
    ///         ctx.it("should run second", |_| Ok(()) as Result<(),()>);
    ///
    ///         ctx.describe("in a describe", (), |ctx| {
    ///
    ///             ctx.describe("in a describe", (), |_| {});
    ///
    ///             ctx.it("should run third", |_| Ok(()) as Result<(),()>);
    ///
    ///         });
    ///     });
    ///
    ///     ctx.it("should run last", |_| Ok(()) as Result<(),()>);
    /// });
    /// ```
    pub fn context<S, F>(&mut self, name: S, body: F)
        where S: Into<String>,
              F: 'a + Send + Sync + FnOnce(&mut Context<'a, T>) -> ()
    {
        let info = ContextInfo {
            label: ContextLabel::Context,
            name: name.into(),
        };
        self.context_internal(info, body)
    }

    /// Alias for [`context`](struct.Context.html#method.context).
    ///
    /// See [`context`](struct.Context.html#method.context) for more info.
    pub fn specify<S, F>(&mut self, name: S, body: F)
        where S: Into<String>,
              F: 'a + Send + Sync + FnOnce(&mut Context<'a, T>) -> ()
    {
        let info = ContextInfo {
            label: ContextLabel::Specify,
            name: name.into(),
        };
        self.context_internal(info, body)
    }

    /// Alias for [`describe`](struct.Context.html#method.describe).
    ///
    /// See [`describe`](struct.Context.html#method.describe) for more info.
    pub fn when<S, F>(&mut self, name: S, body: F)
        where S: Into<String>,
              F: 'a + Send + Sync + FnOnce(&mut Context<'a, T>) -> ()
    {
        let info = ContextInfo {
            label: ContextLabel::When,
            name: name.into(),
        };
        self.context_internal(info, body)
    }

    fn context_internal<F>(&mut self, info: ContextInfo, body: F)
        where F: 'a + Send + Sync + FnOnce(&mut Context<'a, T>) -> ()
    {
        let mut child = Context::new(info, self.env.clone());
        body(&mut child);
        self.testables.push(Testable::Context(child))
    }

    //    /// Register and name a closure as an example
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```no_run
    //    /// use rspec::context::rdescribe;
    //    ///
    //    /// // `rdescribe` instanciate a runner and run it transparently
    //    /// rdescribe("inside this describe, we use the context", (), |ctx| {
    //    ///
    //    ///     ctx.it("test at the root", || Ok(()) as Result<(),()>);
    //    ///
    //    ///     ctx.describe("a group of examples", (), |ctx| {
    //    ///
    //    ///         ctx.it("should be usable inside a describe", || Ok(()) as Result<(),()>);
    //    ///
    //    ///         ctx.describe("a nested describe", (), |ctx| {
    //    ///
    //    ///             ctx.it("should be usabel inside multiple describes", || Ok(()) as Result<(),()>);
    //    ///             ctx.it("should be able to declare multiple tests", || Ok(()) as Result<(),()>);
    //    ///
    //    ///         });
    //    ///
    //    ///         ctx.it("doesn't care if it's before or after a describe", || Ok(()) as Result<(),()>);
    //    ///     });
    //    /// });
    //    /// ```
    pub fn it<S, F, U>(&mut self, name: S, body: F)
        where S: Into<String>,
              F: 'a + Send + Sync + FnMut(T) -> U,
              U: Into<ExampleResult>
    {
        let info = TestInfo {
            label: TestLabel::It,
            name: name.into(),
        };
        self.test_internal(info, body)
    }

    /// Alias for [`it`](struct.Context.html#method.it).
    ///
    /// See [`it`](struct.Context.html#method.it) for more info.
    pub fn example<S, F, U>(&mut self, name: S, body: F)
        where S: Into<String>,
              F: 'a + Send + Sync + FnMut(T) -> U,
              U: Into<ExampleResult>
    {
        let info = TestInfo {
            label: TestLabel::Example,
            name: name.into(),
        };
        self.test_internal(info, body)
    }

    /// Alias for [`it`](struct.Context.html#method.it).
    ///
    /// See [`it`](struct.Context.html#method.it) for more info.
    pub fn then<S, F, U>(&mut self, name: S, body: F)
        where S: Into<String>,
              F: 'a + Send + Sync + FnMut(T) -> U,
              U: Into<ExampleResult>
    {
        let info = TestInfo {
            label: TestLabel::Then,
            name: name.into(),
        };
        self.test_internal(info, body)
    }

    pub fn test_internal<F, U>(&mut self, info: TestInfo, mut body: F)
        where F: 'a + Send + Sync + FnMut(T) -> U,
              U: Into<ExampleResult>
    {
        let test = Test::new(info, move |env| body(env).into());
        self.testables.push(Testable::Test(test))
    }

    //    /// Declares a closure that will be executed once before the tests of the current Context.
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```no_run
    //    /// use rspec::context::rdescribe;
    //    /// use std::sync::atomic::{AtomicUsize, Ordering};
    //    ///
    //    /// let counter = &mut AtomicUsize::new(0);
    //    ///
    //    /// // `rdescribe` instanciate a runner and run it transparently
    //    /// rdescribe("inside this describe, we use the context", counter, |ctx| {
    //    ///
    //    ///     // This will increment the counter once before the tests:
    //    ///     ctx.before_all(|| { counter.fetch_add(1, Ordering::SeqCst); });
    //    ///
    //    ///     ctx.it("should run after the before_all", || {
    //    ///         assert_eq!(1, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    ///
    //    ///     ctx.describe("a group of examples", (), |ctx| {
    //    ///
    //    ///         ctx.it("should see no further increment", || {
    //    ///             assert_eq!(1, counter.load(Ordering::SeqCst));
    //    ///             Ok(()) as Result<(),()>
    //    ///         });
    //    ///     });
    //    ///
    //    ///     ctx.it("should run after all the before_alls AND the previous it", || {
    //    ///         assert_eq!(1, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    /// });
    //    /// ```
    pub fn before_all<F>(&mut self, body: F)
        where F: 'a + Send + Sync + FnMut(&mut T)
    {

        self.before_all.push(Box::new(body))
    }

    //    /// Declares a closure that will be executed once after all tests of the current Context.
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```no_run
    //    /// use rspec::context::rdescribe;
    //    /// use std::sync::atomic::{AtomicUsize, Ordering};
    //    ///
    //    /// let counter = &mut AtomicUsize::new(0);
    //    ///
    //    /// // `rdescribe` instanciate a runner and run it transparently
    //    /// rdescribe("inside this describe, we use the context", (), |ctx| {
    //    ///
    //    ///     // This will increment the counter once after the tests
    //    ///     ctx.after_all(|counter| {
    //    ///         counter.fetch_add(1, Ordering::SeqCst);
    //    ///     });
    //    ///
    //    ///     ctx.it("should run after the after_each", || {
    //    ///         assert_eq!(0, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    ///
    //    ///     ctx.describe("a group of examples", (), |ctx| {
    //    ///         ctx.it("should see no further increment", || {
    //    ///             assert_eq!(0, counter.load(Ordering::SeqCst));
    //    ///             Ok(()) as Result<(),()>
    //    ///         });
    //    ///     });
    //    ///
    //    ///     ctx.it("should run after all the after_eachs AND the previous it", || {
    //    ///         assert_eq!(0, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    /// });
    //    /// ```
    pub fn after_all<F>(&mut self, body: F)
        where F: 'a + Send + Sync + FnMut(&mut T)
    {

        self.after_all.push(Box::new(body))
    }

    //    /// Declares a closure that will be executed before each test of the current Context.
    //    ///
    //    /// **PLEASE NOTE**: due to a bug in current versions of rspec, the before closures **WILL BE
    //    /// CALLED ONLY ONCE** for all the children of the current context.
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```no_run
    //    /// use rspec::context::rdescribe;
    //    /// use std::sync::atomic::{AtomicUsize, Ordering};
    //    ///
    //    /// let counter = &mut AtomicUsize::new(0);
    //    ///
    //    /// // `rdescribe` instanciate a runner and run it transparently
    //    /// rdescribe("inside this describe, we use the context", (), |ctx| {
    //    ///
    //    ///     // This will increment the counter at each test
    //    ///     ctx.before_each(|counter| {
    //    ///         counter.fetch_add(1, Ordering::SeqCst);
    //    ///         counter
    //    ///     });
    //    ///
    //    ///     ctx.it("should run after the before_each", || {
    //    ///         assert_eq!(1, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    ///
    //    ///     ctx.describe("a group of examples", (), |ctx| {
    //    ///
    //    ///         ctx.it("should see 1 increment", || {
    //    ///             assert_eq!(2, counter.load(Ordering::SeqCst));
    //    ///             Ok(()) as Result<(),()>
    //    ///         });
    //    ///
    //    ///         // XXX - note that the before_each has not been applied another time
    //    ///         ctx.it("should NOT see another increment", || {
    //    ///             assert_eq!(2, counter.load(Ordering::SeqCst));
    //    ///             Ok(()) as Result<(),()>
    //    ///         });
    //    ///     });
    //    ///
    //    ///     ctx.it("should run after all the before_eachs AND the previous it", || {
    //    ///         assert_eq!(3, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    /// });
    //    /// ```
    pub fn before_each<F>(&mut self, body: F)
        where F: 'a + Send + Sync + FnMut(&mut T)
    {

        self.before_each.push(Box::new(body))
    }

    //    /// Declares a closure that will be executed after each test of the current Context.
    //    ///
    //    /// **PLEASE NOTE**: due to a bug in current versions of rspec, the after closures **WILL BE
    //    /// CALLED ONLY ONCE** for all the children of the current context.
    //    ///
    //    /// # Examples
    //    ///
    //    /// ```no_run
    //    /// use rspec::context::rdescribe;
    //    /// use std::sync::atomic::{AtomicUsize, Ordering};
    //    ///
    //    /// let counter = &mut AtomicUsize::new(0);
    //    ///
    //    /// // `rdescribe` instanciate a runner and run it transparently
    //    /// rdescribe("inside this describe, we use the context", (), |ctx| {
    //    ///
    //    ///     // This will increment the counter at each test
    //    ///     ctx.after_each(|counter| {
    //    ///         counter.fetch_add(1, Ordering::SeqCst);
    //    ///     });
    //    ///
    //    ///     ctx.it("should run after the after_each", |counter| {
    //    ///         assert_eq!(0, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    ///
    //    ///     ctx.describe("a group of examples", (), |ctx| {
    //    ///
    //    ///         ctx.it("should see 1 increment", |counter| {
    //    ///             assert_eq!(1, counter.load(Ordering::SeqCst));
    //    ///             Ok(()) as Result<(),()>
    //    ///         });
    //    ///
    //    ///         // XXX - note that the after_each has not been applied another time
    //    ///         ctx.it("should NOT see another increment", |counter| {
    //    ///             assert_eq!(1, counter.load(Ordering::SeqCst));
    //    ///             Ok(()) as Result<(),()>
    //    ///         });
    //    ///     });
    //    ///
    //    ///     ctx.it("should run after all the after_eachs AND the previous it", |counter| {
    //    ///         assert_eq!(2, counter.load(Ordering::SeqCst));
    //    ///         Ok(()) as Result<(),()>
    //    ///     });
    //    /// });
    //    /// ```
    pub fn after_each<F>(&mut self, body: F)
        where F: 'a + Send + Sync + FnMut(&mut T)
    {

        self.after_each.push(Box::new(body))
    }
}

// /// This is the root describe. It will instanciate a root `Context` that you can use to declare
// /// examples, and will returns a Runner ready to run the tests.
// ///
// /// See [`rdescribe`](fn.rdescribe.html) if you want an helper which will setup and run the tests
// /// for you.
// ///
// /// # Examples
// ///
// /// ```no_run
// /// use rspec::context::describe;
// ///
// /// let mut runner = describe("inside this describe, we use the context", (), |ctx| {
// ///
// ///     ctx.it("test at the root", || Ok(()) as Result<(),()>);
// ///
// ///     ctx.describe("a group of examples", (), |ctx| {
// ///
// ///         ctx.it("should be usable inside a describe", || Ok(()) as Result<(),()>);
// ///
// ///         ctx.describe("a nested describe", (), |ctx| {
// ///
// ///             ctx.it("should be usabel inside multiple describes", || Ok(()) as Result<(),()>);
// ///             ctx.it("should be able to declare multiple tests", || Ok(()) as Result<(),()>);
// ///
// ///         });
// ///
// ///         ctx.it("doesn't care if it's before or after a describe", || Ok(()) as Result<(),()>);
// ///     });
// /// });
// /// let result = runner.run();
// /// ```
pub fn describe<'a, 'b, S, F, T>(name: S, env: T, body: F) -> Runner<'a, T>
    where S: Into<String>,
          F: 'a + FnOnce(&mut Context<'a, T>) -> (),
          T: Clone
{
    let info = SuiteInfo {
        label: SuiteLabel::Describe,
        name: name.into(),
    };
    suite_internal(info, env, body)
}

pub fn suite<'a, 'b, S, F, T>(name: S, env: T, body: F) -> Runner<'a, T>
    where S: Into<String>,
          F: 'a + FnOnce(&mut Context<'a, T>) -> (),
          T: Clone
{
    let info = SuiteInfo {
        label: SuiteLabel::Suite,
        name: name.into(),
    };
    suite_internal(info, env, body)
}

pub fn given<'a, 'b, S, F, T>(name: S, env: T, body: F) -> Runner<'a, T>
    where S: Into<String>,
          F: 'a + FnOnce(&mut Context<'a, T>) -> (),
          T: Clone
{
    let info = SuiteInfo {
        label: SuiteLabel::Given,
        name: name.into(),
    };
    suite_internal(info, env, body)
}

fn suite_internal<'a, 'b, F, T>(info: SuiteInfo, env: T, body: F) -> Runner<'a, T>
    where F: 'a + FnOnce(&mut Context<'a, T>) -> (),
          T: Clone
{
    // Note: root context's info get's ignored.
    let ctx_info = ContextInfo {
        label: ContextLabel::Context,
        name: "HANDS OFF!".into(),
    };
    let mut ctx = Context::new(ctx_info, env.clone());
    body(&mut ctx);
    let suite = Suite::new(info, ctx);
    Runner::new(suite)
}

#[cfg(test)]
mod tests {
    pub use super::*;
    pub use example_result::ExampleResult;

    mod describe {
        pub use super::*;

        macro_rules! test_describe_alias {
            ($alias: ident) => {
                describe("A Root", (), |ctx| {
                    ctx.$alias("nested describe", (), |_| {})
                });
            }
        }

        #[test]
        fn describe_has_alias_specify() {
            test_describe_alias!(specify);
        }

        #[test]
        fn describe_has_alias_context() {
            test_describe_alias!(context);
        }

        #[test]
        fn describe_has_alias_given() {
            test_describe_alias!(given);
        }

        #[test]
        fn it_has_a_root_describe_function() {
            let _: Runner<()> = describe("A Test", (), |_| {});
        }

        #[test]
        fn it_can_call_describe_inside_describe_body() {
            describe("A Root",
                     (),
                     |ctx| ctx.describe("nested describe", (), |_| {}));
        }

        #[test]
        fn it_can_call_given_inside_describe_body() {
            describe("A Root", (), |ctx| ctx.given("nested describe", (), |_| {}));
        }

        #[test]
        fn it_can_call_when_inside_describe_body() {
            describe("A Root", (), |ctx| ctx.when("nested describe", (), |_| {}));
        }

        #[test]
        fn it_can_call_it_inside_describe_body() {
            let _: Runner<()> = describe("A root",
                                         (),
                                         |ctx| ctx.it("is a test", |_| Ok(()) as Result<(), ()>));
        }

        #[test]
        fn it_can_call_example_inside_describe_body() {
            let _: Runner<()> = describe("A root", (), |ctx| {
                ctx.example("is a test", |_| Ok(()) as Result<(), ()>)
            });
        }

        #[test]
        fn it_can_call_given_when_then_inside_describe_body() {
            describe("A root", (), |ctx| {
                ctx.given("nested given", (), |ctx| {
                    ctx.when("nested when", (), |ctx| {
                        ctx.then("nested then", |_| Ok(()) as Result<(), ()>);
                    });
                });
            });
        }
    }

    // mod it {
    //     pub use super::*;
    //
    //     macro_rules! test_it_alias {
    //         ($alias: ident) => {
    //             describe("A Root", (), |ctx| ctx.$alias("nested it", || {}));
    //         }
    //     }
    //
    //     #[test]
    //     fn it_has_alias_example() {
    //         test_it_alias!(example);
    //     }
    //
    //     #[test]
    //     fn it_has_alias_then() {
    //         test_it_alias!(then);
    //     }
    //
    //     #[test]
    //     fn it_can_return_a_unit() {
    //         rdescribe("A root", (), |ctx| {
    //             ctx.it("a unit is ok", || {} )
    //         })
    //     }
    //
    //     #[test]
    //     fn is_can_return_a_bool_true() {
    //         rdescribe("a root", (), |ctx| {
    //             ctx.it("a bool true is err", || { true });
    //         });
    //     }
    //
    //     #[test]
    //     fn is_can_return_a_bool_false() {
    //         let runner = describe("a root", (), |ctx| {
    //             ctx.it("a bool true is err", || { false });
    //         });
    //         assert!(runner.run().is_err())
    //     }
    //
    //     #[test]
    //     fn it_can_return_a_result_ok() {
    //         rdescribe("a root", (), |ctx| {
    //             ctx.it("is ok", || Ok(()) as Result<(), ()>);
    //         });
    //     }
    //
    //     #[test]
    //     fn it_can_return_a_result_err() {
    //         let runner = describe("a root", (), |ctx| {
    //             ctx.it("is err", || Err(()) as Result<(), ()>);
    //         });
    //         assert!(runner.run().is_err())
    //     }
    //
    //     #[test]
    //     fn it_can_return_any_result() {
    //         rdescribe("a root", (), |ctx| {
    //             ctx.it("is ok", || Ok(3) as Result<i32, ()>);
    //         });
    //     }
    //
    //     // XXX this MUST NOT compiles
    //     //#[test]
    //     //fn it_cant_returns_something_that_dont_implements_to_res() {
    //     //    let mut runner = describe("a root", (), |ctx| {
    //     //        ctx.it("a bool true is err", || { 3 });
    //     //    });
    //     //    assert!(runner.run().is_err())
    //     //}
    // }
    //
    // mod before_each {
    //     pub use super::*;
    //
    //     #[test]
    //     fn can_be_called_inside_describe() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         {
    //             let runner = describe("a root", counter, |ctx| {
    //                 ctx.before_each(|counter| {
    //                     counter.fetch_add(1, Ordering::Relaxed);
    //                 });
    //                 ctx.it("first", |_| Ok(()) as Result<(),()>);
    //                 ctx.it("second", |_| Ok(()) as Result<(),()>);
    //                 ctx.it("third", |_| Ok(()) as Result<(),()>);
    //             });
    //             let _ = runner.run();
    //         }
    //
    //         assert_eq!(3, counter.load(Ordering::Relaxed));
    //     }
    //
    //     #[test]
    //     fn it_is_only_applied_to_childs_describe() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         rdescribe("root", (), |ctx| {
    //             ctx.it("shouldn't see the before_each hook",
    //                    |counter| (0 == counter.load(Ordering::SeqCst)));
    //             ctx.describe("a sub-root", |ctx, counter| {
    //                 ctx.before_each(|counter| {
    //                     counter.fetch_add(1, Ordering::SeqCst);
    //                 });
    //                 ctx.it("should see the before_each hook",
    //                        |counter| (1 == counter.load(Ordering::SeqCst)));
    //             })
    //
    //         })
    //     }
    // }
    //
    // mod after_each {
    //     pub use super::*;
    //
    //     #[test]
    //     fn can_be_called_inside_describe() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         {
    //             let runner = describe("a root", (), |ctx| {
    //                 ctx.after_each(|counter| {
    //                     counter.fetch_add(1, Ordering::Relaxed);
    //                 });
    //                 ctx.it("first", |_| Ok(()) as Result<(),()>);
    //                 ctx.it("second", |_| Ok(()) as Result<(),()>);
    //                 ctx.it("third", |_| Ok(()) as Result<(),()>);
    //             });
    //             let _ = runner.run();
    //         }
    //
    //         assert_eq!(3, counter.load(Ordering::Relaxed));
    //     }
    //
    //     #[test]
    //     fn it_is_not_like_before() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         let report = {
    //             let runner = describe("a root", (), |ctx| {
    //                 ctx.after_each(|counter| {
    //                     counter.fetch_add(1, Ordering::SeqCst);
    //                 });
    //                 ctx.it("first",
    //                        |counter| 0 == counter.load(Ordering::SeqCst));
    //                 ctx.it("second",
    //                        |counter| 1 == counter.load(Ordering::SeqCst));
    //                 ctx.it("third",
    //                        |counter| 2 == counter.load(Ordering::SeqCst));
    //             });
    //             runner.run()
    //         };
    //
    //         assert!(report.is_ok());
    //     }
    // }
    //
    // mod before_all {
    //     pub use super::*;
    //
    //     #[test]
    //     fn can_be_called_inside_describe() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         {
    //             let runner = describe("a root", (), |ctx| {
    //                 ctx.before_all(|| {
    //                     counter.fetch_add(1, Ordering::Relaxed);
    //                 });
    //                 ctx.it("first", || Ok(()) as Result<(),()>);
    //                 ctx.it("second", || Ok(()) as Result<(),()>);
    //                 ctx.it("third", || Ok(()) as Result<(),()>);
    //             });
    //             let _ = runner.run();
    //         }
    //
    //         assert_eq!(1, counter.load(Ordering::Relaxed));
    //     }
    //
    //     #[test]
    //     fn it_is_only_applied_to_childs_describe() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         rdescribe("root", (), |ctx| {
    //             ctx.it("shouldn't see the before_all hook",
    //                    || (0 == counter.load(Ordering::SeqCst)));
    //             ctx.describe("a sub-root", (), |ctx| {
    //                 ctx.before_all(|| {
    //                     counter.fetch_add(1, Ordering::SeqCst);
    //                 });
    //                 ctx.it("should see the before_all hook",
    //                        || (1 == counter.load(Ordering::SeqCst)));
    //             })
    //
    //         })
    //     }
    // }
    //
    // mod after_all {
    //     pub use super::*;
    //
    //     #[test]
    //     fn can_be_called_inside_describe() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         {
    //             let runner = describe("a root", (), |ctx| {
    //                 ctx.after_all(|counter| {
    //                     counter.fetch_add(1, Ordering::Relaxed);
    //                 });
    //                 ctx.it("first", || Ok(()) as Result<(),()>);
    //                 ctx.it("second", || Ok(()) as Result<(),()>);
    //                 ctx.it("third", || Ok(()) as Result<(),()>);
    //             });
    //             let _ = runner.run();
    //         }
    //
    //         assert_eq!(1, counter.load(Ordering::Relaxed));
    //     }
    //
    //     #[test]
    //     fn it_is_not_like_before() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         let report = {
    //             let runner = describe("a root", counter, |ctx| {
    //                 ctx.after_all(|counter| {
    //                     counter.fetch_add(1, Ordering::SeqCst);
    //                 });
    //                 ctx.it("it",
    //                        || 0 == counter.load(Ordering::SeqCst));
    //             });
    //             runner.run()
    //         };
    //
    //         assert!(report.is_ok());
    //     }
    // }
    //
    // mod rdescribe {
    //     pub use super::*;
    //
    //     #[test]
    //     fn it_implicitely_allocate_and_run_a_runner() {
    //         use std::sync::atomic::{AtomicUsize, Ordering};
    //         let counter = &mut AtomicUsize::new(0);
    //
    //         rdescribe("allocates a runner", (), |ctx| {
    //             ctx.before_each(|| {
    //                 counter.fetch_add(1, Ordering::SeqCst);
    //             });
    //             ctx.it("should be runned (1)",
    //                    || 1 == counter.load(Ordering::SeqCst));
    //             ctx.it("should be runned (2)",
    //                    || 2 == counter.load(Ordering::SeqCst));
    //             ctx.it("should be runned (3)",
    //                    || 3 == counter.load(Ordering::SeqCst));
    //         })
    //     }
    //
    //     #[test]
    //     #[should_panic]
    //     fn it_fails_when_run_fails() {
    //         rdescribe("a failed root", (), |ctx| {
    //             ctx.it("a ok test", || Ok(()) as Result<(),()>);
    //             ctx.it("a failed test", || Err(()) as Result<(),()>);
    //             ctx.it("a ok test", || Ok(()) as Result<(),()>);
    //         })
    //     }
    // }
}
