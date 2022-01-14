use float_eq::assert_float_eq;

use good_lp::{
    constraint,
    solvers::{DualValues, SolutionWithDual, highs::{HighsProblem, HighsSolution}},
    variable, variables, Solution, Solver, SolverModel,
};

// Using a generic function here ensures the dual can be retrieved in a generic,
// solver-independent manner.
#[allow(dead_code)]
fn determine_shadow_prices_for_solver<S: Solver>(solver: S)
where
    for<'a> <<S as Solver>::Model as SolverModel>::Solution: SolutionWithDual<'a>,
{
    // Instantiate the Variables
    let mut vars = variables!();
    // Non-negative values
    let x1 = vars.add(variable().min(0));
    let x2 = vars.add(variable().min(0));

    // Define the Problem and Objective
    let objective = 3 * x1 + 2 * x2;
    let mut p = vars.maximise(objective.clone()).using(solver);

    // Subject to
    let c1 = p.add_constraint(constraint!(4 * x1 <= 100.0));
    let c2 = p.add_constraint(constraint!(7 * x2 <= 100.0));
    let c3 = p.add_constraint(constraint!(4 * x1 + 3 * x2 <= 100.0));
    let c4 = p.add_constraint(constraint!(3 * x1 + 6 * x2 <= 100.0));

    // Solve Problem
    let mut solution = p.solve().expect("Library test");

    assert_float_eq!(75.0, solution.eval(&objective), abs <= 1e-3);
    assert_float_eq!(25.0, solution.value(x1), abs <= 1e-3);
    assert_float_eq!(-0.0, solution.value(x2), abs <= 1e-3);

    let dual = solution.compute_dual();
    assert_float_eq!(0., dual.dual(c1), abs <= 1e-1);
    assert_float_eq!(0., dual.dual(c2), abs <= 1e-1);
    assert_float_eq!(0.667, dual.dual(c3), abs <= 1e-3);
    assert_float_eq!(0.0, dual.dual(c4), abs <= 1e-3);
}

#[allow(dead_code)]
fn furniture_problem_for_solver<S: Solver>(solver: S)
where
    for<'a> <<S as Solver>::Model as SolverModel>::Solution: SolutionWithDual<'a>,
{
    // Non-negative values
    let mut vars = variables!();
    let n_chairs = vars.add(variable().min(0));
    let n_tables = vars.add(variable().min(0));

    // Objective and Problem
    let objective = 70 * n_chairs + 50 * n_tables;
    let mut p = vars.maximise(objective.clone()).using(solver);

    // Subject to
    let c1 = p.add_constraint(constraint!(4 * n_chairs + 3 * n_tables <= 240.0));
    let c2 = p.add_constraint(constraint!(2 * n_chairs + n_tables <= 100.0));

    // Solve
    let mut solution = p.solve().expect("Library test");
    assert_float_eq!(4100.0, solution.eval(&objective), abs <= 1e-10);
    assert_float_eq!(30.0, solution.value(n_chairs), abs <= 1e-1);
    assert_float_eq!(40.0, solution.value(n_tables), abs <= 1e-1);

    let dual = solution.compute_dual();
    assert_float_eq!(15.0, dual.dual(c1), abs <= 1e-1);
    assert_float_eq!(5.0, dual.dual(c2), abs <= 1e-1);
}

#[allow(dead_code)]
fn reduced_cost_problem_for_solver<S: Solver>(solver: S)
where
    for<'a> <<S as Solver>::Model as SolverModel>::Solution: SolutionWithDual<'a>,
{
    // Non-negative values
    let mut vars = variables!();
    let s1 = vars.add(variable().min(0));
    let s2 = vars.add(variable().min(0));
    let d1 = vars.add(variable().min(0));
    let d2 = vars.add(variable().min(0));

    let s1_d1 = vars.add(variable().min(0));
    let s1_d2= vars.add(variable().min(0));
    let s2_d2 = vars.add(variable().min(0));

    // Objective and Problem
    let objective = 10 * s1 + 20 * s2 + s1_d2 * 5;
    let mut p : HighsProblem = vars.minimise(objective.clone()).using(good_lp::highs);

    // Subject to
    let c_s1 = p.add_constraint(constraint!(s1 <= 100.0));
    let c_s2 = p.add_constraint(constraint!(s2 <= 100.0));
    let c_d2 = p.add_constraint(constraint!(d2 >= 90.0));
    let c_d1 = p.add_constraint(constraint!(d1 >= 90.0));

    // let c_s_d2 = p.add_constraint(constraint!(s1 + s2 == d2));
    // let c_s1_d1 = p.add_constraint(constraint!(s1 == d1));

    let s1_out = p.add_constraint(constraint!(s1 == s1_d1 + s1_d2));
    let s2_out = p.add_constraint(constraint!(s2 == s2_d2));

    //let s1_out_forced = p.add_constraint(constraint!(s1 == 100));

    let d1_in = p.add_constraint(constraint!(d1 == s1_d1));
    let d2_in = p.add_constraint(constraint!(d2 == s1_d2 + s2_d2));

    // Solve
    let mut solution : HighsSolution = p.solve().expect("Library test");
    assert_float_eq!(2650.0, solution.eval(&objective), abs <= 1e-10);

    assert_float_eq!(100.0, solution.value(s1), abs <= 1e-1);
    assert_float_eq!(80.0, solution.value(s2), abs <= 1e-1);
    assert_float_eq!(90.0, solution.value(s1_d1), abs <= 1e-1);
    assert_float_eq!(10.0, solution.value(s1_d2), abs <= 1e-1);
    assert_float_eq!(80.0, solution.value(s2_d2), abs <= 1e-1);

    let dual = solution.compute_dual();
    assert_float_eq!(-15.0, dual.dual(d1_in.clone()), abs <= 1e-1);
    assert_float_eq!(-20.0, dual.dual(d2_in.clone()), abs <= 1e-1);

    println!("{:?}",  dual.dual_columns());
    println!("{:?}",  dual.dual_rows());

    println!("{:?}", solution.into_inner().columns())
}

macro_rules! dual_test {
    ($solver_feature:literal, $solver:expr) => {
        #[test]
        #[cfg(feature = $solver_feature)]
        fn determine_shadow_prices() {
            determine_shadow_prices_for_solver($solver)
        }

        #[test]
        #[cfg(feature = $solver_feature)]
        fn furniture_problem() {
            furniture_problem_for_solver($solver)
        }

        #[test]
        #[cfg(feature = $solver_feature)]
        fn reduced_cost_problem() {
            reduced_cost_problem_for_solver($solver)
        }
    };
}

dual_test!("highs", good_lp::highs);
