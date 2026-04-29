module PostulatesRegressionTests

open Xunit
open Entailment
open PostulatesPBT

[<Fact>]
let ``Success regression: FsCheck counterexample 1`` () =
    let beliefBase =
        [ Not (Term "s")
          Not (Not (Term "s"))
          Or (
              Implies (Implies (Term "t", Term "q"), Term "p"),
              Implies (Implies (Term "q", Term "t"), Implies (Term "t", Term "p"))) ]

    let phi =
        And (Term "q", Implies (Term "q", Implies (Term "t", Term "q")))

    Assert.True(
        match success beliefBase phi with
        | Some result -> result
        | None -> true)

[<Fact>]
let ``Success regression: FsCheck counterexample 2`` () =
    let beliefBase =
        [ And (
              Biconditional (Not (Term "q"), Not (Term "s")),
              Implies (Biconditional (Term "t", Term "q"), Term "t"))

          Biconditional (
              Or (Or (Term "q", Term "q"), Or (Term "q", Term "q")),
              Implies (Biconditional (Term "p", Term "q"), Not (Term "q")))

          Not (Term "q") ]

    let phi =
        And (
            And (Term "t", And (Term "s", Term "t")),
            Implies (Or (Term "p", Term "s"), And (Term "p", Term "t")))

    Assert.True(
        match success beliefBase phi with
        | Some result -> result
        | None -> true)

[<Fact>]
let ``Inclusion regression: FsCheck counterexample 1`` () =
    let beliefBase =
        [ Or (
              Or (Implies (Term "t", Term "r"), And (Term "r", Term "t")),
              Implies (Not (Term "r"), Biconditional (Term "p", Term "t")))
          Biconditional (Term "r", Implies (Term "r", Implies (Term "p", Term "s")))
          Biconditional (Implies (Term "p", Or (Term "s", Term "p")), Not (Term "p")) ]

    let phi =
        Implies (And (Not (Term "r"), Or (Term "t", Term "r")), Not (And (Term "q", Term "p")))

    Assert.True(inclusion beliefBase phi)

[<Fact>]
let ``Vacuity regression: FsCheck counterexample 1`` () =
    let beliefBase =
        [ Term "q"
          Or (
              Implies (Or (Term "p", Term "q"), Or (Term "p", Term "p")),
              Biconditional (Implies (Term "s", Term "p"), Or (Term "r", Term "r"))) ]

    let phi =
        And (
            Not (Not (Term "t")),
            Implies (Biconditional (Term "r", Term "s"), Biconditional (Term "t", Term "s")))

    Assert.True(
        match vacuity beliefBase phi with
        | Some result -> result
        | None -> true)

[<Fact>]
let ``Vacuity regression: FsCheck counterexample 2`` () =
    let beliefBase =
        [ Implies (Term "t", Or (Not (Term "s"), Not (Term "q")))
          Not (Term "r") ]

    let phi =
        Implies (Term "t", Or (Term "q", Biconditional (Term "r", Term "s")))

    Assert.True(
        match vacuity beliefBase phi with
        | Some result -> result
        | None -> true)

[<Fact>]
let ``Vacuity regression: FsCheck counterexample 3`` () =
    let beliefBase =
        [ Biconditional (
              Biconditional (Or (Term "q", Term "p"), Term "t"),
              And (Implies (Term "q", Term "r"), Term "r"))
          Or (
              Not (Or (Term "r", Term "q")),
              Or (Or (Term "r", Term "r"), Implies (Term "r", Term "p")))
          Implies (
              Not (Term "t"),
              Biconditional (Or (Term "q", Term "r"), Not (Term "p"))) ]

    let phi =
        Biconditional (
            Biconditional (
                Implies (Term "s", Term "s"),
                Biconditional (Term "r", Term "p")),
            Not (Or (Term "p", Term "q")))

    Assert.True(
        match vacuity beliefBase phi with
        | Some result -> result
        | None -> true)