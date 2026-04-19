module Tests

open Xunit
open Entailment

// ── helpers ─────────────────────────────────────────────────────────────────

let isSatisfiable s   = toCNF s |> cnfToConjunctionSet |> reduceConjunctionSet |> Option.isSome
let isUnsatisfiable s = toCNF s |> cnfToConjunctionSet |> reduceConjunctionSet |> Option.isNone

// ── toCnf / structure tests ──────────────────────────────────────────────────

[<Fact>]
let ``Implication is eliminated correctly`` () =
    // A -> B  ≡  ¬A ∨ B
    let result = toCNF (Implies (Term "a", Term "b"))
    Assert.Equal(Disjunction (Negation (Literal "a"), Literal "b"), result)

[<Fact>]
let ``Double negation is removed`` () =
    let result = toCNF (Not (Not (Term "a")))
    Assert.Equal(Literal "a", result)

// ── satisfiability tests ─────────────────────────────────────────────────────

[<Fact>]
let ``Simple tautology p ∨ ¬p is satisfiable`` () =
    Assert.True(isSatisfiable (Or (Term "p", Not (Term "p"))))

[<Fact>]
let ``Contradiction p ∧ ¬p is unsatisfiable`` () =
    Assert.True(isUnsatisfiable (And (Term "p", Not (Term "p"))))

[<Fact>]
let ``Single term is satisfiable`` () =
    Assert.True(isSatisfiable (Term "a"))

[<Fact>]
let ``Biconditional r ↔ (p ∨ s) is satisfiable`` () =
    Assert.True(isSatisfiable (Biconditional (Term "r", Or (Term "p", Term "s"))))

[<Fact>]
let ``Modus ponens: {p, p→q, ¬q} is unsatisfiable`` () =
    // p ∧ (p→q) ∧ ¬q  should be a contradiction
    let kb = And (Term "p", And (Implies (Term "p", Term "q"), Not (Term "q")))
    Assert.True(isUnsatisfiable kb)

[<Fact>]
let ``(p→q) ∧ (q→r) ∧ p ∧ ¬r is unsatisfiable`` () =
    let s =
        And (
            Implies (Term "p", Term "q"),
            And (
                Implies (Term "q", Term "r"),
                And (Term "p", Not (Term "r"))))
    Assert.True(isUnsatisfiable s)

[<Fact>]
let ``(p→q) ∧ p is satisfiable`` () =
    Assert.True(isSatisfiable (And (Implies (Term "p", Term "q"), Term "p")))

