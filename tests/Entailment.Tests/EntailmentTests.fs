module EntailmentTests

open Xunit
open Entailment

// ── helpers ───────────────────────────────────────────────────────────────────

let entails kb alpha = checkEntailment (kb, alpha)
let doesNotEntail kb alpha = not (checkEntailment (kb, alpha))

// ── modus ponens ──────────────────────────────────────────────────────────────

[<Fact>]
let ``KB {p, p→q} entails q`` () =
    let kb = [ Term "p"; Implies (Term "p", Term "q") ]
    Assert.True(entails kb (Term "q"))

[<Fact>]
let ``KB {p} does not entail q`` () =
    let kb = [ Term "p" ]
    Assert.True(doesNotEntail kb (Term "q"))

// ── modus tollens ─────────────────────────────────────────────────────────────

[<Fact>]
let ``KB {p→q, ¬q} entails ¬p`` () =
    let kb = [ Implies (Term "p", Term "q"); Not (Term "q") ]
    Assert.True(entails kb (Not (Term "p")))

// ── transitivity ─────────────────────────────────────────────────────────────

[<Fact>]
let ``KB {p→q, q→r, p} entails r`` () =
    let kb = [ Implies (Term "p", Term "q"); Implies (Term "q", Term "r"); Term "p" ]
    Assert.True(entails kb (Term "r"))

[<Fact>]
let ``KB {p→q, q→r} does not entail r without p`` () =
    let kb = [ Implies (Term "p", Term "q"); Implies (Term "q", Term "r") ]
    Assert.True(doesNotEntail kb (Term "r"))

// ── tautologies ───────────────────────────────────────────────────────────────

[<Fact>]
let ``Empty KB entails tautology p∨¬p`` () =
    Assert.True(entails [] (Or (Term "p", Not (Term "p"))))

[<Fact>]
let ``Empty KB does not entail plain term p`` () =
    Assert.True(doesNotEntail [] (Term "p"))

// ── conjunction ───────────────────────────────────────────────────────────────

[<Fact>]
let ``KB {p, q} entails p∧q`` () =
    let kb = [ Term "p"; Term "q" ]
    Assert.True(entails kb (And (Term "p", Term "q")))

[<Fact>]
let ``KB {p∧q} entails p`` () =
    Assert.True(entails [ And (Term "p", Term "q") ] (Term "p"))

// ── biconditional ─────────────────────────────────────────────────────────────

[<Fact>]
let ``KB {p↔q, p} entails q`` () =
    let kb = [ Biconditional (Term "p", Term "q"); Term "p" ]
    Assert.True(entails kb (Term "q"))

[<Fact>]
let ``KB {p↔q, ¬p} entails ¬q`` () =
    let kb = [ Biconditional (Term "p", Term "q"); Not (Term "p") ]
    Assert.True(entails kb (Not (Term "q")))
