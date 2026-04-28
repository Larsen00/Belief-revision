module BelifTests

open Xunit
open Entailment

// ── entrenchment operators ────────────────────────────────────────────────────

[<Fact>]
let ``p <=. p∨q (p entails p∨q)`` () =
    Assert.True(Term "p" <=. Or (Term "p", Term "q"))

[<Fact>]
let ``p∨q does not <=. p (p∨q does not entail p)`` () =
    Assert.False(Or (Term "p", Term "q") <=. Term "p")

[<Fact>]
let ``p <. p∨q (p is strictly less entrenched than p∨q)`` () =
    Assert.True(Term "p" <. Or (Term "p", Term "q"))

[<Fact>]
let ``p∨q is not <. p`` () =
    Assert.False(Or (Term "p", Term "q") <. Term "p")

[<Fact>]
let ``p is not <. p (not strictly less than itself)`` () =
    Assert.False(Term "p" <. Term "p")

// ── compareEntries ────────────────────────────────────────────────────────────

[<Fact>]
let ``compareEntries: p less entrenched than p∨q returns -1`` () =
    Assert.Equal(-1, compareEntries (Term "p") (Or (Term "p", Term "q")))

[<Fact>]
let ``compareEntries: p∨q more entrenched than p returns 1`` () =
    Assert.Equal(1, compareEntries (Or (Term "p", Term "q")) (Term "p"))

[<Fact>]
let ``compareEntries: equivalent sentences return 0`` () =
    // p∧q ↔ q∧p: both entail each other
    Assert.Equal(0, compareEntries (And (Term "p", Term "q")) (And (Term "q", Term "p")))

[<Fact>]
let ``compareEntries: unrelated sentences return 0`` () =
    // Neither p nor r entails the other
    Assert.Equal(0, compareEntries (Term "p") (Term "r"))

// ── sortBeliefBase ────────────────────────────────────────────────────────────

[<Fact>]
let ``sortBeliefBase orders from least to most entrenched`` () =
    // p <=. p∨q so p should come before p∨q
    let kb = [ Or (Term "p", Term "q"); Term "p" ]
    let sorted = sortBeliefBase kb
    Assert.Equal<sentence list>([ Term "p"; Or (Term "p", Term "q") ], sorted)

[<Fact>]
let ``sortBeliefBase: tautology is most entrenched`` () =
    // p∨¬p is a tautology, entailed by everything but entails nothing specific
    // everything entails a tautology, so tautology is least-surprising → most entrenched
    let taut = Or (Term "p", Not (Term "p"))
    let kb = [ taut; Term "p" ]
    let sorted = sortBeliefBase kb
    // p <=. taut (p entails taut), taut does not entail p → p comes first
    Assert.Equal<sentence list>([ Term "p"; taut ], sorted)

// ── contraction ───────────────────────────────────────────────────────────────

[<Fact>]
let ``contraction by p removes p itself from belief base`` () =
    let kb = [ Term "p"; Term "q" ]
    let result = contraction kb (Term "p")
    Assert.DoesNotContain(Term "p", result)

[<Fact>]
let ``contraction keeps sentences more entrenched than contracted sentence`` () =
    // q∨p is more general (less entrenched) than q, but q is more entrenched than p
    // contracting by p: q survives because p <. p∨q
    let kb = [ Term "p"; Term "q" ]
    let result = contraction kb (Term "p")
    Assert.Contains(Term "q", result)

[<Fact>]
let ``contraction by tautology leaves belief base unchanged (maximality)`` () =
    let taut = Or (Term "p", Not (Term "p"))
    let kb = [ Term "p"; Term "q" ]
    // Nothing is less entrenched than a tautology, so maximality holds → k unchanged
    let result = contraction kb taut
    Assert.Equal<sentence list>(kb, result)

// ── expansion ─────────────────────────────────────────────────────────────────

[<Fact>]
let ``expansion adds a new sentence`` () =
    let kb = [ Term "p" ]
    let result = expansion kb (Term "q")
    Assert.Contains(Term "p", result)
    Assert.Contains(Term "q", result)

[<Fact>]
let ``expansion does not duplicate an existing sentence`` () =
    let kb = [ Term "p" ]
    let result = expansion kb (Term "p")
    Assert.Equal<sentence list>([ Term "p" ], result)

// ── revision ──────────────────────────────────────────────────────────────────

[<Fact>]
let ``revision adds the revising sentence`` () =
    let kb = [ Term "p"; Term "q" ]
    let result = revision kb (Not (Term "p"))
    Assert.Contains(Not (Term "p"), result)

[<Fact>]
let ``revision by not p removes p from belief base`` () =
    let kb = [ Term "p"; Term "q" ]
    let result = revision kb (Not (Term "p"))
    Assert.DoesNotContain(Term "p", result)

[<Fact>]
let ``revision by not p keeps unrelated beliefs`` () =
    let kb = [ Term "p"; Term "q" ]
    let result = revision kb (Not (Term "p"))
    Assert.Contains(Term "q", result)
