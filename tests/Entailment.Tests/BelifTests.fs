module BelifTests

open Xunit
open Entailment

// All tests work directly with Knowledge throughout.
// Assertions use rankof and isBelieved rather than converting back to bbase.

// -- rank ordering --------------------------------------------------------------

[<Fact>]
let ``p has lower rank than p?q`` () =
    let k = beliefBaseToKnowledge [ Term "p"; Or (Term "p", Term "q") ]
    Assert.True(Entrenchment.rankof k (Term "p") < Entrenchment.rankof k (Or (Term "p", Term "q")))

[<Fact>]
let ``p?q has higher rank than p`` () =
    let k = beliefBaseToKnowledge [ Term "p"; Or (Term "p", Term "q") ]
    Assert.True(Entrenchment.rankof k (Or (Term "p", Term "q")) > Entrenchment.rankof k (Term "p"))

[<Fact>]
let ``p?q and q?p have equal rank (logically equivalent)`` () =
    let k = beliefBaseToKnowledge [ And (Term "p", Term "q"); And (Term "q", Term "p") ]
    Assert.Equal(
        Entrenchment.rankof k (And (Term "p", Term "q")),
        Entrenchment.rankof k (And (Term "q", Term "p")))

[<Fact>]
let ``tautology gets maximal rank`` () =
    let taut = Or (Term "p", Not (Term "p"))
    let k = beliefBaseToKnowledge [ Term "p"; taut ]
    Assert.Equal(Entrenchment.maxEntrenchment, Entrenchment.rankof k taut)

[<Fact>]
let ``non-tautology gets rank below maximal`` () =
    let k = beliefBaseToKnowledge [ Term "p" ]
    Assert.True(Entrenchment.rankof k (Term "p") < Entrenchment.maxEntrenchment)

// -- contraction ----------------------------------------------------------------

[<Fact>]
let ``contraction by p removes belief in p`` () =
    let k = beliefBaseToKnowledge [ Term "p"; Term "q" ]
    let k' = Entrenchment.contraction k (Term "p")
    Assert.False(isBelieved k' (Term "p"))

[<Fact>]
let ``contraction by p keeps more entrenched q`` () =
    let k = beliefBaseToKnowledge [ Term "p"; Term "q" ]
    let k' = Entrenchment.contraction k (Term "p")
    Assert.True(isBelieved k' (Term "q"))

[<Fact>]
let ``contraction by tautology is a no-op`` () =
    let taut = Or (Term "p", Not (Term "p"))
    let k = beliefBaseToKnowledge [ Term "p"; Term "q" ]
    let k' = Entrenchment.contraction k taut
    Assert.True(isBelieved k' (Term "p"))
    Assert.True(isBelieved k' (Term "q"))

// -- expansion ------------------------------------------------------------------

[<Fact>]
let ``expansion adds a new sentence to knowledge`` () =
    let k = beliefBaseToKnowledge [ Term "p" ]
    let k' = Entrenchment.expansion k (Term "q")
    Assert.True(isBelieved k' (Term "p"))
    Assert.True(isBelieved k' (Term "q"))

[<Fact>]
let ``expansion does not duplicate an existing sentence`` () =
    let k = beliefBaseToKnowledge [ Term "p" ]
    let k' = Entrenchment.expansion k (Term "p")
    let count = List.length (List.filter (fun rs -> rs.Sentence = Term "p") k')
    Assert.Equal(1, count)

// -- revision -------------------------------------------------------------------

[<Fact>]
let ``revision adds the revising sentence to knowledge`` () =
    let k = beliefBaseToKnowledge [ Term "p"; Term "q" ]
    let k' = Entrenchment.revision k (Not (Term "p"))
    Assert.True(isBelieved k' (Not (Term "p")))

[<Fact>]
let ``revision by not p removes belief in p`` () =
    let k = beliefBaseToKnowledge [ Term "p"; Term "q" ]
    let k' = Entrenchment.revision k (Not (Term "p"))
    Assert.False(isBelieved k' (Term "p"))

[<Fact>]
let ``revision by not p keeps unrelated belief q`` () =
    let k = beliefBaseToKnowledge [ Term "p"; Term "q" ]
    let k' = Entrenchment.revision k (Not (Term "p"))
    Assert.True(isBelieved k' (Term "q"))
