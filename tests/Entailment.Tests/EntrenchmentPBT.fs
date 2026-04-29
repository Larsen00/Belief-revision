module EntrenchmentPBT

open FsCheck
open Entailment
open Generators


// Ensure that BB to knowlegde (k1) to BB to knowledge to BB (k2) then k1 and k2 are the same 

let beliefBaseToKnowledgeToBeliefBase (B: bbase) =
    let k1 = beliefBaseToKnowledge B
    let b2 = KnowledgeToBeliefBase k1
    let k2 = beliefBaseToKnowledge b2
    k1 = k2

[<Xunit.Fact>]
let ``BeliefBase to Knowledge to BeliefBase`` () =
    Check.One(
        { Config.QuickThrowOnFailure with
            MaxTest = 15
            Arbitrary = [ typeof<BeliefBaseGen> ] },
        beliefBaseToKnowledgeToBeliefBase
    )


