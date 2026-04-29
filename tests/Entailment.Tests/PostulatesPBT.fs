module PostulatesPBT

open FsCheck
open Entailment
open Generators

let pbtConfig maxTests =
    let progressBar n =
        let current = min maxTests (n + 1)
        let width = 20
        let filled = current * width / maxTests
        let empty = width - filled

        let bar =
            String.replicate filled "#" +
            String.replicate empty "-"

        sprintf "\r[%s] %d/%d" bar current maxTests

    { Config.QuickThrowOnFailure with
        MaxTest = maxTests
        Arbitrary = [ typeof<BeliefBaseGen> ]
        Every = fun n _ -> progressBar n }


// Sucess: If ϕ /∈ Cn(∅), then ϕ /∈ Cn(B ÷ ϕ) 
// Same as: If Ø |≠ ϕ, then B ÷ ϕ |≠ ϕ
let success (B: bbase) (phi: sentence) =
    match [] |= phi with
    | true -> None
    | false -> 
        let p = KnowledgeToBeliefBase (Entrenchment.contraction (beliefBaseToKnowledge B) phi)
        Some (not (p |= phi))

let successPBT (b: bbase) (phi: sentence) =
    match success b phi with
    | Some result -> Prop.classify true "non-tautology" result
    | None -> Prop.classify true "tautology" true
    
[<Xunit.Fact>]  
let ``Success postulate`` () =
    Check.One(
        pbtConfig 10,
        successPBT
    )

// Inclusion: B ÷ ϕ ⊆ B
let inclusion (B: bbase) (phi: sentence) =
    let contracted = Entrenchment.contraction (beliefBaseToKnowledge B) phi |> KnowledgeToBeliefBase
    List.forall (fun p -> List.contains p B) contracted

[<Xunit.Fact>]
let ``Inclusion postulate`` () =
    Check.One(
        pbtConfig 10,
        inclusion
    )


// Vacuity: If ϕ /∈ Cn(B), then B ÷ ϕ = B
// Same as: If B |≠ ϕ, then B
let vacuity (B: bbase) (phi: sentence) =
    match B |= phi with
    | true -> None
    | false -> 
        let contracted =
            Entrenchment.contraction (beliefBaseToKnowledge B) phi
            |> KnowledgeToBeliefBase

        // Compare as sets: contraction should not remove any element when B |≠ phi
        let sameElements =
            List.length contracted = List.length B &&
            List.forall (fun s -> List.contains s contracted) B

        Some sameElements

let vacuityPBT (b: bbase) (phi: sentence) =
    match vacuity b phi with
    | Some result -> Prop.classify true "non-entailed" result
    | None -> Prop.classify true "entailed" true

// We use a different generator for this test, that has the property B |≠ phi
// so the vacuity branch (contracted = B) is always exercised.
[<Xunit.Fact>]
let ``Vacuity postulate`` () =
    let prop (b, phi) = vacuityPBT b phi
    Check.One(
        pbtConfig 15,
        Prop.forAll (Arb.fromGen nonEntailingGen) prop
    )