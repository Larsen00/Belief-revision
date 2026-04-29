module Generators

open FsCheck
open Entailment

let private maxDepth = 3
let private availableTerms = ["p"; "q"; "r"; "s"; "t"]



// Can generate a term from the available terms ie. "p", "q", "r", "s", "t"
let private termGen =
    Gen.map Term (Gen.elements availableTerms)

// Can generate a random sentence with a maximum tree depth of 3
let rec sentenceGeneratorHelper depth =
    if depth >= maxDepth then 
        termGen
    else
        Gen.oneof [
            termGen
            Gen.map2 (fun s1 s2 -> And (s1, s2)) (sentenceGeneratorHelper (depth + 1)) (sentenceGeneratorHelper (depth + 1))
            Gen.map2 (fun s1 s2 -> Or (s1, s2)) (sentenceGeneratorHelper (depth + 1)) (sentenceGeneratorHelper (depth + 1))
            Gen.map2 (fun s1 s2 -> Implies (s1, s2)) (sentenceGeneratorHelper (depth + 1)) (sentenceGeneratorHelper (depth + 1))
            Gen.map (fun s -> Not s) (sentenceGeneratorHelper (depth + 1))
            Gen.map2 (fun s1 s2 -> Biconditional (s1, s2)) (sentenceGeneratorHelper (depth + 1)) (sentenceGeneratorHelper (depth + 1))
        ]


let sentenceGen =
    sentenceGeneratorHelper 0

let beliefBaseGen : Gen<bbase> =
    Gen.oneof [
        Gen.listOfLength 1 sentenceGen
        Gen.listOfLength 2 sentenceGen
        Gen.listOfLength 3 sentenceGen
        // Gen.listOfLength 4 sentenceGen
    ]

// Generates a (beliefBase, phi) pair where beliefBase |= phi is guaranteed.
// phi = And(kb1, kb2) where both kb1 and kb2 are members of the belief base,
// so no single element needs to entail phi individually.
let entailingGen : Gen<bbase * sentence> =
    gen {
        let! kb1 = sentenceGen
        let! kb2 = sentenceGen
        let phi = And (kb1, kb2)
        let! extra = Gen.oneof [
            Gen.listOfLength 0 sentenceGen
            Gen.listOfLength 1 sentenceGen
        ]
        let b = kb1 :: kb2 :: extra
        return (b, phi)
    }

// Generates a (beliefBase, phi) pair where beliefBase |≠ phi is guaranteed.
// Filters out cases where B entails phi, so vacuity's interesting branch is always exercised.
let nonEntailingGen : Gen<bbase * sentence> =
    Gen.zip beliefBaseGen sentenceGen
    |> Gen.where (fun (b, phi) -> not (b |= phi))

type BeliefBaseGen =
    static member Sentence() : Arbitrary<sentence> =
        Arb.fromGen sentenceGen

    static member BBase() : Arbitrary<bbase> =
        Arb.fromGen beliefBaseGen