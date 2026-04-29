/// TEST FILE - To test the Entailment module. 

#r "src/Entailment/bin/Debug/net10.0/Entailment.dll"

open Entailment

let beliefBase =
    [ Biconditional (
            Biconditional (Or (Term "q", Term "p"), Term "t"),
            And (Implies (Term "q", Term "r"), Term "r"));
        Or (
            Not (Or (Term "r", Term "q")),
            Or (Or (Term "r", Term "r"), Implies (Term "r", Term "p")));
        Implies (
            Not (Term "t"),
            Biconditional (Or (Term "q", Term "r"), Not (Term "p"))) ]

let phi =
    Biconditional (
        Biconditional (
            Implies (Term "s", Term "s"),
            Biconditional (Term "r", Term "p")),
        Not (Or (Term "p", Term "q")))

// valcuity test

match beliefBase |= phi with
| true -> printfn "Phi is entailed by the belief base."
| false ->
    let contracted = Entrenchment.contraction (beliefBaseToKnowledge beliefBase) phi |> KnowledgeToBeliefBase
    printfn "Contracted belief base: %A" contracted
    printfn "Contracted belief base equals original: %b" (contracted = beliefBase)



// let b =       [Biconditional
//          (Biconditional (Or (Term "r", Term "q"), Term "p"), Not (Term "r"));
//        Biconditional
//          (And (Term "t", And (Term "p", Term "s")),
//           Biconditional
//             (Biconditional (Term "r", Term "r"), Biconditional (Term "q", Term "t")));
//        And (Or (Not (Term "t"), Or (Term "p", Term "q")), Term "s")]
       
// let k1 = beliefBaseToKnowledge b
// let b2 = KnowledgeToBeliefBase k1
// let k2 = beliefBaseToKnowledge b2
// printfn "Original belief base: \n%A\n" b
// k1 |> prettyPrintKnowledge |> printfn "%s"
// printfn "Belief base from knowledge: \n%A\n" b2
// k2 |> prettyPrintKnowledge |> printfn "%s"