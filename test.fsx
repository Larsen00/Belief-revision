/// TEST FILE - To test the Entailment module. 

#r "src/Entailment/bin/Debug/net10.0/Entailment.dll"

open Entailment

let a = [
    Implies (Term "q", Term "p")
    Biconditional (Term "p", Term "q")
    Implies (Term "p", Term "q")
    And (Term "p", Term "q")
    Or (Term "p", Term "q")
]

printfn "Belief base: %A" <| sortBeliefBase a

let b = [
    Term "p"
    Biconditional (Term "p", Term "q")
    Not (Term "r")
]


printfn "Belief base: %A" <| contraction b (Not (Term "q"))
printfn "Belief base: %A" <| contraction b (Implies (Term "p", Term "q"))


let p = Term "p"
let q = Or (Term "p", Term "q") 

printfn "Entailment check %A" <| checkEntailment ([p], q)
printfn "compare 1: %A" <| (p <=. q)
printfn "compare: %A" <| compareEntries p q
printfn "compareint: %A" <| compare 0 1