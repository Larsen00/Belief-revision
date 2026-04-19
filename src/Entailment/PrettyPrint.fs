[<AutoOpen>]
module Entailment.PrettyPrint

/// Helper functions for pretty printing CNF and sets of literals ////
let rec prittyPrint (c:cnf) : string =
    match c with
    | Conjunction (c1, c2) -> sprintf "(%s ∧ %s)" (prittyPrint c1) (prittyPrint c2)
    | Disjunction (c1, c2) -> sprintf "(%s ∨ %s)" (prittyPrint c1) (prittyPrint c2)
    | Negation c -> sprintf "¬%s" (prittyPrint c)
    | Literal l -> l

let prittyPrintDisjunctionSet ds =
    ds
    |> Set.map (function
        | Pos l -> l
        | Neg l -> sprintf "¬%s" l)
    |> String.concat " ∨ "

let rec prittyPrintConjunctionSet (cs:ConjunctionSet) : string =
    cs
    |> Set.map prittyPrintDisjunctionSet
    |> String.concat ", " |> sprintf "{%s}"

let fastPrint x =
    printfn "fast: %A" x
    x
