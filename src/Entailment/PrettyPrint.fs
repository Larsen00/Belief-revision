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

// Pretty print a sentence (not CNF) with correct parenthesisation
let private sentencePrec = function
    | Term _ -> 6 | Not _ -> 5 | And _ -> 4 | Or _ -> 3 | Implies _ -> 2 | Biconditional _ -> 1

let rec prettyPrintSentence (s: sentence) : string =
    match s with
    | Term t -> t
    | Not inner ->
        if sentencePrec inner < 5 then sprintf "¬(%s)" (prettyPrintSentence inner)
        else sprintf "¬%s" (prettyPrintSentence inner)
    | And (a, b) ->
        let wrap x = if sentencePrec x < 4 then sprintf "(%s)" (prettyPrintSentence x) else prettyPrintSentence x
        sprintf "%s ∧ %s" (wrap a) (wrap b)
    | Or (a, b) ->
        let wrap x = if sentencePrec x < 3 then sprintf "(%s)" (prettyPrintSentence x) else prettyPrintSentence x
        sprintf "%s ∨ %s" (wrap a) (wrap b)
    | Implies (a, b) ->
        let wrapL x = if sentencePrec x <= 2 then sprintf "(%s)" (prettyPrintSentence x) else prettyPrintSentence x
        sprintf "%s → %s" (wrapL a) (prettyPrintSentence b)
    | Biconditional (a, b) ->
        sprintf "%s ↔ %s" (prettyPrintSentence a) (prettyPrintSentence b)
