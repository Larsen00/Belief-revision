[<AutoOpen>]
module Entailment.ToCnf

/// Convert a sentence to CNF

// STEP 1: Convert input sentence to CNF by eliminating implications and biconditionals
let rec elimination (s:sentence) : cnf =
    match s with
    | Biconditional (a, b) -> Conjunction (elimination (Implies (a, b)), elimination (Implies (b, a))) // A <-> B is equivalent to (A -> B) ∧ (B -> A)
    | Implies (a, b) -> Disjunction (Negation (elimination a), elimination b) // A -> B is equivalent to ¬A ∨ B
    | And (s1, s2) -> Conjunction (elimination s1, elimination s2)
    | Or (s1, s2) -> Disjunction (elimination s1, elimination s2)
    | Not s -> Negation (elimination s)
    | Term t -> Literal t

// STEP 2: Move negations inward using De Morgan's laws
let rec moveNegations (c:cnf) : cnf =
    match c with
    | Negation (Negation c) -> moveNegations c
    | Negation (Conjunction (c1, c2)) -> Disjunction (moveNegations (Negation c1), moveNegations (Negation c2))
    | Negation (Disjunction (c1, c2)) -> Conjunction (moveNegations (Negation c1), moveNegations (Negation c2))
    | Negation (Literal l) -> Negation (Literal l)

    | Conjunction (c1, c2) -> Conjunction (moveNegations c1, moveNegations c2)
    | Disjunction (c1, c2) -> Disjunction (moveNegations c1, moveNegations c2)
    | Literal l -> Literal l


// Step 3: Distribute disjunctions over conjunctions to get CNF
let rec distribute c = 
    match c with
    | Disjunction (Conjunction (c2, c3), c1) 
    | Disjunction (c1, Conjunction (c2, c3)) -> Conjunction (distribute (Disjunction (c1, c2)), distribute (Disjunction (c1, c3)))
    | Disjunction (c1, c2) ->
        // Recurse first; if either child became a Conjunction, distribute again
        let result = Disjunction (distribute c1, distribute c2)
        match result with
        | Disjunction (Conjunction _, _) | Disjunction (_, Conjunction _) -> distribute result
        | _ -> result
    | Conjunction (c1, c2) -> Conjunction (distribute c1, distribute c2)
    | Negation c -> Negation (distribute c)
    | Literal l -> Literal l


// Combine all steps into a single function
let toCNF (s:sentence) : cnf =
    s |> elimination |> moveNegations |> distribute
