
type sentence =
    | And of sentence * sentence
    | Or of sentence * sentence
    | Implies of sentence * sentence
    | Not of sentence
    | Biconditional of sentence * sentence
    | Term of string


type cnf =
    | Conjunction of cnf * cnf
    | Disjunction of cnf * cnf
    | Negation of cnf
    | Literal of string


// Mabye we can use a diffrent type than cnf??
type clause = Set<cnf>


// Helper functions
let rec prittyPrint (c:cnf) : string =
    match c with
    | Conjunction (c1, c2) -> sprintf "(%s ∧ %s)" (prittyPrint c1) (prittyPrint c2)
    | Disjunction (c1, c2) -> sprintf "(%s ∨ %s)" (prittyPrint c1) (prittyPrint c2)
    | Negation c -> sprintf "¬%s" (prittyPrint c)
    | Literal l -> l

let rec prittyPrintClause (cl:clause) : string =
    cl
    |> Set.map prittyPrint
    |> Set.toList
    |> String.concat ", "


/// Convert a sentence to CNF


// STEP 1: Convert input sentence to CNF by eliminating implications and biconditionals
let rec elimination (s:sentence) : cnf =
    match s with
    | Biconditional (s1, s2) -> Conjunction (elimination (Implies (s1, s2)), elimination (Implies (s2, s1)))
    | Implies (s1, s2) -> Disjunction (Negation (elimination s1), elimination s2)
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
    | Disjunction (c1, c2) -> Disjunction (distribute c1, distribute c2)
    | Conjunction (c1, c2) -> Conjunction (distribute c1, distribute c2)
    | Negation c -> Negation (distribute c)
    | Literal l -> Literal l


// Combine all steps into a single function
let toCNF (s:sentence) : cnf =
    s |> elimination |> moveNegations |> distribute


// Example form slides
Biconditional (Term "r", Or (Term "p", Term "s")) |> toCNF |> prittyPrint |> printfn "%s"



// Resolution
let rec cnfToClause c : clause = 
    match c with
    | Conjunction (c1, c2) -> Set.union (cnfToClause c1) (cnfToClause c2)
    | x -> Set.singleton x


// test
Biconditional (Term "r", Or (Term "p", Term "s")) |> toCNF |> cnfToClause |> prittyPrintClause |> printfn "%s"