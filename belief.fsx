
type literal =
    | Pos of string
    | Neg of string

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


type DisjunctionSet = Set<literal>
type ConjunctionSet = Set<DisjunctionSet>

// Helper functions
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
    | Disjunction (c1, c2) -> Disjunction (distribute c1, distribute c2)
    | Conjunction (c1, c2) -> Conjunction (distribute c1, distribute c2)
    | Negation c -> Negation (distribute c)
    | Literal l -> Literal l


// Combine all steps into a single function
let toCNF (s:sentence) : cnf =
    s |> elimination |> moveNegations |> distribute


// Example form slides
Biconditional (Term "r", Or (Term "p", Term "s")) |> toCNF |> printfn "%A"


// Resolution
let rec cnfToConjunctionSet c : ConjunctionSet = 
    match c with
    | Conjunction (c1, c2) -> cnfToConjunctionSet c1 |> Set.union <| cnfToConjunctionSet c2
    | _ -> cnfToDisjunctionSet c |> Set.singleton

and cnfToDisjunctionSet c : DisjunctionSet =
    match c with
    | Disjunction (c1, c2) -> cnfToDisjunctionSet c1 |> Set.union <| cnfToDisjunctionSet c2
    | Negation (Literal l) -> Set.singleton (Neg l)
    | Literal l -> Set.singleton (Pos l)
    | _ -> failwith "Invalid CNF format"


// test
Biconditional (Term "r", Or (Term "p", Term "s")) |> toCNF |> cnfToConjunctionSet |> prittyPrintConjunctionSet |> printfn "\ncnfToDisjunctionSet:\n%s"

let negateLiteral (l:literal) : literal =
    match l with 
    | Pos s -> Neg s
    | Neg s -> Pos s

let rec fullResolution (ll:literal list) (cs_acc:ConjunctionSet) =
    match ll with 
    | [] -> cs_acc
    | literal :: literal_tail when Set.exists (fun x -> Set.contains (negateLiteral literal) x) cs_acc ->
        // Remove both m and ¬m from the clauses
        Set.map (fun clause -> Set.difference clause (set [negateLiteral literal; literal])) cs_acc |> fullResolution literal_tail
    | _ :: literal_tail -> fullResolution literal_tail cs_acc

let rec reduceConjunctionSet (cs:ConjunctionSet) =
    let ll = Set.fold Set.union Set.empty cs |> Set.toList
    fullResolution ll cs 

let fastPrint x =
    printfn "fast: %A" x
    x

// test
Biconditional (Term "r", Or (Term "p", Term "s")) |> toCNF |> cnfToConjunctionSet |> fastPrint |> reduceConjunctionSet |> fastPrint |> prittyPrintConjunctionSet |> printfn "\nResolution:\n%s"