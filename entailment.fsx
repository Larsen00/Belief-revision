
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

let fastPrint x =
    printfn "fast: %A" x
    x


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


// Retrives the first set where f is true
let setTryFind f s =
    match Set.toList s |> List.tryFind f with
    | Some x -> Some (set x)
    | None -> None

let setAllPairs s1 s2 =
    Set.fold (fun acc x -> Set.fold (fun acc' y -> Set.add (x, y) acc') acc s2) Set.empty s1

let isTautology (ds:DisjunctionSet) : bool =
    Set.exists (fun l -> Set.contains (negateLiteral l) ds) ds

let rec removeTautologies (dl:DisjunctionSet list) : DisjunctionSet list =
    match dl with 
    | [] -> []
    | ds :: tails when isTautology ds -> removeTautologies tails // If the disjunction contains both a literal and its negation, it is a tautology and can be removed
    | ds :: tails -> ds :: removeTautologies tails // Otherwise, we keep the disjunction and continue checking the rest of the list        

// cs_pais is the set of all pairs of sets where one contains m and the other contains ¬m
let resx cs_pais cs m =
    // Construct a new set 
    let new_css = 
        Set.fold (fun acc (d1, d2) -> Set.add (Set.union (Set.remove (negateLiteral m) d1) (Set.remove m d2)) acc) Set.empty cs_pais 
        |> Set.toList 
        |> removeTautologies
        |> Set.ofList
    // printfn "m: %A" m
    // printfn "new_css: %s" (prittyPrintConjunctionSet new_css)
    // printfn "cs: %s\n" (prittyPrintConjunctionSet cs)
    if Set.isSubset new_css cs then None else Some (Set.union cs new_css)

let rec res (cs:ConjunctionSet) m : ConjunctionSet option =
    match Set.filter (Set.contains (negateLiteral m)) cs, Set.filter (Set.contains m) cs with
    | disjuntion, disjuntion' when not (Set.isEmpty disjuntion) && not (Set.isEmpty disjuntion') ->
        resx (setAllPairs disjuntion disjuntion') cs m
    | _ -> None


and fullResolution (ll:literal list) (cs:ConjunctionSet) : ConjunctionSet option =
    match ll with 
    | [] -> Some cs
    | literal :: literal_tail -> 
        match res cs literal with
        | Some new_cs -> reduceConjunctionSet new_cs   
        | None -> fullResolution literal_tail cs       

and reduceConjunctionSet (cs:ConjunctionSet) : ConjunctionSet option =
    match Set.contains Set.empty cs with
    | true -> None // Empty clause found: contradiction, so the clause set is unsatisfiable
    | false -> 
        let ll = Set.fold Set.union Set.empty cs |> Set.toList      
        fullResolution ll cs                                        



let stringConjunctionSet cs :string =
    Set.map (fun ds -> Set.map (function Pos l -> l | Neg l -> sprintf "¬%s" l) ds) cs
    |> Set.map (String.concat " ∨ ") |> String.concat ", " |> sprintf "{%s}"


// test
let c = Biconditional (Term "r", Or (Term "p", Term "s"))

match toCNF c |> cnfToConjunctionSet |> reduceConjunctionSet with
| Some cs -> printfn "The sentence is satisfiable. Conjunction set: %s" (stringConjunctionSet cs)
| None -> printfn "A contradiction was found. The sentence is unsatisfiable."




//////////////// TEST of resolution ////////////


type prediction = Satisfiable | Unsatisfiable

let test s prediction =
    match toCNF s |> cnfToConjunctionSet |> reduceConjunctionSet, prediction with
    | Some cs, Satisfiable -> printfn "Test passed: The sentence is satisfiable. Conjunction set: %s" (stringConjunctionSet cs)
    | Some cs, Unsatisfiable -> printfn "Test failed: Expected unsatisfiable but got satisfiable. Conjunction set: %s" (stringConjunctionSet cs)
    | None, Satisfiable -> printfn "Test failed: Expected satisfiable but got unsatisfiable."
    | None, Unsatisfiable -> printfn "Test passed: A contradiction was found. The sentence is unsatisfiable."



// --------------------
// satisfiable
// --------------------

// p ∧ q
let s1 = And (Term "p", Term "q")
test s1 Satisfiable

// p ∨ q
let s2 = Or (Term "p", Term "q")
test s2 Satisfiable

// p -> q
let s3 = Implies (Term "p", Term "q")
test s3 Satisfiable

// p <-> p
let s4 = Biconditional (Term "p", Term "p")
test s4 Satisfiable

// r <-> (p ∨ s)
let s5 = Biconditional (Term "r", Or (Term "p", Term "s"))
test s5 Satisfiable

// (p -> q) ∧ p
let s6 = And (Implies (Term "p", Term "q"), Term "p")
test s6 Satisfiable

// (p ∨ q) ∧ (¬p ∨ q)
let s7 = And (Or (Term "p", Term "q"), Or (Not (Term "p"), Term "q"))
test s7 Satisfiable

// ¬(p ∧ q)
let s8 = Not (And (Term "p", Term "q"))
test s8 Satisfiable

// (p -> q) ∧ (q -> r)
let s9 = And (Implies (Term "p", Term "q"), Implies (Term "q", Term "r"))
test s9 Satisfiable


// --------------------
// unsatisfiable
// --------------------

// p ∧ ¬p
let u1 = And (Term "p", Not (Term "p"))
test u1 Unsatisfiable

// (p ∧ q) ∧ ¬p
let u2 = And (And (Term "p", Term "q"), Not (Term "p"))
test u2 Unsatisfiable

// (p -> q) ∧ p ∧ ¬q
let u3 = And (And (Implies (Term "p", Term "q"), Term "p"), Not (Term "q"))
test u3 Unsatisfiable

// (p ∨ q) ∧ ¬p ∧ ¬q
let u4 = And (And (Or (Term "p", Term "q"), Not (Term "p")), Not (Term "q"))
test u4 Unsatisfiable

// (p <-> q) ∧ p ∧ ¬q
let u5 = And (And (Biconditional (Term "p", Term "q"), Term "p"), Not (Term "q"))
test u5 Unsatisfiable

// (p -> q) ∧ (q -> r) ∧ p ∧ ¬r
let u6 =
    And (
        And (
            And (Implies (Term "p", Term "q"), Implies (Term "q", Term "r")),
            Term "p"
        ),
        Not (Term "r")
    )
test u6 Unsatisfiable

// p ∧ ¬p ∧ q
let u7 = And (And (Term "p", Not (Term "p")), Term "q")
test u7 Unsatisfiable

// (p ∨ q) ∧ ¬p ∧ (p -> r) ∧ ¬r ∧ ¬q
let u8 =
    And (
        And (
            And (Or (Term "p", Term "q"), Not (Term "p")),
            And (Implies (Term "p", Term "r"), Not (Term "r"))
        ),
        Not (Term "q")
    )
test u8 Unsatisfiable
