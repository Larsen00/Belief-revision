[<AutoOpen>]
module Entailment.Resolution

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
