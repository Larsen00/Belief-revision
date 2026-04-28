[<AutoOpen>]
module Entailment.Belif

// Define <= and < for sentences based on entailment
let (<=.) p q = checkEntailment ([p], q)
let (<.)  p q = not (checkEntailment ([q], p))

let compareEntries p q =
    match p <=. q, q <=. p with
    | true, true -> 0
    | true, false -> -1 // p entails q but not vice versa: p is less entrenched than q
    | false, true -> 1  // q entails p but not vice versa: p is more entrenched than q
    | false, false -> 0
    
let sortBeliefBase (b: bbase) : bbase =
    List.sortWith compareEntries b

let maximality (k:bbase) p =
    List.forall (fun q -> not (p <. q)) k

let contraction (k:bbase) p =
    if maximality k p then k else 
    List.filter (fun q -> p <. Or (p, q)) k





