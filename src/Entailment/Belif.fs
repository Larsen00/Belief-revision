[<AutoOpen>]
module Entailment.Belif

// Define <= and < for sentences based on entailment
let (<=.) p q = checkEntailment ([p], q)
let (<.)  p q = not (checkEntailment ([q], p))

// Helper method to compare two sentences for sorting
let compareEntries p q =
    match p <=. q, q <=. p with
    | true, true -> 0
    | true, false -> -1 // p entails q but not vice versa: p is less entrenched than q
    | false, true -> 1  // q entails p but not vice versa: p is more entrenched than q
    | false, false -> 0
    
// Sort a belif base using enrichment ordering
let sortBeliefBase (b: bbase) : bbase =
    List.sortWith compareEntries b

// if p <= p for all q, then p in Cn(ø)
let maximality (k:bbase) p =
    List.forall (fun q -> q <=. p) k

// Contraction: Remove p from the belief base using entrenchment-based contraction: q in K % p iff q in K and either p <. (q or p) or p in Cn(ø)
let contraction (k:bbase) p =
    if maximality k p then k else 
    List.filter (fun q -> p <. Or (p, q)) k

// Expansion: B + ϕ; ϕ is added to B giving a new belief set B'
let expansion (k:bbase) p =
    Set.ofList (p :: k) |> Set.toList

// Revision using the Levi identity: B * ϕ = (B - ¬ϕ) + ϕ
let revision (k:bbase) p =
    expansion (contraction k (Not p)) p
