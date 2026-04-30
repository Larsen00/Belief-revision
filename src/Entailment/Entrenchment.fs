[<AutoOpen>]
module Entailment.Entrenchment

type RankedSentence = { Sentence: sentence; Rank: float}
type Knowledge = RankedSentence list

// We define 0 as the most entrenched and negative infinity as the least entrenched
let maxEntrenchment = 0.0

let extractRankedSentence (k: Knowledge) (p: sentence) : RankedSentence option =
    match List.tryFind (fun rs -> rs.Sentence = p) k with
    | Some rs -> Some rs
    | None -> None


let KnowledgeToBeliefBase (e: Knowledge) : bbase =
    List.sortBy (fun rs -> rs.Rank) e |> List.map (fun rs -> rs.Sentence)


let isBelieved (e: Knowledge) (p: sentence) : bool =
    KnowledgeToBeliefBase e |= p

let minimalRank (e: Knowledge) : float =
    if List.isEmpty e then
        maxEntrenchment - 1.0
    else
        (List.minBy (fun rs -> rs.Rank) e).Rank - 1.0

let weakestPthatEntailsQ (qs: Knowledge) (p: sentence) : RankedSentence option =
    List.sortBy (fun q -> q.Rank) qs |> List.tryFind (fun q -> [p] |= q.Sentence)

let strongestQthatEntailsP (qs: Knowledge) (p: sentence) : RankedSentence option =
    List.sortByDescending (fun q -> q.Rank) qs |> List.tryFind (fun q -> [q.Sentence] |= p)

let strongestRankBelowRank (qs: Knowledge) (rank: float) : float =
    try
        qs
        |> List.filter (fun q -> q.Rank < rank)
        |> List.maxBy (fun q -> q.Rank)
        |> fun q -> q.Rank
    with
    | :? System.ArgumentException -> minimalRank qs


let weakestRankAboveRank (qs: Knowledge) (rank: float) : float =
    try
        qs
        |> List.filter (fun q -> q.Rank > rank)
        |> List.minBy (fun q -> q.Rank)
        |> fun q -> q.Rank
    with
    | :? System.ArgumentException -> maxEntrenchment

let extractTautologies (k: Knowledge) =
    List.partition (fun rs -> rs.Rank = maxEntrenchment) k

let updateRanksToInts (e: Knowledge) : Knowledge =

    let rec updateNonTautologies (nonTautologies: RankedSentence list) i =
        match nonTautologies with
        | [] -> []
        | q :: qnext :: rest when q.Rank = qnext.Rank ->
            { Sentence = q.Sentence; Rank = i } :: updateNonTautologies (qnext :: rest) i
        | q :: rest ->
            { Sentence = q.Sentence; Rank = i } :: updateNonTautologies rest (i - 1.0)

    let tautologies, nonTautologies = extractTautologies e

    let sortedNonTautologies =
        nonTautologies |> List.sortByDescending (fun rs -> rs.Rank)

    tautologies @ updateNonTautologies sortedNonTautologies -1.0

let rankof (e: Knowledge) (p: sentence) : float =

    let insertSentence e p =

        // According to dominance:
        // if p |= q then rank(p) <= rank(q)
        // and if p |= q and q |= p then rank(p) = rank(q)

        let weakestPthatEntailsQ = weakestPthatEntailsQ e p
        let strongestQthatEntailsP = strongestQthatEntailsP e p

        let weakestOfAll = List.minBy (fun rs -> rs.Rank) e

        match weakestPthatEntailsQ, strongestQthatEntailsP with
        | None, None -> 
            match not (KnowledgeToBeliefBase e |= p) with
            | true -> weakestOfAll.Rank - 1.0
            | false -> 0.5
        | Some q, None ->
            let below = strongestRankBelowRank e q.Rank
            below + abs(below - q.Rank) / 2.0
        | None, Some q ->
            let above = weakestRankAboveRank e q.Rank
            // printfn "weakest above %.2f is %.2f" q.Rank above
            // printfn "q.rank is %.2f" q.Rank
            // printfn "res: %.2f" (above - abs(above - q.Rank) / 2.0)
            above - abs(above - q.Rank) / 2.0

        | Some q', Some q when q'.Rank = q.Rank ->
            q'.Rank

        | Some q', Some q ->
            (q.Rank + q'.Rank) / 2.0

    if isTautology p then
        maxEntrenchment
    elif List.isEmpty e then
        maxEntrenchment - 1.0
    elif extractRankedSentence e p |> Option.isSome then
        extractRankedSentence e p |> Option.get |> fun rs -> rs.Rank
    elif not (isBelieved e p) then
        minimalRank e
    else
        insertSentence e p

let expansion (e: Knowledge) (p: sentence) : Knowledge =
    match extractRankedSentence e p with
    | Some _ ->
        e
    | None ->
        let newRank = rankof e p
        { Sentence = p; Rank = newRank } :: e |> updateRanksToInts

let beliefBaseToKnowledge (b: bbase) : Knowledge =
    // add all tautologies first 
    let tautologies, nonTautologies = List.partition (fun p -> isTautology p) b
    List.fold expansion [] (tautologies @ nonTautologies)

let contraction (e: Knowledge) (s: sentence) : Knowledge =

    let (<=.) p q =
        let rankP = rankof e p
        let rankQ = rankof e q
        // printfn "\n\nComparing ranks: \n\t%A \n\t(rank %.2f) \n with \n\t%A \n\t(rank %.2f)" p rankP q rankQ
        rankP <= rankQ // lower rank means less entrenched; 0 is strongest

    let (<.) p q =
        // printfn "\n\nComparing: %A < %A" p q
        p <=. q && not (q <=. p)

    // q in K ÷ s iff q in K and either s < (s ∨ q) or s in Cn(Ø)
    if isTautology s then
        e
    else
        List.filter (fun q -> s <. Or(s, q.Sentence)) e


// Revision using the Levi identity: B * ϕ = (B - ¬ϕ) + ϕ
let revision (kb:Knowledge) p =
    expansion (contraction kb (Not p)) p