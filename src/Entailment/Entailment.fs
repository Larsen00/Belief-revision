[<AutoOpen>]
module Entailment.Entailment

// Type for belief base
type bbase = sentence list

// Type for entailment: a pair of a belief base and a sentence ie. {p1, p2, p3} |= alpha is represented as ([p1; p2; p3], alpha)
type entailment = bbase * sentence


// Turn a list of sentences into a single sentence by conjoining them with And ie. [p1; p2; p3] -> And (p1, And (p2, p3))
let sentencesListTosentence (s :sentence list) : sentence =
    match s with
    | [] -> failwith "Empty list of sentences"
    | [s] -> s
    | s1 :: tail -> List.fold (fun acc s -> And (acc, s)) s1 tail

// Checks if the knowledge base (kb) entails the sentence alpha using resolution ie. KB |= alpha iff KB ∪ {¬alpha} is unsatisfiable
let checkEntailment (kb:bbase, alpha:sentence) : bool =
    sentencesListTosentence (Not alpha :: kb) 
    |> toCNF
    |> cnfToConjunctionSet
    |> reduceConjunctionSet
    |> Option.isNone
    
