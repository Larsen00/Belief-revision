[<AutoOpen>]
module Entailment.Entailment

type entailment = sentence list * sentence


let sentencesListTosentence (s :sentence list) : sentence =
    match s with
    | [] -> failwith "Empty list of sentences"
    | [s] -> s
    | s1 :: tail -> List.fold (fun acc s -> And (acc, s)) s1 tail


// Checks if the knowledge base (kb) entails the sentence alpha using resolution ie. KB |= alpha iff KB ∪ {¬alpha} is unsatisfiable
let checkEntailment (kb:sentence list, alpha:sentence) : bool =
    sentencesListTosentence (Not alpha :: kb) 
    |> toCNF 
    |> cnfToConjunctionSet 
    |> reduceConjunctionSet 
    |> Option.isNone
    
