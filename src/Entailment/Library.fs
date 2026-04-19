namespace Entailment

///////////// Data types for sentences and CNF /////////////
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
