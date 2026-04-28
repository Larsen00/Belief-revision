namespace Entailment

///////////// Common Data types for sentences and CNF /////////////
type literal =
    | Pos of string
    | Neg of string


// Type for standard propositional sentences
type sentence =
    | And of sentence * sentence
    | Or of sentence * sentence
    | Implies of sentence * sentence
    | Not of sentence
    | Biconditional of sentence * sentence
    | Term of string


// Type for sentences in Conjunctive Normal Form (CNF) - Notice it dont have Implies or Biconditionals
type cnf =
    | Conjunction of cnf * cnf
    | Disjunction of cnf * cnf
    | Negation of cnf
    | Literal of string

// Set of literals representing a disjunction (e.g., A ∨ ¬B ∨ C would be represented as {Pos "A", Neg "B", Pos "C"}) - Used for resolution
type DisjunctionSet = Set<literal>

// Set of disjunctions representing a conjunction (e.g., (A ∨ B) ∧ (¬C ∨ D) would be represented as {{Pos "A", Pos "B"}, {Neg "C", Pos "D"}}) - Used for resolution
type ConjunctionSet = Set<DisjunctionSet>

