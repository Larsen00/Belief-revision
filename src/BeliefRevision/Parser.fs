module BeliefRevision.Parser

open System
open Entailment

// ── Tokens ───────────────────────────────────────────────────────────────────

type private Token =
    | TAtom of string
    | TNot
    | TAnd
    | TOr
    | TImplies
    | TBicond
    | TLParen
    | TRParen
    | TEOF

// ── Tokenizer ────────────────────────────────────────────────────────────────

let private tokenize (s: string) : Token list =
    let mutable i = 0
    let result = Collections.Generic.List<Token>()
    while i < s.Length do
        match s.[i] with
        | ' ' | '\t' -> i <- i + 1
        | '(' -> result.Add TLParen;  i <- i + 1
        | ')' -> result.Add TRParen;  i <- i + 1
        | '!' | '~' | '¬' -> result.Add TNot; i <- i + 1
        | '&' | '∧' -> result.Add TAnd; i <- i + 1
        | '|' | '∨' -> result.Add TOr;  i <- i + 1
        | '→' -> result.Add TImplies; i <- i + 1
        | '↔' -> result.Add TBicond;  i <- i + 1
        | '-' when i + 1 < s.Length && s.[i+1] = '>' ->
            result.Add TImplies; i <- i + 2
        | '<' when i + 2 < s.Length && s.[i+1] = '-' && s.[i+2] = '>' ->
            result.Add TBicond; i <- i + 3
        | c when Char.IsLetter c || c = '_' ->
            let start = i
            while i < s.Length && (Char.IsLetterOrDigit s.[i] || s.[i] = '_') do
                i <- i + 1
            result.Add (TAtom s.[start..i-1])
        | c -> failwithf "Unknown character: '%c'" c
    result.Add TEOF
    result |> Seq.toList

// ── Recursive-descent parser ─────────────────────────────────────────────────
// Precedence (low → high): <->  ->  |  &  !  atom

let private doParse (tokens: Token list) : sentence =
    let toks = Array.ofList tokens
    let mutable pos = 0
    let peek ()    = toks.[pos]
    let consume () = let t = toks.[pos] in pos <- pos + 1; t
    let expect t   =
        if toks.[pos] <> t then failwithf "Expected %A but got %A" t toks.[pos]
        pos <- pos + 1

    let rec parseExpr ()   = parseBicond ()

    and parseBicond () =
        let mutable left = parseImplies ()
        while peek () = TBicond do
            consume () |> ignore
            left <- Biconditional (left, parseImplies ())
        left

    and parseImplies () =
        let left = parseOr ()
        if peek () = TImplies then
            consume () |> ignore
            Implies (left, parseImplies ())   // right-associative
        else left

    and parseOr () =
        let mutable left = parseAnd ()
        while peek () = TOr do
            consume () |> ignore
            left <- Or (left, parseAnd ())
        left

    and parseAnd () =
        let mutable left = parseNot ()
        while peek () = TAnd do
            consume () |> ignore
            left <- And (left, parseNot ())
        left

    and parseNot () =
        if peek () = TNot then consume () |> ignore; Not (parseNot ())
        else parseAtom ()

    and parseAtom () =
        match consume () with
        | TAtom name -> Term name
        | TLParen ->
            let e = parseExpr ()
            expect TRParen
            e
        | t -> failwithf "Unexpected token: %A" t

    let result = parseExpr ()
    if peek () <> TEOF then failwith "Unexpected tokens after expression"
    result

/// Parse a propositional formula string into a sentence.
/// Returns Ok sentence or Error message.
let parse (input: string) : Result<sentence, string> =
    try
        tokenize input |> doParse |> Ok
    with ex ->
        Error ex.Message
