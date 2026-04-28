module BeliefRevision.Program

open System
open Entailment
open BeliefRevision.Parser

// ── Helpers ──────────────────────────────────────────────────────────────────

let private pp = prettyPrintSentence

let private colored (color: ConsoleColor) (text: string) =
    let prev = Console.ForegroundColor
    Console.ForegroundColor <- color
    printf "%s" text
    Console.ForegroundColor <- prev

let private coloredLn color text = colored color text; printfn ""

let private line () = printfn "%s" (String.replicate 62 "─")

let private printKb (kb: bbase) =
    if List.isEmpty kb then
        coloredLn ConsoleColor.DarkGray "  (empty)"
    else
        kb |> List.iteri (fun i s ->
            colored ConsoleColor.DarkGray (sprintf "  [%d] " (i + 1))
            coloredLn ConsoleColor.White (pp s))

// ── Help ─────────────────────────────────────────────────────────────────────

let private showHelp () =
    printfn ""
    coloredLn ConsoleColor.Cyan "Commands:"
    printfn "  show                 Show the current belief base"
    printfn "  add <φ>              Expansion:   B + φ"
    printfn "  contract <φ>         Contraction: B ─ φ  (epistemic entrenchment)"
    printfn "  revise <φ>           Revision:    B * φ  (Levi identity)"
    printfn "  entails <φ>          Check whether B ⊨ φ"
    printfn "  sort                 Show belief base sorted by entrenchment"
    printfn "  reset                Clear the belief base"
    printfn "  demo                 Run demonstration of all four stages"
    printfn "  help                 Show this message"
    printfn "  exit / quit          Exit"
    printfn ""
    coloredLn ConsoleColor.Cyan "Formula syntax:"
    printfn "  p  q  rain           Atomic propositions"
    printfn "  !p   ~p   ¬p         Negation"
    printfn "  p & q    p ∧ q       Conjunction"
    printfn "  p | q    p ∨ q       Disjunction"
    printfn "  p -> q   p → q       Implication  (right-associative)"
    printfn "  p <-> q  p ↔ q       Biconditional"
    printfn "  (p | q) & r          Parentheses for grouping"
    printfn ""

// ── Demo ─────────────────────────────────────────────────────────────────────

let private runDemo () =
    let step n title =
        printfn ""
        colored ConsoleColor.Cyan (sprintf "── Stage %d: " n)
        coloredLn ConsoleColor.Yellow title

    let showKb (kb: bbase) =
        colored ConsoleColor.DarkGray "  Belief base B = {"
        if List.isEmpty kb then
            colored ConsoleColor.DarkGray " (empty)"
        else
            kb |> List.iteri (fun i s ->
                if i > 0 then colored ConsoleColor.DarkGray ",  "
                colored ConsoleColor.White (pp s))
        coloredLn ConsoleColor.DarkGray " }"

    let checkKb (kb: bbase) (phi: sentence) =
        let result = checkEntailment (kb, phi)
        colored ConsoleColor.DarkGray "  B ⊨ "
        colored ConsoleColor.White (pp phi)
        colored ConsoleColor.DarkGray "  →  "
        if result then coloredLn ConsoleColor.Green "YES ✓"
        else coloredLn ConsoleColor.Red "NO  ✗"
        result

    printfn ""
    line ()
    coloredLn ConsoleColor.Cyan "  BELIEF REVISION AGENT — DEMONSTRATION"
    line ()
    printfn ""
    printfn "  Domain: weather and road conditions"
    coloredLn ConsoleColor.DarkGray "  r = it is raining   w = ground is wet   s = ground is slippery"

    // ── Stage 1: Belief Base Design ──────────────────────────────────────────
    step 1 "Belief Base Design"
    printfn "  We design a belief base B over propositions r, w, s."
    let kb0 : bbase = []
    printfn "  Initially B is empty."
    showKb kb0

    // ── Stage 2: Entailment check (empty base) ───────────────────────────────
    step 2 "Logical Entailment (empty base)"
    printfn "  An empty belief base entails nothing."
    checkKb kb0 (Term "r") |> ignore
    checkKb kb0 (Or (Term "r", Not (Term "r"))) |> ignore   // tautology

    // ── Stage 3: Expansion ───────────────────────────────────────────────────
    step 3 "Expansion  (B + φ)"
    printfn "  Adding beliefs one by one:"

    let f1 = Implies (Term "r", Term "w")      // r → w
    let f2 = Implies (Term "w", Term "s")      // w → s
    let f3 = Term "r"                          // r

    colored ConsoleColor.DarkGray "  add "
    coloredLn ConsoleColor.White (sprintf "%s   (if raining, ground is wet)" (pp f1))
    let kb1 = expansion kb0 f1

    colored ConsoleColor.DarkGray "  add "
    coloredLn ConsoleColor.White (sprintf "%s   (if wet, ground is slippery)" (pp f2))
    let kb2 = expansion kb1 f2

    colored ConsoleColor.DarkGray "  add "
    coloredLn ConsoleColor.White (sprintf "%s         (it is raining)" (pp f3))
    let kb3 = expansion kb2 f3

    showKb kb3
    printfn ""
    printfn "  Entailment after expansion:"
    checkKb kb3 (Term "w") |> ignore   // yes: r, r→w ⊨ w
    checkKb kb3 (Term "s") |> ignore   // yes: transitive chain
    checkKb kb3 (Term "q") |> ignore   // no:  unrelated atom

    // ── Stage 4: Contraction ─────────────────────────────────────────────────
    step 4 "Contraction  (B ─ φ)"
    printfn "  Contracting by r (it is no longer certain that it is raining)."
    printfn "  Epistemic entrenchment: beliefs with weaker support are removed first."
    let kb4 = contraction kb3 (Term "r")
    showKb kb4
    printfn ""
    printfn "  Entailment after contraction by r:"
    checkKb kb4 (Term "r") |> ignore   // no
    checkKb kb4 (Term "s") |> ignore   // no (r gone, chain broken)
    checkKb kb4 f1         |> ignore   // yes: conditional still present
    checkKb kb4 f2         |> ignore   // yes: conditional still present

    // ── Bonus: Revision ──────────────────────────────────────────────────────
    printfn ""
    colored ConsoleColor.Cyan "── Bonus: "
    coloredLn ConsoleColor.Yellow "Revision  (B * φ)  via Levi identity"
    printfn "  Levi identity:  B * φ  =  (B ─ ¬φ) + φ"
    let notR = Not (Term "r")
    colored ConsoleColor.DarkGray (sprintf "  Revising B = %s" "{r → w, w → s, r}")
    colored ConsoleColor.DarkGray "  with  "
    coloredLn ConsoleColor.White (pp notR)
    let kb5 = revision kb3 notR
    showKb kb5
    printfn ""
    printfn "  Entailment after revision with ¬r:"
    checkKb kb5 (Not (Term "r")) |> ignore  // yes
    checkKb kb5 (Term "r")       |> ignore  // no
    checkKb kb5 (Term "s")       |> ignore  // no (r removed, chain broken)

    printfn ""
    line ()
    coloredLn ConsoleColor.Cyan "  End of demonstration."
    line ()
    printfn ""

// ── Command processing ────────────────────────────────────────────────────────

/// Returns the new belief base (or the same one on error / display commands).
let private processCommand (kb: bbase) (line: string) : bbase =
    let line = line.Trim()
    if line = "" then kb
    else

    let parts = line.Split([|' '|], 2, StringSplitOptions.RemoveEmptyEntries)
    let cmd   = parts.[0].ToLowerInvariant()
    let rest  = if parts.Length > 1 then parts.[1].Trim() else ""

    let requireFormula () =
        if rest = "" then
            coloredLn ConsoleColor.Red (sprintf "  Error: '%s' requires a formula argument." cmd)
            None
        else
            match parse rest with
            | Ok phi   -> Some phi
            | Error msg ->
                coloredLn ConsoleColor.Red (sprintf "  Parse error: %s" msg)
                None

    match cmd with
    | "show" ->
        printfn ""
        colored ConsoleColor.Cyan "  Belief base:  "
        printfn "(%d formula%s)" (List.length kb) (if List.length kb = 1 then "" else "s")
        printKb kb
        kb

    | "add" ->
        match requireFormula () with
        | None     -> kb
        | Some phi ->
            let kb' = expansion kb phi
            colored ConsoleColor.Green "  Expansion  B + "
            coloredLn ConsoleColor.White (pp phi)
            colored ConsoleColor.Cyan "  New belief base:  "
            printfn "(%d formula%s)" (List.length kb') (if List.length kb' = 1 then "" else "s")
            printKb kb'
            kb'

    | "contract" ->
        match requireFormula () with
        | None     -> kb
        | Some phi ->
            let kb' = contraction kb phi
            colored ConsoleColor.Green "  Contraction  B ─ "
            coloredLn ConsoleColor.White (pp phi)
            colored ConsoleColor.Cyan "  New belief base:  "
            printfn "(%d formula%s)" (List.length kb') (if List.length kb' = 1 then "" else "s")
            printKb kb'
            kb'

    | "revise" ->
        match requireFormula () with
        | None     -> kb
        | Some phi ->
            let kb' = revision kb phi
            colored ConsoleColor.Green "  Revision  B * "
            coloredLn ConsoleColor.White (pp phi)
            coloredLn ConsoleColor.DarkGray (sprintf "  (Levi: contracted by ¬%s, then added %s)" (pp phi) (pp phi))
            colored ConsoleColor.Cyan "  New belief base:  "
            printfn "(%d formula%s)" (List.length kb') (if List.length kb' = 1 then "" else "s")
            printKb kb'
            kb'

    | "entails" ->
        match requireFormula () with
        | None     -> kb
        | Some phi ->
            let result = checkEntailment (kb, phi)
            colored ConsoleColor.DarkGray "  B ⊨ "
            colored ConsoleColor.White (pp phi)
            colored ConsoleColor.DarkGray "  →  "
            if result then coloredLn ConsoleColor.Green "YES ✓"
            else            coloredLn ConsoleColor.Red   "NO  ✗"
            kb

    | "sort" ->
        let sorted = sortBeliefBase kb
        printfn ""
        coloredLn ConsoleColor.Cyan "  Belief base sorted by epistemic entrenchment (weakest first):"
        printKb sorted
        coloredLn ConsoleColor.DarkGray "  (Ordering: p ≤ q iff {p} ⊨ q)"
        kb

    | "reset" ->
        coloredLn ConsoleColor.Yellow "  Belief base cleared."
        []

    | "demo" ->
        runDemo ()
        kb

    | "help" | "?" ->
        showHelp ()
        kb

    | "exit" | "quit" ->
        printfn ""
        coloredLn ConsoleColor.Cyan "  Goodbye."
        printfn ""
        Environment.Exit 0
        kb

    | _ ->
        coloredLn ConsoleColor.Red (sprintf "  Unknown command: '%s'.  Type 'help' for usage." cmd)
        kb

// ── Entry point ───────────────────────────────────────────────────────────────

[<EntryPoint>]
let main _ =
    printfn ""
    line ()
    coloredLn ConsoleColor.Cyan "  BELIEF REVISION AGENT"
    coloredLn ConsoleColor.DarkGray "  AGM-style belief revision with epistemic entrenchment"
    line ()
    printfn ""
    printfn "  Operations:"
    printfn "    Expansion    B + φ    — add a new belief"
    printfn "    Contraction  B ─ φ    — remove a belief (entrenchment-based)"
    printfn "    Revision     B * φ    — revise via Levi identity: (B ─ ¬φ) + φ"
    printfn "    Entailment   B ⊨ φ    — resolution-based entailment check"
    printfn ""
    coloredLn ConsoleColor.DarkGray "  Type 'demo' to see a worked example, or 'help' for all commands."
    printfn ""

    let mutable kb : bbase = []

    let rec loop () =
        colored ConsoleColor.Cyan "B> "
        let input = Console.ReadLine()
        if input = null then ()   // EOF
        else
            kb <- processCommand kb input
            loop ()

    loop ()
    0
