# Belief Revision Agent

This project contains a terminal interface for a belief revision agent implemented in F#.

The console app lets you interact with a belief base and test:

- belief base construction
- logical entailment
- contraction
- expansion
- revision via the Levi identity

## Requirements

- .NET SDK 10.0

## Run the Program

From the repository root, run:

```powershell
dotnet run --project src\BeliefRevision\BeliefRevision.fsproj
```

You will then enter the interactive prompt:

```text
B>
```

## Available Commands

| Command | Description |
| --- | --- |
| `show` | Show the current belief base |
| `cnf` | Show each formula in the belief base converted to CNF |
| `add <formula>` | Expand the belief base with a formula |
| `contract <formula>` | Contract the belief base by a formula |
| `revise <formula>` | Revise the belief base by a formula |
| `entails <formula>` | Check whether the current belief base entails a formula |
| `sort` | Show the belief base sorted by epistemic entrenchment |
| `reset` | Clear the belief base |
| `demo` | Run the built-in demonstration of the four stages |
| `help` | Show command help in the terminal |
| `exit` or `quit` | Exit the program |

## Formula Syntax

The parser supports standard propositional logic syntax:

| Syntax | Meaning |
| --- | --- |
| `p`, `q`, `rain` | Atomic propositions |
| `!p`, `~p`, `¬p` | Negation |
| `p & q`, `p ∧ q` | Conjunction |
| `p | q`, `p ∨ q` | Disjunction |
| `p -> q`, `p → q` | Implication |
| `p <-> q`, `p ↔ q` | Biconditional |
| `(p | q) & r` | Parenthesized expressions |

## Example Session

```text
B> add p -> q
B> add p
B> entails q
B> revise p <-> q
B> show
B> exit
```

## Run the Demo

If you want to see a full walkthrough of the assignment stages, start the program and run:

```text
B> demo
```

## Run Tests

To run the test suite:

```powershell
dotnet test tests\Entailment.Tests\Entailment.Tests.fsproj
```