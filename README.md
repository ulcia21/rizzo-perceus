# Rizzo with Perceus-style Reference Counting

An F# interpreter combining Rizzo’s reactive semantics
with Perceus-style reference counting.

The project uses small-step evaluation and explicit `dup` and `drop`
operations to manage heap references.

## Main files

- `Source.fs`, `Target.fs` — expression representations.
- `Elaborator.fs` — translation with explicit `dup` and `drop`.
- `FreeAndBoundVars.fs`, `Substitution.fs` — variable handling.
- `Heap.fs` — runtime values and reference counts.
- `SignalStore.fs` — ordered signal entries.
- `Ticking.fs` — checks whether delayed computations tick.
- `Interpreter.fs` — ordinary small-step evaluation including reference-counting operations.
- `Tests.fs`, `Program.fs` — examples and test execution.

## Running

Requires the .NET 9 SDK.

From the repository root (runs tests):

    dotnet run --project Perceus/Perceus.fsproj

## Scope and references

The implementation follows the Rizzo and Perceus papers, adapting
their rules to a combined small-step runtime. This combination is
work in progress; not finished yet!.


Relevant references:

- *Simple Modal Types for Functional Reactive Programming* —
  especially Figures 8–10.
- *Perceus: Garbage Free Reference Counting with Reuse* —
  especially Figures 7–8.
