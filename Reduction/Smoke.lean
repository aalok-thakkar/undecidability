/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Lean
public import Reduction
public import Reduction.Search

public meta section

/-!
# Smoke test for the reduction graph + search

`#eval`s the registered graph and runs `searchPath` on each
`EncodedX` problem. With a sample anchor on `EncodedHalt`, the search
should find paths to `EncodedHaltMPCP`, `MPCP_LB`, `EncodedPCP`, and
`EncodedCFGIntersection` once the missing `EncodedHalt ≤ₘ
EncodedHaltMPCP` edge is wired (it isn't yet — that's the HUM
normalisation TODO). For now, the path to `EncodedHalt` itself is
empty (the anchor matches the target directly).
-/

open Lean DiagonaLean DiagonaLean.ReductionGraph DiagonaLean.Problems

/-- Sample anchor: postulate that `EncodedHaltMPCP` is undecidable.
This sits at the source of the chain
`EncodedHaltMPCP ≤ₘ MPCP_LB ≤ₘ EncodedPCP ≤ₘ EncodedCFGIntersection`,
so paths to any later node should resolve. The TM-level proof in
`Halt.Undecidable` doesn't yet bridge to the framework's `Undecidable`
notion (see TODO) — this is a postulate purely to exercise the search. -/
axiom encodedHaltMPCP_undecidable : Undecidable EncodedHaltMPCP

attribute [undecidable_anchor] encodedHaltMPCP_undecidable

/-- Print all registered edges. -/
def printReductionGraph : CoreM Unit := do
  let edges ← getReductionGraph
  IO.println s!"Graph has {edges.length} edge(s):"
  for e in edges.reverse do
    IO.println s!"  • {e.declName}"

/-- Run `searchPath` and print the result. -/
def trySearch (name : String) (target : Expr) : MetaM Unit := do
  IO.println s!"\nsearchPath for {name}:"
  match ← searchPath target with
  | none => IO.println "  (no path)"
  | some p =>
    IO.println s!"  anchor: {p.anchor.proofName}"
    IO.println s!"  {p.edges.length} edge(s)"
    for e in p.edges do
      IO.println s!"    via {e.declName}"

#eval printReductionGraph

#eval show MetaM Unit from do
  trySearch "EncodedHaltMPCP"        (Expr.const ``EncodedHaltMPCP [])
  trySearch "MPCP_LB"                (Expr.const ``MPCP_LB [])
  trySearch "EncodedPCP"             (Expr.const ``EncodedPCP [])
  trySearch "EncodedCFGIntersection" (Expr.const ``EncodedCFGIntersection [])
