/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Lean
public import Reduction
public import Reduction.Search
public import Reduction.Tactic

public meta section

/-!
# Smoke test for `by reduce`

Postulates an anchor on `EncodedHaltMPCP` (the leaf of the closed
chain), then asks the tactic to close downstream undecidability goals.
With the chain
`EncodedHaltMPCP ≤ₘ MPCP_LB ≤ₘ EncodedPCP ≤ₘ EncodedCFGIntersection`
fully registered, `by reduce` finds and composes the right path for
each goal.
-/

open Lean DiagonaLean DiagonaLean.ReductionGraph DiagonaLean.Problems

/-- Sample anchor: postulate that `EncodedHaltMPCP` is undecidable.
The TM-level proof in `Halt.Undecidable` doesn't yet bridge to the
framework's `Undecidable` notion (see TODO). -/
axiom encodedHaltMPCP_undecidable : Undecidable EncodedHaltMPCP

attribute [undecidable_anchor] encodedHaltMPCP_undecidable

/-- Print all registered edges. -/
def printReductionGraph : CoreM Unit := do
  let edges ← getReductionGraph
  IO.println s!"Graph has {edges.length} edge(s):"
  for e in edges.reverse do
    IO.println s!"  • {e.declName}"

#eval printReductionGraph

/-! ## The `by reduce` tactic in action -/

example : Undecidable EncodedHaltMPCP := by reduce
example : Undecidable MPCP_LB := by reduce
example : Undecidable EncodedPCP := by reduce
example : Undecidable EncodedCFGIntersection := by reduce
