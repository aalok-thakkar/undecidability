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
# Smoke test for `by reduce_diag` + TM-undecidability

Postulates an anchor on `EncodedHaltMPCP` (the leaf of the closed
chain), then asks `by reduce_diag` to close downstream undecidability
goals via the registered graph. With the chain
`EncodedHaltMPCP ≤ₘ MPCP_LB ≤ₘ EncodedPCP ≤ₘ EncodedCFGIntersection`
fully registered, the tactic finds and composes the right path.

(The tactic is named `reduce_diag` to avoid a name clash with
Mathlib's `reduce` tactic.)
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

/-! ## The `by reduce_diag` tactic in action -/

example : Undecidable EncodedHaltMPCP := by reduce_diag
example : Undecidable MPCP_LB := by reduce_diag
example : Undecidable EncodedPCP := by reduce_diag
example : Undecidable EncodedCFGIntersection := by reduce_diag

/-! ## TM-level undecidability via `by reduce_diag`

`EncodedSelfHalt.predicate` is the registered `@[tm_undecidable_anchor]`
(via `selfHaltPred_TMUndecidable`, which is derived from
`Halt.halt_undecidable` without postulates). The tactic searches the
graph and composes TMComputable witnesses (looked up by naming
convention `<edgeDeclName>_TMComputable`) to close downstream
`TMUndecidable _.predicate` goals. -/

example : TMUndecidable selfHaltPred := selfHaltPred_TMUndecidable
example : TMUndecidable EncodedSelfHalt.predicate := by reduce_diag
example : TMUndecidable EncodedHalt.predicate := by reduce_diag
