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
public import Halt.Rice.Theorem

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

/-- Sample anchor (classical): postulate that `EncodedHaltMPCP` is
undecidable. -/
axiom encodedHaltMPCP_undecidable : Undecidable EncodedHaltMPCP

attribute [undecidable_anchor] encodedHaltMPCP_undecidable

/-- Sample anchor (TM-level): postulate that `EncodedHaltMPCP.predicate`
is TM-undecidable. This is exactly the HUM-normalisation gap: a real
proof would compose `selfHaltPred_TMUndecidable` with the
TM-normalisation reduction `EncodedHalt → EncodedHaltMPCP`. We
postulate it so the LB chain to `EncodedCFGI_LB` is reachable. -/
axiom encodedHaltMPCP_tm_undecidable : TMUndecidable EncodedHaltMPCP.predicate

attribute [tm_undecidable_anchor] encodedHaltMPCP_tm_undecidable

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
`TMUndecidable _.predicate` goals.

The chain runs end-to-end:
`EncodedSelfHalt → EncodedHalt → EncodedHaltMPCP → EncodedMPCP_LB
  → EncodedPCP_LB → EncodedCFGI_LB`. Note: the
`EncodedHalt → EncodedHaltMPCP` edge is **not** in the graph (the HUM
normalisation gap), so the chain breaks at `EncodedHalt`. -/

example : TMUndecidable selfHaltPred := selfHaltPred_TMUndecidable
example : TMUndecidable EncodedSelfHalt.predicate := by reduce_diag
example : TMUndecidable EncodedHalt.predicate := by reduce_diag

/-! ### Downstream LB chain (anchored at the postulated `encodedHaltMPCP_tm_undecidable`)

With `encodedHaltMPCP_tm_undecidable` as the TM anchor, `by reduce_diag`
walks the chain to `EncodedCFGI_LB.predicate`. -/

example : TMUndecidable EncodedHaltMPCP.predicate := by reduce_diag
example : TMUndecidable EncodedMPCP_LB.predicate := by reduce_diag
example : TMUndecidable EncodedPCP_LB.predicate := by reduce_diag
example : TMUndecidable EncodedCFGI_LB.predicate := by reduce_diag

/-! ### Rice's theorem (restricted form): `HaltsOnEverything`

Anchored at `CanonicalSelfHalt.predicate` (TM-undecidable from
`halt_undecidable`, no postulate), via the Rice reduction
`canonicalSelfHalt_to_haltsOnEverything` (postulated `semHalt_riceConstTM_dichotomy`
+ `TMComputable`). -/

example : TMUndecidable CanonicalSelfHalt.predicate := by reduce_diag
example : TMUndecidable HaltsOnEverything.predicate := by reduce_diag
