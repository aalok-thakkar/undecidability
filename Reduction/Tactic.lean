/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Lean
public import Reduction.Search
public import Reduction.Transfer

public meta section

/-!
# `by reduce` tactic

Component 3 of the DiagonaLean tactic. Given a goal `⊢ Undecidable T`,
the tactic:

1. Extracts `T` from the goal.
2. Calls `searchPath T` to find a `Path` anchored at some
   `@[undecidable_anchor] proof : Undecidable A` with edges
   `A ≤ₘ … ≤ₘ T`.
3. Composes the edges via `ManyOneReduction.trans` into a single
   `r : ManyOneReduction A T`.
4. Applies `Undecidable.of_manyOne r anchor.proof` to close the goal.

## Usage

```lean
@[undecidable_anchor]
axiom my_undecidable : Undecidable SomeProblem

example : Undecidable OtherProblem := by reduce
```

## Limitations (MVP)

* Only handles **ground** edges (no polymorphic universal binders).
  A polymorphic edge like `mpcpToPcp α` raises an error. Future work:
  thread metavariables through the search and apply edges at the
  unified types.
-/

open Lean Meta Elab Tactic

namespace DiagonaLean.ReductionGraph

/-- Build the Lean term for a single edge. For ground edges this is
just `e.declName` with fresh universe levels. For polymorphic edges
(those whose type has Pi binders for type/instance args), this is not
yet supported. -/
def mkEdgeTerm (e : Edge) : MetaM Expr := do
  let info ← getConstInfo e.declName
  if info.type.isForall then
    throwError "composeReductions: polymorphic edge `{e.declName}` is not \
      supported in MVP (its type has unresolved binders). Use \
      monomorphic reductions or instantiate the edge manually."
  mkConstWithFreshMVarLevels e.declName

/-- Compose a `Path` into a single `ManyOneReduction A T` Expr, where
`A` is the anchor's problem and `T` is the search target. For an empty
path, returns the identity reduction at the anchor's problem. -/
def composeReductions (path : Path) : MetaM Expr := do
  match path.edges with
  | [] =>
    let problem ← instantiateEndpoint path.anchor.problem
    mkAppM ``DiagonaLean.ManyOneReduction.id #[problem]
  | first :: rest => do
    let mut acc ← mkEdgeTerm first
    for e in rest do
      let next ← mkEdgeTerm e
      acc ← mkAppM ``DiagonaLean.ManyOneReduction.trans #[acc, next]
    return acc

/-- The `by reduce` tactic. Closes a goal of the form
`Undecidable T` by finding a chain of registered reductions from a
known-undecidable anchor to `T`. -/
elab "reduce" : tactic => Tactic.withMainContext do
  let target ← Tactic.getMainTarget
  let target ← instantiateMVars target
  let (name, args) := target.getAppFnArgs
  unless name = ``DiagonaLean.Undecidable do
    throwError "`by reduce`: expected goal of form `Undecidable P`, got: {target}"
  unless args.size = 1 do
    throwError "`by reduce`: expected `Undecidable P` (1 argument), got arity {args.size}"
  let goalProblem := args[0]!
  match ← searchPath goalProblem with
  | none =>
    throwError "`by reduce`: no path found from any registered anchor to {goalProblem}"
  | some path =>
    let reduction ← composeReductions path
    let anchorProof ← mkConstWithFreshMVarLevels path.anchor.proofName
    let proof ← mkAppM ``DiagonaLean.Undecidable.of_manyOne #[reduction, anchorProof]
    Tactic.closeMainGoal `reduce proof

end DiagonaLean.ReductionGraph
