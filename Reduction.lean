/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import Reduction.Basic
public import Reduction.Composition
public import Reduction.Transfer
public import Reduction.Notation
public import Reduction.Graph
public import Reduction.Search
public import Reduction.Tactic
public import Reduction.TMDecidable
public import Reduction.Instances
public import Reduction.Encoded
public import Reduction.HaltUndecidable
public import Reduction.StackMap
public import Reduction.EncodedPCP
public import Reduction.EncodedHaltMPCP
public import Reduction.EncodedCFG
public import Reduction.StackEncoding
public import Reduction.EncodedLB

@[expose] public section

/-!
# Reduction — DiagonaLean Phase 1 framework

This library defines the abstract reduction framework:

* `DiagonaLean.Problem`           — a decision problem (Input + predicate).
* `DiagonaLean.ManyOneReduction`  — a function-level many-one reduction.
* `DiagonaLean.Decidable`         — abstract decidability.
* `DiagonaLean.Undecidable`       — its negation.
* Composition laws: `.id`, `.trans`, identity/assoc lemmas.
* Transfer theorems: `Decidable.of_manyOne`, `Undecidable.of_manyOne`.
* Notation: `P ≤ₘ Q`, `P ≡ₘ Q`.

The framework is Lean-function-level: `ManyOneReduction.f` is an
arbitrary `Lean → Lean` function, with no computability constraint. A
TM-level refinement (`TMComputableReduction`) is on the TODO; see
[`TODO.md`](../TODO.md).

For instances wrapping the existing reductions (`mpcp_iff_pcp`,
`halt_le_mpcp`, `halts_iff_pcp`, `hasSolution_iff_intersectionNonempty`,
`halts_codeOf_iff`), see `Reduction.Instances`.

## Encoded graph (`List Bool`-input variants)

To give the reduction graph stable `Type`-level node identities, the
`Reduction.Encoded*` modules wrap problems at fixed alphabets:

* `Reduction.Encoded`        — `EncodedHalt` (`HaltTMCode ≡ₘ EncodedHalt`).
* `Reduction.StackMap`       — generic per-symbol injection lifting.
* `Reduction.EncodedPCP`     — `MPCP_LB`, `EncodedPCP`, and the
                                `mpcpLB_to_encodedPCP` edge via `flattenExt`.
* `Reduction.EncodedHaltMPCP` — `EncodedHaltMPCP` and the
                                `encodedHaltMPCP_to_mpcpLB` edge via `encodeAlpha`.
* `Reduction.EncodedCFG`     — `EncodedCFGIntersection` and the
                                `encodedPCP_to_encodedCFGIntersection` edge.

The chain
`EncodedHaltMPCP ≤ₘ MPCP_LB ≤ₘ EncodedPCP ≤ₘ EncodedCFGIntersection`
runs end-to-end. The missing edge `EncodedHalt ≤ₘ EncodedHaltMPCP`
(TM normalisation to `NoBlankWrites ∧ NoLeftBoundary`) is the remaining
gap to a fully end-to-end undecidability transfer from `HaltTM`.

## Tactic infrastructure

* `Reduction.Graph`          — `Edge` record, persistent env extension,
                                `@[reduction_graph]` attribute, plus
                                anchors (`@[undecidable_anchor]`).
                                Component 1.
* `Reduction.Search`         — depth-bounded backward DFS from a target
                                `Problem` to an anchor, with cycle
                                detection and metavariable
                                instantiation for polymorphic edges.
                                Component 2.
* `Reduction.Tactic`         — `composeReductions` (fold a `Path` via
                                `ManyOneReduction.trans`) and the
                                `by reduce_diag` tactic that closes
                                `Undecidable T` goals end-to-end via
                                `Undecidable.of_manyOne`. Component 3.
                                (The tactic is named `reduce_diag` to
                                avoid a name clash with Mathlib's
                                `reduce` tactic.)

The full MVP tactic chain is operational: tag reductions with
`@[reduction_graph]`, an anchor with `@[undecidable_anchor]`, and write
`example : Undecidable T := by reduce_diag`.

Known limitation: only ground edges are supported by `composeReductions`
(polymorphic edges throw); the search itself handles polymorphic
endpoints. Threading metavariables from search through term emission is
future work.

## TM-level undecidability

The framework's `Undecidable` is classically vacuous (`¬ ∃ Lean-function-decider`).
For a genuinely meaningful claim:

* `Reduction.TMDecidable`     — `TMDecides`, `TMDecidable`,
                                 `TMUndecidable`, `TMComputable` on
                                 `List Bool → Prop`. Transfer theorem
                                 `TMUndecidable.of_TMReduction` and
                                 composition `TMComputable.comp` are
                                 **axiomatised** (standard TM
                                 constructions, awaiting cslib primitives).
* `Reduction.HaltUndecidable` — bridges `Halt.halt_undecidable` (the
                                 cslib `IsSelfHaltDecider` refutation) to
                                 `TMUndecidable selfHaltPred` (no
                                 postulate). The duplication reduction
                                 `EncodedSelfHalt ≤ₘ EncodedHalt` is
                                 registered with `@[reduction_graph]`,
                                 the anchor with `@[tm_undecidable_anchor]`,
                                 and a postulated `TMComputable`
                                 witness named per the convention
                                 `<reductionName>_TMComputable`.

The `by reduce_diag` tactic dispatches on the goal:

* `Undecidable P` (or `Decidable P → False`) — uses
  `@[undecidable_anchor]` and composes via `ManyOneReduction.trans` +
  `Undecidable.of_manyOne`.
* `TMUndecidable (Problem.predicate P)` — uses
  `@[tm_undecidable_anchor]`, looks up each edge's
  `<edgeName>_TMComputable` witness, and composes via
  `ManyOneReduction.trans` + `TMComputable.comp` +
  `TMUndecidable.of_TMReduction`.

This makes the framework non-vacuous: a real anchor at the TM level
plus a (axiomatised) transfer mechanism that the tactic uses
automatically.
-/
