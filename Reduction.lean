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
public import Reduction.Instances
public import Reduction.Encoded
public import Reduction.StackMap
public import Reduction.EncodedPCP
public import Reduction.EncodedHaltMPCP
public import Reduction.EncodedCFG

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

Term emission (Component 3) — composing the path into a
`Undecidable target` proof via `Undecidable.of_manyOne` — is planned next.
-/
