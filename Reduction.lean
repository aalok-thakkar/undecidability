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
public import Reduction.Instances

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
`halts_codeOf_iff`), see `Reduction.Instances` (forthcoming).
-/
