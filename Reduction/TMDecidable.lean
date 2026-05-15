/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Basic
public import PCP.Halt

@[expose] public section

/-!
# TM-level decidability

The framework's `Decidable P` / `Undecidable P` (in `Reduction.Basic`)
are *classically vacuous* — every predicate has a classical Bool-valued
decider, so `Undecidable P` is literally never inhabited classically.
That's useful only as an abstract bookkeeping notion.

This file defines the **TM-level** versions, which are the genuinely
meaningful undecidability claims:

* `TMDecides D pred`     — the `SingleTapeTM Bool` `D` outputs `[true]`
                            on inputs satisfying `pred`, `[false]`
                            otherwise.
* `TMDecidable pred`     — there exists such a `D`.
* `TMUndecidable pred`   — there exists no such `D`.

Notes:

* Restricted to `List Bool → Prop` predicates because cslib's
  `SingleTapeTM Bool` has alphabet `Bool`; the input/output tapes are
  `List Bool`. Other `Problem` types need an encoding to `List Bool`
  first (this is what the `Reduction.Encoded*` modules give us).
* `TMComputable f` is the analogous notion for a function — there
  exists a TM that outputs `f bits` on input `bits`.
* The transfer theorem `TMUndecidable.of_TMReduction` is **axiomatised**
  here. The standard textbook proof is: given a decider `D` for `pred₂`
  and a computer `D_f` for `f`, compose them into a decider for
  `pred₁`. Implementing cslib-level TM composition is tedious bookkeeping
  (substituting state spaces, threading transitions); we postulate the
  result here and revisit if a cslib-level TM-composition primitive
  becomes available.

These notions coexist with the classical `Decidable`/`Undecidable` in
`Reduction.Basic`; the eventual goal is for the headline framework
claims to use `TMUndecidable` and the tactic to operate on it.
-/

namespace DiagonaLean

open PCP Turing

/-! ## TM-level decidability of `List Bool → Prop` predicates -/

/-- `TMDecides D pred`: the `SingleTapeTM Bool` `D` decides `pred` by
emitting `[true]` on inputs satisfying `pred` and `[false]` otherwise. -/
def TMDecides (D : SingleTapeTM Bool) (pred : List Bool → Prop) : Prop :=
  ∀ bits : List Bool,
    (pred bits → SingleTapeTM.Outputs D bits [true]) ∧
    (¬ pred bits → SingleTapeTM.Outputs D bits [false])

/-- TM-decidability of `pred`: some `SingleTapeTM Bool` decides it. -/
def TMDecidable (pred : List Bool → Prop) : Prop :=
  ∃ D : SingleTapeTM Bool, TMDecides D pred

/-- TM-undecidability of `pred`: no `SingleTapeTM Bool` decides it. -/
def TMUndecidable (pred : List Bool → Prop) : Prop :=
  ¬ TMDecidable pred

/-- A function `f : List Bool → List Bool` is TM-computable iff some
`SingleTapeTM Bool` outputs `f bits` on input `bits` for every `bits`. -/
def TMComputable (f : List Bool → List Bool) : Prop :=
  ∃ D : SingleTapeTM Bool, ∀ bits, SingleTapeTM.Outputs D bits (f bits)

/-! ## Transfer theorem (axiomatised) -/

/-- **TM-undecidability transfers along TM-computable reductions.**

Standard textbook proof: given a TM `D` deciding `pred₂` and a TM `D_f`
computing `f`, compose them — the composite decides `pred₁` by running
`D_f` on the input then `D` on the result.

This is **postulated** in this module because cslib does not currently
expose a TM-composition primitive. A direct proof would build the
composite TM by interleaving state spaces and transition relations,
threading the output of `D_f` into the input position of `D`. -/
axiom TMUndecidable.of_TMReduction
    {pred₁ pred₂ : List Bool → Prop}
    (f : List Bool → List Bool)
    (_h_comp : TMComputable f)
    (_h_iff : ∀ bits, pred₁ bits ↔ pred₂ (f bits))
    (_h₁ : TMUndecidable pred₁) :
    TMUndecidable pred₂

/-- **Composition of TM-computable functions.** Postulated for the same
reason as `TMUndecidable.of_TMReduction`: the standard construction
interleaves two TMs' state spaces, but cslib doesn't expose the
primitive yet. -/
axiom TMComputable.comp
    {f g : List Bool → List Bool}
    (_h_f : TMComputable f) (_h_g : TMComputable g) :
    TMComputable (g ∘ f)

/-- **Identity is TM-computable.** A 1-state TM that reads its input
and immediately halts (without modifying the tape) computes the identity.
This is implementable in cslib but axiomatised here for uniformity with
the other TM primitives. -/
axiom TMComputable.id : TMComputable (fun bits : List Bool => bits)

/-! ## Connection to the framework's classical `Undecidable` -/

/-- TM-decidability implies (classical) `Decidable`-style decidability,
since any TM `D` induces a `Bool`-valued Lean function via "run `D` on
the input and read the output". This direction is the easy one. -/
theorem TMDecidable.toDecidable
    {pred : List Bool → Prop} (h : TMDecidable pred) :
    Decidable { Input := List Bool, predicate := pred : Problem } := by
  obtain ⟨_, _⟩ := h
  classical
  refine ⟨fun bits => decide (pred bits), ?_⟩
  intro bits
  by_cases hp : pred bits <;> simp [hp]

/-- Therefore, classical `Undecidable` is **weaker** than `TMUndecidable`:
no Lean function decides ⇒ no TM decides. Since `Undecidable` is
classically vacuous, this direction is useless on its own — but the
contrapositive (`TMUndecidable → Undecidable`?) is **not** valid in
general (a non-TM Lean function might decide a TM-undecidable predicate). -/
theorem Undecidable.of_TMUndecidable
    {pred : List Bool → Prop} :
    Undecidable { Input := List Bool, predicate := pred : Problem } →
    TMUndecidable pred := by
  intro h_undec h_tm_dec
  exact h_undec (TMDecidable.toDecidable h_tm_dec)

end DiagonaLean
