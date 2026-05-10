/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

/-!
# The Universal Language `Lu` (Halting Problem)

`Lu` is the language

  `{ ⟨M, w⟩ | M is a Turing machine that halts on input w }`.

Its undecidability is the classical *Halting Problem*. We assume this as a
starting point for the reduction chain `Lu ≤_m MPCP ≤_m PCP`.

This file defines the halting predicate `Halts` for CSLib's
`Turing.SingleTapeTM` and proves the basic equivalences used by the
reduction in `PCP.Reductions.LuToMPCP`.
-/

namespace PCP

open Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- `Halts tm w` holds iff `tm` started on input `w` reaches the halting
state (`state = none`) after some finite number of transitions. The
contents of the tape at halt time are existentially quantified — `Halts`
records reachability of *some* halting configuration. -/
def Halts (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩

/-- `HaltsWithinTime tm w n` holds iff `tm` started on input `w` reaches the
halting state in at most `n` steps. -/
def HaltsWithinTime (tm : SingleTapeTM Symbol) (w : List Symbol) (n : ℕ) : Prop :=
  ∃ tape : BiTape Symbol,
    Relation.RelatesWithinSteps tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) ⟨none, tape⟩ n

/-- `Halts` is logically equivalent to halting in some bounded number of
steps. -/
theorem halts_iff_exists_haltsWithinTime (tm : SingleTapeTM Symbol)
    (w : List Symbol) :
    Halts tm w ↔ ∃ n, HaltsWithinTime tm w n := by
  constructor
  · rintro ⟨tape, h⟩
    obtain ⟨n, hn⟩ := h.relatesInSteps
    exact ⟨n, tape, .of_relatesInSteps hn⟩
  · rintro ⟨n, tape, m, _, hm⟩
    exact ⟨tape, hm.reflTransGen⟩

end PCP
