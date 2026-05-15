/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Notation
public import PCP.Basic
public import PCP.MPCP
public import PCP.Reduction

@[expose] public section

/-!
# Encoded PCP: alphabet flattening to `List Bool`

The standard `mpcpToPcp : Tile α → Stack α → Stack (Ext α)` shifts the
alphabet from `α` to `Ext α`. For the DiagonaLean reduction graph to
have stable node identities, we collapse `Ext (List Bool)` back to
`List Bool` via an injective per-symbol encoding `flattenExt` and a
solution-preservation iff for the induced stack-level map.

## Roadmap

* `flattenExt : Ext (List Bool) → List Bool` — injective per-symbol
  encoding (`sym l ↦ false :: l`; `hash ↦ [true, false]`;
  `dollar ↦ [true, true]`).
* `flattenTile`, `flattenStack` — lift to tiles and stacks.
* `tau1_flattenStack`, `tau2_flattenStack` — `tau (flatten P) = (tau P).map flatten`.
* `hasSolution_flattenStack_iff` — solution preservation.
* `Problems.MPCP_LB`, `Problems.EncodedPCP` — fixed-Input `Problem`s.
* `Reductions.mpcpLB_to_encodedPCP` — the `MPCP_LB ≤ₘ EncodedPCP`
  edge, composing `mpcp_iff_pcp` (at `α = List Bool`) with the
  flatten preservation.
-/

namespace DiagonaLean

open PCP

/-! ## `flattenExt`: injective encoding of `Ext (List Bool)` -/

/-- Encode each `Ext (List Bool)` symbol as a `List Bool` with a
distinguishing prefix bit. Injective. -/
def flattenExt : PCP.Ext (List Bool) → List Bool
  | .sym l    => false :: l
  | .hash     => [true, false]
  | .dollar   => [true, true]

lemma flattenExt_injective : Function.Injective flattenExt := by
  intro a b h
  cases a <;> cases b <;> simp_all [flattenExt]

/-! ## `flattenTile`, `flattenStack`: lift to stacks -/

/-- Apply `flattenExt` to each symbol in a tile. -/
def flattenTile (t : PCP.Tile (PCP.Ext (List Bool))) :
    PCP.Tile (List Bool) where
  top := t.top.map flattenExt
  bot := t.bot.map flattenExt

@[simp] lemma flattenTile_top (t : PCP.Tile (PCP.Ext (List Bool))) :
    (flattenTile t).top = t.top.map flattenExt := rfl

@[simp] lemma flattenTile_bot (t : PCP.Tile (PCP.Ext (List Bool))) :
    (flattenTile t).bot = t.bot.map flattenExt := rfl

lemma flattenTile_injective : Function.Injective flattenTile := by
  intro a b h
  obtain ⟨at_top, at_bot⟩ := a
  obtain ⟨bt_top, bt_bot⟩ := b
  simp [flattenTile] at h
  obtain ⟨h_top, h_bot⟩ := h
  have h_top' := List.map_injective_iff.mpr flattenExt_injective h_top
  have h_bot' := List.map_injective_iff.mpr flattenExt_injective h_bot
  rw [h_top', h_bot']

/-- Apply `flattenTile` to each tile in a stack. -/
def flattenStack (P : PCP.Stack (PCP.Ext (List Bool))) :
    PCP.Stack (List Bool) :=
  P.map flattenTile

lemma flattenStack_injective : Function.Injective flattenStack := by
  intro P P' h
  exact List.map_injective_iff.mpr flattenTile_injective h

/-! ## `tau1`/`tau2` commute with `flattenStack` -/

@[simp] lemma tau1_flattenStack (P : PCP.Stack (PCP.Ext (List Bool))) :
    PCP.tau1 (flattenStack P) = (PCP.tau1 P).map flattenExt := by
  induction P with
  | nil => rfl
  | cons t ts ih =>
    show PCP.tau1 (flattenTile t :: flattenStack ts) = _
    rw [PCP.tau1_cons, PCP.tau1_cons, List.map_append, flattenTile_top, ih]

@[simp] lemma tau2_flattenStack (P : PCP.Stack (PCP.Ext (List Bool))) :
    PCP.tau2 (flattenStack P) = (PCP.tau2 P).map flattenExt := by
  induction P with
  | nil => rfl
  | cons t ts ih =>
    show PCP.tau2 (flattenTile t :: flattenStack ts) = _
    rw [PCP.tau2_cons, PCP.tau2_cons, List.map_append, flattenTile_bot, ih]

/-! ## Solution preservation -/

/-- A solution to `P` lifts to a solution to `flattenStack P` via
`flattenStack`. -/
private lemma hasSolution_flattenStack_of_hasSolution
    {P : PCP.Stack (PCP.Ext (List Bool))} (h : PCP.HasSolution P) :
    PCP.HasSolution (flattenStack P) := by
  obtain ⟨A, h_ne, h_in, h_eq⟩ := h
  refine ⟨flattenStack A, ?_, ?_, ?_⟩
  · intro h_empty
    apply h_ne
    have : flattenStack A = [] := h_empty
    unfold flattenStack at this
    exact List.map_eq_nil_iff.mp this
  · intro t ht
    rcases List.mem_map.mp ht with ⟨t', ht'_mem, ht'_eq⟩
    subst ht'_eq
    exact List.mem_map_of_mem (h_in t' ht'_mem)
  · rw [tau1_flattenStack, tau2_flattenStack, h_eq]

/-- The reverse direction: a solution to `flattenStack P` descends to
a solution to `P`. The lift uses classical choice to pick a preimage
for each tile (preimages exist because every tile in the flat solution
is in `flattenStack P = P.map flattenTile`). -/
private lemma hasSolution_of_hasSolution_flattenStack
    {P : PCP.Stack (PCP.Ext (List Bool))}
    (h : PCP.HasSolution (flattenStack P)) :
    PCP.HasSolution P := by
  obtain ⟨flatA, h_ne, h_in, h_eq⟩ := h
  -- Pre-image function: each tile in flatA has a preimage in P.
  have h_pre : ∀ t ∈ flatA, ∃ t' : PCP.Tile (PCP.Ext (List Bool)),
      t' ∈ P ∧ flattenTile t' = t :=
    fun t ht => List.mem_map.mp (h_in t ht)
  -- Build A by classical choice.
  -- Pick a preimage for each tile in flatA via classical choice.
  let pick : (t : PCP.Tile (List Bool)) → t ∈ flatA →
      PCP.Tile (PCP.Ext (List Bool)) := fun t ht => Classical.choose (h_pre t ht)
  have h_pick_mem : ∀ t (ht : t ∈ flatA), pick t ht ∈ P := fun t ht =>
    (Classical.choose_spec (h_pre t ht)).1
  have h_pick_flat : ∀ t (ht : t ∈ flatA), flattenTile (pick t ht) = t := fun t ht =>
    (Classical.choose_spec (h_pre t ht)).2
  let A : PCP.Stack (PCP.Ext (List Bool)) :=
    flatA.attach.map (fun s => pick s.1 s.2)
  have h_len : A.length = flatA.length := by simp [A]
  have h_flat : flattenStack A = flatA := by
    have : flattenStack A
        = flatA.attach.map (fun s => flattenTile (pick s.1 s.2)) := by
      simp [flattenStack, A, List.map_map, Function.comp]
    rw [this]
    have h_fn : (fun (s : {t // t ∈ flatA}) => flattenTile (pick s.1 s.2)) =
        (Subtype.val) := by
      funext s
      exact h_pick_flat s.1 s.2
    rw [h_fn, List.attach_map_subtype_val]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro h_e
    apply h_ne
    rw [← h_flat, h_e]
    rfl
  · intro t ht
    simp only [A, List.mem_map, List.mem_attach, true_and] at ht
    obtain ⟨⟨t', ht'_mem⟩, ht'_eq⟩ := ht
    rw [← ht'_eq]
    exact h_pick_mem t' ht'_mem
  · have h_tau : (PCP.tau1 A).map flattenExt = (PCP.tau2 A).map flattenExt := by
      rw [← tau1_flattenStack, ← tau2_flattenStack, h_flat]
      exact h_eq
    exact List.map_injective_iff.mpr flattenExt_injective h_tau

/-- **Flatten preservation**: `flattenStack P` has a solution iff `P`
does. -/
theorem hasSolution_flattenStack_iff
    (P : PCP.Stack (PCP.Ext (List Bool))) :
    PCP.HasSolution (flattenStack P) ↔ PCP.HasSolution P :=
  ⟨hasSolution_of_hasSolution_flattenStack, hasSolution_flattenStack_of_hasSolution⟩

end DiagonaLean

/-! ## `Problem` definitions and the reduction -/

namespace DiagonaLean.Problems

open PCP

/-- The MPCP problem at alphabet `List Bool`. Input is a (start-tile,
stack) pair; predicate is `MHasSolution`. Specific instantiation of
`MPCP α` from `Reduction.Instances` at `α := List Bool`. -/
def MPCP_LB : Problem where
  Input := Tile (List Bool) × Stack (List Bool)
  predicate := fun ⟨c, P⟩ => MHasSolution c P

/-- The encoded PCP problem at alphabet `List Bool`. Input is a Stack
over `List Bool`; predicate is `HasSolution`. -/
def EncodedPCP : Problem where
  Input := Stack (List Bool)
  predicate := HasSolution

end DiagonaLean.Problems

namespace DiagonaLean.Reductions

open DiagonaLean.Problems

/-- `MPCP_LB ≤ₘ EncodedPCP`: compose `mpcp_iff_pcp` at `α = List Bool`
with the `flattenStack` solution-preservation. The reducing function
is `(c, P) ↦ flattenStack (mpcpToPcp c P)`. -/
def mpcpLB_to_encodedPCP : ManyOneReduction MPCP_LB EncodedPCP where
  f := fun ⟨c, P⟩ => DiagonaLean.flattenStack (PCP.mpcpToPcp c P)
  spec := fun ⟨c, P⟩ => by
    show PCP.MHasSolution c P ↔
      PCP.HasSolution (DiagonaLean.flattenStack (PCP.mpcpToPcp c P))
    rw [DiagonaLean.hasSolution_flattenStack_iff]
    exact PCP.mpcp_iff_pcp c P

end DiagonaLean.Reductions
