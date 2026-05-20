/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Rice.Extender

@[expose] public section

/-!
# Rice extender bisimulation — phase lemmas

Working toward discharging `semHalt_riceConstTM_dichotomy` (postulated
in `Halt.Rice.Theorem`). The behaviour of `riceConstTM c` on an input
`w` runs in four phases (see `Halt.Rice.Extender`):

1. **erase** — scan right writing blanks until the first blank.
2. **write** — write `encodeTMCode c` left-to-right.
3. **move-back** — return the head to the start of `encodeTMCode c`.
4. **simulate** — run `c.toTM`.

This file proves the phases as standalone lemmas. The headline
dichotomy theorem then composes them.

## Phase 1: erase

The key observation is that cslib's `BiTape`/`StackTape` *trims*
trailing blanks: `StackTape.cons none ∅ = ∅`. So when the erase phase
writes a blank over the head symbol and moves right, the just-blanked
cell is trimmed away — `mk₁ (a :: rest)` steps directly to `mk₁ rest`.
Consequently the erase phase drives `⟨erase, mk₁ w⟩` to
`⟨writeBit 0, ∅⟩` for **every** `w`, so the post-erase configuration is
input-independent. This is what makes `SemHalt (riceConstTM c)` either
`univ` or `∅`.
-/

namespace Halt.Rice

open Turing PCP Relation

variable (c : Halt.TMCode)

/-! ### `BiTape` erase step -/

/-- Writing a blank over the head of `mk₁ (a :: rest)` and moving right
yields `mk₁ rest`: the blanked cell is trimmed by `StackTape.cons`. -/
lemma biTape_writeNone_moveRight_mk₁_cons (a : Bool) (rest : List Bool) :
    ((BiTape.mk₁ (a :: rest)).write none).optionMove (some Dir.right) =
      BiTape.mk₁ rest := by
  cases rest with
  | nil => rfl
  | cons b rest' => rfl

/-! ### Erase-phase single steps -/

/-- An erase step over a non-empty tape: `⟨erase, mk₁ (a :: rest)⟩`
transitions to `⟨erase, mk₁ rest⟩`. -/
lemma erase_step_cons (a : Bool) (rest : List Bool) :
    (riceConstTM c).step ⟨some RiceState.erase, BiTape.mk₁ (a :: rest)⟩ =
      some ⟨some RiceState.erase, BiTape.mk₁ rest⟩ := by
  show (riceConstTM c).step ⟨some RiceState.erase, BiTape.mk₁ (a :: rest)⟩ = _
  have h_head : (BiTape.mk₁ (a :: rest)).head = some a := rfl
  simp only [SingleTapeTM.step, riceConstTM, riceTr, h_head]
  rw [biTape_writeNone_moveRight_mk₁_cons]

/-- An erase step over the empty tape: `⟨erase, ∅⟩` transitions to the
write phase `⟨writeBit 0, ∅⟩`. -/
lemma erase_step_nil :
    (riceConstTM c).step ⟨some RiceState.erase, BiTape.nil⟩ =
      some ⟨some (RiceState.writeBit ⟨0, encodedLen_pos c⟩), BiTape.nil⟩ := by
  rfl

/-! ### Phase 1 lemma -/

/-- **Erase phase.** From the initial configuration `⟨erase, mk₁ w⟩`,
`riceConstTM c` reaches `⟨writeBit 0, ∅⟩` — the start of the write
phase — for *every* input `w`. -/
theorem erase_phase (w : List Bool) :
    ReflTransGen (riceConstTM c).TransitionRelation
      ⟨some RiceState.erase, BiTape.mk₁ w⟩
      ⟨some (RiceState.writeBit ⟨0, encodedLen_pos c⟩), BiTape.nil⟩ := by
  induction w with
  | nil =>
    exact ReflTransGen.single (erase_step_nil c)
  | cons a rest ih =>
    refine ReflTransGen.head ?_ ih
    exact erase_step_cons c a rest

end Halt.Rice
