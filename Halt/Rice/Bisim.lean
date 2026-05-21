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

/-! ## Phase 2: write

The write phase lays `encodeTMCode c` onto the tape one bit at a time,
moving right after each write. After `k` bits the tape is `writtenTape
c k`: head blank, the first `k` bits sit *reversed* on the left stack
(`map_some` — all `some`, so no trimming), right stack empty. -/

/-- `StackTape.map_some` of a cons is a `cons` of `map_some`. -/
lemma map_some_cons (x : Bool) (xs : List Bool) :
    StackTape.map_some (x :: xs) =
      StackTape.cons (some x) (StackTape.map_some xs) := rfl

/-- The tape after the write phase has placed the first `k` bits of
`encodeTMCode c`. -/
def writtenTape (c : Halt.TMCode) (k : ℕ) : BiTape Bool :=
  ⟨none, StackTape.map_some ((Halt.Encoding.encodeTMCode c).take k).reverse, ∅⟩

lemma writtenTape_zero : writtenTape c 0 = BiTape.nil := rfl

/-- Writing bit `k` over the (blank) head of `writtenTape c k` and
moving right yields `writtenTape c (k+1)`. -/
lemma writtenTape_step (k : ℕ) (hk : k < encodedLen c) :
    ((writtenTape c k).write (some (encodedBit c ⟨k, hk⟩))).optionMove
        (some Dir.right) =
      writtenTape c (k + 1) := by
  have h_len : k < (Halt.Encoding.encodeTMCode c).length := hk
  have h_take : (Halt.Encoding.encodeTMCode c).take (k + 1) =
      (Halt.Encoding.encodeTMCode c).take k ++
        [(Halt.Encoding.encodeTMCode c).get ⟨k, h_len⟩] := by
    rw [List.take_succ]
    congr 1
    rw [List.getElem?_eq_getElem h_len]
    rfl
  show (⟨some (encodedBit c ⟨k, hk⟩),
          StackTape.map_some ((Halt.Encoding.encodeTMCode c).take k).reverse,
          ∅⟩ : BiTape Bool).move_right = writtenTape c (k + 1)
  show (⟨none, StackTape.cons (some (encodedBit c ⟨k, hk⟩))
          (StackTape.map_some ((Halt.Encoding.encodeTMCode c).take k).reverse),
          ∅⟩ : BiTape Bool) = writtenTape c (k + 1)
  unfold writtenTape
  rw [h_take, List.reverse_append, List.reverse_singleton,
      List.singleton_append, map_some_cons]
  rfl

/-- A write step at a *non-final* index `k` (`k+1 < encodedLen c`):
move to `writeBit (k+1)`. -/
lemma writeBit_step_mid (k : ℕ) (hk : k < encodedLen c)
    (hk1 : k + 1 < encodedLen c) :
    (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ =
      some ⟨some (RiceState.writeBit ⟨k + 1, hk1⟩), writtenTape c (k + 1)⟩ := by
  show (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ = _
  have h_head : (writtenTape c k).head = none := rfl
  simp only [SingleTapeTM.step, riceConstTM, riceTr, h_head, dif_pos hk1]
  rw [writtenTape_step]

/-- A write step at the *final* index `k` (`k+1 = encodedLen c`): move
to `moveBack (encodedLen c)`. -/
lemma writeBit_step_last (k : ℕ) (hk : k < encodedLen c)
    (hk1 : k + 1 = encodedLen c) :
    (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ =
      some ⟨some (RiceState.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩),
              writtenTape c (k + 1)⟩ := by
  show (riceConstTM c).step ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩ = _
  have h_head : (writtenTape c k).head = none := rfl
  have h_not : ¬ (k + 1 < encodedLen c) := by omega
  simp only [SingleTapeTM.step, riceConstTM, riceTr, h_head, dif_neg h_not]
  rw [writtenTape_step]

/-- Induction core for the write phase: from `⟨writeBit k, writtenTape
c k⟩`, with `d` bits still to write, reach the move-back phase. -/
private lemma write_phase_aux (d : ℕ) :
    ∀ (k : ℕ) (hk : k < encodedLen c), k + d + 1 = encodedLen c →
      ReflTransGen (riceConstTM c).TransitionRelation
        ⟨some (RiceState.writeBit ⟨k, hk⟩), writtenTape c k⟩
        ⟨some (RiceState.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩),
          writtenTape c (encodedLen c)⟩ := by
  induction d with
  | zero =>
    intro k hk hd
    have hk1 : k + 1 = encodedLen c := by omega
    have h_step := writeBit_step_last c k hk hk1
    rw [hk1] at h_step
    exact ReflTransGen.single h_step
  | succ d ih =>
    intro k hk hd
    have hk1 : k + 1 < encodedLen c := by omega
    refine ReflTransGen.head (writeBit_step_mid c k hk hk1) ?_
    exact ih (k + 1) hk1 (by omega)

/-- **Write phase.** From `⟨writeBit 0, ∅⟩`, `riceConstTM c` reaches
`⟨moveBack (encodedLen c), writtenTape c (encodedLen c)⟩` — the start
of the move-back phase, with `encodeTMCode c` fully laid down. -/
theorem write_phase :
    ReflTransGen (riceConstTM c).TransitionRelation
      ⟨some (RiceState.writeBit ⟨0, encodedLen_pos c⟩), BiTape.nil⟩
      ⟨some (RiceState.moveBack ⟨encodedLen c, Nat.lt_succ_self _⟩),
        writtenTape c (encodedLen c)⟩ := by
  have h := write_phase_aux c (encodedLen c - 1) 0 (encodedLen_pos c)
    (by have := encodedLen_pos c; omega)
  rwa [writtenTape_zero] at h

end Halt.Rice
