/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Notation
public import Reduction.StackMap
public import Reduction.EncodedPCP
public import Halt.Pair
public import Halt.TMCode
public import PCP.Basic
public import PCP.MPCP
public import PCP.Reductions.HaltToMPCP

@[expose] public section

/-!
# `EncodedHaltMPCP` → `MPCP_LB`: closing the alphabet shift

The HMU `Halt ≤ MPCP` reduction `halt_le_mpcp` is stated over the
TM-dependent simulation alphabet `PCP.HaltToMPCP.Alpha tm.State Symbol`
and is gated by `NoBlankWrites tm ∧ NoLeftBoundary tm w`. To wire this
into the DiagonaLean graph with a *fixed* `List Bool` input, we:

1. Encode `Alpha (Fin (n+1)) Bool → List Bool` via `encodeAlpha` (a
   tag-prefix injection). Combined with `StackMap.mhasSolution_mapStack_iff`
   this collapses the TM-dependent alphabet to `List Bool`.
2. Define `EncodedHaltMPCP`: input `List Bool`, predicate "decode to
   `(c, w)` with `c.toTM` *normalised* (NBW + NLB) and halting on `w`".
3. Build the reduction `EncodedHaltMPCP ≤ₘ MPCP_LB`: decode, check the
   normalisation conditions, then output the `(startTile, haltTiles)`
   pair under `mapTile`/`mapStack` of `encodeAlpha`. Inputs that decode
   to non-normalised TMs (or fail to decode) map to a fixed sentinel
   `(Tile, Stack)` pair with no solution.

The remaining edge `EncodedHalt ≤ₘ EncodedHaltMPCP` is the TM
normalisation step (a standard textbook construction; deferred).

## Contents

* `encodeAlpha`, `encodeAlpha_injective` — the alphabet encoding.
* `noSolutionSentinel`, `not_mhasSolution_noSolutionSentinel` — sentinel
  for the malformed-input branches of the reduction.
* `Problems.EncodedHaltMPCP` — the encoded halt problem restricted to
  normalised TMs.
* `Reductions.encodedHaltMPCP_to_mpcpLB` — the canonical edge.
-/

namespace DiagonaLean

open PCP PCP.HaltToMPCP Halt

/-! ## `encodeAlpha`: injection `Alpha (Fin (n+1)) Bool → List Bool` -/

/-- Encode each `Alpha (Fin (n+1)) Bool` symbol as a `List Bool` with a
distinguishing tag prefix.

* `tape none`         ↦ `[false, false, false]`
* `tape (some false)` ↦ `[false, false, true, false]`
* `tape (some true)`  ↦ `[false, false, true, true]`
* `state q`           ↦ `false :: true :: encodeFin q`
* `halt`              ↦ `[true, false]`
* `sep`               ↦ `[true, true]`

The 1-bit prefix splits tape/state from halt/sep; the 2nd bit splits
tape from state, halt from sep. Within `tape`, the 3rd bit splits
`none` from `some _`. Within `state`, `encodeFin` (unary with `false`
terminator) is itself injective. -/
def encodeAlpha {n : ℕ} : Alpha (Fin (n+1)) Bool → List Bool
  | .tape none         => [false, false, false]
  | .tape (some false) => [false, false, true, false]
  | .tape (some true)  => [false, false, true, true]
  | .state q           => false :: true :: Halt.Encoding.encodeFin q
  | .halt              => [true, false]
  | .sep               => [true, true]

/-- Left inverse of `encodeAlpha`. Reads a tag prefix and dispatches.
The `n` parameter is needed for `decodeFin`. -/
def decodeAlpha (n : ℕ) : List Bool →
    Option (Alpha (Fin (n+1)) Bool × List Bool)
  | false :: false :: false :: rest =>
      some (.tape none, rest)
  | false :: false :: true :: false :: rest =>
      some (.tape (some false), rest)
  | false :: false :: true :: true :: rest =>
      some (.tape (some true), rest)
  | false :: true :: rest =>
      match Halt.Encoding.decodeFin (n+1) rest with
      | some (q, rest') => some (.state q, rest')
      | none => none
  | true :: false :: rest => some (.halt, rest)
  | true :: true :: rest => some (.sep, rest)
  | _ => none

@[simp] lemma decodeAlpha_encodeAlpha_append {n : ℕ}
    (a : Alpha (Fin (n+1)) Bool) (rest : List Bool) :
    decodeAlpha n (encodeAlpha a ++ rest) = some (a, rest) := by
  cases a with
  | tape ob =>
    cases ob with
    | none => rfl
    | some b => cases b <;> rfl
  | state q =>
    show decodeAlpha n (false :: true :: Halt.Encoding.encodeFin q ++ rest) =
      some (.state q, rest)
    simp only [List.cons_append, decodeAlpha,
      Halt.Encoding.decodeFin_encodeFin_append]
  | halt => rfl
  | sep => rfl

lemma decodeAlpha_encodeAlpha {n : ℕ} (a : Alpha (Fin (n+1)) Bool) :
    decodeAlpha n (encodeAlpha a) = some (a, []) := by
  have := decodeAlpha_encodeAlpha_append a []
  simpa using this

lemma encodeAlpha_injective {n : ℕ} :
    Function.Injective (@encodeAlpha n) := by
  intro a b h
  have hb := decodeAlpha_encodeAlpha (n := n) b
  rw [← h, decodeAlpha_encodeAlpha] at hb
  injection hb with hb_pair
  exact ((Prod.mk.injEq ..).mp hb_pair).1

/-! ## Sentinel `(Tile, Stack)` with no `MHasSolution` -/

/-- A fixed `(Tile, Stack)` pair over `List Bool` whose predicate
`MHasSolution` is `False`. The tile has empty top and a single-symbol
bot (the symbol being the word `[true]`); the stack is empty. Used for
the malformed-input branches of `encodedHaltMPCP_to_mpcpLB`. -/
def noSolutionSentinel : Tile (List Bool) × Stack (List Bool) :=
  (⟨[], [[true]]⟩, [])

lemma not_mhasSolution_noSolutionSentinel :
    ¬ MHasSolution noSolutionSentinel.1 noSolutionSentinel.2 := by
  rintro ⟨A, h_in, h_eq⟩
  have h_in' : ∀ t ∈ A, t = ⟨[], [[true]]⟩ := by
    intro t ht
    have := h_in t ht
    simp [noSolutionSentinel] at this
    exact this
  have aux : ∀ (A' : Stack (List Bool)),
      (∀ t ∈ A', t = ⟨[], [[true]]⟩) → tau1 A' = [] := by
    intro A' h
    induction A' with
    | nil => rfl
    | cons t ts ih =>
      have ht_eq : t = ⟨[], [[true]]⟩ := h t (by simp)
      have h_ts : ∀ t' ∈ ts, t' = ⟨[], [[true]]⟩ :=
        fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
      show t.top ++ tau1 ts = []
      rw [ht_eq, ih h_ts]
      rfl
  have h_tau1 : tau1 A = [] := aux A h_in'
  show False
  have h_top : noSolutionSentinel.1.top = ([] : List (List Bool)) := rfl
  have h_bot : noSolutionSentinel.1.bot = [[true]] := rfl
  rw [h_top, h_bot, h_tau1] at h_eq
  exact List.cons_ne_nil _ _ h_eq.symm

end DiagonaLean

/-! ## `Problem` and reduction -/

namespace DiagonaLean.Problems

open PCP PCP.HaltToMPCP

/-- The "MPCP-reducible halt" problem: input is bits encoding a pair
`(codeBits, w)` such that `codeBits` decodes to a `TMCode c` whose
realised TM `c.toTM` satisfies `NoBlankWrites` and `NoLeftBoundary` on
`w`, and halts on `w`.

The normalisation conditions are part of the predicate so that
`halt_le_mpcp` applies directly. The downstream edge `EncodedHalt ≤ₘ
EncodedHaltMPCP` (TM normalisation) remains to be wired in (TODO). -/
def EncodedHaltMPCP : Problem where
  Input := List Bool
  predicate := fun bits =>
    match Halt.Pair.decodePair bits with
    | none => False
    | some (codeBits, w) =>
      match Halt.Encoding.decodeTMCode codeBits with
      | none => False
      | some c =>
        NoBlankWrites c.toTM ∧ NoLeftBoundary c.toTM w ∧ PCP.Halts c.toTM w

end DiagonaLean.Problems

namespace DiagonaLean.Reductions

open DiagonaLean DiagonaLean.Problems PCP PCP.HaltToMPCP
open scoped Classical

/-- The reducing function. Decodes the bits to `(c, w)`; if `c.toTM` is
normalised, returns the `(startTile, haltTiles)` pair under
`mapTile`/`mapStack` of `encodeAlpha`. Otherwise returns the
`noSolutionSentinel`. -/
noncomputable def encodedHaltMPCP_to_mpcpLB_f
    (bits : List Bool) : Tile (List Bool) × Stack (List Bool) :=
  match Halt.Pair.decodePair bits with
  | none => DiagonaLean.noSolutionSentinel
  | some (codeBits, w) =>
    match Halt.Encoding.decodeTMCode codeBits with
    | none => DiagonaLean.noSolutionSentinel
    | some c =>
      if _h_norm : NoBlankWrites c.toTM ∧ NoLeftBoundary c.toTM w then
        (StackMap.mapTile (@DiagonaLean.encodeAlpha c.numStates)
          (PCP.HaltToMPCP.startTile c.toTM w),
         StackMap.mapStack (@DiagonaLean.encodeAlpha c.numStates)
          (PCP.HaltToMPCP.haltTiles c.toTM))
      else
        DiagonaLean.noSolutionSentinel

/-- `EncodedHaltMPCP ≤ₘ MPCP_LB`: the canonical edge, composing
`halt_le_mpcp` with `StackMap.mhasSolution_mapStack_iff` at
`σ = encodeAlpha`. Malformed or non-normalised inputs route to
`noSolutionSentinel`, whose `MHasSolution` is `False`. -/
noncomputable def encodedHaltMPCP_to_mpcpLB :
    ManyOneReduction EncodedHaltMPCP MPCP_LB where
  f := encodedHaltMPCP_to_mpcpLB_f
  spec := fun bits => by
    show (match Halt.Pair.decodePair bits with
      | none => False
      | some (codeBits, w) =>
        match Halt.Encoding.decodeTMCode codeBits with
        | none => False
        | some c =>
          NoBlankWrites c.toTM ∧ NoLeftBoundary c.toTM w ∧
            PCP.Halts c.toTM w) ↔
      MHasSolution (encodedHaltMPCP_to_mpcpLB_f bits).1
                   (encodedHaltMPCP_to_mpcpLB_f bits).2
    unfold encodedHaltMPCP_to_mpcpLB_f
    split
    case h_1 => -- decodePair = none
      refine ⟨False.elim, fun h => ?_⟩
      exact (DiagonaLean.not_mhasSolution_noSolutionSentinel h).elim
    case h_2 codeBits w h_pair => -- decodePair = some (codeBits, w)
      split
      case h_1 => -- decodeTMCode = none
        refine ⟨False.elim, fun h => ?_⟩
        exact (DiagonaLean.not_mhasSolution_noSolutionSentinel h).elim
      case h_2 c h_code => -- decodeTMCode = some c
        by_cases h_norm : NoBlankWrites c.toTM ∧ NoLeftBoundary c.toTM w
        · rw [dif_pos h_norm,
            StackMap.mhasSolution_mapStack_iff
              (DiagonaLean.encodeAlpha_injective)]
          refine ⟨fun ⟨_, _, h_halts⟩ => ?_, fun h_mhas => ?_⟩
          · exact (halt_le_mpcp c.toTM h_norm.1 w h_norm.2).mp h_halts
          · exact ⟨h_norm.1, h_norm.2,
              (halt_le_mpcp c.toTM h_norm.1 w h_norm.2).mpr h_mhas⟩
        · rw [dif_neg h_norm]
          refine ⟨fun ⟨h_nbw, h_nlb, _⟩ => ?_, fun h => ?_⟩
          · exact (h_norm ⟨h_nbw, h_nlb⟩).elim
          · exact (DiagonaLean.not_mhasSolution_noSolutionSentinel h).elim

end DiagonaLean.Reductions
