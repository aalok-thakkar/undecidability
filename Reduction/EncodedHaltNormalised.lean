/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Reduction.Graph
public import Reduction.Encoded
public import Reduction.EncodedHaltMPCP
public import Halt.Normalise

@[expose] public section

/-!
# `EncodedHalt ≤ₘ EncodedHaltMPCP` via the normalising wrapper

Closes the long-standing HUM-normalisation gap: given any
`(c : TMCode, w : List Bool)` pair, apply
`DiagonaLean.normalisingWrapper.wrap c w` to obtain a *normalised*
`(c', w')` satisfying `NoBlankWrites c'.toTM ∧ NoLeftBoundary c'.toTM w'`,
with `Halts c'.toTM w' ↔ Halts c.toTM w`.

The reduction is then `bits ↦ encodePair (encodeTMCode c') w'` after
decoding. Malformed inputs route to `[]`, which fails both predicates
(empty bits don't decode).

The single substantive postulate this depends on — `normalisingWrapper`
in `Halt/Normalise.lean` — captures the standard textbook
sentinel-shift / blank-replacement construction.
-/

namespace DiagonaLean.Reductions

open DiagonaLean DiagonaLean.Problems PCP PCP.HaltToMPCP Halt

/-! ## The reducing function -/

/-- Decode bits to `(c, w)`, run the normalising wrapper, re-encode. -/
noncomputable def encodedHalt_to_encodedHaltMPCP_f (bits : List Bool) : List Bool :=
  match Halt.Pair.decodePair bits with
  | none => []
  | some (codeBits, w) =>
    match Halt.Encoding.decodeTMCode codeBits with
    | none => []
    | some c =>
      let (c', w') := normalisingWrapper.wrap c w
      Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c') w'

/-! ## The reduction -/

/-- `EncodedHalt ≤ₘ EncodedHaltMPCP` via the HUM-normalising wrapper.
The wrapper provides NBW + NLB by construction; the iff is
`Halts c.toTM w ↔ Halts c'.toTM w' ↔ NBW c' ∧ NLB c' w' ∧ Halts c' w'`. -/
@[reduction_graph]
noncomputable def encodedHalt_to_encodedHaltMPCP :
    ManyOneReduction EncodedHalt EncodedHaltMPCP where
  f := encodedHalt_to_encodedHaltMPCP_f
  spec := fun bits => by
    show (match Halt.Pair.decodePair bits with
            | none => False
            | some (codeBits, w) =>
              match Halt.Encoding.decodeTMCode codeBits with
              | none => False
              | some c => PCP.Halts c.toTM w) ↔
      EncodedHaltMPCP.predicate (encodedHalt_to_encodedHaltMPCP_f bits)
    unfold encodedHalt_to_encodedHaltMPCP_f
    have h_empty_pred : ¬ EncodedHaltMPCP.predicate [] := by
      show ¬ (match Halt.Pair.decodePair ([] : List Bool) with
        | none => False
        | some (codeBits, w) =>
          match Halt.Encoding.decodeTMCode codeBits with
          | none => False
          | some c =>
            NoBlankWrites c.toTM ∧ NoLeftBoundary c.toTM w ∧ PCP.Halts c.toTM w)
      have : Halt.Pair.decodePair ([] : List Bool) = none := rfl
      rw [this]
      exact id
    split
    case h_1 =>
      exact ⟨False.elim, fun h => (h_empty_pred h).elim⟩
    case h_2 codeBits w h_pair =>
      split
      case h_1 =>
        exact ⟨False.elim, fun h => (h_empty_pred h).elim⟩
      case h_2 c h_code =>
        -- Successful decode: apply the wrapper.
        set cw' := normalisingWrapper.wrap c w with hcw
        show PCP.Halts c.toTM w ↔
          (match Halt.Pair.decodePair
                  (Halt.Pair.encodePair
                    (Halt.Encoding.encodeTMCode cw'.1) cw'.2) with
            | none => False
            | some (codeBits, w_in) =>
              match Halt.Encoding.decodeTMCode codeBits with
              | none => False
              | some c' =>
                NoBlankWrites c'.toTM ∧ NoLeftBoundary c'.toTM w_in ∧
                  PCP.Halts c'.toTM w_in)
        rw [Halt.Pair.decodePair_encodePair]
        change PCP.Halts c.toTM w ↔
          (match Halt.Encoding.decodeTMCode (Halt.Encoding.encodeTMCode cw'.1) with
            | none => False
            | some c' =>
              NoBlankWrites c'.toTM ∧ NoLeftBoundary c'.toTM cw'.2 ∧
                PCP.Halts c'.toTM cw'.2)
        rw [Halt.Encoding.decodeTMCode_encodeTMCode]
        refine ⟨fun h => ?_, fun ⟨_, _, h⟩ => ?_⟩
        · refine ⟨normalisingWrapper.no_blank_writes c w,
                  normalisingWrapper.no_left_boundary c w, ?_⟩
          exact (normalisingWrapper.halts_iff c w).mpr h
        · exact (normalisingWrapper.halts_iff c w).mp h

/-- Postulate: the reduction function is TM-computable.
`encodedHalt_to_encodedHaltMPCP_f` decodes a bit-string, runs the
normalising wrapper (a TM-computable construction), and re-encodes — a
standard transformation. -/
axiom encodedHalt_to_encodedHaltMPCP_TMComputable :
    TMComputable encodedHalt_to_encodedHaltMPCP.f

end DiagonaLean.Reductions
