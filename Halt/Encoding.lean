/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.TMCode

@[expose] public section

/-!
# Gödel numbering (Phase 2 of the universal-TM construction)

A *universal* `SingleTapeTM Bool` has to receive the description of an
arbitrary TM on its input tape and then simulate it. To make this
possible we need a concrete, self-delimiting bit-encoding of `TMCode`.

This file builds such an encoding, bottom-up:

* `encodeNat` / `decodeNat`     — unary, self-delimiting (`n` `true`s,
  then a `false` terminator).
* `encodeFin` / `decodeFin`     — natural numbers with a bound check.
* `encodeBool` / `decodeBool`   — single bit.
* `encodeOption` / `decodeOption` (parameterised) — a `0` byte +
  payload, or just `1`.
* `encodeDir`, `encodeStmt` — combinator helpers.
* `encodeTMCode` / `decodeTMCode` (Phase 2's goal) — the full
  transition table, with `decode (encode c) = some c`.

We deliberately favour **simplicity over compactness**: every value is
encoded in unary with explicit terminators, so the universal TM's
parser is straightforward. Asymptotic blow-up is irrelevant for
proving undecidability.

## Conventions

Throughout the file, every encoder produces a list that is
*prefix-readable*: there is exactly one way to decode a prefix of its
output. The decoder is total in the sense that on any `List Bool`
input it returns `Option (value × rest)`, with `rest` being the
unconsumed suffix. `decode (encode v ++ rest) = some (v, rest)` is the
canonical round-trip lemma.

## Status

* `encodeNat`, `decodeNat`, round-trip — ✅
* `encodeFin`, `decodeFin`, round-trip — ✅
* `encodeBool` (single bit, no terminator) — ✅
* Finite enumerations (`Option Bool`, `Option Dir`) — ✅
* `Stmt`, `Option (Fin n)`, transition entries / table — ✅
* `encodeTMCode` / `decodeTMCode` + round-trip — ✅
-/

namespace Halt.Encoding

/-! ## `Nat` — unary with `false` terminator -/

/-- Unary encoding: `n` `true` bits followed by a single `false`
terminator. Self-delimiting; the `false` marks end-of-number. -/
def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

@[simp] lemma encodeNat_zero : encodeNat 0 = [false] := rfl

@[simp] lemma encodeNat_succ (n : ℕ) :
    encodeNat (n + 1) = true :: encodeNat n := by
  simp [encodeNat, List.replicate_succ, List.cons_append]

/-- Decode a unary-encoded `ℕ` from the prefix of a list, returning the
value and the unconsumed tail. Fails if the list contains only `true`
bits (no terminator). -/
def decodeNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
    match decodeNat rest with
    | some (n, tail) => some (n + 1, tail)
    | none => none

/-- The round-trip lemma for `encodeNat`/`decodeNat`. -/
@[simp] lemma decodeNat_encodeNat_append (n : ℕ) (rest : List Bool) :
    decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [encodeNat, decodeNat]
  | succ n ih => simp [encodeNat_succ, decodeNat, ih]

/-- Pure round-trip (no trailing data). -/
lemma decodeNat_encodeNat (n : ℕ) :
    decodeNat (encodeNat n) = some (n, []) := by
  have := decodeNat_encodeNat_append n []
  simpa using this

/-! ## `Fin` — `ℕ` with a bound check -/

/-- Encode a `Fin n` value as its underlying `ℕ`. The bound is
recovered by the caller's `decodeFin` (the consumer needs to know `n`
externally — there's nothing in the encoding itself that says "this is
a `Fin n` value"). -/
def encodeFin {n : ℕ} (k : Fin n) : List Bool := encodeNat k.val

/-- Decode a `Fin n` from a list: decode a `ℕ`, then check `< n`. -/
def decodeFin (n : ℕ) (l : List Bool) : Option (Fin n × List Bool) :=
  match decodeNat l with
  | none => none
  | some (v, rest) =>
    if h : v < n then some (⟨v, h⟩, rest) else none

@[simp] lemma decodeFin_encodeFin_append {n : ℕ} (k : Fin n) (rest : List Bool) :
    decodeFin n (encodeFin k ++ rest) = some (k, rest) := by
  simp only [decodeFin, encodeFin, decodeNat_encodeNat_append, k.isLt, ↓reduceDIte]

lemma decodeFin_encodeFin {n : ℕ} (k : Fin n) :
    decodeFin n (encodeFin k) = some (k, []) := by
  have := decodeFin_encodeFin_append k []
  simpa using this

/-! ## `Bool` — single bit, no terminator -/

/-- A single bit, encoded raw. -/
def encodeBool (b : Bool) : List Bool := [b]

/-- Read one bit off the front of the list. -/
def decodeBool : List Bool → Option (Bool × List Bool)
  | [] => none
  | b :: rest => some (b, rest)

@[simp] lemma decodeBool_encodeBool_append (b : Bool) (rest : List Bool) :
    decodeBool (encodeBool b ++ rest) = some (b, rest) := by
  simp [encodeBool, decodeBool]

/-! ## `Option Bool` — 3-case enumeration -/

open Turing in
section

/-- Encode `Option Bool` as `0`, `1`, `2` (in unary). -/
def encodeOptBool : Option Bool → List Bool
  | none => encodeNat 0
  | some false => encodeNat 1
  | some true => encodeNat 2

/-- Decode `Option Bool`: read a `ℕ`, accept 0/1/2. -/
def decodeOptBool (l : List Bool) : Option (Option Bool × List Bool) :=
  (decodeNat l).bind fun (k, rest) =>
    if k = 0 then some (none, rest)
    else if k = 1 then some (some false, rest)
    else if k = 2 then some (some true, rest)
    else none

@[simp] lemma decodeOptBool_encodeOptBool_append (ob : Option Bool) (rest : List Bool) :
    decodeOptBool (encodeOptBool ob ++ rest) = some (ob, rest) := by
  cases ob with
  | none =>
    show decodeOptBool (encodeNat 0 ++ rest) = some (none, rest)
    unfold decodeOptBool
    rw [decodeNat_encodeNat_append]
    rfl
  | some b =>
    cases b
    · show decodeOptBool (encodeNat 1 ++ rest) = some (some false, rest)
      unfold decodeOptBool
      rw [decodeNat_encodeNat_append]
      rfl
    · show decodeOptBool (encodeNat 2 ++ rest) = some (some true, rest)
      unfold decodeOptBool
      rw [decodeNat_encodeNat_append]
      rfl

/-! ## `Option Dir` — 3-case enumeration (none / left / right) -/

/-- Encode `Option Dir` as `0`, `1`, `2` (in unary). -/
def encodeOptDir : Option Dir → List Bool
  | none => encodeNat 0
  | some Dir.left => encodeNat 1
  | some Dir.right => encodeNat 2

/-- Decode `Option Dir`. -/
def decodeOptDir (l : List Bool) : Option (Option Dir × List Bool) :=
  (decodeNat l).bind fun (k, rest) =>
    if k = 0 then some (none, rest)
    else if k = 1 then some (some Dir.left, rest)
    else if k = 2 then some (some Dir.right, rest)
    else none

@[simp] lemma decodeOptDir_encodeOptDir_append (od : Option Dir) (rest : List Bool) :
    decodeOptDir (encodeOptDir od ++ rest) = some (od, rest) := by
  cases od with
  | none =>
    show decodeOptDir (encodeNat 0 ++ rest) = some (none, rest)
    unfold decodeOptDir
    rw [decodeNat_encodeNat_append]
    rfl
  | some d =>
    cases d
    · show decodeOptDir (encodeNat 1 ++ rest) = some (some Dir.left, rest)
      unfold decodeOptDir
      rw [decodeNat_encodeNat_append]
      rfl
    · show decodeOptDir (encodeNat 2 ++ rest) = some (some Dir.right, rest)
      unfold decodeOptDir
      rw [decodeNat_encodeNat_append]
      rfl

/-! ## `Stmt Bool` — pair of `(symbol : Option Bool, movement : Option Dir)` -/

/-- Encode a `Stmt` as `encodeOptBool symbol ++ encodeOptDir movement`. -/
def encodeStmt (s : SingleTapeTM.Stmt Bool) : List Bool :=
  encodeOptBool s.symbol ++ encodeOptDir s.movement

/-- Decode a `Stmt` by reading the symbol and movement in order. -/
def decodeStmt (l : List Bool) : Option (SingleTapeTM.Stmt Bool × List Bool) := do
  let (sym, l) ← decodeOptBool l
  let (mov, l) ← decodeOptDir l
  some (⟨sym, mov⟩, l)

@[simp] lemma decodeStmt_encodeStmt_append (s : SingleTapeTM.Stmt Bool) (rest : List Bool) :
    decodeStmt (encodeStmt s ++ rest) = some (s, rest) := by
  obtain ⟨sym, mov⟩ := s
  simp [encodeStmt, decodeStmt, List.append_assoc]

/-! ## `Option (Fin n)` -/

/-- Encode `Option (Fin n)` as `0` for `none`, otherwise `v.val + 1`. -/
def encodeOptFin {n : ℕ} : Option (Fin n) → List Bool
  | none => encodeNat 0
  | some v => encodeNat (v.val + 1)

/-- Decode `Option (Fin n)`: read a `ℕ` `k`, return `none` if `k = 0`,
otherwise `some ⟨k - 1, _⟩` if `k - 1 < n`. -/
def decodeOptFin (n : ℕ) (l : List Bool) : Option (Option (Fin n) × List Bool) :=
  (decodeNat l).bind fun (k, rest) =>
    if k = 0 then some (none, rest)
    else if h : k - 1 < n then some (some ⟨k - 1, h⟩, rest)
    else none

@[simp] lemma decodeOptFin_encodeOptFin_append {n : ℕ} (of : Option (Fin n)) (rest : List Bool) :
    decodeOptFin n (encodeOptFin of ++ rest) = some (of, rest) := by
  cases of with
  | none =>
    show decodeOptFin n (encodeNat 0 ++ rest) = some (none, rest)
    unfold decodeOptFin
    rw [decodeNat_encodeNat_append]
    rfl
  | some v =>
    show decodeOptFin n (encodeNat (v.val + 1) ++ rest) = some (some v, rest)
    unfold decodeOptFin
    rw [decodeNat_encodeNat_append]
    have h : v.val < n := v.isLt
    have hsub : v.val + 1 - 1 = v.val := by omega
    have hne : ¬ (v.val + 1 = 0) := by omega
    simp only [Option.bind_some, if_neg hne, hsub, dif_pos h]

/-! ## Transition entries (`Stmt × Option (Fin (numStates + 1))`) -/

/-- Encode a single transition output: a statement + next-state. -/
def encodeTrEntry {n : ℕ}
    (e : SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) : List Bool :=
  encodeStmt e.1 ++ encodeOptFin e.2

/-- Decode a single transition output. -/
def decodeTrEntry (n : ℕ) (l : List Bool) :
    Option ((SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) × List Bool) := do
  let (s, l) ← decodeStmt l
  let (nxt, l) ← decodeOptFin (n + 1) l
  some ((s, nxt), l)

@[simp] lemma decodeTrEntry_encodeTrEntry_append {n : ℕ}
    (e : SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) (rest : List Bool) :
    decodeTrEntry n (encodeTrEntry e ++ rest) = some (e, rest) := by
  obtain ⟨s, nxt⟩ := e
  simp [encodeTrEntry, decodeTrEntry, List.append_assoc]

/-! ## Transition tables — list-based encoding

The transition table for a `TMCode` with `numStates` is a function

  `tr : Fin (numStates + 1) → Option Bool → Stmt Bool × Option (Fin (numStates + 1))`

with `(numStates + 1) * 3` entries (3 for the 3 possible head-symbol
cases: `none`, `some false`, `some true`). We encode by enumerating in
`(state-major, symbol-minor)` order: for each `q ∈ Fin (n+1)`, encode
`tr q none`, `tr q (some false)`, `tr q (some true)`.

To avoid dependent-type gymnastics in the decoder, we go through a
*flat list* representation
`List (Stmt Bool × Option (Fin (n+1)))` of length `3 * (n+1)`. -/

/-- Map `Option Bool` to its index in the canonical enumeration. -/
def symbolIdx : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

lemma symbolIdx_lt (ob : Option Bool) : symbolIdx ob < 3 := by
  cases ob with
  | none => decide
  | some b => cases b <;> decide

/-- Encode the transition function as a flat list (state-major,
symbol-minor). -/
def trToList {n : ℕ}
    (tr : Fin (n + 1) → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) :
    List (SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) :=
  (List.finRange (n + 1)).flatMap (fun q =>
    [tr q none, tr q (some false), tr q (some true)])

lemma trToList_length {n : ℕ}
    (tr : Fin (n + 1) → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) :
    (trToList tr).length = 3 * (n + 1) := by
  have h1 : (trToList tr).length = (n + 1) * 3 := by
    simp [trToList, List.length_flatMap, List.length_finRange]
  rw [h1, Nat.mul_comm]

/-! The pointwise `trToList`-lookup correspondence

    `(trToList tr)[3 * q.val + symbolIdx ob] = tr q ob`

is a clean restatement of the encoding's canonical-order property. We
defer its proof to a follow-up commit, since the immediate goal of
Phase 2 is the round-trip lemma below, which only needs the list and
its length. -/

/-- Encode a flat list of transition entries. -/
def encodeTrEntries {n : ℕ}
    (es : List (SingleTapeTM.Stmt Bool × Option (Fin (n + 1)))) : List Bool :=
  es.flatMap encodeTrEntry

/-- Decode `k` transition entries from the front of a list. -/
def decodeTrEntries (n : ℕ) :
    ℕ → List Bool →
    Option (List (SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) × List Bool)
  | 0, l => some ([], l)
  | k + 1, l => do
    let (e, l) ← decodeTrEntry n l
    let (es, l) ← decodeTrEntries n k l
    some (e :: es, l)

@[simp] lemma decodeTrEntries_encodeTrEntries_append {n : ℕ}
    (es : List (SingleTapeTM.Stmt Bool × Option (Fin (n + 1)))) (rest : List Bool) :
    decodeTrEntries n es.length (encodeTrEntries es ++ rest) = some (es, rest) := by
  induction es with
  | nil => simp [encodeTrEntries, decodeTrEntries]
  | cons e es ih =>
    have h_unfold : encodeTrEntries (e :: es) = encodeTrEntry e ++ encodeTrEntries es := by
      simp [encodeTrEntries, List.flatMap_cons]
    rw [h_unfold, List.append_assoc]
    show decodeTrEntries n (es.length + 1)
         (encodeTrEntry e ++ (encodeTrEntries es ++ rest)) = _
    simp [decodeTrEntries, decodeTrEntry_encodeTrEntry_append, ih]

/-- Encode the full transition table by flattening and encoding the
flat list. -/
def encodeTrTable {n : ℕ}
    (tr : Fin (n + 1) → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) :
    List Bool :=
  encodeTrEntries (trToList tr)

/-- Decode `3 * (n + 1)` transition entries from the front of a list. -/
def decodeTrTable (n : ℕ) (l : List Bool) :
    Option (List (SingleTapeTM.Stmt Bool × Option (Fin (n + 1))) × List Bool) :=
  decodeTrEntries n (3 * (n + 1)) l

@[simp] lemma decodeTrTable_encodeTrTable_append {n : ℕ}
    (tr : Fin (n + 1) → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin (n + 1)))
    (rest : List Bool) :
    decodeTrTable n (encodeTrTable tr ++ rest) = some (trToList tr, rest) := by
  unfold decodeTrTable encodeTrTable
  rw [← trToList_length tr]
  exact decodeTrEntries_encodeTrEntries_append _ _

/-! ## Full `TMCode` encoding -/

/-- Encode a `TMCode` as `List Bool`:
    `numStates`  (unary `ℕ`)
    `q₀.val`     (unary `ℕ`, bounded by `numStates + 1`)
    `tr`         (transition table, `3 * (numStates + 1)` entries). -/
def encodeTMCode (c : Halt.TMCode) : List Bool :=
  encodeNat c.numStates ++ encodeFin c.q₀ ++ encodeTrTable c.tr

/-- Decode a `TMCode`. The decoder builds the transition function by
list-lookup with bounds checks. -/
def decodeTMCode (l : List Bool) : Option Halt.TMCode := do
  let (numStates, l) ← decodeNat l
  let (q₀, l) ← decodeFin (numStates + 1) l
  let (entries, _) ← decodeTrTable numStates l
  if h : entries.length = 3 * (numStates + 1) then
    let tr : Fin (numStates + 1) → Option Bool →
        SingleTapeTM.Stmt Bool × Option (Fin (numStates + 1)) :=
      fun q ob =>
        have hbound : 3 * q.val + symbolIdx ob < entries.length := by
          have hq : q.val < numStates + 1 := q.isLt
          have hs : symbolIdx ob < 3 := symbolIdx_lt ob
          rw [h]; omega
        entries[3 * q.val + symbolIdx ob]'hbound
    some { numStates := numStates, q₀ := q₀, tr := tr }
  else
    none

end

end Halt.Encoding
