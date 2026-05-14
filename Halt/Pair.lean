/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import Halt.Encoding

@[expose] public section

/-!
# Pair encoding (Phase 3a)

To feed `(c, w)` to a halt-decider over the alphabet `Bool`, we need a
concrete encoding of a pair of `List Bool`s as a single `List Bool`.

We use a length-prefix scheme:

  `encodePair u v = encodeNat u.length ++ u ++ v`

The unary length prefix is self-delimiting, so `decodePair` can read
`|u|` from the front, then split the rest at position `|u|`.
-/

namespace Halt.Pair

open Halt.Encoding

/-- Encode a pair `(u, v) : List Bool × List Bool` as a single
`List Bool` using a unary length prefix for `u`. -/
def encodePair (u v : List Bool) : List Bool :=
  encodeNat u.length ++ u ++ v

/-- Decode a length-prefixed pair from a `List Bool`. Returns `none` if
the prefix is malformed or shorter than its declared length. -/
def decodePair (l : List Bool) : Option (List Bool × List Bool) :=
  match decodeNat l with
  | none => none
  | some (n, rest) =>
    if n ≤ rest.length then
      some (rest.take n, rest.drop n)
    else
      none

/-- Round-trip: decoding the encoded pair recovers the originals. -/
@[simp] lemma decodePair_encodePair (u v : List Bool) :
    decodePair (encodePair u v) = some (u, v) := by
  unfold decodePair encodePair
  rw [List.append_assoc, decodeNat_encodeNat_append]
  simp

end Halt.Pair
