/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import Halt.Diagonal
public import Halt.Basic
public import Halt.TMCode
public import Halt.Encoding
public import Halt.Pair
public import Halt.Helpers
public import Halt.CodeOf

@[expose] public section

/-!
# Halt — library root

This module re-exports the public Halt-undecidability API:

* `Halt.Diagonal`  — model-independent diagonalisation: Cantor's theorem
  and the abstract self-referential contradiction at the heart of the
  Halting Problem.
* `Halt.Basic`     — the formal statement of "the halting problem for
  cslib's `Turing.SingleTapeTM` is decidable" (the predicate
  `HaltDecidable`), together with the goal theorem
  `halt_undecidable : ¬ HaltDecidable …` (proof: see `ROADMAP.md`).
* `Halt.TMCode`    — normalised TM representation (Phase 1):
  `Bool` alphabet, `Fin (n+1)` states, with an interpretation map
  `tmCodeToTM : TMCode → SingleTapeTM Bool`.
* `Halt.Encoding`  — Gödel numbering (Phase 2): self-delimiting bit
  encoding of `TMCode` as `List Bool`.
* `Halt.Pair`      — pair encoding (Phase 3a): length-prefixed
  serialisation of `(c, w)` as a single `List Bool`.
* `Halt.Helpers`   — concrete helper TMs for the diagonal: `invertTM`
  (loops on `[true]`, halts on `[false]`). Phases 3c–3d.
* `Halt.CodeOf`    — generic state-renaming `SingleTapeTM Bool → TMCode`
  with the bisimulation theorem
  `halts_codeOf_iff : Halts (codeOf tm).toTM w ↔ PCP.Halts tm w`.
  Phase 3e.
-/
