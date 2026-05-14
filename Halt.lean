/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import Halt.Diagonal
public import Halt.Basic
public import Halt.TMCode

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
* `Halt.TMCode`    — normalised TM representation (Phase 1 of Path C):
  `Bool` alphabet, `Fin (n+1)` states, with an interpretation map
  `tmCodeToTM : TMCode → SingleTapeTM Bool`.
-/
