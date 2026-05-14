/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import PCP.Halt
public import Halt.Diagonal

@[expose] public section

/-!
# The Halting Problem decision predicate

This file states the decision problem **HALT** for cslib's
`Turing.SingleTapeTM`:

  Given a TM `tm` and an input `w`, does `tm` halt on `w`?

formalised by the predicate `Halts` (see `PCP.Halt`). We define
`HaltDecidable` — the proposition that a Bool-valued *decider* for
`Halts` exists — and lay out the goal theorem `halt_undecidable`.

## Important caveat on the formalisation

In dependent type theory, *every* predicate admits a Bool-valued
decider classically (take `fun x => decide (Halts tm w)` via classical
choice). So `HaltDecidable` as written below is *vacuously true*. To
make the claim non-trivial, the decider has to be required to be
*computable* in some externally-fixed sense (e.g. expressible as a
Turing machine, partial recursive function, or URM program).

We isolate two parts:
* The shape of the decider — `HaltDecidable` below — which is just
  "some Bool-valued function decides `Halts`".
* The model-specific "computable" hypothesis — formalised separately
  (see `Halt.ROADMAP.md`) once the bridge to Mathlib's `Nat.Partrec`
  framework, or a direct universal `SingleTapeTM`, is built.

The kernel of the diagonal argument (`Halt.Diagonal`) is already in
place and is independent of these choices.

## Status

This file currently provides only `HaltDecidable Symbol` — the
(non-computability-constrained) decision predicate.

The main theorem `halt_undecidable` (when stated with a computability
constraint) is *not yet proved* — it is the subject of the rest of the
`Halt/` library; see `Halt/ROADMAP.md` for the dependency tree.
-/

namespace Halt

open PCP Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-! ## The decision predicate -/

/-- **`HaltDecidable Symbol`** holds iff some Bool-valued function on
`SingleTapeTM Symbol × List Symbol` decides `Halts`.

This predicate, taken in isolation, is provable classically (apply
`Classical.dec` to `Halts tm w`). Its real content is what comes when
we *additionally* require the decider to be expressible in a fixed
computational model — see `Halt.ROADMAP.md`. -/
def HaltDecidable (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] : Prop :=
  ∃ decide : SingleTapeTM Symbol → List Symbol → Bool,
    ∀ tm w, decide tm w = true ↔ Halts tm w

end Halt
