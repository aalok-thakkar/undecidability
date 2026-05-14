/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/
module

public import PCP.Halt
public import Halt.Diagonal
public import Halt.TMCode
public import Halt.Encoding
public import Halt.Pair

@[expose] public section

/-!
# The Halting Problem decision predicate

This file states the decision problem **HALT** for cslib's
`Turing.SingleTapeTM`:

  Given a TM `tm` and an input `w`, does `tm` halt on `w`?

formalised by the predicate `Halts` (see `PCP.Halt`).

We use two decision-predicate forms.

## `HaltDecidable` (loose form)

```
∃ decide : SingleTapeTM Symbol → List Symbol → Bool, …
```

is **vacuously true classically** (any `Halts tm w : Prop` admits a
`Classical.dec`-style Bool decider). Useful only for stating what we
*want* to refute — the real content comes from the second form below.

## `IsHaltDecider` (strict form)

```
∀ (c : TMCode) (w : List Bool),
    Outputs D (encodePair (encodeTMCode c) w)
      (if Halts c.toTM w then [true] else [false])
```

The decider `D : SingleTapeTM Bool` is itself a TM, and "decides" by
writing `[true]`/`[false]` on its output tape. **Refuting**
`∃ D, IsHaltDecider D` is the genuine Halting-Problem-undecidability
result for cslib's `SingleTapeTM`. The proof is the goal of the rest
of `Halt/`; see `Halt/ROADMAP.md` for the plan.
-/

namespace Halt

open PCP Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-! ## Loose form: any Bool-valued decider -/

/-- **`HaltDecidable Symbol`** holds iff some Bool-valued function on
`SingleTapeTM Symbol × List Symbol` decides `Halts`.

This predicate, taken in isolation, is provable classically. Its real
content arrives only when paired with a computability constraint on
the decider — see `IsHaltDecider` below. -/
def HaltDecidable (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] : Prop :=
  ∃ decide : SingleTapeTM Symbol → List Symbol → Bool,
    ∀ tm w, decide tm w = true ↔ Halts tm w

/-! ## Strict form: a TM that decides halting -/

/-- **`IsHaltDecider D`** holds iff the single-tape TM `D` over `Bool`,
when run on the encoded pair `(c, w)`, halts with output `[true]` if
the encoded TM `c` halts on `w`, and `[false]` otherwise. -/
def IsHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (c : Halt.TMCode) (w : List Bool),
    (Halts c.toTM w →
      SingleTapeTM.Outputs D
        (Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c) w) [true]) ∧
    (¬ Halts c.toTM w →
      SingleTapeTM.Outputs D
        (Halt.Pair.encodePair (Halt.Encoding.encodeTMCode c) w) [false])

end Halt
