# Halt roadmap

Plan for proving the Halting Problem undecidable for cslib's
`Turing.SingleTapeTM`.

## ✅ Done

### `Halt.Diagonal`
The pure-mathematical kernel of the diagonal argument — Cantor's
theorem (`not_surjective_cantor`), the diagonal-disagreement lemma
(`cantor_diag`), and the abstract self-referential contradiction
(`halt_diag_contradiction`). No Turing machines, no computability —
just `Bool` and function equality. This file does not change as the
rest of the library is built; it's the once-and-for-all logical core.

### `Halt.Basic`
The decision predicate `HaltDecidable Symbol` and a few small
structural lemmas. **Caveat**: this predicate is vacuously true
classically — its formal content arrives only when paired with a
*computability* constraint on the decider. We do not commit to a
specific notion of computability here.

## 🚧 To do — Path C (chosen)

We're going with **Path C**: build a universal `SingleTapeTM` directly,
then close via self-application using `Halt.Diagonal.halt_diag_contradiction`.
This is the largest path but the most self-contained — no Mathlib
`Primcodable` machinery, no bridge to a different computation model.

The end goal:

```lean
theorem halt_undecidable :
    ¬ ∃ decider : SingleTapeTM Bool,
        IsHaltDecider decider ∧
        Halts decider w_for_every_input_etc
```

where `IsHaltDecider` says "decider on input `encode (tm, w)` halts
with output `[true]` iff `tm` halts on `w`, and with output `[false]`
otherwise".

### Phase 1 — Normalised TM representation

Fix the alphabet `Symbol := Bool` and require the state set to be
`Fin n`. Two things:
* `TMCode` — a finite, transferable code for a TM (number of states +
  initial state + transition table).
* `tmCodeToTM : TMCode → SingleTapeTM Bool` — interpretation as a real
  cslib `SingleTapeTM`. Prove that `Halts (tmCodeToTM c) w` is
  preserved by the interpretation (i.e. corresponds to "the TM `c`
  halts on `w`" intuitively).

This is mechanical but tedious. ~200–400 LoC.

### Phase 2 — Gödel numbering

* `encodeTMCode : TMCode → List Bool` — serialise a TM.
* `decodeTMCode : List Bool → Option TMCode` — partial inverse.
* `decodeEncode : decodeTMCode (encodeTMCode c) = some c`.

Then `encodePair : List Bool → List Bool → List Bool` for encoding
`(tm, w)` as a single tape input (with a separator).

~150–300 LoC.

### Phase 3 — Universal TM

Build `U : SingleTapeTM Bool` (with its own concrete state set, say
`Fin k` for some k determined by the construction) such that

```lean
theorem universal_correct (c : TMCode) (w : List Bool) :
    Halts U (encodePair (encodeTMCode c) w) ↔
    Halts (tmCodeToTM c) w
```

This is the bulk of Path C. The universal TM has to:
* Parse the encoded `TMCode` off the tape.
* Maintain a simulated state pointer + simulated head position.
* On each "outer" step, look up the encoded transition rule for the
  current simulated state + head symbol, then execute it (write +
  move).
* Halt when the simulated state is the halt state (`none`).

Estimated ~2000–4000 LoC (this is the textbook universal-TM construction
formalised). Can be broken into:
* `Halt/UniversalTM/State.lean` — the U's state set + helpers.
* `Halt/UniversalTM/Step.lean` — per-step simulation invariant.
* `Halt/UniversalTM/Correctness.lean` — the `universal_correct` theorem.

### Phase 4 — Self-application diagonal

Given a hypothetical decider `D : SingleTapeTM Bool` for halting,
construct `Diag : SingleTapeTM Bool` that on input `code`:
1. Forms `encodePair code code` (self-application).
2. Simulates `D` on it via `U`.
3. Branches on `D`'s output:
   * `D` says "halts" → enter an infinite loop.
   * `D` says "doesn't halt" → halt.

Then run `Diag` on `encodeTMCode (codeOf Diag)`:
* If `Diag` halts → by construction, `D` says it doesn't → contradiction.
* If `Diag` doesn't halt → by construction, `D` says it halts → contradiction.

Closes via `Halt.Diagonal.halt_diag_contradiction`.

~300–800 LoC.

## Total estimate

Phase 1: ~200–400
Phase 2: ~150–300
Phase 3: ~2000–4000  ← the bulk
Phase 4: ~300–800

Total: ~2650–5500 LoC across many sessions. Phase 3 is where most
work concentrates.

## Status

* `Halt.Diagonal` — ✅ done (model-independent).
* `Halt.Basic` — ✅ done (decision predicate, vacuous without
  computability constraint).
* Phase 1 (`Halt.TMCode`) — 🚧 in progress.
* Phases 2–4 — 🚧 not yet started.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings, same as the rest of the project.
