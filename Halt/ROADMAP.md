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

## 🚧 To do

The end goal is:

```lean
theorem halt_undecidable (Symbol : Type) [Inhabited Symbol] [Fintype Symbol]
    [Nonempty Symbol] :
    ¬ ∃ decide : SingleTapeTM Symbol → List Symbol → Bool,
        <computable in some fixed model> ∧
        ∀ tm w, decide tm w = true ↔ Halts tm w
```

Closing it requires picking a model of "computable" and bridging it to
the diagonal argument. Two viable paths:

### Path A — via Mathlib's `halting_problem`

Mathlib already has

```lean
theorem halting_problem (n) : ¬ ComputablePred fun c => (eval c n).Dom
```

for `c : Nat.Partrec.Code`. To use this here we need a **computability
bridge**: a `Computable`-preserving translation from cslib's
`SingleTapeTM Symbol` halting to `Nat.Partrec.Code` halting. Concretely:

1. **Pick a fixed alphabet**: `Symbol := Fin n` (or `Bool`, or `ℕ` — any
   `Primcodable` type). The general `[Inhabited] [Fintype]` will need
   to specialise.
2. **`Primcodable` instances** for `SingleTapeTM (Fin n)` and `List (Fin n)`.
   This requires `Primcodable` for the TM's state space (so we
   restrict to finitely-many states), transition function, etc.
3. **A computable translation**
   `tmEncoding : SingleTapeTM (Fin n) × List (Fin n) → Nat.Partrec.Code`
   such that for every `(tm, w)`, `eval (tmEncoding tm w) 0` is defined
   iff `Halts tm w`. This is the "every TM is a partrec function"
   theorem — comparable in scope to Mathlib's `Computability.TMToPartrec`
   for *its own* TM model, but for cslib's `SingleTapeTM`.
4. **Conclude**: any `Computable` decider for `Halts` gives a
   `Computable` decider for partrec halting, contradicting
   `halting_problem`.

Estimated scope: ~2000–4000 LoC of `Primcodable` plumbing +
`tmEncoding` construction + simulation correctness.

### Path B — via cslib's `URM` and a URM-to-Partrec bridge

cslib has a URM (Unlimited Register Machine) computability framework
(`Cslib.Computability.URM`) with `URM.Computable`. URM ↔ partial
recursive functions is a classical equivalence; if we build one
direction (say `URM.Computable → Nat.Partrec`), we can transport
Mathlib's `halting_problem` to URM. Then if we *also* build
SingleTapeTM ↔ URM, we get SingleTapeTM halting undecidability.

Estimated scope: SingleTapeTM ↔ URM is ~500–1500 LoC; URM → Partrec
is ~500–2000 LoC.

### Path C — direct universal SingleTapeTM + self-application

Bypass the bridges and build a universal `SingleTapeTM` together with
a self-application diagonal. Closes via `Halt.Diagonal.halt_diag_contradiction`
once the right encoding is in place.

Estimated scope: comparable to Path A in size, but the work is
self-contained (no Mathlib `Primcodable` setup) at the cost of doing
the universal-TM construction by hand.

## Recommended path

**Path A** is cleanest because Mathlib already has `halting_problem`
proved; we only do the simulation work, not the diagonal proof. The
`Computability.TMToPartrec` template in Mathlib is also directly
relevant. Path C is the most self-contained but largest.

## Suggested incremental subgoals (Path A)

1. **Specialise the alphabet** to `Fin n` (or `Bool`). Add
   `Primcodable` for `SingleTapeTM (Fin n)` — likely via a sigma over
   `[Fintype State]`.
2. **Encode TM configurations**: `Cfg`, `BiTape`, step relation —
   prove each step is `Primrec` (or at least `Computable`) over the
   encoding.
3. **Define `tmEncoding`**: build the partrec code that, on input `0`,
   simulates `tm` from `initCfg tm w`. Show it halts iff `Halts tm w`.
4. **State and prove `halt_undecidable`**: contraposition of
   `Computability.Halting.halting_problem`.

Each step is independent and can be a separate file in `Halt/`.

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings, same as the rest of the project.
