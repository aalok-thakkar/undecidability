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
The decision predicate `HaltDecidable Symbol`. We are switching from
the loose `decide : SingleTapeTM Symbol → List Symbol → Bool` form
(which is vacuously true classically) to the strict
`IsHaltDecider (D : SingleTapeTM Bool)` form below, where `D` is a
*concrete TM* that decides halting via its output tape.

### Phase 1 — `Halt.TMCode` (normalised TM representation)
Fix the alphabet `Symbol := Bool` and the state set to `Fin (n+1)`.
* `TMCode` record.
* `tmCodeToTM : TMCode → SingleTapeTM Bool`.
* Simulation `simp` lemmas.

### Phase 2 — `Halt.Encoding` (Gödel numbering)
Self-delimiting bit-encoding of `TMCode` as `List Bool`:
* `encodeNat`/`decodeNat` (unary), `encodeFin`/`decodeFin`,
  `encodeBool`/`decodeBool`, `encodeOptBool`, `encodeOptDir`,
  `encodeStmt`, `encodeOptFin`, `encodeTrEntry`, `encodeTrEntries`,
  `encodeTrTable`, `encodeTMCode`/`decodeTMCode`, with round-trip
  lemmas at every layer.
* The pointwise transition-lookup `trToList_getElem` is deferred
  (needed for Phase 4 injectivity, not for the diagonal).

## 🚧 To do — composition-based diagonal (revised plan)

The textbook construction builds a universal `SingleTapeTM`
(~2000–4000 LoC). We **don't need that.** The diagonal only needs:

1. To assume a hypothetical decider `D : SingleTapeTM Bool` (as a
   black box, satisfying `IsHaltDecider`).
2. To build `diagTM := dupTM ⋙ D ⋙ invertTM`, where:
   * `dupTM` is a concrete TM that on input `c` writes
     `encodePair c c`.
   * `invertTM` is a concrete TM that loops on `[true]` and halts on
     `[false]`.
   * `⋙` is cslib's `compComputer` (composition).
3. To express `diagTM` as a `TMCode` via a generic
   `codeOf : SingleTapeTM Bool → TMCode` (state renaming through a
   `Fintype.equivFin` bijection).
4. To apply `Halt.Diagonal.halt_diag_contradiction` to the diagonal
   point `c_diag := encodeTMCode (codeOf diagTM)`.

The hypothetical `D` does the heavy lifting of "interpret a TMCode";
since we never construct it, we never build a universal TM. We only
build the two concrete helper TMs (`dupTM` and `invertTM`) and the
generic `codeOf` operation.

### Phase 3a — `Halt.Pair`: tape encoding of pairs (~50 LoC)
* `encodePair : List Bool → List Bool → List Bool` —
  `encodeNat |w| ++ w ++ v` is enough: the unary length prefix
  delimits the first half.
* `decodePair : List Bool → Option (List Bool × List Bool)`.
* Round-trip lemma.

### Phase 3b — `Halt.Basic`: refined `IsHaltDecider` (~30 LoC)
```lean
def IsHaltDecider (D : SingleTapeTM Bool) : Prop :=
  ∀ (c : Halt.TMCode) (w : List Bool),
    Outputs D (encodePair (encodeTMCode c) w)
      (if PCP.Halts c.toTM w then [true] else [false])
```

### Phase 3c — `Halt.Helpers.DupTM` (~200 LoC)
Concrete `SingleTapeTM Bool` (small explicit state set,
`Fin k` for k≈5–10) that on input `w` halts with output
`encodePair w w`. Correctness lemma:
`Outputs dupTM w (encodePair w w)`.

### Phase 3d — `Halt.Helpers.InvertTM` (~50 LoC)
Concrete `SingleTapeTM Bool` (2 states) that on input `[true]` loops
forever and on input `[false]` halts immediately. Correctness lemmas:
* `¬ Halts invertTM [true]`.
* `Outputs invertTM [false] []` (or some chosen empty output).

### Phase 3e — `Halt.CodeOf` (~150–250 LoC)
A function `codeOf : SingleTapeTM Bool → TMCode` and the lemma
`Halts (codeOf tm).toTM w ↔ Halts tm w`. Uses `Fintype.equivFin` to
rename the state set through `Fin (Fintype.card tm.State)`.

### Phase 4 — `Halt.Undecidable` (~150 LoC)
1. Define `diagTM (D)` via `compComputer dupTM (compComputer D invertTM)`.
2. Prove the chain of equivalences:
   `Halts (diagTM D) c
     ↔ Halts (compComputer D invertTM) (encodePair c c)        -- via dupTM
     ↔ Halts invertTM [false]                                  -- via D, decider
     ↔ True`
   And similarly the "doesn't halt" path leads to `[true]` and `¬ True`.
3. Apply to `c_diag := encodeTMCode (codeOf (diagTM D))`.
4. Use `halt_diag_contradiction` to close.

## Total estimate

Phase 3a: ~50
Phase 3b: ~30
Phase 3c: ~200
Phase 3d: ~50
Phase 3e: ~200
Phase 4: ~150

Total: ~680 LoC — about **5× smaller** than the universal-TM route.

## Status

* `Halt.Diagonal` ✅
* `Halt.Basic` (loose form) ✅; strict `IsHaltDecider` 🚧
* Phase 1 (`Halt.TMCode`) ✅
* Phase 2 (`Halt.Encoding`) ✅ (deferred pointwise lookup)
* Phase 3a (`Halt.Pair`) 🚧
* Phase 3b (refined `Halt.Basic`) 🚧
* Phase 3c (`Halt.Helpers.DupTM`) 🚧
* Phase 3d (`Halt.Helpers.InvertTM`) 🚧
* Phase 3e (`Halt.CodeOf`) 🚧
* Phase 4 (`Halt.Undecidable`) 🚧

## Build invariant

Every commit on this roadmap MUST keep `lake build` clean with
**no `sorry`** and no warnings, same as the rest of the project.
