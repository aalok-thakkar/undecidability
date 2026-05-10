/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

module

public import PCP.Lu
public import PCP.MPCP

@[expose] public section

/-!
# Lu ≤_m MPCP

This file builds the reduction from the Halting Problem (`Halts`, see
`PCP.Lu`) to the Modified Post Correspondence Problem (`MHasSolution`).

## High-level idea

Given a Turing machine `tm` and an input `w`, we construct an MPCP
instance whose solutions encode accepting computation histories of `tm`
on `w`. The classical Hopcroft–Ullman construction uses an alphabet that
extends the TM tape alphabet with the TM state labels, a configuration
separator `#`, and a synthetic `halt` symbol. A configuration

  `⟨q, tape⟩` with tape contents `… b₋₁ b₀ b₁ …`

is encoded as the finite string

  `# b₋ₖ … b₋₁ q b₀ b₁ … bₖ #`

with the state symbol `q` placed immediately before the head symbol.

The reduction produces an MPCP instance with five families of tiles:

| Family       | Effect                                                  |
|--------------|---------------------------------------------------------|
| start tile   | seeds the bottom string with the initial configuration  |
| copy tiles   | copy a tape symbol from one configuration to the next   |
| separator    | copy `#` between configurations                         |
| transition   | rewrite the local window around the head per `tm.tr`    |
| halt-shrink  | absorb tape symbols once the TM has halted              |

A solution to the resulting MPCP instance must trace a halting
computation of `tm` on `w`, and conversely every halting computation
yields a solution.

## Simulation invariant

Throughout a matching solution, the bottom string is **one configuration
ahead** of the top:

  `bot = top ++ "encoded next configuration ++ #"`.

The start tile establishes this offset with `top = [#]` and
`bot = # :: encodeCfg(C₀) ++ [#]`. Each TM step `Cⱼ → Cⱼ₊₁` is realised
by a tile sub-sequence whose `tau1 = encodeCfg(Cⱼ) ++ [#]` reproduces
the *current* lookahead and whose `tau2 = encodeCfg(Cⱼ₊₁) ++ [#]`
extends it with the next configuration. After halt, the absorb tiles
shrink the lookahead one tape symbol at a time until only `h⊥` remains,
then the final tile equalises top and bot.

## Status

This file provides:

* Alphabet `Alpha` and configuration encoding (`encodeRunningCfg`,
  `encodeHaltedCfg`, `encodeCfg`, `block`, `initBlock`).
* All tile constructors (`startTile`, `copyTile`, `sepTile`, the
  six transition-tile constructors, `absorbLeftTile`, `absorbRightTile`,
  `finalTile`).
* Tile enumeration (`copyTiles`, `absorbTiles`, `transitionTiles`,
  `luTiles`) and the reduction function `luToMpcp`.
* Membership lemmas relating each tile family to `luTiles`.
* `tau1`/`tau2` of copy-tile sequences.
* The full simulation lemma for the **no-move** TM-step case
  (`stepTilesNoMove` plus `tau1_stepTilesNoMove`,
  `tau2_stepTilesNoMove`, `stepTilesNoMove_subset_luTiles`).

Remaining work — see `ROADMAP.md` at the project root for the detailed
plan:

1. Right-move and left-move step-simulation lemmas (interior + boundary).
2. Halt-absorption iteration lemmas.
3. Forward direction `Halts → MHasSolution`.
4. Backward direction `MHasSolution → Halts`.
5. Final theorem `lu_le_mpcp`.

The Coq counterpart in `coq-library-undecidability` runs to ~1500
lines, so this remaining work spans multiple sessions.
-/

namespace PCP.LuToMPCP

open Turing PCP

/-! ## Alphabet of the reduced MPCP instance -/

/-- The alphabet of the reduced MPCP instance.

* `tape`   lifts a tape symbol of the original TM (an `Option Symbol`,
  where `none` is the blank).
* `state`  lifts a TM state (used to mark the head position in a
  configuration encoding).
* `halt`   marks the halted TM (CSLib's halting state is `none`, which
  has no tag — we introduce `halt` as the encoding's marker).
* `sep`    is the `#` configuration separator.
-/
inductive Alpha (Q : Type) (S : Type) where
  | tape  : Option S → Alpha Q S
  | state : Q → Alpha Q S
  | halt  : Alpha Q S
  | sep   : Alpha Q S
  deriving DecidableEq

@[inherit_doc Alpha.tape]  prefix:max "↟ₜ" => Alpha.tape
@[inherit_doc Alpha.state] prefix:max "↟ₛ" => Alpha.state
@[inherit_doc Alpha.sep]   notation "#"   => Alpha.sep
@[inherit_doc Alpha.halt]  notation "h⊥"  => Alpha.halt

/-! ## Encoding configurations -/

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Lift a list of TM tape symbols to a list over the reduced alphabet. -/
def liftTape (tm : SingleTapeTM Symbol) (l : List (Option Symbol)) :
    List (Alpha tm.State Symbol) :=
  l.map Alpha.tape

@[simp] lemma liftTape_nil (tm : SingleTapeTM Symbol) :
    liftTape tm ([] : List (Option Symbol)) = [] := rfl

@[simp] lemma liftTape_cons (tm : SingleTapeTM Symbol) (a : Option Symbol)
    (l : List (Option Symbol)) :
    liftTape tm (a :: l) = ↟ₜa :: liftTape tm l := rfl

@[simp] lemma liftTape_append (tm : SingleTapeTM Symbol) (l₁ l₂ : List (Option Symbol)) :
    liftTape tm (l₁ ++ l₂) = liftTape tm l₁ ++ liftTape tm l₂ := by
  simp [liftTape, List.map_append]

/-- Encode a `BiTape` as the finite word
    `left.reverse ++ [head] ++ right`
    over `Option Symbol`. This captures exactly the non-blank window of
    the tape (with the head symbol in the middle). -/
def biTapeToList (t : BiTape Symbol) : List (Option Symbol) :=
  t.left.toList.reverse ++ t.head :: t.right.toList

/-- Encode a non-halted configuration `⟨some q, t⟩` as
    `left.reverse ++ ↟ₛq :: ↟ₜhead :: right`,
    placing the state marker immediately before the head symbol. -/
def encodeRunningCfg (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    List (Alpha tm.State Symbol) :=
  liftTape tm t.left.toList.reverse ++ ↟ₛq :: liftTape tm (t.head :: t.right.toList)

/-- Encode a halted configuration `⟨none, t⟩` using the synthetic `halt`
    marker in place of a state symbol. -/
def encodeHaltedCfg (tm : SingleTapeTM Symbol) (t : BiTape Symbol) :
    List (Alpha tm.State Symbol) :=
  liftTape tm t.left.toList.reverse ++ h⊥ :: liftTape tm (t.head :: t.right.toList)

/-- Encode an arbitrary configuration. -/
def encodeCfg (tm : SingleTapeTM Symbol) : tm.Cfg → List (Alpha tm.State Symbol)
  | ⟨some q, t⟩ => encodeRunningCfg tm q t
  | ⟨none,   t⟩ => encodeHaltedCfg tm t

/-- Wrap a configuration encoding in `#…#` separators (one full block). -/
def block (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    List (Alpha tm.State Symbol) :=
  # :: encodeCfg tm cfg ++ [#]

/-- The encoding of the initial configuration on input `w`. -/
def initBlock (tm : SingleTapeTM Symbol) (w : List Symbol) :
    List (Alpha tm.State Symbol) :=
  block tm (SingleTapeTM.initCfg tm w)

@[simp] lemma encodeCfg_running (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) :
    encodeCfg tm { state := some q, BiTape := t } = encodeRunningCfg tm q t := rfl

@[simp] lemma encodeCfg_halted (tm : SingleTapeTM Symbol) (t : BiTape Symbol) :
    encodeCfg tm { state := none, BiTape := t } = encodeHaltedCfg tm t := rfl

/-! ## Tile constructors

These are the building blocks of the reduced MPCP instance. The simulation
invariant maintained throughout a matching solution is:

  `bot = top ++ "lookahead by one configuration"`.

The start tile establishes this offset with `top = #` and
`bot = # initBlock #`. Copy tiles and the separator tile preserve the
offset. Transition tiles advance the bot by one TM step relative to the
top. Halt-absorb tiles and the final tile let the top catch up once the
TM has halted. -/

/-- The *start* tile: forces every solution to begin by seeding the bottom
    string with the encoded initial configuration `# C₀ #`, while the top
    is just `#`. The resulting offset is the simulation lookahead. -/
def startTile (tm : SingleTapeTM Symbol) (w : List Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [#]
  bot := # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#]

/-- A *copy* tile for tape symbol `a`. Replicating these advances the
    portion of a configuration that is unchanged by the current step. -/
def copyTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜa]
  bot := [↟ₜa]

/-- The *separator-copy* tile, used between configurations. -/
def sepTile (tm : SingleTapeTM Symbol) : Tile (Alpha tm.State Symbol) where
  top := [#]
  bot := [#]

/-! ### Transition tiles

For each transition `tm.tr q a = ((w, dir), q?)` the reduction provides one
or more tiles realising the local rewrite around the head. The new state
`q?` is `Option tm.State`: `some q'` if the TM continues, `none` if the
TM halts (in which case the encoded bot uses the synthetic `h⊥` marker
in place of a state symbol).

Below, each tile constructor takes the *new state encoding* `qNew :
Alpha tm.State Symbol` directly. This is either `↟ₛq'` for a continuing
transition or `h⊥` for a halting one — see `stateMarker` below. -/

/-- The encoding of a possibly-halting next state as a single alphabet
    symbol: `↟ₛq'` if the TM continues to state `q'`, otherwise `h⊥`. -/
def stateMarker (tm : SingleTapeTM Symbol) :
    Option tm.State → Alpha tm.State Symbol
  | some q' => ↟ₛq'
  | none    => h⊥

/-- Transition tile for a *no-move* step `q a → qNew w (no movement)`.
    Local rewrite: `↟ₛq ↟ₜa  →  qNew ↟ₜw`. -/
def noMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜw]

/-- Transition tile for a *right-move* step `q a → qNew w right`, in the
    interior of the encoded tape.
    Local rewrite: `↟ₛq ↟ₜa  →  ↟ₜw qNew`. -/
def rightMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [↟ₜw, stateMarker tm qNew]

/-- Right-move transition at the *right boundary* of the encoded tape:
    the head moves into a previously blank cell, requiring an explicit
    `none` (blank) symbol to be inserted before the closing `#`.
    Local rewrite: `↟ₛq ↟ₜa #  →  ↟ₜw qNew ↟ₜnone #`. -/
def rightMoveBoundaryTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa, #]
  bot := [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #]

/-- Transition tile for a *left-move* step `q a → qNew w left`, in the
    interior of the encoded tape, with `b` the symbol immediately to the
    left of the head.
    Local rewrite: `↟ₜb ↟ₛq ↟ₜa  →  qNew ↟ₜb ↟ₜw`. -/
def leftMoveTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol)
    (b : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜb, ↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜb, ↟ₜw]

/-- Left-move transition at the *left boundary* of the encoded tape:
    the head moves into a previously blank cell, requiring an explicit
    `none` (blank) symbol to be inserted just after the opening `#`.
    Local rewrite: `# ↟ₛq ↟ₜa  →  # qNew ↟ₜnone ↟ₜw`. -/
def leftMoveBoundaryTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [#, ↟ₛq, ↟ₜa]
  bot := [#, stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw]

/-! ### Halt-absorb tiles

After the TM halts the bot ends in `# … h⊥ … #`. The top must catch up.
Each absorb tile extends the top by *two* alphabet symbols and the bot by
*one* (`h⊥`), shrinking the tape window around `h⊥` until only `h⊥`
remains adjacent to the surrounding `#`s. -/

/-- Absorb a tape symbol immediately to the *left* of the halt marker:
    `↟ₜa h⊥  →  h⊥`. -/
def absorbLeftTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₜa, h⊥]
  bot := [h⊥]

/-- Absorb a tape symbol immediately to the *right* of the halt marker:
    `h⊥ ↟ₜa  →  h⊥`. -/
def absorbRightTile (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [h⊥, ↟ₜa]
  bot := [h⊥]

/-- The *final* tile, closing the matching. After all tape symbols have
    been absorbed, the bot ends in `# h⊥ #` and the top lags by `h⊥ # #`.
    Applying `(h⊥ # #, #)` extends the top by `h⊥ # #` and the bot by
    `#`, equalising the two. -/
def finalTile (tm : SingleTapeTM Symbol) : Tile (Alpha tm.State Symbol) where
  top := [h⊥, #, #]
  bot := [#]

/-! ### Tile-projection simp lemmas -/

@[simp] lemma copyTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (copyTile tm a).top = [↟ₜa] := rfl

@[simp] lemma copyTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (copyTile tm a).bot = [↟ₜa] := rfl

@[simp] lemma sepTile_top (tm : SingleTapeTM Symbol) :
    (sepTile tm).top = [#] := rfl

@[simp] lemma sepTile_bot (tm : SingleTapeTM Symbol) :
    (sepTile tm).bot = [#] := rfl

@[simp] lemma stateMarker_some (tm : SingleTapeTM Symbol) (q' : tm.State) :
    stateMarker tm (some q') = ↟ₛq' := rfl

@[simp] lemma stateMarker_none (tm : SingleTapeTM Symbol) :
    stateMarker tm (none : Option tm.State) = h⊥ := rfl

@[simp] lemma finalTile_top (tm : SingleTapeTM Symbol) :
    (finalTile tm).top = [h⊥, #, #] := rfl

@[simp] lemma finalTile_bot (tm : SingleTapeTM Symbol) :
    (finalTile tm).bot = [#] := rfl

/-! ## Tile enumeration

We enumerate the regular MPCP tiles arising from a TM. The start tile is
*not* in this list — it is the dedicated `MHasSolution` start argument. -/

/-- All copy tiles, one per tape symbol (`Option Symbol`, including the
    blank). -/
noncomputable def copyTiles (tm : SingleTapeTM Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (Finset.univ : Finset (Option Symbol)).toList.map (copyTile tm)

/-- The two halt-absorb tiles for a given tape symbol. -/
def absorbTilesFor (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  [absorbLeftTile tm a, absorbRightTile tm a]

/-- All halt-absorb tiles, two per tape symbol. -/
noncomputable def absorbTiles (tm : SingleTapeTM Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (Finset.univ : Finset (Option Symbol)).toList.flatMap (absorbTilesFor tm)

/-- The transition tiles for a single `(q, a)` pair: depending on the
    movement direction, this is either a single tile (no movement),
    two tiles (right move + boundary), or `1 + |Option Symbol|` tiles
    (left move at boundary + one per possible left-neighbour symbol). -/
noncomputable def transitionTilesFor (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) : List (Tile (Alpha tm.State Symbol)) :=
  match tm.tr q a with
  | (⟨w, none⟩, qNew) =>
      [noMoveTile tm q a qNew w]
  | (⟨w, some Dir.right⟩, qNew) =>
      [rightMoveTile tm q a qNew w, rightMoveBoundaryTile tm q a qNew w]
  | (⟨w, some Dir.left⟩, qNew) =>
      leftMoveBoundaryTile tm q a qNew w ::
      (Finset.univ : Finset (Option Symbol)).toList.map
        (fun b => leftMoveTile tm q a qNew w b)

/-- All transition tiles, ranging over every `(q, a)` input pair. -/
noncomputable def transitionTiles (tm : SingleTapeTM Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (Finset.univ : Finset (tm.State × Option Symbol)).toList.flatMap
    (fun qa => transitionTilesFor tm qa.1 qa.2)

/-- The full list of MPCP tiles for the reduction (excluding the start
    tile, which is the dedicated start argument of `MHasSolution`).

    This is `noncomputable` because it relies on `Finset.toList`, which is
    noncomputable in Lean. The underlying enumeration is conceptually a
    finite set of tiles — we use it only as a mathematical object inside
    `MHasSolution`. -/
noncomputable def luTiles (tm : SingleTapeTM Symbol) :
    Stack (Alpha tm.State Symbol) :=
  copyTiles tm ++
  [sepTile tm] ++
  transitionTiles tm ++
  absorbTiles tm ++
  [finalTile tm]

/-! ## The reduction

Pair the start tile with the rest of the tiles. The MPCP instance for
`Halts tm w` is `MHasSolution (startTile tm w) (luTiles tm)`. -/

/-- The reduction `Lu ≤_m MPCP` packaged as a function from
    `(tm, w)` to an MPCP instance `(start, rest)`. -/
noncomputable def luToMpcp (tm : SingleTapeTM Symbol) (w : List Symbol) :
    Tile (Alpha tm.State Symbol) × Stack (Alpha tm.State Symbol) :=
  (startTile tm w, luTiles tm)

/-! ## Tile-membership lemmas

These are the basic facts that the constructed tiles actually belong to
`luTiles tm`. They form the bookkeeping backbone of both directions of
the main theorem (the start-tile is *not* in `luTiles` — it is the
forced start argument of `MHasSolution`). -/

/-- The copy tile for `a` is in `luTiles`. -/
lemma copyTile_mem_luTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    copyTile tm a ∈ luTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  exact List.mem_map.mpr ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩

/-- The separator-copy tile is in `luTiles`. -/
lemma sepTile_mem_luTiles (tm : SingleTapeTM Symbol) :
    sepTile tm ∈ luTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The final tile is in `luTiles`. -/
lemma finalTile_mem_luTiles (tm : SingleTapeTM Symbol) :
    finalTile tm ∈ luTiles tm := by
  refine List.mem_append_right _ ?_
  exact List.mem_singleton.mpr rfl

/-- The left halt-absorb tile for `a` is in `luTiles`. -/
lemma absorbLeftTile_mem_luTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    absorbLeftTile tm a ∈ luTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_right _ ?_
  refine List.mem_flatMap.mpr ?_
  refine ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), ?_⟩
  exact List.mem_cons_self

/-- The right halt-absorb tile for `a` is in `luTiles`. -/
lemma absorbRightTile_mem_luTiles (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    absorbRightTile tm a ∈ luTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_right _ ?_
  refine List.mem_flatMap.mpr ?_
  refine ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), ?_⟩
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Helper: every tile produced by `transitionTilesFor tm q a` belongs to
    `transitionTiles tm`. -/
lemma transitionTilesFor_subset_transitionTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (t : Tile (Alpha tm.State Symbol))
    (ht : t ∈ transitionTilesFor tm q a) :
    t ∈ transitionTiles tm := by
  refine List.mem_flatMap.mpr ⟨(q, a), ?_, ht⟩
  exact Finset.mem_toList.mpr (Finset.mem_univ _)

/-- Every transition tile is in `luTiles`. -/
lemma transitionTile_mem_luTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (t : Tile (Alpha tm.State Symbol))
    (ht : t ∈ transitionTilesFor tm q a) :
    t ∈ luTiles tm := by
  refine List.mem_append_left _ ?_
  refine List.mem_append_left _ ?_
  refine List.mem_append_right _ ?_
  exact transitionTilesFor_subset_transitionTiles tm q a t ht

/-! ## Concatenation lemmas for sequences of copy tiles

The forward direction of the main reduction repeatedly concatenates copy
tiles to walk through the unchanged portion of a configuration. These
lemmas reduce `tau1`/`tau2` of such sequences to the underlying lifted
tape list. -/

/-- The top of a sequence of copy tiles is the lifted tape list. -/
@[simp]
lemma tau1_map_copyTile (tm : SingleTapeTM Symbol) (syms : List (Option Symbol)) :
    tau1 (syms.map (copyTile tm)) = liftTape tm syms := by
  induction syms with
  | nil => rfl
  | cons a syms ih => simp [tau1_cons, ih, liftTape]

/-- The bottom of a sequence of copy tiles is the lifted tape list. -/
@[simp]
lemma tau2_map_copyTile (tm : SingleTapeTM Symbol) (syms : List (Option Symbol)) :
    tau2 (syms.map (copyTile tm)) = liftTape tm syms := by
  induction syms with
  | nil => rfl
  | cons a syms ih => simp [tau2_cons, ih, liftTape]

/-- The top of a single-tile stack is just that tile's top. -/
@[simp]
lemma tau1_singleton (tm : SingleTapeTM Symbol) (t : Tile (Alpha tm.State Symbol)) :
    tau1 [t] = t.top := by
  simp [tau1_cons]

/-- The bottom of a single-tile stack is just that tile's bottom. -/
@[simp]
lemma tau2_singleton (tm : SingleTapeTM Symbol) (t : Tile (Alpha tm.State Symbol)) :
    tau2 [t] = t.bot := by
  simp [tau2_cons]

/-- A list of copy tiles consists entirely of tiles from `luTiles`. -/
lemma map_copyTile_subset_luTiles (tm : SingleTapeTM Symbol)
    (syms : List (Option Symbol)) (t : Tile (Alpha tm.State Symbol))
    (ht : t ∈ syms.map (copyTile tm)) :
    t ∈ luTiles tm := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
  exact copyTile_mem_luTiles tm a

/-! ## Structural facts about `startTile` and `block` -/

@[simp]
lemma startTile_top (tm : SingleTapeTM Symbol) (w : List Symbol) :
    (startTile tm w).top = [#] := rfl

@[simp]
lemma startTile_bot (tm : SingleTapeTM Symbol) (w : List Symbol) :
    (startTile tm w).bot =
      # :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] := rfl

@[simp]
lemma block_eq (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    block tm cfg = # :: encodeCfg tm cfg ++ [#] := rfl

/-! ## Simulation tiles for one TM step (no-move case)

For a TM step `(q, t.head) → ((w, none), qNew)` where `none` is the
no-move direction, the simulation tile sequence is:

  copy l_n … copy l_1   transition   copy r_1 … copy r_m   sepTile

with `tau1` reproducing the *old* configuration block and `tau2`
producing the *new* configuration block. -/

/-- Tile sequence simulating a single no-move TM step. -/
def stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [noMoveTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma noMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (noMoveTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

@[simp] lemma noMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (noMoveTile tm q a qNew w).bot = [stateMarker tm qNew, ↟ₜw] := rfl

/-- The top concatenation of `stepTilesNoMove` reproduces the *current*
    configuration block (modulo the leading `#` which is shared with the
    previous block). -/
lemma tau1_stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau1 (stepTilesNoMove tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesNoMove, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, noMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesNoMove` produces the *next*
    configuration block — the one obtained by writing `w` and not moving,
    with new state `qNew`. -/
lemma tau2_stepTilesNoMove (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesNoMove tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [stateMarker tm qNew] ++
      liftTape tm (w :: t.right.toList) ++
      [#] := by
  simp only [stepTilesNoMove, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, noMoveTile_bot, sepTile_bot,
             List.append_nil, liftTape_cons]
  simp [List.append_assoc]

/-- Every tile in `stepTilesNoMove` is a member of `luTiles`. -/
lemma stepTilesNoMove_subset_luTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, none⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesNoMove tm q qNew t w) :
    tile ∈ luTiles tm := by
  simp only [stepTilesNoMove, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · -- copy of a left symbol
    exact map_copyTile_subset_luTiles tm _ tile hl
  · -- the transition tile itself
    refine transitionTile_mem_luTiles tm q a _ ?_
    simp only [transitionTilesFor]
    rw [show tm.tr q a = (⟨w, none⟩, qNew) from htr]
    subst hhead
    exact List.mem_cons_self
  · -- copy of a right symbol
    exact map_copyTile_subset_luTiles tm _ tile hr
  · -- the separator tile
    exact sepTile_mem_luTiles tm

/-! ## Simulation tiles for one TM step (right-move, interior case)

For a TM step `tm.tr q t.head = (⟨w, some right⟩, qNew)` where
`t.right.toList ≠ []` (the head is not at the right boundary of the
encoded window), the simulation tile sequence is:

  copy l_n … copy l_1   rightMoveTile   copy r_1 … copy r_m   sepTile

The `tau1` reproduces the *current* configuration block (modulo the
leading `#` shared with the previous block). The `tau2` extends
`bot` by an explicit list expression which agrees with
`encodeCfg(next config) ++ [#]` whenever the move does not run into
the cslib `StackTape.cons` blank-stripping degenerate case
(`w = none ∧ t.left.toList = []`). -/

/-- Tile sequence simulating a single right-move TM step in the
    *interior* (when `t.right` is non-empty). -/
def stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [rightMoveTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma rightMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (rightMoveTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

@[simp] lemma rightMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    (rightMoveTile tm q a qNew w).bot = [↟ₜw, stateMarker tm qNew] := rfl

/-- The top concatenation of `stepTilesRightInterior` reproduces the
    *current* configuration block — exactly as in the no-move case,
    since the top side of the transition tile records `q` and the
    head symbol identically in both cases. -/
lemma tau1_stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau1 (stepTilesRightInterior tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesRightInterior, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, rightMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesRightInterior`, in explicit
    list form. The connection to `encodeCfg` of the post-step
    configuration requires non-degeneracy
    (`w = some _ ∨ t.left.toList ≠ []`) — see
    `encodeCfg_after_right_move_eq` below. -/
lemma tau2_stepTilesRightInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesRightInterior tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesRightInterior, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, rightMoveTile_bot, sepTile_bot,
             List.append_nil]

/-- Every tile in `stepTilesRightInterior` is a member of `luTiles`. -/
lemma stepTilesRightInterior_subset_luTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.right⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesRightInterior tm q qNew t w) :
    tile ∈ luTiles tm := by
  simp only [stepTilesRightInterior, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · -- copy of a left symbol
    exact map_copyTile_subset_luTiles tm _ tile hl
  · -- the transition tile itself
    refine transitionTile_mem_luTiles tm q a _ ?_
    simp only [transitionTilesFor]
    rw [show tm.tr q a = (⟨w, some Dir.right⟩, qNew) from htr]
    subst hhead
    exact List.mem_cons_self
  · -- copy of a right symbol
    exact map_copyTile_subset_luTiles tm _ tile hr
  · -- the separator tile
    exact sepTile_mem_luTiles tm

/-! ### Connecting `tau2_stepTilesRightInterior` to `encodeCfg` of the
    post-step configuration (non-degenerate case). -/

omit [Inhabited Symbol] [Fintype Symbol] in
/-- In the non-degenerate case (`w ≠ none ∨ xs.toList ≠ []`),
    the cslib `StackTape.cons` does *not* strip blanks, so the new
    `toList` is exactly `w :: xs.toList`. -/
lemma cons_toList_of_nondeg (w : Option Symbol)
    (xs : Turing.StackTape Symbol)
    (h : w ≠ none ∨ xs.toList ≠ []) :
    (Turing.StackTape.cons w xs).toList = w :: xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with
  | nil =>
    cases w with
    | none =>
      rcases h with h | h
      · exact absurd rfl h
      · exact absurd rfl h
    | some s => rfl
  | cons hd tl' =>
    cases w with
    | none => rfl
    | some _ => rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- For a non-empty `StackTape`, `head :: tail.toList = toList`. This
    is the `toList`-projection of cslib's `cons_head_tail`, valid
    whenever `xs.toList` is non-empty (so that `cons xs.head xs.tail`
    does not degenerate). -/
lemma head_cons_tail_toList (xs : Turing.StackTape Symbol)
    (h : xs.toList ≠ []) :
    xs.head :: xs.tail.toList = xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with
  | nil => exact absurd rfl h
  | cons a rest => rfl

/-- Lifted form of `head_cons_tail_toList`: when `xs.toList ≠ []`,
    rewriting `↟ₜxs.head :: liftTape tm xs.tail.toList` to
    `liftTape tm xs.toList`. -/
lemma liftTape_head_cons_tail_toList (tm : SingleTapeTM Symbol)
    (xs : Turing.StackTape Symbol) (h : xs.toList ≠ []) :
    ↟ₜxs.head :: liftTape tm xs.tail.toList = liftTape tm xs.toList := by
  rw [show (↟ₜxs.head : Alpha tm.State Symbol) :: liftTape tm xs.tail.toList
       = liftTape tm (xs.head :: xs.tail.toList) from rfl,
      head_cons_tail_toList _ h]

/-- The encoding of the configuration after one right-move step,
    in the non-degenerate case (so the new left side really is
    `w :: t.left.toList`). -/
lemma encodeCfg_after_right_move_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_ne : t.right.toList ≠ []) :
    encodeCfg tm ⟨qNew, (t.write w).move_right⟩ =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew] ++
      liftTape tm t.right.toList := by
  -- Unfold the cslib step on the BiTape side.
  have h_left :
      ((t.write w).move_right).left.toList = w :: t.left.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.left h_nondeg
  have h_head : ((t.write w).move_right).head = t.right.head := rfl
  have h_right :
      ((t.write w).move_right).right.toList = t.right.tail.toList := rfl
  -- Now compute the encoding.
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_none]
    rw [liftTape_head_cons_tail_toList _ _ h_right_ne]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_some]
    rw [liftTape_head_cons_tail_toList _ _ h_right_ne]
    simp [List.append_assoc]

/-- Combined statement: in the non-degenerate, interior right-move
    case, `tau2 = encodeCfg(post-step config) ++ [#]`, matching the
    simulation invariant. -/
lemma tau2_stepTilesRightInterior_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_ne : t.right.toList ≠ []) :
    tau2 (stepTilesRightInterior tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_right⟩ ++ [#] := by
  rw [tau2_stepTilesRightInterior,
      encodeCfg_after_right_move_eq tm qNew t w h_nondeg h_right_ne]

end PCP.LuToMPCP
