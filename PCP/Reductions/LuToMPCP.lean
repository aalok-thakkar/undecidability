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
    `none` (blank) symbol to be inserted as the new head.
    Local rewrite: `↟ₛq ↟ₜa  →  qNew ↟ₜnone ↟ₜw`. The opening `#` of
    the block is NOT included here; it is the closing `#` of the
    previous block (already produced by the previous step's `sepTile`
    or the `startTile`). The new tile has top length 2 and bot
    length 3, the `none` extending the encoded window leftward. -/
def leftMoveBoundaryTile (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol) :
    Tile (Alpha tm.State Symbol) where
  top := [↟ₛq, ↟ₜa]
  bot := [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw]

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

/-! ## Simulation tiles for one TM step (right-move, boundary case)

When the head is at the right boundary of the encoded window
(`t.right.toList = []`), the right-move transition uses
`rightMoveBoundaryTile`, which packages the local rewrite together
with the closing `#` and the explicit blank for the new head:

  copy l_n … copy l_1   rightMoveBoundaryTile

The boundary tile already contains the closing `#`, so no separate
`sepTile` is appended. -/

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The `head` of a `StackTape` whose `toList` is empty is `none`. -/
lemma head_of_toList_eq_nil (xs : Turing.StackTape Symbol)
    (h : xs.toList = []) : xs.head = none := by
  obtain ⟨tl, hLast⟩ := xs
  simp only at h
  subst h
  rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The `tail` of an empty `StackTape` is also empty. -/
lemma tail_toList_of_toList_eq_nil (xs : Turing.StackTape Symbol)
    (h : xs.toList = []) : xs.tail.toList = [] := by
  obtain ⟨tl, hLast⟩ := xs
  simp only at h
  subst h
  rfl

/-- Tile sequence simulating a single right-move TM step in the
    *boundary* case (`t.right.toList = []`). -/
def stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.toList.reverse.map (copyTile tm)) ++
  [rightMoveBoundaryTile tm q t.head qNew w]

@[simp] lemma rightMoveBoundaryTile_top (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (rightMoveBoundaryTile tm q a qNew w).top = [↟ₛq, ↟ₜa, #] := rfl

@[simp] lemma rightMoveBoundaryTile_bot (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (rightMoveBoundaryTile tm q a qNew w).bot =
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #] := rfl

/-- The top concatenation of `stepTilesRightBoundary` reproduces the
    *current* configuration block. The hypothesis
    `t.right.toList = []` is used to simplify the encoding (no right
    symbols to copy after the transition tile). -/
lemma tau1_stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_right_empty : t.right.toList = []) :
    tau1 (stepTilesRightBoundary tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesRightBoundary, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, rightMoveBoundaryTile_top,
             List.append_nil, encodeRunningCfg, h_right_empty,
             liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesRightBoundary`, in explicit
    list form. -/
lemma tau2_stepTilesRightBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesRightBoundary tm q qNew t w) =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol), #] := by
  simp only [stepTilesRightBoundary, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, rightMoveBoundaryTile_bot,
             List.append_nil]

/-- Every tile in `stepTilesRightBoundary` is a member of `luTiles`. -/
lemma stepTilesRightBoundary_subset_luTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.right⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesRightBoundary tm q qNew t w) :
    tile ∈ luTiles tm := by
  simp only [stepTilesRightBoundary, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with hl | rfl
  · -- copy of a left symbol
    exact map_copyTile_subset_luTiles tm _ tile hl
  · -- the right-move boundary tile
    refine transitionTile_mem_luTiles tm q a _ ?_
    simp only [transitionTilesFor]
    rw [show tm.tr q a = (⟨w, some Dir.right⟩, qNew) from htr]
    subst hhead
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The encoding of the configuration after one right-move step at
    the right boundary, in the non-degenerate case. -/
lemma encodeCfg_after_right_move_boundary_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_empty : t.right.toList = []) :
    encodeCfg tm ⟨qNew, (t.write w).move_right⟩ =
      liftTape tm t.left.toList.reverse ++
      [↟ₜw, stateMarker tm qNew, ↟ₜ(none : Option Symbol)] := by
  have h_left :
      ((t.write w).move_right).left.toList = w :: t.left.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.left h_nondeg
  have h_head : ((t.write w).move_right).head = none := by
    show t.right.head = _
    exact head_of_toList_eq_nil _ h_right_empty
  have h_right :
      ((t.write w).move_right).right.toList = [] := by
    show t.right.tail.toList = _
    exact tail_toList_of_toList_eq_nil _ h_right_empty
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_none]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_cons, liftTape_append, liftTape_cons,
               liftTape_nil, stateMarker_some]
    simp [List.append_assoc]

/-- Combined statement: in the non-degenerate right-move boundary
    case, `tau2 = encodeCfg(post-step config) ++ [#]`. -/
lemma tau2_stepTilesRightBoundary_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.left.toList ≠ [])
    (h_right_empty : t.right.toList = []) :
    tau2 (stepTilesRightBoundary tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_right⟩ ++ [#] := by
  rw [tau2_stepTilesRightBoundary,
      encodeCfg_after_right_move_boundary_eq tm qNew t w h_nondeg h_right_empty]
  simp [List.append_assoc]

/-! ## Simulation tiles for one TM step (left-move, interior case)

For a TM step `tm.tr q t.head = (⟨w, some left⟩, qNew)` where the head
is *not* at the left boundary (`t.left.toList ≠ []`), the simulation
tile sequence is:

  copy l_n … copy l_2   leftMoveTile (b = l_1)   copy r_1 … copy r_m   sepTile

The `leftMoveTile` swaps the local window
`l_1 q t.head  →  qNew l_1 w`, where `l_1 = t.left.head` is the symbol
that becomes the new head after moving left. -/

/-- The `leftMoveTile` for any "left-neighbour" symbol `b` belongs to
    `transitionTilesFor q a` whenever the TM transition there is a
    left move. -/
lemma leftMoveTile_mem_transitionTilesFor (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (w : Option Symbol)
    (qNew : Option tm.State) (b : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.left⟩, qNew)) :
    leftMoveTile tm q a qNew w b ∈ transitionTilesFor tm q a := by
  simp only [transitionTilesFor]
  rw [htr]
  refine List.mem_cons_of_mem _ (List.mem_map.mpr ?_)
  exact ⟨b, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩

/-- The `leftMoveBoundaryTile` belongs to `transitionTilesFor q a` whenever
    the TM transition there is a left move. -/
lemma leftMoveBoundaryTile_mem_transitionTilesFor (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (w : Option Symbol)
    (qNew : Option tm.State)
    (htr : tm.tr q a = (⟨w, some Dir.left⟩, qNew)) :
    leftMoveBoundaryTile tm q a qNew w ∈ transitionTilesFor tm q a := by
  simp only [transitionTilesFor]
  rw [htr]
  exact List.mem_cons_self

/-- Tile sequence simulating a single left-move TM step in the
    *interior* (when `t.left` is non-empty). -/
def stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  (t.left.tail.toList.reverse.map (copyTile tm)) ++
  [leftMoveTile tm q t.head qNew w t.left.head] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma leftMoveTile_top (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol)
    (b : Option Symbol) :
    (leftMoveTile tm q a qNew w b).top = [↟ₜb, ↟ₛq, ↟ₜa] := rfl

@[simp] lemma leftMoveTile_bot (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (qNew : Option tm.State) (w : Option Symbol)
    (b : Option Symbol) :
    (leftMoveTile tm q a qNew w b).bot =
      [stateMarker tm qNew, ↟ₜb, ↟ₜw] := rfl

/-- The top concatenation of `stepTilesLeftInterior` reproduces the
    *current* configuration block. The hypothesis
    `t.left.toList ≠ []` is used to splice the head of `t.left` back
    into the encoding via `head_cons_tail_toList`. -/
lemma tau1_stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_left_ne : t.left.toList ≠ []) :
    tau1 (stepTilesLeftInterior tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesLeftInterior, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, leftMoveTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, liftTape_cons]
  have h_split :
      t.left.toList.reverse = t.left.tail.toList.reverse ++ [t.left.head] := by
    conv_lhs => rw [← head_cons_tail_toList t.left h_left_ne]
    simp [List.reverse_cons]
  rw [h_split, liftTape_append, liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesLeftInterior`, in explicit
    list form. -/
lemma tau2_stepTilesLeftInterior (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesLeftInterior tm q qNew t w) =
      liftTape tm t.left.tail.toList.reverse ++
      [stateMarker tm qNew, ↟ₜt.left.head, ↟ₜw] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesLeftInterior, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, leftMoveTile_bot, sepTile_bot,
             List.append_nil]

/-- Every tile in `stepTilesLeftInterior` is a member of `luTiles`. -/
lemma stepTilesLeftInterior_subset_luTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.left⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesLeftInterior tm q qNew t w) :
    tile ∈ luTiles tm := by
  simp only [stepTilesLeftInterior, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_luTiles tm _ tile hl
  · refine transitionTile_mem_luTiles tm q a _ ?_
    subst hhead
    exact leftMoveTile_mem_transitionTilesFor tm q t.head w qNew t.left.head htr
  · exact map_copyTile_subset_luTiles tm _ tile hr
  · exact sepTile_mem_luTiles tm

/-- The encoding of the configuration after one left-move step,
    in the non-degenerate case (so the new right side really is
    `w :: t.right.toList`). Note: this holds regardless of whether
    `t.left` is empty — when `t.left` is empty, `tail` is empty and
    `head` is `none`, so both sides reduce to the same expression. -/
lemma encodeCfg_after_left_move_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ []) :
    encodeCfg tm ⟨qNew, (t.write w).move_left⟩ =
      liftTape tm t.left.tail.toList.reverse ++
      [stateMarker tm qNew, ↟ₜt.left.head, ↟ₜw] ++
      liftTape tm t.right.toList := by
  have h_left :
      ((t.write w).move_left).left.toList = t.left.tail.toList := rfl
  have h_head : ((t.write w).move_left).head = t.left.head := rfl
  have h_right :
      ((t.write w).move_left).right.toList = w :: t.right.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.right h_nondeg
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               liftTape_cons, stateMarker_none]
    simp [List.append_assoc]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               liftTape_cons, stateMarker_some]
    simp [List.append_assoc]

/-- Combined statement: in the non-degenerate left-move interior
    case, `tau2 = encodeCfg(post-step config) ++ [#]`. -/
lemma tau2_stepTilesLeftInterior_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ []) :
    tau2 (stepTilesLeftInterior tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_left⟩ ++ [#] := by
  rw [tau2_stepTilesLeftInterior,
      encodeCfg_after_left_move_eq tm qNew t w h_nondeg]

/-! ## Simulation tiles for one TM step (left-move, boundary case)

When the head is at the left boundary of the encoded window
(`t.left.toList = []`), the left-move transition uses
`leftMoveBoundaryTile`, which inserts an explicit `none` for the new
head (extending the encoded window leftward by one blank). The
opening `#` of the block stays with the previous step's `sepTile`
(or `startTile`), so the boundary tile here, like the no-move and
right-interior tiles, contains no leading or trailing `#`. -/

/-- Tile sequence simulating a single left-move TM step in the
    *boundary* case (`t.left.toList = []`). -/
def stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    List (Tile (Alpha tm.State Symbol)) :=
  [leftMoveBoundaryTile tm q t.head qNew w] ++
  (t.right.toList.map (copyTile tm)) ++
  [sepTile tm]

@[simp] lemma leftMoveBoundaryTile_top (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (leftMoveBoundaryTile tm q a qNew w).top = [↟ₛq, ↟ₜa] := rfl

@[simp] lemma leftMoveBoundaryTile_bot (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (w : Option Symbol) :
    (leftMoveBoundaryTile tm q a qNew w).bot =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] := rfl

/-- The top concatenation of `stepTilesLeftBoundary` reproduces the
    *current* configuration block. Uses `t.left.toList = []` to
    simplify the encoding. -/
lemma tau1_stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_left_empty : t.left.toList = []) :
    tau1 (stepTilesLeftBoundary tm q qNew t w) =
      encodeRunningCfg tm q t ++ [#] := by
  simp only [stepTilesLeftBoundary, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, leftMoveBoundaryTile_top, sepTile_top,
             List.append_nil, encodeRunningCfg, h_left_empty,
             liftTape_cons, liftTape_nil, List.reverse_nil]
  simp [List.append_assoc]

/-- The bottom concatenation of `stepTilesLeftBoundary`, in explicit
    list form. -/
lemma tau2_stepTilesLeftBoundary (tm : SingleTapeTM Symbol) (q : tm.State)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    tau2 (stepTilesLeftBoundary tm q qNew t w) =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] ++
      liftTape tm t.right.toList ++
      [#] := by
  simp only [stepTilesLeftBoundary, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, leftMoveBoundaryTile_bot, sepTile_bot,
             List.append_nil]

/-- Every tile in `stepTilesLeftBoundary` is a member of `luTiles`. -/
lemma stepTilesLeftBoundary_subset_luTiles (tm : SingleTapeTM Symbol)
    (q : tm.State) (a : Option Symbol) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (htr : tm.tr q a = (⟨w, some Dir.left⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesLeftBoundary tm q qNew t w) :
    tile ∈ luTiles tm := by
  simp only [stepTilesLeftBoundary, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with (rfl | hr) | rfl
  · -- the boundary tile
    refine transitionTile_mem_luTiles tm q a _ ?_
    subst hhead
    exact leftMoveBoundaryTile_mem_transitionTilesFor tm q t.head w qNew htr
  · -- copy of a right symbol
    exact map_copyTile_subset_luTiles tm _ tile hr
  · -- the separator tile
    exact sepTile_mem_luTiles tm

/-- The encoding of the configuration after one left-move step at the
    left boundary, in the non-degenerate case. -/
lemma encodeCfg_after_left_move_boundary_eq (tm : SingleTapeTM Symbol)
    (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (h_left_empty : t.left.toList = []) :
    encodeCfg tm ⟨qNew, (t.write w).move_left⟩ =
      [stateMarker tm qNew, ↟ₜ(none : Option Symbol), ↟ₜw] ++
      liftTape tm t.right.toList := by
  have h_left :
      ((t.write w).move_left).left.toList = [] := by
    show t.left.tail.toList = _
    exact tail_toList_of_toList_eq_nil _ h_left_empty
  have h_head : ((t.write w).move_left).head = none := by
    show t.left.head = _
    exact head_of_toList_eq_nil _ h_left_empty
  have h_right :
      ((t.write w).move_left).right.toList = w :: t.right.toList := by
    show (Turing.StackTape.cons _ _).toList = _
    exact cons_toList_of_nondeg w t.right h_nondeg
  cases qNew with
  | none =>
    show encodeHaltedCfg tm _ = _
    simp only [encodeHaltedCfg, h_left, h_head, h_right,
               List.reverse_nil, liftTape_cons, liftTape_nil,
               stateMarker_none, List.nil_append, List.cons_append]
  | some q' =>
    show encodeRunningCfg tm q' _ = _
    simp only [encodeRunningCfg, h_left, h_head, h_right,
               List.reverse_nil, liftTape_cons, liftTape_nil,
               stateMarker_some, List.nil_append, List.cons_append]

/-- Combined statement: in the non-degenerate left-move boundary
    case, `tau2 = encodeCfg(post-step config) ++ [#]`. -/
lemma tau2_stepTilesLeftBoundary_eq_encodeCfg (tm : SingleTapeTM Symbol)
    (q : tm.State) (qNew : Option tm.State)
    (t : BiTape Symbol) (w : Option Symbol)
    (h_nondeg : w ≠ none ∨ t.right.toList ≠ [])
    (h_left_empty : t.left.toList = []) :
    tau2 (stepTilesLeftBoundary tm q qNew t w) =
      encodeCfg tm ⟨qNew, (t.write w).move_left⟩ ++ [#] := by
  rw [tau2_stepTilesLeftBoundary,
      encodeCfg_after_left_move_boundary_eq tm qNew t w h_nondeg h_left_empty]

/-! ## Halt-absorption phase

After the TM halts the lookahead in `bot` ends with the encoded halt
configuration

  `[l_n … l_1, h⊥, head, r_1 … r_m, #]`.

We catch `top` up by repeatedly applying *absorb-left* and
*absorb-right* iterations, each shrinking the encoded window by
exactly one tape symbol. After all `n + (m+1)` iterations the
remaining lookahead is `[h⊥, #]`, which the `finalTile` then closes:
`(h⊥ # #, #)` makes `top` and `bot` equal.

Because the absorption phase eventually shrinks past the BiTape head
itself (which always has a value, even when blank), it is cleanest to
parameterise the iteration on raw `List (Option Symbol)` rather than
on `BiTape`. -/

/-- The *list-parameterised* halted encoding: `# ... l_n … l_1 h⊥ r ... #`
    (without the surrounding `#`s; those appear in the calling context). -/
def encodeHaltList (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol)) : List (Alpha tm.State Symbol) :=
  liftTape tm left.reverse ++ [h⊥] ++ liftTape tm right

/-- Bridge: the BiTape-based halted encoding equals the list-parameterised
    one with `left = t.left.toList` and `right = t.head :: t.right.toList`. -/
lemma encodeHaltedCfg_eq_encodeHaltList (tm : SingleTapeTM Symbol)
    (t : BiTape Symbol) :
    encodeHaltedCfg tm t =
      encodeHaltList tm t.left.toList (t.head :: t.right.toList) := by
  simp [encodeHaltedCfg, encodeHaltList, List.append_assoc]

@[simp] lemma absorbLeftTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbLeftTile tm a).top = [↟ₜa, h⊥] := rfl

@[simp] lemma absorbLeftTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbLeftTile tm a).bot = [h⊥] := rfl

@[simp] lemma absorbRightTile_top (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbRightTile tm a).top = [h⊥, ↟ₜa] := rfl

@[simp] lemma absorbRightTile_bot (tm : SingleTapeTM Symbol) (a : Option Symbol) :
    (absorbRightTile tm a).bot = [h⊥] := rfl

/-- Tile sequence for one *absorb-left* iteration. Removes the
    innermost left symbol `l` from the encoding `encodeHaltList (l :: rest) right`,
    yielding `encodeHaltList rest right`. -/
def stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    List (Tile (Alpha tm.State Symbol)) :=
  rest.reverse.map (copyTile tm) ++
  [absorbLeftTile tm l] ++
  right.map (copyTile tm) ++
  [sepTile tm]

/-- Tile sequence for one *absorb-right* iteration. Removes the
    leftmost right symbol `r` from the encoding `encodeHaltList left (r :: rest)`,
    yielding `encodeHaltList left rest`. -/
def stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol)) :
    List (Tile (Alpha tm.State Symbol)) :=
  left.reverse.map (copyTile tm) ++
  [absorbRightTile tm r] ++
  rest.map (copyTile tm) ++
  [sepTile tm]

/-! ### `tau1` / `tau2` for one absorption iteration -/

lemma tau1_stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    tau1 (stepTilesAbsorbLeft tm l rest right) =
      encodeHaltList tm (l :: rest) right ++ [#] := by
  simp only [stepTilesAbsorbLeft, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, absorbLeftTile_top, sepTile_top,
             List.append_nil, encodeHaltList,
             List.reverse_cons, liftTape_append, liftTape_cons, liftTape_nil]
  simp [List.append_assoc]

lemma tau2_stepTilesAbsorbLeft (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol)) :
    tau2 (stepTilesAbsorbLeft tm l rest right) =
      encodeHaltList tm rest right ++ [#] := by
  simp only [stepTilesAbsorbLeft, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, absorbLeftTile_bot, sepTile_bot,
             List.append_nil, encodeHaltList]

lemma tau1_stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol)) :
    tau1 (stepTilesAbsorbRight tm left r rest) =
      encodeHaltList tm left (r :: rest) ++ [#] := by
  simp only [stepTilesAbsorbRight, tau1_append, tau1_cons, tau1_nil,
             tau1_map_copyTile, absorbRightTile_top, sepTile_top,
             List.append_nil, encodeHaltList, liftTape_cons]
  simp [List.append_assoc]

lemma tau2_stepTilesAbsorbRight (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol)) :
    tau2 (stepTilesAbsorbRight tm left r rest) =
      encodeHaltList tm left rest ++ [#] := by
  simp only [stepTilesAbsorbRight, tau2_append, tau2_cons, tau2_nil,
             tau2_map_copyTile, absorbRightTile_bot, sepTile_bot,
             List.append_nil, encodeHaltList]

/-! ### Membership of absorption iterations in `luTiles` -/

lemma stepTilesAbsorbLeft_subset_luTiles (tm : SingleTapeTM Symbol)
    (l : Option Symbol) (rest right : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAbsorbLeft tm l rest right) :
    tile ∈ luTiles tm := by
  simp only [stepTilesAbsorbLeft, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_luTiles tm _ tile hl
  · exact absorbLeftTile_mem_luTiles tm l
  · exact map_copyTile_subset_luTiles tm _ tile hr
  · exact sepTile_mem_luTiles tm

lemma stepTilesAbsorbRight_subset_luTiles (tm : SingleTapeTM Symbol)
    (left : List (Option Symbol)) (r : Option Symbol)
    (rest : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAbsorbRight tm left r rest) :
    tile ∈ luTiles tm := by
  simp only [stepTilesAbsorbRight, List.mem_append, List.mem_cons,
             List.not_mem_nil, or_false] at htile
  rcases htile with ((hl | rfl) | hr) | rfl
  · exact map_copyTile_subset_luTiles tm _ tile hl
  · exact absorbRightTile_mem_luTiles tm r
  · exact map_copyTile_subset_luTiles tm _ tile hr
  · exact sepTile_mem_luTiles tm

/-! ### `absorbAndFinish`: the absorption-phase tile suffix

Given a halt config presented as raw lists `(left, right)`, produce
the full tile sequence that:
1. Iteratively absorbs each left symbol (innermost first), then each
   right symbol (leftmost first), shrinking the encoded window down
   to `[h⊥]`.
2. Ends with `finalTile`.

The matching invariant
  `tau1 = encodeHaltList tm left right ++ [#] ++ tau2`
holds for every `(left, right)`, by structural induction. -/
def absorbAndFinish (tm : SingleTapeTM Symbol) :
    List (Option Symbol) → List (Option Symbol) →
      Stack (Alpha tm.State Symbol)
  | [],         []          => [finalTile tm]
  | [],         r :: rest   => stepTilesAbsorbRight tm [] r rest ++
                                 absorbAndFinish tm [] rest
  | l :: rest,  right       => stepTilesAbsorbLeft tm l rest right ++
                                 absorbAndFinish tm rest right

/-- The matching invariant for `absorbAndFinish`. -/
lemma absorbAndFinish_matching (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol)) :
    tau1 (absorbAndFinish tm left right) =
      encodeHaltList tm left right ++ [#] ++
        tau2 (absorbAndFinish tm left right) := by
  induction left, right using absorbAndFinish.induct with
  | case1 =>
    -- left = [], right = []
    simp [absorbAndFinish, finalTile, encodeHaltList, liftTape]
  | case2 r rest ih =>
    -- left = [], right = r :: rest
    simp only [absorbAndFinish, tau1_append, tau2_append,
               tau1_stepTilesAbsorbRight, tau2_stepTilesAbsorbRight, ih,
               List.append_assoc]
  | case3 l rest right ih =>
    -- left = l :: rest, right = right
    simp only [absorbAndFinish, tau1_append, tau2_append,
               tau1_stepTilesAbsorbLeft, tau2_stepTilesAbsorbLeft, ih,
               List.append_assoc]

/-- Every tile in `absorbAndFinish` belongs to `luTiles`. -/
lemma absorbAndFinish_subset_luTiles (tm : SingleTapeTM Symbol)
    (left right : List (Option Symbol))
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ absorbAndFinish tm left right) :
    tile ∈ luTiles tm := by
  induction left, right using absorbAndFinish.induct with
  | case1 =>
    simp only [absorbAndFinish, List.mem_singleton] at htile
    rw [htile]
    exact finalTile_mem_luTiles tm
  | case2 r rest ih =>
    simp only [absorbAndFinish, List.mem_append] at htile
    rcases htile with hL | hR
    · exact stepTilesAbsorbRight_subset_luTiles tm [] r rest tile hL
    · exact ih hR
  | case3 l rest right ih =>
    simp only [absorbAndFinish, List.mem_append] at htile
    rcases htile with hL | hR
    · exact stepTilesAbsorbLeft_subset_luTiles tm l rest right tile hL
    · exact ih hR

/-! ## Dispatch over a single TM step

Given a running configuration `⟨some q, t⟩`, this section produces the
corresponding tile sequence and proves its `tau1`/`tau2`/membership
properties — dispatching on the direction and on the relevant
emptiness sub-case. The `tau2 = encodeCfg(post-step) ++ [#]`
identity holds under `NoBlankWrites`, which sidesteps the cslib
`StackTape.cons` blank-stripping degenerate sub-case where the TM
writes a blank and the corresponding side of the tape is empty. -/

/-- A TM is *blank-write free* iff its transition function never writes
    the blank symbol. This sidesteps the cslib `BiTape` stripping
    issue that arises in the `Lu ≤_m MPCP` simulation when a blank is
    written into a previously-empty boundary side. -/
def NoBlankWrites (tm : SingleTapeTM Symbol) : Prop :=
  ∀ q : tm.State, ∀ a : Option Symbol, ((tm.tr q a).1).symbol ≠ none

/-- The configuration reached by a single TM step from `⟨some q, t⟩`. -/
def stepResult (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    tm.Cfg :=
  ⟨(tm.tr q t.head).2,
    (t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement⟩

@[simp] lemma tm_step_running (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) :
    tm.step ⟨some q, t⟩ = some (stepResult tm q t) := by
  simp only [SingleTapeTM.step, stepResult]

/-- Auxiliary dispatcher: given the destructured pieces of one TM step
    `(w, mov, qNew)` (the symbol to write, the direction, and the new
    state) plus the current tape `t`, produce the simulation tile
    sequence. -/
def stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol)
    (w : Option Symbol) (mov : Option Dir) (qNew : Option tm.State) :
    Stack (Alpha tm.State Symbol) :=
  match mov with
  | none           => stepTilesNoMove tm q qNew t w
  | some Dir.right =>
      match t.right.toList with
      | []       => stepTilesRightBoundary tm q qNew t w
      | _ :: _   => stepTilesRightInterior tm q qNew t w
  | some Dir.left  =>
      match t.left.toList with
      | []       => stepTilesLeftBoundary tm q qNew t w
      | _ :: _   => stepTilesLeftInterior tm q qNew t w

/-- The simulation tile sequence for one running TM step. -/
def stepTiles (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    Stack (Alpha tm.State Symbol) :=
  stepTilesAux tm q t (tm.tr q t.head).1.symbol
    (tm.tr q t.head).1.movement (tm.tr q t.head).2

/-! ### Lemmas about `stepTilesAux`

These lemmas dispatch on the explicit `mov` parameter and the relevant
emptiness sub-case. Because `mov`, `t.left.toList`, and `t.right.toList`
are simple types (`Option Dir`, `List _`), case analysis is direct. -/

lemma tau1_stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) (w : Option Symbol) (mov : Option Dir)
    (qNew : Option tm.State) :
    tau1 (stepTilesAux tm q t w mov qNew) = encodeRunningCfg tm q t ++ [#] := by
  unfold stepTilesAux
  cases mov with
  | none => exact tau1_stepTilesNoMove tm q qNew t w
  | some dir =>
    cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil => exact tau1_stepTilesRightBoundary tm q qNew t w h_right
      | cons _ _ => exact tau1_stepTilesRightInterior tm q qNew t w
    | left =>
      cases h_left : t.left.toList with
      | nil => exact tau1_stepTilesLeftBoundary tm q qNew t w h_left
      | cons _ _ =>
        refine tau1_stepTilesLeftInterior tm q qNew t w ?_
        rw [h_left]; exact List.cons_ne_nil _ _

lemma stepTilesAux_subset_luTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (a : Option Symbol) (t : BiTape Symbol) (w : Option Symbol)
    (mov : Option Dir) (qNew : Option tm.State)
    (htr : tm.tr q a = (⟨w, mov⟩, qNew))
    (hhead : t.head = a)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTilesAux tm q t w mov qNew) :
    tile ∈ luTiles tm := by
  unfold stepTilesAux at htile
  cases mov with
  | none => exact stepTilesNoMove_subset_luTiles tm q a qNew t w htr hhead tile htile
  | some dir =>
    cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil =>
        rw [h_right] at htile
        exact stepTilesRightBoundary_subset_luTiles tm q a qNew t w htr hhead tile htile
      | cons _ _ =>
        rw [h_right] at htile
        exact stepTilesRightInterior_subset_luTiles tm q a qNew t w htr hhead tile htile
    | left =>
      cases h_left : t.left.toList with
      | nil =>
        rw [h_left] at htile
        exact stepTilesLeftBoundary_subset_luTiles tm q a qNew t w htr hhead tile htile
      | cons _ _ =>
        rw [h_left] at htile
        exact stepTilesLeftInterior_subset_luTiles tm q a qNew t w htr hhead tile htile

lemma tau2_stepTilesAux (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) (w : Option Symbol) (mov : Option Dir)
    (qNew : Option tm.State) (h_w_ne : w ≠ none) :
    tau2 (stepTilesAux tm q t w mov qNew) =
      encodeCfg tm ⟨qNew, (t.write w).optionMove mov⟩ ++ [#] := by
  unfold stepTilesAux
  cases mov with
  | none =>
    -- optionMove _ none = id; new tape is t.write w
    rw [tau2_stepTilesNoMove]
    show _ = encodeCfg tm ⟨qNew, t.write w⟩ ++ [#]
    cases qNew with
    | none =>
      simp only [encodeCfg_halted, encodeHaltedCfg, BiTape.write,
                 stateMarker_none, liftTape_cons, List.append_assoc,
                 List.cons_append, List.nil_append]
    | some q' =>
      simp only [encodeCfg_running, encodeRunningCfg, BiTape.write,
                 stateMarker_some, liftTape_cons, List.append_assoc,
                 List.cons_append, List.nil_append]
  | some dir =>
    cases dir with
    | right =>
      cases h_right : t.right.toList with
      | nil =>
        exact tau2_stepTilesRightBoundary_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne) h_right
      | cons _ _ =>
        refine tau2_stepTilesRightInterior_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne) ?_
        rw [h_right]; exact List.cons_ne_nil _ _
    | left =>
      cases h_left : t.left.toList with
      | nil =>
        exact tau2_stepTilesLeftBoundary_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne) h_left
      | cons _ _ =>
        exact tau2_stepTilesLeftInterior_eq_encodeCfg tm q qNew t w
          (Or.inl h_w_ne)

/-! ### Main `stepTiles` lemmas (derived from `stepTilesAux`) -/

/-- The top concatenation of `stepTiles` is the encoded current
    configuration block. -/
lemma tau1_stepTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol) :
    tau1 (stepTiles tm q t) = encodeRunningCfg tm q t ++ [#] := by
  unfold stepTiles
  exact tau1_stepTilesAux tm q t _ _ _

/-- Every tile in `stepTiles` is a member of `luTiles`. -/
lemma stepTiles_subset_luTiles (tm : SingleTapeTM Symbol) (q : tm.State)
    (t : BiTape Symbol)
    (tile : Tile (Alpha tm.State Symbol))
    (htile : tile ∈ stepTiles tm q t) :
    tile ∈ luTiles tm := by
  unfold stepTiles at htile
  -- Provide htr by unfolding the transition products.
  have htr : tm.tr q t.head =
      (⟨(tm.tr q t.head).1.symbol, (tm.tr q t.head).1.movement⟩, (tm.tr q t.head).2) := by
    rcases tm.tr q t.head with ⟨⟨_, _⟩, _⟩; rfl
  exact stepTilesAux_subset_luTiles tm q t.head t _ _ _ htr rfl tile htile

/-- The bottom concatenation of `stepTiles` is the encoded *next*
    configuration block. Requires `NoBlankWrites` to rule out the
    cslib `BiTape` blank-stripping sub-cases. -/
lemma tau2_stepTiles (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (q : tm.State) (t : BiTape Symbol) :
    tau2 (stepTiles tm q t) = encodeCfg tm (stepResult tm q t) ++ [#] := by
  unfold stepTiles stepResult
  exact tau2_stepTilesAux tm q t _ _ _ (h_nbw q t.head)

/-! ## Forward direction: `Halts → MHasSolution`

The forward-direction proof proceeds by induction on the length `n`
of the halting computation `cfg →ⁿ ⟨none, target_tape⟩`. The base
case (`n = 0`, i.e., `cfg` is already halted) uses `absorbAndFinish`
to shrink the encoded halt configuration down to `[h⊥]` and close
with `finalTile`. The inductive step prepends one `stepTiles`
sub-sequence and invokes the IH on the residual chain. -/

/-- The auxiliary forward lemma, indexed by the chain length `n`. -/
lemma forward_aux (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (target_tape : BiTape Symbol) :
    ∀ (cfg : tm.Cfg) (n : ℕ),
      Relation.RelatesInSteps tm.TransitionRelation cfg
        ⟨none, target_tape⟩ n →
      ∃ A : Stack (Alpha tm.State Symbol),
        (∀ tile ∈ A, tile ∈ luTiles tm) ∧
        tau1 A = encodeCfg tm cfg ++ [#] ++ tau2 A := by
  intro cfg n h_chain
  induction n generalizing cfg with
  | zero =>
    -- `cfg = ⟨none, target_tape⟩` by `RelatesInSteps.zero`.
    have hzero : cfg = ⟨none, target_tape⟩ := h_chain.zero
    subst hzero
    refine ⟨absorbAndFinish tm target_tape.left.toList
              (target_tape.head :: target_tape.right.toList),
            ?_, ?_⟩
    · intro tile htile
      exact absorbAndFinish_subset_luTiles tm _ _ tile htile
    · rw [show
          encodeCfg tm (⟨none, target_tape⟩ : tm.Cfg) = encodeHaltedCfg tm target_tape from rfl,
          encodeHaltedCfg_eq_encodeHaltList]
      exact absorbAndFinish_matching tm _ _
  | succ n ih =>
    -- Chain of length `n+1` decomposes as `cfg →¹ cfg' →ⁿ halted`.
    obtain ⟨cfg', h_step, h_rest⟩ := h_chain.succ'
    -- For `tm.step cfg = some cfg'`, we must have `cfg.state = some q`.
    cases hcfg : cfg with
    | mk state tape =>
      cases state with
      | none =>
        -- `tm.step ⟨none, tape⟩ = none`, contradicting `h_step`.
        rw [hcfg] at h_step
        unfold SingleTapeTM.TransitionRelation at h_step
        simp [SingleTapeTM.step] at h_step
      | some q =>
        -- `cfg' = stepResult tm q tape`.
        rw [hcfg] at h_step
        unfold SingleTapeTM.TransitionRelation at h_step
        rw [tm_step_running] at h_step
        have h_cfg' : cfg' = stepResult tm q tape := (Option.some.inj h_step).symm
        subst h_cfg'
        -- Apply IH to the n-step residual chain.
        obtain ⟨A', hA'_mem, hA'_match⟩ := ih (stepResult tm q tape) h_rest
        -- A = stepTiles ++ A'.
        refine ⟨stepTiles tm q tape ++ A', ?_, ?_⟩
        · intro tile htile
          rw [List.mem_append] at htile
          rcases htile with hL | hR
          · exact stepTiles_subset_luTiles tm q tape tile hL
          · exact hA'_mem tile hR
        · rw [tau1_append, tau2_append,
              tau1_stepTiles, tau2_stepTiles tm h_nbw, hA'_match]
          rw [encodeCfg_running]

/-- **Forward direction**: if `Halts tm w`, then the reduced MPCP
    instance `(startTile tm w, luTiles tm)` has a solution. Requires
    the TM to never write a blank symbol. -/
theorem halts_implies_mhasSolution (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol) (h : Halts tm w) :
    MHasSolution (startTile tm w) (luTiles tm) := by
  obtain ⟨target_tape, h_chain⟩ := h
  -- Convert `ReflTransGen` to `RelatesInSteps`.
  obtain ⟨n, h_chain_n⟩ := h_chain.relatesInSteps
  obtain ⟨A, hA_mem, hA_match⟩ :=
    forward_aux tm h_nbw target_tape (SingleTapeTM.initCfg tm w) n h_chain_n
  refine ⟨A, ?_, ?_⟩
  · -- Every tile in A is in `startTile :: luTiles`.
    intro tile htile
    exact List.mem_cons_of_mem _ (hA_mem tile htile)
  · -- The matching condition.
    show (startTile tm w).top ++ tau1 A = (startTile tm w).bot ++ tau2 A
    rw [startTile_top, startTile_bot, hA_match]
    show
      [#] ++ (encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#] ++ tau2 A) =
      (# :: encodeCfg tm (SingleTapeTM.initCfg tm w) ++ [#]) ++ tau2 A
    simp [List.append_assoc]

/-! ## Backward direction: `MHasSolution → Halts`

### Proof plan

We want:
```
theorem mhasSolution_implies_halts (tm : SingleTapeTM Symbol)
    (h_nbw : NoBlankWrites tm) (w : List Symbol)
    (h : MHasSolution (startTile tm w) (luTiles tm)) :
    Halts tm w
```

Unpacking `MHasSolution` gives a tile list `A` with
`∀ t ∈ A, t ∈ luTiles tm` and the matching equation

  `tau1 A = encodeCfg tm (initCfg tm w) ++ [#] ++ tau2 A`   … (★)

The proof proceeds by **strong induction on `A.length`**, maintaining (★)
as the invariant and the current configuration `cfg` as a parameter.

---

#### Step 1 — `mem_luTiles_top`: characterise every tile top in `luTiles`

Every tile `t ∈ luTiles tm` has top of one of these eight shapes:

| Top shape            | Tile family          |
|----------------------|----------------------|
| `[↟ₜa]`             | `copyTile a`         |
| `[#]`               | `sepTile`            |
| `[↟ₛq, ↟ₜa]`        | `noMoveTile`, `rightMoveTile`, `leftMoveBoundaryTile` |
| `[↟ₛq, ↟ₜa, #]`     | `rightMoveBoundaryTile` |
| `[↟ₜb, ↟ₛq, ↟ₜa]`   | `leftMoveTile`       |
| `[↟ₜa, h⊥]`         | `absorbLeftTile a`   |
| `[h⊥, ↟ₜa]`         | `absorbRightTile a`  |
| `[h⊥, #, #]`        | `finalTile`          |

Proof: unfold `luTiles`, case-split on membership in each sub-list, then
read off the `top` field using the `@[simp]` projection lemmas.

---

#### Step 2 — `copy_prefix_forced`: tape-lift prefix forces copy tiles

**Lemma.** If `tau1 A = liftTape tm L ++ rest ++ tau2 A`
and `rest` does not begin with `h⊥`, then
`A = L.map (copyTile tm) ++ A'` for some `A'` with
`tau1 A' = rest ++ tau2 A'`.

*Key argument* (by induction on `L`):
The invariant's first character is `↟ₜa` (a tape lift). From
`mem_luTiles_top`, the only tiles with first top character `↟ₜa` are:
- `copyTile a` (top = `[↟ₜa]`, bot = `[↟ₜa]`) — transparent.
- `leftMoveTile` (top = `[↟ₜa, ↟ₛq, ↟ₜh]`) — second char `↟ₛq`, but
  the invariant's second character is either `↟ₜ_` (another tape lift,
  when `L` has more elements) or `↟ₛq` (only at the last left symbol).
- `absorbLeftTile a` (top = `[↟ₜa, h⊥]`) — ruled out by the `rest`
  hypothesis (second char would need to be `h⊥`).

When `L` has ≥ 2 elements the second char is `↟ₜ_`, ruling out
`leftMoveTile` and `absorbLeftTile`; hence the first tile is `copyTile a`.
When `L` has exactly one element, the second char is the first char of
`rest`; the `rest ≠ h⊥…` hypothesis rules out `absorbLeftTile`, and
whether `leftMoveTile` applies is decided in Step 3.

---

#### Step 3 — `transition_forced`: state-marker forces unique transition tile

**Lemma.** If `tau1 A = [↟ₛq] ++ stuff ++ tau2 A` and
`∀ t ∈ A, t ∈ luTiles tm`, then the first tile of `A` is the unique
transition tile for `(q, head)` determined by `tm.tr q head`.

*Key argument*: from `mem_luTiles_top`, the only tiles whose top begins
with `↟ₛq` are those in `transitionTilesFor tm q _`. Since `transitionTiles`
is indexed over all `(q, a)` pairs, only tiles for the specific `a` matching
the second invariant character can have their top align; and
`transitionTilesFor tm q a` contains exactly one move-direction variant
(no-move, right, or left) per the value of `tm.tr q a`.

In the left-boundary sub-case (tape.left = []) the tile is
`leftMoveBoundaryTile`; in the left-interior sub-case (one left symbol
remaining) the tile is `leftMoveTile`, whose 3-character top
`[↟ₜb, ↟ₛq, ↟ₜa]` is forced by `copy_prefix_forced` having already
consumed all but the last left symbol.

---

#### Step 4 — `starts_with_stepTiles`: running cfg forces a full step group

**Lemma.** If `tau1 A = encodeRunningCfg tm q tape ++ [#] ++ tau2 A`
and `∀ t ∈ A, t ∈ luTiles tm`, then
```
∃ A', A = stepTiles tm q tape ++ A' ∧
      (∀ t ∈ A', t ∈ luTiles tm) ∧
      tau1 A' = encodeCfg tm (stepResult tm q tape) ++ [#] ++ tau2 A'
```

*Proof*: Apply `copy_prefix_forced` for the `|tape.left|` left-tape symbols,
then `transition_forced` for the transition tile, then `copy_prefix_forced`
again for the right-tape symbols, then observe the next char is `#` (forcing
`sepTile`). Together these tiles are exactly `stepTiles tm q tape`, and
the residual invariant follows from `tau1_stepTiles` and `tau2_stepTiles`.

---

#### Step 5 — `starts_with_absorbAndFinish`: halted cfg forces absorption

**Lemma.** If `tau1 A = encodeHaltedCfg tm tape ++ [#] ++ tau2 A`
and `∀ t ∈ A, t ∈ luTiles tm`, then
`A = absorbAndFinish tm tape.left.toList (tape.head :: tape.right.toList) ++ A'`
for some `A'` satisfying `tau1 A' = tau2 A'`.

*Proof*: Similar character-by-character forcing, using `absorbLeftTile`/
`absorbRightTile` to consume the tape-lift symbols around `h⊥`, and
`finalTile` (top = `[h⊥, #, #]`, bot = `[#]`) to close when
the encoding has shrunk to `[h⊥]`.

---

#### Step 6 — `backward_aux`: main induction

```
∀ n (A : Stack _) (cfg : tm.Cfg),
    A.length ≤ n →
    (∀ t ∈ A, t ∈ luTiles tm) →
    tau1 A = encodeCfg tm cfg ++ [#] ++ tau2 A →
    ∃ tape, ReflTransGen tm.TransitionRelation cfg ⟨none, tape⟩
```

- **Base** (`n = 0`, so `A = []`): `tau1 [] = [] ≠ encodeCfg … ++ [#]`. Contradiction.
- **Halted** (`cfg = ⟨none, tape⟩`): `ReflTransGen.refl`.
- **Running** (`cfg = ⟨some q, tape⟩`): apply `starts_with_stepTiles` to
  get `A = stepTiles ++ A'` with `A'.length < A.length`; apply the IH to
  `A'` and `stepResult tm q tape`; chain with one `TransitionRelation` step.

---

#### Step 7 — final theorem

```
theorem lu_le_mpcp (tm : SingleTapeTM Symbol) (h_nbw : NoBlankWrites tm)
    (w : List Symbol) :
    Halts tm w ↔ MHasSolution (startTile tm w) (luTiles tm)
```

Forward: `halts_implies_mhasSolution` (already proved).
Backward: unpack `MHasSolution`, cancel the leading `[#]` from the
matching equation to obtain the invariant (★), then call `backward_aux`
with `cfg = initCfg tm w`.

-/

end PCP.LuToMPCP
