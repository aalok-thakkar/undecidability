import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.Polynomial.Eval.Defs
import Cslib.Computability.Machines.SingleTapeTuring.Basic

/-!
# Post Correspondence Problem (PCP)

This file formalises the Post Correspondence Problem in two equivalent ways:

* **Frontend** (`HasSolution`): a computable definition over `Fin`-indexed sequences,
  suitable for `#eval` and concrete instances.
* **Backend** (`dPCP`): an inductive-relation definition, suitable for structural
  induction and metatheory reductions.

The two definitions are shown to be equivalent in `hasSolution_iff_dPCP`.
-/

namespace PCP

variable {α : Type}

/-! ## Basic types -/

/-- A word over alphabet `α` is a list of symbols. -/
abbrev Word (α : Type) := List α

/-- A PCP tile consists of a top word and a bottom word. -/
structure Tile (α : Type) where
  top : Word α
  bot : Word α
  deriving DecidableEq, Repr

/-- A PCP instance is a finite list of tiles. -/
abbrev Instance (α : Type) := List (Tile α)

/-! ## Frontend: computable definition -/

/-- Concatenate the top words of the tiles selected by `idxs`. -/
def concatTop (P : Instance α) (idxs : List (Fin P.length)) : Word α :=
  idxs.flatMap fun i => (P.get i).top

/-- Concatenate the bottom words of the tiles selected by `idxs`. -/
def concatBot (P : Instance α) (idxs : List (Fin P.length)) : Word α :=
  idxs.flatMap fun i => (P.get i).bot

/-- `idxs` is a solution to `P` if it is nonempty and the top and bottom
concatenations agree. -/
def IsSolution (P : Instance α) (idxs : List (Fin P.length)) : Prop :=
  idxs ≠ [] ∧ concatTop P idxs = concatBot P idxs

/-- `P` has a solution if some nonempty index sequence is a solution. -/
def HasSolution (P : Instance α) : Prop :=
  ∃ idxs : List (Fin P.length), IsSolution P idxs

/-! ## Backend: inductive-relation definition -/

/-- `Derivable P u v` holds when the pair `(u, v)` can be built by
concatenating tiles from `P` (at least one tile must be used). -/
inductive Derivable (P : Instance α) : Word α → Word α → Prop
  | single (t : Tile α) (ht : t ∈ P) :
      Derivable P t.top t.bot
  | cons (t : Tile α) (u v : Word α) (ht : t ∈ P) (h : Derivable P u v) :
      Derivable P (t.top ++ u) (t.bot ++ v)

/-- The inductive (Coq-style) PCP predicate: `P` has a solution iff some
word `u` is derivable from itself. -/
def dPCP (P : Instance α) : Prop :=
  ∃ u : Word α, Derivable P u u

/-! ## Auxiliary lemmas -/

/-- Membership in a list is equivalent to existence of a `Fin` index. -/
@[simp]
theorem mem_iff_exists_fin (P : Instance α) (t : Tile α) :
    t ∈ P ↔ ∃ i : Fin P.length, P.get i = t :=
  ⟨List.get_of_mem, fun ⟨i, hi⟩ => hi ▸ List.get_mem P i⟩

@[simp]
theorem concatTop_nil (P : Instance α) :
    concatTop P [] = [] := rfl

@[simp]
theorem concatBot_nil (P : Instance α) :
    concatBot P [] = [] := rfl

@[simp]
theorem concatTop_cons (P : Instance α) (i : Fin P.length)
    (is : List (Fin P.length)) :
    concatTop P (i :: is) = (P.get i).top ++ concatTop P is := by
  simp [concatTop]

@[simp]
theorem concatBot_cons (P : Instance α) (i : Fin P.length)
    (is : List (Fin P.length)) :
    concatBot P (i :: is) = (P.get i).bot ++ concatBot P is := by
  simp [concatBot]

/-! ## Bridge: equivalence between frontend and backend -/

/-- Any nonempty index sequence gives a `Derivable` pair. -/
theorem derivable_of_isSolution {P : Instance α}
    {idxs : List (Fin P.length)} (hne : idxs ≠ []) :
    Derivable P (concatTop P idxs) (concatBot P idxs) := by
  induction idxs with
  | nil => grind
  | cons x xs ih => cases xs with
      |nil => simp[concatTop, concatBot, Derivable.single]
      |cons y ys =>
        simp at ih
        refine
          Derivable.cons P[↑x] (P[↑y].top ++ concatTop P ys) (P[↑y].bot ++ concatBot P ys) ?_ ih
        grind



/-- Any `Derivable` pair arises from a nonempty index sequence. -/
theorem isSolution_of_derivable {P : Instance α} {u v : Word α}
    (h : Derivable P u v) :
    ∃ idxs : List (Fin P.length),
      u = concatTop P idxs ∧ v = concatBot P idxs ∧ idxs ≠ [] := by
  induction h with
  | single t ht =>
    rw [mem_iff_exists_fin] at ht
    obtain ⟨i, rfl⟩ := ht
    exact ⟨[i], by simp, by simp, List.cons_ne_nil i []⟩
  | cons t u v _ht _h ih =>
    obtain ⟨idxs, hu, hv, hne⟩ := ih
    rw [mem_iff_exists_fin] at _ht
    obtain ⟨i, rfl⟩ := _ht
    exact ⟨i :: idxs, by simp [hu], by simp [hv], List.cons_ne_nil i idxs⟩

/-- `HasSolution P` implies `dPCP P`. -/
theorem hasSolution_implies_dPCP {P : Instance α} (h : HasSolution P) :
    dPCP P := by
  obtain ⟨idxs, hne, heq⟩ := h
  exact ⟨concatTop P idxs, heq ▸ derivable_of_isSolution hne⟩

/-- `dPCP P` implies `HasSolution P`. -/
theorem dPCP_implies_hasSolution {P : Instance α} (h : dPCP P) :
    HasSolution P := by
  obtain ⟨u, hd⟩ := h
  obtain ⟨idxs, hu, hv, hne⟩ := isSolution_of_derivable hd
  exact ⟨idxs, hne, hu ▸ hv ▸ rfl⟩

/-- **Main equivalence**: the two PCP definitions coincide. -/
theorem hasSolution_iff_dPCP (P : Instance α) :
    HasSolution P ↔ dPCP P :=
  ⟨hasSolution_implies_dPCP, dPCP_implies_hasSolution⟩


structure MInstance (α : Type) where
  /-- The full tile list (the start tile is `tiles[startIdx]`). -/
  tiles    : Instance α
  /-- Index of the tile that must begin every solution. -/
  startIdx : Fin tiles.length
  deriving Repr

/-- Concatenate the top words of `idxs` from `M.tiles`. -/
def mconcatTop (M : MInstance α) (idxs : List (Fin M.tiles.length)) : Word α :=
  idxs.flatMap fun i => (M.tiles.get i).top

/-- Concatenate the bottom words of `idxs` from `M.tiles`. -/
def mconcatBot (M : MInstance α) (idxs : List (Fin M.tiles.length)) : Word α :=
  idxs.flatMap fun i => (M.tiles.get i).bot

/-- `idxs` is an MPCP solution for `M` if:
    * it is nonempty,
    * it starts with the designated start tile, and
    * the top and bottom concatenations agree. -/
def MIsSolution (M : MInstance α) (idxs : List (Fin M.tiles.length)) : Prop :=
  idxs ≠ [] ∧
  idxs.head? = some M.startIdx ∧
  mconcatTop M idxs = mconcatBot M idxs

/-- `M` has an MPCP solution. -/
def MHasSolution (M : MInstance α) : Prop :=
  ∃ idxs : List (Fin M.tiles.length), MIsSolution M idxs

/-! ### Basic simp lemmas for `mconcatTop`/`mconcatBot` -/

@[simp]
theorem mconcatTop_nil (M : MInstance α) :
    mconcatTop M [] = [] := rfl

@[simp]
theorem mconcatBot_nil (M : MInstance α) :
    mconcatBot M [] = [] := rfl

@[simp]
theorem mconcatTop_cons (M : MInstance α) (i : Fin M.tiles.length)
    (is : List (Fin M.tiles.length)) :
    mconcatTop M (i :: is) = (M.tiles.get i).top ++ mconcatTop M is := by
  simp [mconcatTop]

@[simp]
theorem mconcatBot_cons (M : MInstance α) (i : Fin M.tiles.length)
    (is : List (Fin M.tiles.length)) :
    mconcatBot M (i :: is) = (M.tiles.get i).bot ++ mconcatBot M is := by
  simp [mconcatBot]

/-! ## Alphabet extension for the reduction -/

/-- Extend the alphabet `α` with two fresh markers used in the MPCP→PCP
    reduction:
    * `old a`   — a lifted symbol from the original alphabet;
    * `star`    — the interleaving marker `⋆`, placed *before* each symbol
                  in the top interleaving and *after* each symbol in the
                  bottom interleaving;
    * `dollar`  — the end-of-string marker `$` appended to close the solution. -/
inductive SymbolExt (α : Type) : Type
  | old    : α → SymbolExt α
  | marker : SymbolExt α
  | endMarker : SymbolExt α
  deriving DecidableEq

notation "⋆" => SymbolExt.marker
notation "⋄" => SymbolExt.endMarker

prefix:max "↑ₛ" => SymbolExt.old   -- `↑ₛ` to avoid clashing with `↑` (coe)

-- For the Goal State (infoview)
instance {α : Type} [Repr α] : Repr (SymbolExt α) where
  reprPrec
    | SymbolExt.old a, _ => f!"↑ₛ{repr a}"
    | SymbolExt.marker, _ => f!"⋆"
    | SymbolExt.endMarker, _ => f!"⋄"

-- For string conversions (like `#eval`)
instance {α : Type} [ToString α] : ToString (SymbolExt α) where
  toString
    | SymbolExt.old a => toString a
    | SymbolExt.marker => "⋆"
    | SymbolExt.endMarker => "⋄"

/-! ### Interleaving functions

The two interleaving functions are *duals*:

| Function         | Pattern per symbol `a` |
|------------------|------------------------|
| `topInterleave`  | `⋆ · ↑ₛa`             |
| `botInterleave`  | `↑ₛa · ⋆`             |

This means a top-interleaved string `⋆a₁⋆a₂…` and a bottom-interleaved string
`a₁⋆a₂⋆…` can only be equal if both source words are equal — the key invariant
used in the correctness proof. -/

/-- Interleave `⋆` **before** each symbol: `[a, b, c] ↦ [⋆, a, ⋆, b, ⋆, c]`. -/

def topInterleave (l : List α) : List (SymbolExt α) :=
  l.flatMap fun x => [⋆, ↑ₛx]

/-- Interleave `⋆` **after** each symbol: `[a, b, c] ↦ [a, ⋆, b, ⋆, c, ⋆]`. -/
def botInterleave (l : List α) : List (SymbolExt α) :=
  l.flatMap fun x => [↑ₛx, ⋆]

-- Sanity checks.
#eval topInterleave ['a', 'b', 'c']
-- [⋆, 'a', ⋆, 'b', ⋆, 'c']
#eval botInterleave ['a', 'b', 'c']
-- ['a', ⋆, 'b', ⋆, 'c', ⋆]

/-! #### Simp lemmas for interleaving -/

@[simp]
theorem topInterleave_nil : topInterleave ([] : List α) = [] := rfl

@[simp]
theorem botInterleave_nil : botInterleave ([] : List α) = [] := rfl

@[simp]
theorem topInterleave_cons (a : α) (l : List α) :
    topInterleave (a :: l) = ⋆ :: ↑ₛa :: topInterleave l := by
  simp [topInterleave]

@[simp]
theorem botInterleave_cons (a : α) (l : List α) :
    botInterleave (a :: l) = ↑ₛa :: ⋆ :: botInterleave l := by
  simp [botInterleave]

@[simp]
theorem topInterleave_append (l₁ l₂ : List α) :
    topInterleave (l₁ ++ l₂) = topInterleave l₁ ++ topInterleave l₂ := by
  simp [topInterleave, List.flatMap_append]

@[simp]
theorem botInterleave_append (l₁ l₂ : List α) :
    botInterleave (l₁ ++ l₂) = botInterleave l₁ ++ botInterleave l₂ := by
  simp [botInterleave, List.flatMap_append]

/-! ## The MPCP → PCP reduction

Given MPCP instance `M` (with tiles `t₀, t₁, …, tₙ` and start tile `t₀`), we
build a PCP instance over `SymbolExt α` with the following tiles:

| Role              | Top                            | Bottom                          |
|-------------------|--------------------------------|---------------------------------|
| Start tile `t₀`   | `⋆ · topInterleave t₀.top`    | `botInterleave t₀.bot`          |
| Regular tile `tᵢ` | `topInterleave tᵢ.top`        | `botInterleave tᵢ.bot`          |
| End tile          | `[⋆, ⋄]`                      | `[⋄]`                           |

The start tile is given an extra leading `⋆` so that the top string always
starts one marker ahead of the bottom — the only way to close the gap is with
the end tile. -/

/-- Translate a single tile for use in the middle of a solution (regular role). -/
def regularTile (t : Tile α) : Tile (SymbolExt α) where
  top := topInterleave t.top
  bot := botInterleave t.bot

/-- Translate the designated start tile (given an extra leading `⋆` on top). -/
def startTile (t : Tile α) : Tile (SymbolExt α) where
  top := ⋆ :: topInterleave t.top
  bot := botInterleave t.bot

/-- The end tile closes a solution: top = `[⋆, ⋄]`, bottom = `[⋄]`. -/
def endTile : Tile (SymbolExt α) where
  top := [⋆, ⋄]
  bot := [⋄]

/-- Build the PCP instance corresponding to an MPCP instance `M`.

    Layout (indices into the resulting `Instance`):
    * Index `0`       — the translated start tile.
    * Indices `1..n`  — the `n` regular tiles (one per tile of `M`).
    * Index `n+1`     — the end tile.

    Every MPCP tile appears as both a *regular* tile (usable anywhere in the
    suffix) and the *start* tile (used exactly once, at position 0). -/
def mpcp_to_pcp (M : MInstance α) : Instance (SymbolExt α) :=
  [startTile (M.tiles.get M.startIdx)] ++
  M.tiles.map regularTile ++
  [endTile]



/-! ### Index helpers for `mpcp_to_pcp` -/

/-- Number of tiles in the reduced PCP instance. -/
@[simp]
theorem mpcp_to_pcp_length (M : MInstance α) :
    (mpcp_to_pcp M).length = M.tiles.length + 2 := by
  simp [mpcp_to_pcp]

/-- The first tile of the reduced instance is the start tile. -/
@[simp]
theorem mpcp_to_pcp_get_zero (M : MInstance α) :
    (mpcp_to_pcp M).get ⟨0, by simp⟩ = startTile (M.tiles.get M.startIdx) := by
  simp [mpcp_to_pcp]

/-- The last tile of the reduced instance is the end tile. -/
@[simp]
theorem mpcp_to_pcp_get_last (M : MInstance α) :
    (mpcp_to_pcp M).get ⟨M.tiles.length + 1, by simp⟩ = endTile := by
  simp [mpcp_to_pcp]



end PCP
