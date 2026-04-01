import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.Polynomial.Eval.Defs
import Cslib.Computability.Machines.SingleTapeTuring.Basic
set_option linter.dupNamespace false
/-!
# MPCP ⪯ PCP

This file formalises the reduction from the Modified Post Correspondence Problem
(MPCP) to PCP, following the Coq proof in Undecidability.PCP.Reductions.MPCP_PCP.

## Structure of the proof

1. **Alphabet extension** — extend `α` with two fresh symbols `#` (hash) and `$`
   (dollar), proven disjoint from the original alphabet by construction.

2. **Tile constructors** — three classes of tile in the reduced PCP instance:
   - start tile `d`:   `$ · #_L x₀  /  $ · # · #_R y₀`
   - regular tiles:    `#_L xᵢ  /  #_R yᵢ`  for each card in the instance
   - end tile `e`:     `[#, $]  /  [$]`

3. **Invariant lemmas** (`P_inv`, `P_inv_top`, `P_inv_bot`, `match_start`) —
   structural constraints on what tiles can appear in P and how a matching
   solution must begin.

4. **Direction lemmas** — `mpcp_to_pcp_solution` and `pcp_to_mpcp_solution`.

5. **Main equivalence** and the `reduction` computable function.

## Key design choices vs the Coq version

- We use `List.Sublist`-free `∀ t ∈ A, t ∈ ...` for `incl`, matching Mathlib.
- `tau1`/`tau2` recurse structurally on tile lists, making induction trivial.
- `SymbolExt` uses a dependent sum rather than `fresh`, making disjointness
  a *type-level* fact rather than a proof obligation.
- `#_L` / `#_R` are named `hashL` / `hashR` following Mathlib snake_case.
-/

namespace PCP

/-! ## Core types -/

abbrev Word   (α : Type) := List α
abbrev Stack  (α : Type) := List (Word α × Word α)

/-- Concatenate the upper strings of a stack. -/
def tau1 {α : Type} : Stack α → Word α
  | []            => []
  | (x, _) :: A  => x ++ tau1 A

/-- Concatenate the lower strings of a stack. -/
def tau2 {α : Type} : Stack α → Word α
  | []            => []
  | (_, y) :: A  => y ++ tau2 A

@[simp] theorem tau1_nil {α} : tau1 ([] : Stack α) = [] := rfl
@[simp] theorem tau2_nil {α} : tau2 ([] : Stack α) = [] := rfl

@[simp] theorem tau1_cons {α} (x y : Word α) (A : Stack α) :
    tau1 ((x, y) :: A) = x ++ tau1 A := rfl

@[simp] theorem tau2_cons {α} (x y : Word α) (A : Stack α) :
    tau2 ((x, y) :: A) = y ++ tau2 A := rfl

@[simp] theorem tau1_append {α} (A B : Stack α) :
    tau1 (A ++ B) = tau1 A ++ tau1 B := by
  induction A with
  | nil => simp
  | cons p A ih => cases p; simp [ih, List.append_assoc]

@[simp] theorem tau2_append {α} (A B : Stack α) :
    tau2 (A ++ B) = tau2 A ++ tau2 B := by
  induction A with
  | nil => simp
  | cons p A ih => cases p; simp [ih, List.append_assoc]

/-- PCP: does `P` have a nonempty matching stack? -/
def PCP {α : Type} (P : Stack α) : Prop :=
  ∃ A : Stack α, A ≠ [] ∧ (∀ c ∈ A, c ∈ P) ∧ tau1 A = tau2 A

/-- MPCP: does the instance `(c₀, P)` have a matching stack starting from `c₀`? -/
def MPCP {α : Type} (c₀ : Word α × Word α) (P : Stack α) : Prop :=
  ∃ A : Stack α, (∀ c ∈ A, c ∈ c₀ :: P) ∧
    c₀.1 ++ tau1 A = c₀.2 ++ tau2 A

/-! ## Alphabet extension

Instead of `fresh` (which requires a side-condition proof), we use a sum type.
Disjointness from the original alphabet is a *Type fact, not a lemma. -/

/-- Extend alphabet `α` with two distinguished markers. -/
inductive Ext (α : Type) : Type
  | sym    : α → Ext α      -- original symbol
  | hash   : Ext α           -- the  #  marker
  | dollar : Ext α           -- the  $  marker
  deriving DecidableEq

notation "⋕"  => Ext.hash    -- # in the Coq proof
notation "＄"  => Ext.dollar  -- $ in the Coq proof
prefix:max "↟" => Ext.sym    -- lift an original symbol

/-! ## Interleaving functions

`hashL` puts `#` *before* each symbol; `hashR` puts `#` *after* each symbol.
These are the Coq `#_L` and `#_R`. They are exact duals:
  `hashL x ++ [#] = # :: hashR x`  (see `hashL_snoc_eq`). -/

def hashL {α} : Word α → Word (Ext α)
  | []      => []
  | a :: x  => ⋕ :: ↟a :: hashL x

def hashR {α} : Word α → Word (Ext α)
  | []      => []
  | a :: x  => ↟a :: ⋕ :: hashR x

@[simp] theorem hashL_nil {α} : hashL ([] : Word α) = [] := rfl
@[simp] theorem hashR_nil {α} : hashR ([] : Word α) = [] := rfl

@[simp] theorem hashL_cons {α} (a : α) (x : Word α) :
    hashL (a :: x) = ⋕ :: ↟a :: hashL x := rfl

@[simp] theorem hashR_cons {α} (a : α) (x : Word α) :
    hashR (a :: x) = ↟a :: ⋕ :: hashR x := rfl

@[simp] theorem hashL_append {α} (x y : Word α) :
    hashL (x ++ y) = hashL x ++ hashL y := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih, ]

@[simp] theorem hashR_append {α} (x y : Word α) :
    hashR (x ++ y) = hashR x ++ hashR y := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

/-- The key duality: `hashL x ++ [#] = # :: hashR x`.
    This is what allows the end tile to close a solution. -/
theorem hashL_snoc_eq {α} (x : Word α) :
    hashL x ++ [⋕] = ⋕ :: hashR x := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [ih]

/-- `hashR` is injective. -/
theorem hashR_injective {α} {x y : Word α} (h : hashR x = hashR y) : x = y := by
  induction x generalizing y with
  | nil => cases y with
    | nil => rfl
    | cons b y => simp at h
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp at h
      obtain ⟨hab, hxy⟩ := h
      have : a = b := by grind
      rw [this, ih hxy]

/-- `hashL` never starts with `# :: hashR _` — used in `match_start`. -/
theorem hashL_ne_hash_hashR {α} (x y : Word α) :
    hashL x ≠ ⋕ :: hashR y := by
  induction x generalizing y with
  | nil => simp [hashL]
  | cons a x ih =>
    simp [hashL_cons]
    intro h
    cases y with
    | nil => simp [hashR] at h
    | cons b y =>
      simp [hashR] at h
      grind

/-! ## The three tile classes -/

variable {α : Type}

/-- The start tile: forces solutions to begin with it. -/
def tileStart (x₀ y₀ : Word α) : Word (Ext α) × Word (Ext α) :=
  (＄ :: hashL x₀, ＄ :: ⋕ :: hashR y₀)

/-- A regular tile: interleaved version of a card from the instance. -/
def tileReg (x y : Word α) : Word (Ext α) × Word (Ext α) :=
  (hashL x, hashR y)

/-- The end tile: the only way to close a solution. -/
def tileEnd : Word (Ext α) × Word (Ext α) :=
  ([⋕, ＄], [＄])

/-- Build the reduced PCP instance from an MPCP instance.
    Layout: [tileStart x₀ y₀] ++ regular tiles ++ [tileEnd] -/
def mpcpToPcp (x₀ y₀ : Word α) (R : Stack α) : Stack (Ext α) :=
  tileStart x₀ y₀ ::
  ((x₀, y₀) :: R).filterMap (fun (x, y) =>
    if x ≠ [] ∨ y ≠ [] then some (tileReg x y) else none) ++
  [tileEnd]

/-! ## Invariant lemmas -/

/-- Every tile in the reduced instance is either `tileStart`, `tileEnd`, or a
    `tileReg`. This is the Coq `P_inv`. -/
theorem mem_mpcpToPcp_iff (x₀ y₀ : Word α) (R : Stack α)
    (c : Word (Ext α) × Word (Ext α)) :
    c ∈ mpcpToPcp x₀ y₀ R ↔
    c = tileStart x₀ y₀ ∨
    c = tileEnd ∨
    ∃ x y, (x, y) ∈ (x₀, y₀) :: R ∧ (x ≠ [] ∨ y ≠ []) ∧ c = tileReg x y := by
  simp only [mpcpToPcp, List.mem_cons, List.mem_append, List.mem_filterMap, Option.ite_none_right_eq_some]
  constructor
  · rintro ⟨_, ⟨⟨x, y⟩, hmem, hne, rfl⟩⟩
    · exact Or.inl rfl
    all_goals grind
  · rintro (rfl | rfl | ⟨x, y, hmem, hne, rfl⟩)
    <;> grind


/-- No tile in the reduced instance has a top word starting with a lifted
    original symbol.  This rules out `Sigma`-headed top strings, matching
    Coq's `P_inv_top`. -/
theorem not_sym_head_top (x₀ y₀ : Word α) (R : Stack α) (a : α) (w : Word (Ext α)) :
    (↟a :: w, u) ∉ mpcpToPcp x₀ y₀ R := by
  rw [mem_mpcpToPcp_iff]
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨x, y, g, j, k⟩)
  simp[tileReg] at k
  unfold hashL at k
  grind



/-- No tile in the reduced instance has a bottom word starting with `#`.
    Matches Coq's `P_inv_bot`. -/
theorem not_hash_head_bot (x₀ y₀ : Word α) (R : Stack α) (w : Word (Ext α)) :
    (v, ⋕ :: w) ∉ mpcpToPcp x₀ y₀ R := by
  rw [mem_mpcpToPcp_iff]
  rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨x, y, g,h, k⟩)
  simp [tileReg] at k
  unfold hashR at k
  grind

/-! ## Invariant lemmas -/

-- Helper: Extending `not_sym_head_top` recursively over the stack `B`
lemma tau1_ne_sym_head {α : Type} (x₀ y₀ : Word α) (R : Stack α) (B : Stack (Ext α)) (a : α) (w : Word (Ext α))
    (hmem : ∀ t ∈ B, t ∈ mpcpToPcp x₀ y₀ R) :
    tau1 B ≠ ↟a :: w := by
  induction B generalizing w with
  | nil => simp
  | cons d B ih =>
    intro h
    have hd : d ∈ mpcpToPcp x₀ y₀ R := hmem d (List.mem_cons_self)
    have hB : ∀ t ∈ B, t ∈ mpcpToPcp x₀ y₀ R := fun t ht => hmem t (List.mem_cons_of_mem _ ht)
    cases d with
    | mk d1 d2 =>
      simp only [tau1_cons] at h
      cases d1 with
      | nil =>
        simp only [List.nil_append] at h
        exact ih w hB h
      | cons c cs =>
        simp only [List.cons_append] at h
        have hc : c = ↟a := by injection h
        subst hc
        exact not_sym_head_top x₀ y₀ R a cs hd

-- Helper: Extending `not_hash_head_bot` recursively over the stack `B`
-- Helper: Extending `not_hash_head_bot` recursively over the stack `B`
lemma tau2_ne_hash_head {α : Type} (x₀ y₀ : Word α) (R : Stack α) (B : Stack (Ext α)) (w : Word (Ext α))
    (hmem : ∀ t ∈ B, t ∈ mpcpToPcp x₀ y₀ R) :
    tau2 B ≠ ⋕ :: w := by
  induction B generalizing w with
  | nil => simp
  | cons d B ih =>
    intro h
    have hd : d ∈ mpcpToPcp x₀ y₀ R := hmem d (List.mem_cons_self)
    have hB : ∀ t ∈ B, t ∈ mpcpToPcp x₀ y₀ R := fun t ht => hmem t (List.mem_cons_of_mem _ ht)
    cases d with
    | mk d1 d2 =>
      simp only [tau2_cons] at h
      cases d2 with
      | nil =>
        simp only [List.nil_append] at h
        exact ih w hB h
      | cons c cs =>
        simp only [List.cons_append] at h
        have hc : c = ⋕ := by injection h
        subst hc
        exact not_hash_head_bot x₀ y₀ R cs hd

/-- Any nonempty matching PCP solution must start with the start tile.
    This is the Coq `match_start` lemma — the most involved invariant. -/
theorem match_start (x₀ y₀ : Word α) (R : Stack α)
    (c : Word (Ext α) × Word (Ext α)) (B : Stack (Ext α))
    (hmem : ∀ t ∈ c :: B, t ∈ mpcpToPcp x₀ y₀ R)
    (heq  : tau1 (c :: B) = tau2 (c :: B)) :
    c = tileStart x₀ y₀ := by
  have hc : c ∈ mpcpToPcp x₀ y₀ R := hmem c (List.mem_cons_self)
  have hB : ∀ t ∈ B, t ∈ mpcpToPcp x₀ y₀ R := fun t ht => hmem t (List.mem_cons_of_mem _ ht)
  rw [mem_mpcpToPcp_iff] at hc
  rcases hc with rfl | rfl | ⟨x, y, _, hne, rfl⟩
  · rfl
  · simp only [tileEnd, tau1_cons, tau2_cons] at heq
    grind
  · simp only [tileReg, tau1_cons, tau2_cons] at heq
    cases x with
    | nil =>
      cases y with
      | nil => grind
      | cons b y =>
        simp only [hashL_nil, hashR_cons, List.nil_append, List.cons_append] at heq
        apply False.elim
        apply (tau1_ne_sym_head x₀ y₀ R B b (⋕ :: hashR y ++ tau2 B) hB heq)
    | cons a x =>
      cases y with
      | nil =>
        simp only [hashL_cons, hashR_nil, List.cons_append, List.nil_append] at heq
        exact False.elim (tau2_ne_hash_head x₀ y₀ R B (↟a :: hashL x ++ tau1 B) hB heq.symm)
      | cons b y =>
        simp only [hashL_cons, hashR_cons, List.cons_append] at heq
        grind

/-! ## Forward direction: MPCP solution → PCP solution -/

theorem mpcp_to_pcp_solution (x₀ y₀ : Word α) (R : Stack α)
  (A : Stack α)
  (hA  : ∀ c ∈ A, c ∈ (x₀, y₀) :: R)
  (heq : x₀ ++ tau1 A = y₀ ++ tau2 A) :
  ∃ B : Stack (Ext α),
    B ≠ [] ∧
    (∀ c ∈ B, c ∈ mpcpToPcp x₀ y₀ R) ∧
    tau1 B = tau2 B := by
  let B_A := A.filterMap fun p => if p.1 ≠ [] ∨ p.2 ≠ [] then some (tileReg p.1 p.2) else none
  refine ⟨tileStart x₀ y₀ :: B_A ++ [tileEnd], ?_, ?_, ?_⟩
  · simp
  · intro c hc
    simp only [B_A, List.mem_cons, List.mem_append] at hc
    simp at hc
    rcases hc with (hc0 | hc1) | hc2
    · -- Case 1: c = tileStart
      simp [mem_mpcpToPcp_iff, hc0]
    · -- Case 2: c ∈ B_A
      simp [mem_mpcpToPcp_iff]
      grind
    · -- Case 3: c = tileEnd
      simp [mem_mpcpToPcp_iff]
      grind

  · -- Prove tau1 and tau2 properties (now trivially clean!)
    have h1 : tau1 B_A = hashL (tau1 A) := by
      dsimp [B_A]
      clear hA heq
      induction A with
      | nil => rfl
      | cons p A' ih =>
        rcases p with ⟨x, y⟩
        simp [tau1_cons, tileReg, hashL_append]
        simp only at ih
        by_cases h : ¬x = [] ∨ ¬y = []
        · simp[h]
          exact ih
        · simp at h
          simp[h]
          exact ih
    have h2 : tau2 B_A = hashR (tau2 A) := by
      dsimp [B_A]
      clear hA heq
      clear h1
      induction A with
      | nil => rfl
      | cons p A' ih =>
        rcases p with ⟨x, y⟩
        simp [tau2_cons, tileReg, hashR_append]
        simp only at ih
        unfold tileReg at ih
        by_cases h : ¬x = [] ∨ ¬y = []
        · simp[h]
          exact ih
        · simp at h
          simp[h]
          exact ih
    have h1_eval : tau1 (tileStart x₀ y₀ :: B_A ++ [tileEnd]) = ＄ :: hashL (x₀ ++ tau1 A) ++ [⋕, ＄] := by
      simp only [tau1_cons, tau1_append, tileStart, tileEnd, tau1_nil, List.append_nil, h1]
      simp only [List.cons_append, ← hashL_append]

    have h2_eval : tau2 (tileStart x₀ y₀ :: B_A ++ [tileEnd]) = ＄ :: ⋕ :: hashR (y₀ ++ tau2 A) ++ [＄] := by
      simp only [tau2_cons, tau2_append, tileStart, tileEnd, tau2_nil, List.append_nil, h2]
      simp only [List.cons_append, ← hashR_append]

    rw [h1_eval, h2_eval, heq]

    have h3 : ∀ w : Word α, hashL w ++ [⋕, ＄] = ⋕ :: hashR w ++ [＄] := by
      intro w
      have h4 : hashL w ++ [⋕, ＄] = (hashL w ++ [⋕]) ++ [＄] := by simp
      rw [h4, hashL_snoc_eq]
    grind


/-! ## Backward direction: PCP solution → MPCP solution -/

lemma hashL_append_dollar_ne {α} (x y : Word α) (w1 w2 : Word (Ext α)) :
    hashL x ++ ＄ :: w1 ≠ ⋕ :: hashR y ++ ＄ :: w2 := by
  induction x generalizing y with
  | nil =>
    cases y <;> intro h <;> simp [hashL, hashR] at h
  | cons a x ih =>
    cases y with
    | nil => intro h; simp [hashL, hashR] at h
    | cons b y =>
      intro h; simp [hashL, hashR] at h
      exact ih y h.2

lemma hashR_append_dollar_inj {α} (x y : Word α) (w1 w2 : Word (Ext α))
    (h : hashR x ++ ＄ :: w1 = hashR y ++ ＄ :: w2) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b y => simp [hashR] at h
  | cons a x ih =>
    cases y with
    | nil => simp [hashR] at h
    | cons b y =>
      simp [hashR] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, ih y h2]

-- Generalize string accumulation to handle recursive tileReg matching
lemma pcp_to_mpcp_solution_gen {α : Type} (x₀ y₀ : Word α) (R : Stack α)
    (B : Stack (Ext α)) (u v : Word α)
    (hB  : ∀ c ∈ B, c ∈ mpcpToPcp x₀ y₀ R)
    (hmatch : hashL u ++ tau1 B = ⋕ :: hashR v ++ tau2 B) :
    ∃ A : Stack α, (∀ c ∈ A, c ∈ (x₀, y₀) :: R) ∧
      u ++ tau1 A = v ++ tau2 A := by
  induction B generalizing u v with
  | nil =>
    simp only [tau1_nil, tau2_nil, List.append_nil] at hmatch
    exact False.elim (hashL_ne_hash_hashR _ _ hmatch)
  | cons c B ih =>
    have hc : c ∈ mpcpToPcp x₀ y₀ R := hB c (List.mem_cons_self)
    have hB' : ∀ t ∈ B, t ∈ mpcpToPcp x₀ y₀ R :=
      fun t ht => hB t (List.mem_cons_of_mem _ ht)
    rw [mem_mpcpToPcp_iff] at hc
    rcases hc with rfl | rfl | ⟨x, y, hxy, _hne, rfl⟩
    · simp only [tileStart, tau1_cons, tau2_cons] at hmatch
      exact False.elim (hashL_append_dollar_ne u v _ _ hmatch)
    · simp only [tileEnd, tau1_cons, tau2_cons] at hmatch
      have h_lhs : hashL u ++ ([⋕, ＄] ++ tau1 B) = ⋕ :: hashR u ++ ＄ :: tau1 B := by
        have h1 : hashL u ++ ([⋕, ＄] ++ tau1 B) = (hashL u ++ [⋕]) ++ (＄ :: tau1 B) := by grind
        rw [h1, hashL_snoc_eq]
      rw [h_lhs] at hmatch
      have hmatch_tail : hashR u ++ ＄ :: tau1 B = hashR v ++ ＄ :: tau2 B := by
        injection hmatch with _ htail
      have huv := hashR_append_dollar_inj u v _ _ hmatch_tail
      subst huv
      refine ⟨[], by simp, by simp⟩
    · simp only [tileReg, tau1_cons, tau2_cons] at hmatch
      have h_lhs : hashL u ++ (hashL x ++ tau1 B) = hashL (u ++ x) ++ tau1 B := by
        rw [← List.append_assoc, ← hashL_append]
      have h_rhs : ⋕ :: hashR v ++ (hashR y ++ tau2 B) = ⋕ :: hashR (v ++ y) ++ tau2 B := by
        simp [← List.append_assoc, ← hashR_append]
      rw [h_lhs, h_rhs] at hmatch
      obtain ⟨A, hA, heq⟩ := ih (u ++ x) (v ++ y) hB' hmatch
      refine ⟨(x, y) :: A, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hxy
        · exact hA c hc
      · simp only [tau1_cons, tau2_cons]
        rw [← List.append_assoc u x, ← List.append_assoc v y]
        exact heq

theorem pcp_to_mpcp_solution (x₀ y₀ : Word α) (R : Stack α)
    (B : Stack (Ext α))
    (hB  : ∀ c ∈ B, c ∈ mpcpToPcp x₀ y₀ R)
    (hmatch : hashL x₀ ++ tau1 B = ⋕ :: hashR y₀ ++ tau2 B) :
    ∃ A : Stack α, (∀ c ∈ A, c ∈ (x₀, y₀) :: R) ∧
      x₀ ++ tau1 A = y₀ ++ tau2 A :=
  pcp_to_mpcp_solution_gen x₀ y₀ R B x₀ y₀ hB hmatch

/-! ## The reduction as a computable function -/
lemma mpcp_iff_pcp (x₀ y₀ : Word α) (R : Stack α) :
    MPCP (x₀, y₀) R ↔ PCP (mpcpToPcp x₀ y₀ R) := by
  constructor
  · intro ⟨A, hA, heq⟩
    -- The forward helper theorem gives exactly the existential witness and properties PCP needs
    exact mpcp_to_pcp_solution x₀ y₀ R A hA heq
  · intro ⟨B, hne, hmem, hB_eq⟩
    -- 1. Pass hne into head to evaluate it to a concrete tile
    have h_first : B.head hne = tileStart x₀ y₀ := by
      have := match_start x₀ y₀ R (B.head hne) B.tail ?_ ?_
      · exact this
      · intro t ht
        have : t ∈ B := by
          cases ht with
          | head h =>  exact List.head_mem hne
          | tail h tl =>
            exact List.mem_of_mem_tail tl
        exact hmem t this
      · --added here
        cases B with
        | nil => contradiction
        | cons hd tl =>
          -- Now Lean automatically knows B is exactly `hd :: tl` everywhere.
          -- No need for hB_decomp, head, or tail lemmas at all!

          -- 1. Prove the head (hd) is the start tile
          have h_first : hd = tileStart x₀ y₀ := by
            apply match_start x₀ y₀ R hd tl
            · intro t ht
              have ht_in : t ∈ hd :: tl := by
                cases ht with
                | head h =>  exact List.head_mem hne
                | tail h tl =>
                  exact List.mem_of_mem_tail tl
              exact hmem t ht_in
            · exact hB_eq

          -- 2. Substitute the start tile directly into our context
          subst h_first

          -- 3. Strip the start tile from hB_eq to match the helper theorem's type
          have heq_tail : hashL x₀ ++ tau1 tl = ⋕ :: hashR y₀ ++ tau2 tl := by
            have hB_eq_copy := hB_eq
            simp only [tau1_cons, tau2_cons, tileStart] at hB_eq_copy
            grind
          -- 4. Prove the tail elements also belong to the PCP instance
          have hmem_tail : ∀ c ∈ tl, c ∈ mpcpToPcp x₀ y₀ R := fun c hc => by
            exact hmem c (List.Mem.tail _ hc)

          -- 5. Call the helper theorem on the tail (tl)
          obtain ⟨A, hA, heq⟩ := pcp_to_mpcp_solution x₀ y₀ R tl hmem_tail heq_tail
          grind
        --to here
    have hB_decomp : B = tileStart x₀ y₀ :: B.tail := by
      have h_cons := (hne).symm
      simp at h_cons
      grind

    -- 3. Strip the start tile from hB_eq to get the EXACT type the helper theorem wants
    have heq_tail : hashL x₀ ++ tau1 B.tail = ⋕ :: hashR y₀ ++ tau2 B.tail := by
      have hB_eq_copy := hB_eq
      rw [hB_decomp] at hB_eq_copy
      simp only [tau1_cons, tau2_cons, tileStart] at hB_eq_copy
      -- Drop the leading '＄' character from both sides!
      grind
    -- 4. Prove the tail elements also belong to the PCP instance
    have hmem_tail : ∀ c ∈ B.tail, c ∈ mpcpToPcp x₀ y₀ R := fun c hc => by
      have h_in_B : c ∈ B := by
        rw [hB_decomp]
        exact List.mem_cons_of_mem _ hc
      exact hmem c h_in_B

    -- 5. Call the helper theorem on the TAIL
    obtain ⟨A, hA, heq⟩ := pcp_to_mpcp_solution x₀ y₀ R B.tail hmem_tail heq_tail
    exact ⟨A, hA, heq⟩

/-- `MPCP ⪯ PCP`: the many-one reduction. -/
theorem reduction :
    ∀ (x₀ y₀ : Word α) (R : Stack α),
      MPCP (x₀, y₀) R ↔ PCP (mpcpToPcp x₀ y₀ R) :=
  fun x₀ y₀ R => mpcp_iff_pcp x₀ y₀ R

end PCP
