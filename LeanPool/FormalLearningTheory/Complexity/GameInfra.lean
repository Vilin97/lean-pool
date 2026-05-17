/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Criterion.Online
-- Removed: import LeanPool.FormalLearningTheory.Complexity.Littlestone
-- Γ₁₉: branch-wise isShattered wrong + trees must be complete (balanced).
-- Corrected: depth-indexed complete trees + path-wise shattering.
import LeanPool.FormalLearningTheory.Complexity.Generalization
-- Path B (Γ₂₁): WithBot (WithTop ℕ) for LittlestoneDim
-- Required for CompleteLattice instance and ConditionallyCompleteLinearOrderBot ℕ
import Mathlib.Data.Nat.Lattice

/-!
# Game-Theoretic Infrastructure for Online Learning

Definitions and interface lemmas for the online learning game:
- `LTree`: depth-indexed complete Littlestone trees
- `LTree.isShattered`: path-wise shattering
- `LittlestoneDim`: Littlestone dimension as `WithBot (WithTop ℕ)`
- `OnlineLearner.mistakesFrom`: mistake counting from arbitrary state
- `adversary_core`: core adversary lemma
- `versionSpace`, `SOA`: Standard Optimal Algorithm and its interface
- Version-space infrastructure lemmas

Characterization theorems live in `FLT_Proofs.Theorem.Online`.
-/

-- ============================================================
-- CORRECTED DEFINITIONS: Depth-indexed complete Littlestone trees
-- ============================================================

/-- A complete binary Littlestone tree of depth n. -/
inductive LTree (X : Type) : ℕ → Type where
  | leaf : LTree X 0
  | branch : {n : ℕ} → X → LTree X n → LTree X n → LTree X (n + 1)

/-- Path-wise shattering for complete trees.
    Path B: leaf case requires C.Nonempty (NA₁₀). -/
def LTree.isShattered {X : Type} {n : ℕ} (C : ConceptClass X Bool) : LTree X n → Prop
  | .leaf => C.Nonempty  -- Path B: was True, now C.Nonempty (Γ₂₁ fix)
  | .branch x l r =>
      (∃ c ∈ C, c x = true) ∧ (∃ c ∈ C, c x = false) ∧
      l.isShattered {c ∈ C | c x = true} ∧
      r.isShattered {c ∈ C | c x = false}

/-- Helper: shattering implies the concept class is nonempty. -/
theorem LTree.nonempty_of_isShattered {X : Type} {C : ConceptClass X Bool}
    {n : ℕ} (T : LTree X n) (hT : T.isShattered C) : C.Nonempty := by
  induction n with
  | zero => match T with | .leaf => exact hT
  | succ k _ =>
    match T with
    | .branch _ _ _ =>
      obtain ⟨⟨c, hc, _⟩, _⟩ := hT
      exact ⟨c, hc⟩

/-- Shattering is upward-monotone in the concept class. -/
theorem LTree.isShattered_mono {X : Type} {n : ℕ} (T : LTree X n)
    {C C' : ConceptClass X Bool} (h : C ⊆ C') :
    T.isShattered C → T.isShattered C' := by
  induction T generalizing C C' with
  | leaf => exact Set.Nonempty.mono h
  | branch x l r ihl ihr =>
    intro ⟨⟨ct, hct, hctx⟩, ⟨cf, hcf, hcfx⟩, hsl, hsr⟩
    refine ⟨⟨ct, h hct, hctx⟩, ⟨cf, h hcf, hcfx⟩, ?_, ?_⟩
    · exact ihl (fun _ hm => ⟨h hm.1, hm.2⟩) hsl
    · exact ihr (fun _ hm => ⟨h hm.1, hm.2⟩) hsr

/-- Littlestone dimension: the maximum depth of a complete shattered tree.
    Path B: returns WithBot (WithTop ℕ) so Ldim(∅) = ⊥ (NA₁₀). -/
noncomputable def LittlestoneDim (X : Type) (C : ConceptClass X Bool) :
    WithBot (WithTop ℕ) :=
  ⨆ (n : ℕ) (_ : ∃ T : LTree X n, T.isShattered C),
    (↑(↑n : WithTop ℕ) : WithBot (WithTop ℕ))

-- ============================================================
-- CORE ADVERSARY LEMMA
-- ============================================================

/-- Core adversary lemma. -/
theorem adversary_core {X : Type}
    (L : OnlineLearner X Bool) (s : L.State)
    {C : ConceptClass X Bool} {n : ℕ}
    (T : LTree X n) (hT : T.isShattered C) (hne : C.Nonempty) :
    ∃ (seq : List X) (c : X → Bool), c ∈ C ∧
      L.mistakesFrom s c seq = n := by
  induction n generalizing C s with
  | zero =>
    obtain ⟨c₀, hc₀⟩ := hne
    exact ⟨[], c₀, hc₀, rfl⟩
  | succ k ih =>
    match T, hT with
    | .branch x l r, ⟨⟨ct, hct, hctx⟩, ⟨cf, hcf, hcfx⟩, hsl, hsr⟩ =>
      by_cases hpred : L.predict s x = true
      · have hne_f : ({c ∈ C | c x = false}).Nonempty := ⟨cf, hcf, hcfx⟩
        obtain ⟨seq', c', hc'mem, hcount⟩ :=
          ih (L.update s x false) r hsr hne_f
        refine ⟨x :: seq', c', hc'mem.1, ?_⟩
        simp only [OnlineLearner.mistakesFrom, hc'mem.2, hpred]
        simp [hcount]; omega
      · have hpf : L.predict s x = false := by
          cases h : L.predict s x <;> simp_all
        have hne_t : ({c ∈ C | c x = true}).Nonempty := ⟨ct, hct, hctx⟩
        obtain ⟨seq', c', hc'mem, hcount⟩ :=
          ih (L.update s x true) l hsl hne_t
        refine ⟨x :: seq', c', hc'mem.1, ?_⟩
        simp only [OnlineLearner.mistakesFrom, hc'mem.2, hpf]
        simp [hcount]; omega

/-- Relate mistakesFrom to the original mistakes function. -/
theorem mistakesFrom_init_eq {X : Type}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    L.mistakesFrom L.init c seq = L.mistakes c seq := by
  rfl

-- ============================================================
-- VERSION SPACE AND SOA
-- ============================================================

/-- Version space after observing a history. -/
def versionSpace {X : Type} (C : ConceptClass X Bool) (history : List (X × Bool)) :
    ConceptClass X Bool :=
  {c ∈ C | ∀ p ∈ history, c p.1 = p.2}

/-- The Standard Optimal Algorithm (SOA). -/
noncomputable def SOA (X : Type) (C : ConceptClass X Bool) : OnlineLearner X Bool where
  State := List (X × Bool)
  init := []
  predict := fun history x =>
    let V := versionSpace C history
    if LittlestoneDim X {c ∈ V | c x = true} ≥ LittlestoneDim X {c ∈ V | c x = false}
    then true else false
  update := fun history x y => history ++ [(x, y)]

-- ============================================================
-- SOA INTERFACE LEMMAS (abstraction barrier for Inv-stability)
-- ============================================================

/-- SOA prediction: picks the label whose version space side has higher Ldim.
    NOT @[simp]: proofs should explicitly opt-in to see SOA internals (Inv-stability). -/
theorem SOA_predict_eq (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) :
    (SOA X C).predict history x =
      if LittlestoneDim X {c ∈ versionSpace C history | c x = true} ≥
         LittlestoneDim X {c ∈ versionSpace C history | c x = false}
      then true else false := rfl

/-- SOA state update: append observation to history.
    NOT @[simp]: explicit use preserves abstraction barrier. -/
theorem SOA_update_eq (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) (y : Bool) :
    (SOA X C).update history x y = history ++ [(x, y)] := rfl

/-- SOA init state is empty history. -/
theorem SOA_init_eq (X : Type) (C : ConceptClass X Bool) :
    (SOA X C).init = ([] : List (X × Bool)) := rfl

/-- SOA mistakesFrom cons: unfold one step using the interface. -/
theorem SOA_mistakesFrom_cons (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (c : X → Bool) (x : X) (xs : List X) :
    (SOA X C).mistakesFrom history c (x :: xs) =
      (if (SOA X C).predict history x ≠ c x then 1 else 0) +
        (SOA X C).mistakesFrom (history ++ [(x, c x)]) c xs := rfl

-- ============================================================
-- VERSION SPACE INFRASTRUCTURE LEMMAS
-- ============================================================

/-- Version space subset. -/
theorem versionSpace_subset {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} :
    versionSpace C history ⊆ C :=
  fun _ hm => hm.1

/-- Target stays in version space. -/
theorem target_in_versionSpace {X : Type} {C : ConceptClass X Bool}
    {c : X → Bool} (hcC : c ∈ C) {history : List (X × Bool)}
    (hcons : ∀ p ∈ history, c p.1 = p.2) :
    c ∈ versionSpace C history :=
  ⟨hcC, hcons⟩

/-- Extending history restricts the version space. -/
theorem versionSpace_append {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} {x : X} {y : Bool} :
    versionSpace C (history ++ [(x, y)]) ⊆ versionSpace C history := by
  intro c ⟨hcC, hcons⟩
  exact ⟨hcC, fun p hp => hcons p (List.mem_append.mpr (Or.inl hp))⟩

/-- Ldim of version space ≤ Ldim of C. -/
theorem ldim_versionSpace_le {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} :
    LittlestoneDim X (versionSpace C history) ≤ LittlestoneDim X C := by
  apply iSup₂_le; intro n ⟨T, hT⟩
  exact le_iSup₂_of_le n ⟨T, T.isShattered_mono versionSpace_subset hT⟩ le_rfl
