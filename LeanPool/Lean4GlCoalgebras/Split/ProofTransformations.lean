/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Sigma.Lex
import LeanPool.Lean4GlCoalgebras.Split.Proof
import LeanPool.Lean4GlCoalgebras.Split.CutProof

/-! ## Defining GL-ext+pre proof system.

Here we define the GL-ext+pre system. This system is different from the paper, where we build in
how we connect non-axiomatic leaf nodes into `RuleApp` directly.
-/

namespace Lean4GlCoalgebras

namespace Ext

/-- Rule applications for the GL-ext+pre proof system. -/
inductive RuleApp {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent)
  | pre : (y : 𝕏.X) → (y ∈ Split.p 𝕏.α x) → RuleApp x τ
  | cutₗ : (Δ : SplitSequent) → (A : Formula) → RuleApp x τ
  | cutᵣ : (Δ : SplitSequent) → (A : Formula) → RuleApp x τ
  | wkₗ : (Δ : SplitSequent) → (A : Formula) → (Sum.inl A) ∈ Δ → RuleApp x τ
  | wkᵣ : (Δ : SplitSequent) → (A : Formula) → (Sum.inr A) ∈ Δ → RuleApp x τ
  | topₗ : (Δ : SplitSequent) → (Sum.inl ⊤) ∈ Δ → RuleApp x τ
  | topᵣ : (Δ : SplitSequent) → (Sum.inr ⊤) ∈ Δ → RuleApp x τ
  | axₗₗ : (Δ : SplitSequent) → (n : Nat) →
      (Sum.inl (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp x τ
  | axₗᵣ : (Δ : SplitSequent) → (n : Nat) →
      (Sum.inl (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp x τ
  | axᵣₗ : (Δ : SplitSequent) → (n : Nat) →
      (Sum.inr (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp x τ
  | axᵣᵣ : (Δ : SplitSequent) → (n : Nat) →
      (Sum.inr (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp x τ
  | andₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A & B) ∈ Δ → RuleApp x τ
  | andᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A & B) ∈ Δ → RuleApp x τ
  | orₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A v B) ∈ Δ → RuleApp x τ
  | orᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A v B) ∈ Δ → RuleApp x τ
  | boxₗ : (Δ : SplitSequent) → (A : Formula) → Sum.inl (□ A) ∈ Δ → RuleApp x τ
  | boxᵣ : (Δ : SplitSequent) → (A : Formula) → Sum.inr (□ A) ∈ Δ → RuleApp x τ

/-- Given a RuleApp, obtain the principal formulas. -/
def fₚ {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent
  | RuleApp.pre _ _ => ∅
  | RuleApp.cutₗ _ _ => ∅
  | RuleApp.cutᵣ _ _ => ∅
  | RuleApp.wkₗ _ A _ => {Sum.inl A}
  | RuleApp.wkᵣ _ A _ => {Sum.inr A}
  | RuleApp.topₗ _ _ => {Sum.inl ⊤}
  | RuleApp.topᵣ _ _ => {Sum.inr ⊤}
  | RuleApp.axₗₗ _ n _ => {Sum.inl (at n), Sum.inl (na n)}
  | RuleApp.axₗᵣ _ n _ => {Sum.inl (at n), Sum.inr (na n)}
  | RuleApp.axᵣₗ _ n _ => {Sum.inr (at n), Sum.inl (na n)}
  | RuleApp.axᵣᵣ _ n _ => {Sum.inr (at n), Sum.inr (na n)}
  | RuleApp.andₗ _ A B _ => {Sum.inl (A & B)}
  | RuleApp.andᵣ _ A B _ => {Sum.inr (A & B)}
  | RuleApp.orₗ _ A B _ => {Sum.inl (A v B)}
  | RuleApp.orᵣ _ A B _ => {Sum.inr (A v B)}
  | RuleApp.boxₗ _ A _ => {Sum.inl (□ A)}
  | RuleApp.boxᵣ _ A _ => {Sum.inr (□ A)}

/-- Given a RuleApp, obtain the split sequent. -/
def f {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} : RuleApp x τ → SplitSequent
  | RuleApp.pre y _ => τ y
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ _ _ => Δ
  | RuleApp.wkᵣ Δ _ _ => Δ
  | RuleApp.topₗ Δ _ => Δ
  | RuleApp.topᵣ Δ _ => Δ
  | RuleApp.axₗₗ Δ _ _ => Δ
  | RuleApp.axₗᵣ Δ _ _ => Δ
  | RuleApp.axᵣₗ Δ _ _ => Δ
  | RuleApp.axᵣᵣ Δ _ _ => Δ
  | RuleApp.andₗ Δ _ _ _ => Δ
  | RuleApp.andᵣ Δ _ _ _ => Δ
  | RuleApp.orₗ Δ _ _ _ => Δ
  | RuleApp.orᵣ Δ _ _ _ => Δ
  | RuleApp.boxₗ Δ _ _ => Δ
  | RuleApp.boxᵣ Δ _ _ => Δ

/-- Given a RuleApp, obtain the non-principal formulas. -/
def fₙ {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent} :
    RuleApp x τ → SplitSequent := fun r ↦ f r \ fₚ r

/-- Relating principal formulas, non-principal formulas, and the split sequent. -/
lemma fₙ_alternate {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent}
    (r : RuleApp x τ) : fₙ r = match r with
  | RuleApp.pre y _ => τ y
  | RuleApp.cutₗ Δ _ => Δ
  | RuleApp.cutᵣ Δ _ => Δ
  | RuleApp.wkₗ Δ A _ => Δ \ {Sum.inl A}
  | RuleApp.wkᵣ Δ A _ => Δ \ {Sum.inr A}
  | RuleApp.topₗ Δ _ => Δ \ {Sum.inl ⊤}
  | RuleApp.topᵣ Δ _ => Δ \ {Sum.inr ⊤}
  | RuleApp.axₗₗ Δ n _ => Δ \ {Sum.inl (at n), Sum.inl (na n)}
  | RuleApp.axₗᵣ Δ n _ => Δ \ {Sum.inl (at n), Sum.inr (na n)}
  | RuleApp.axᵣₗ Δ n _ => Δ \ {Sum.inr (at n), Sum.inl (na n)}
  | RuleApp.axᵣᵣ Δ n _ => Δ \ {Sum.inr (at n), Sum.inr (na n)}
  | RuleApp.andₗ Δ A B _ => Δ \ {Sum.inl (A & B)}
  | RuleApp.andᵣ Δ A B _ => Δ \ {Sum.inr (A & B)}
  | RuleApp.orₗ Δ A B _ => Δ \ {Sum.inl (A v B)}
  | RuleApp.orᵣ Δ A B _ => Δ \ {Sum.inr (A v B)}
  | RuleApp.boxₗ Δ A _ => Δ \ {Sum.inl (□ A)}
  | RuleApp.boxᵣ Δ A _ => Δ \ {Sum.inr (□ A)} := by cases r <;> simp [fₙ, f, fₚ]

universe u

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp] def T {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent) :
    CategoryTheory.Functor Type Type :=
  { obj := fun X ↦ ((RuleApp x τ × List X) : Type)
    map := fun {X Y} f ↦
      TypeCat.ofHom fun z ↦
        match z with
        | (r, A) => (r, A.map (CategoryTheory.ConcreteCategory.hom f))
    map_id := by aesop_cat
    map_comp := by aesop_cat }

/-- Get RuleApp of a node (first projection). -/
def r {X : Type} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent}
    (α : X → (T x τ).obj X) (x : X) := (α x).1

/-- Get premises of a node (second projection). -/
def p {X : Type} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent}
    (α : X → (T x τ).obj X) (x : X) := (α x).2

/-- Edge relation induced by `p`. -/
def edge {X : Type} {𝕏 : Split.Proof} {x : 𝕏.X} {τ : 𝕏.X → SplitSequent}
    (α : X → (T x τ).obj X) (x y : X) : Prop := y ∈ p α x

/-- Auxiliary declaration used in the GL coalgebra development. -/
def RuleApp.isBox {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : RuleApp x τ → Prop
  | RuleApp.boxₗ _ _ _ => true
  | RuleApp.boxᵣ _ _ _ => true
  | _ => false

/-- Auxiliary declaration used in the GL coalgebra development. -/
def RuleApp.isNonAxLeaf {𝕏 : Split.Proof} {x : 𝕏.X} {τ} : RuleApp x τ → Prop
  | RuleApp.pre _ _ => true
  | _ => false

/-- Auxiliary declaration used in the GL coalgebra development. -/
structure PreProof {𝕏 : Split.Proof} (x : 𝕏.X) (τ : 𝕏.X → SplitSequent) where
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  X : Type
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  α : X → (T x τ).obj X
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  root : X
  step : ∀ (x : X), match r α x with
    | RuleApp.pre _ _ => p α x = []
    | RuleApp.cutₗ _ A =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)).filterRight ∪ {Sum.inl A},
            (fₙ (r α x)).filterLeft ∪ {Sum.inr (~A)}]
    | RuleApp.cutᵣ _ A =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)).filterLeft ∪ {Sum.inr A},
            (fₙ (r α x)).filterRight ∪ {Sum.inl (~A)}]
    | RuleApp.wkₗ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.wkᵣ _ _ _ => (p α x).map (fun x ↦ f (r α x)) = [fₙ (r α x)]
    | RuleApp.topₗ _ _ => p α x = ∅
    | RuleApp.topᵣ _ _ => p α x = ∅
    | RuleApp.axₗₗ _ _ _ => p α x = ∅
    | RuleApp.axₗᵣ _ _ _ => p α x = ∅
    | RuleApp.axᵣₗ _ _ _ => p α x = ∅
    | RuleApp.axᵣᵣ _ _ _ => p α x = ∅
    | RuleApp.andₗ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl B}]
    | RuleApp.andᵣ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inr A}, (fₙ (r α x)) ∪ {Sum.inr B}]
    | RuleApp.orₗ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inl A, Sum.inl B}]
    | RuleApp.orᵣ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {Sum.inr A, Sum.inr B}]
    | RuleApp.boxₗ _ A _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inl A}]
    | RuleApp.boxᵣ _ A _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inr A}]
  path :
    ∀ x, ∀ f : {f : ℕ → X // f 0 = x ∧ ∀ (n : ℕ), edge α (f n) (f (n + 1))},
      ∀ n, ∃ m, (r α (f.1 (n + m))).isBox

/-- Auxiliary declaration used in the GL coalgebra development. -/
def Proves {𝕏 : Split.Proof} (x : 𝕏.X) {σ} (𝕐 : PreProof x σ)
    (Δ : SplitSequent) : Prop := f (r 𝕐.α 𝕐.root) = Δ

end Ext

open Split

/- ## Proof Transormations

Defining the Proof Transformation as well as basic properties. -/

/-- Structure morphism of a proof transformation! -/
def proofTransformationMap {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ) :
    (y : 𝕏.X) × (partialProof y).X →
      ExtSkip.T.obj ((y : 𝕏.X) × (partialProof y).X) :=
  fun ⟨y, z_y⟩ ↦
  let children := (Ext.p (partialProof y).α z_y).map (fun z ↦ ⟨y, z⟩)
  match (@Ext.r _ _ _ _ (partialProof y).α z_y) with
  | .pre z _ => ⟨ExtSkip.RuleApp.skp (σ z), [⟨z, (partialProof z).root⟩]⟩ -- map to the root
  | .cutₗ Δ A => ⟨ExtSkip.RuleApp.cutₗ Δ A, children⟩
  | .cutᵣ Δ A => ⟨ExtSkip.RuleApp.cutᵣ Δ A, children⟩
  | .wkₗ Δ A in_Δ => ⟨ExtSkip.RuleApp.wkₗ Δ A in_Δ, children⟩
  | .wkᵣ Δ A in_Δ => ⟨ExtSkip.RuleApp.wkᵣ Δ A in_Δ, children⟩
  | .topₗ Δ in_Δ => ⟨ExtSkip.RuleApp.topₗ Δ in_Δ, children⟩
  | .topᵣ Δ in_Δ => ⟨ExtSkip.RuleApp.topᵣ Δ in_Δ, children⟩
  | .axₗₗ Δ n in_Δ => ⟨ExtSkip.RuleApp.axₗₗ Δ n in_Δ, children⟩
  | .axₗᵣ Δ n in_Δ => ⟨ExtSkip.RuleApp.axₗᵣ Δ n in_Δ, children⟩
  | .axᵣₗ Δ n in_Δ => ⟨ExtSkip.RuleApp.axᵣₗ Δ n in_Δ, children⟩
  | .axᵣᵣ Δ n in_Δ => ⟨ExtSkip.RuleApp.axᵣᵣ Δ n in_Δ, children⟩
  | .andₗ Δ A B in_Δ => ⟨ExtSkip.RuleApp.andₗ Δ A B in_Δ, children⟩
  | .andᵣ Δ A B in_Δ => ⟨ExtSkip.RuleApp.andᵣ Δ A B in_Δ, children⟩
  | .orₗ Δ A B in_Δ => ⟨ExtSkip.RuleApp.orₗ Δ A B in_Δ, children⟩
  | .orᵣ Δ A B in_Δ => ⟨ExtSkip.RuleApp.orᵣ Δ A B in_Δ, children⟩
  | .boxₗ Δ A in_Δ => ⟨ExtSkip.RuleApp.boxₗ Δ A in_Δ, children⟩
  | .boxᵣ Δ A in_Δ => ⟨ExtSkip.RuleApp.boxᵣ Δ A in_Δ, children⟩

@[simp]
lemma proofTransformation_f {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ) (y : 𝕏.X)
    (z_in_Cy : (partialProof y).X) :
    ExtSkip.f (ExtSkip.r (proofTransformationMap partialProof) ⟨y, z_in_Cy⟩) =
      Ext.f (@Ext.r _ _ _ _ (partialProof y).α z_in_Cy) := by
  cases r_def : (Ext.r (partialProof y).α z_in_Cy) <;>
    simp_all [ExtSkip.r, proofTransformationMap, ExtSkip.f, Ext.f]

@[simp]
lemma proofTransformation_fₚ {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ) (y : 𝕏.X)
    (z_in_Cy : (partialProof y).X) :
    ExtSkip.fₚ (ExtSkip.r (proofTransformationMap partialProof) ⟨y, z_in_Cy⟩) =
      Ext.fₚ (@Ext.r _ _ _ _ (partialProof y).α z_in_Cy) := by
  cases r_def : (Ext.r (partialProof y).α z_in_Cy) <;>
    simp_all [ExtSkip.r, proofTransformationMap, ExtSkip.fₚ, Ext.fₚ]

@[simp]
lemma proofTransformation_fₙ {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ) (y : 𝕏.X)
    (z_in_Cy : (partialProof y).X) :
    ExtSkip.fₙ (ExtSkip.r (proofTransformationMap partialProof) ⟨y, z_in_Cy⟩) =
      Ext.fₙ (@Ext.r _ _ _ _ (partialProof y).α z_in_Cy) := by
  cases r_def : (Ext.r (partialProof y).α z_in_Cy) <;>
    simp_all [ExtSkip.r, proofTransformationMap, ExtSkip.fₙ_alternate, Ext.fₙ_alternate]

lemma proofTransformation_isBox {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ)
    (z_in_Cy : (y : 𝕏.X) × (partialProof y).X) :
    (ExtSkip.r (proofTransformationMap partialProof) z_in_Cy).isBox ↔
      (Ext.r (partialProof z_in_Cy.1).α z_in_Cy.2).isBox := by
  cases r_def : (Ext.r (partialProof z_in_Cy.1).α z_in_Cy.2) <;>
    simp_all [ExtSkip.r, proofTransformationMap, ExtSkip.RuleApp.isBox, Ext.RuleApp.isBox]


/- ## Lemmas about infinite sequences and chains of dependent sum types

Defining the Proof Transformation as well as basic properties. -/

open Classical in
/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def depSumSeqProj {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1, ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  : ℕ → α × ℕ
  | 0 => ⟨(f (Nat.find (h 0) + 1)).1, Nat.find (h 0) + 1⟩
  | n + 1 => by
      have ih := depSumSeqProj h n
      exact ⟨(f (Nat.find (h ih.2) + 1)).1, Nat.find (h ih.2) + 1⟩

lemma sigmaMemOfMemMap {α : Type} {β : α → Type} {a : α} {xs : List (β a)}
    {u : (a' : α) × β a'} (hmem : u ∈ xs.map (fun b ↦ Sigma.mk a b)) :
    ∃ h : a = u.1, h ▸ u.2 ∈ xs := by
  rcases List.mem_map.mp hmem with ⟨b, hb, hbu⟩
  cases hbu
  exact ⟨rfl, hb⟩

lemma sigmaCastApplyHEq {α : Type} {β : α → Type} {ρ : (a : α) → β a → Type}
    (r : (a : α) → (b : β a) → ρ a b) {a : α} {s t : (x : α) × β x}
    (ha : s.1 = a) (hst : s = t) :
    r a (ha ▸ s.2) ≍ r t.1 t.2 := by
  cases hst
  cases s
  cases ha
  rfl

lemma sigmaMkCastEq {α : Type} {β : α → Type} {s t : (a : α) × β a} {a : α}
    (ha : s.1 = a) (hst : s = t) : Sigma.mk a (ha ▸ s.2) = t := by
  cases hst
  cases s
  cases ha
  rfl

lemma sigmaPredicateOfEq {α : Type} {β : α → Type} {ρ : (a : α) → β a → Prop}
    {s t : (a : α) × β a} (hst : s = t) (h : ρ t.1 t.2) : ρ s.1 s.2 := by
  cases hst
  exact h

lemma sigmaRootOfEq {α : Type} {β : α → Type} (root : (a : α) → β a)
    {s : (a : α) × β a} {a : α} (hst : s = ⟨a, root a⟩) :
    s.2 = root s.1 := by
  cases hst
  rfl

lemma transformedSuccessorRoot {𝕏 : Proof} {σ}
    {partialProof : (x : 𝕏.X) → Ext.PreProof x σ}
    {f : ℕ → (y : 𝕏.X) × (partialProof y).X}
    (f_succ : ∀ n, ExtSkip.edge (proofTransformationMap partialProof) (f n) (f (n + 1)))
    (i : ℕ)
    (hnot : ∀ h : (f i).1 = (f (i + 1)).1,
      ¬ Ext.edge (partialProof (f i).1).α (f i).2 (h ▸ (f (i + 1)).2)) :
    (f (i + 1)).2 = (partialProof (f (i + 1)).1).root := by
  have edge_succ := f_succ i
  unfold proofTransformationMap ExtSkip.edge ExtSkip.p at edge_succ
  rcases r_def : Ext.r (partialProof (f i).1).α (f i).2 <;>
    simp only [r_def, List.mem_singleton] at edge_succ
  case pre z z_in =>
    exact sigmaRootOfEq (fun x ↦ (partialProof x).root) edge_succ
  all_goals
    exfalso
    have ⟨fst_eq, edge_proof⟩ := sigmaMemOfMemMap edge_succ
    exact hnot fst_eq (by
      unfold Ext.edge
      exact edge_proof)

lemma transformedFinderIsNonAxLeaf {𝕏 : Proof} {σ}
    {partialProof : (x : 𝕏.X) → Ext.PreProof x σ}
    {f : ℕ → (y : 𝕏.X) × (partialProof y).X}
    (f_succ : ∀ n, ExtSkip.edge (proofTransformationMap partialProof) (f n) (f (n + 1)))
    (i : ℕ)
    (hnot : ∀ h : (f i).1 = (f (i + 1)).1,
      ¬ Ext.edge (partialProof (f i).1).α (f i).2 (h ▸ (f (i + 1)).2)) :
    (Ext.r (partialProof (f i).1).α (f i).2).isNonAxLeaf := by
  have edge_succ := f_succ i
  unfold proofTransformationMap ExtSkip.edge ExtSkip.p at edge_succ
  rcases r_def : Ext.r (partialProof (f i).1).α (f i).2 <;>
    simp only [r_def, List.mem_singleton] at edge_succ
  case pre z z_in =>
    simp only [Ext.RuleApp.isNonAxLeaf]
  all_goals
    exfalso
    have ⟨fst_eq, edge_proof⟩ := sigmaMemOfMemMap edge_succ
    exact hnot fst_eq (by
      unfold Ext.edge
      exact edge_proof)

lemma infinite_dep_sum_sequence_proj_eq
    {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
    {Q : (a : α) → β a → β a → Prop}
    (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1,
      ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2)) :
    ∀ n, (f (depSumSeqProj h n).2).1 = (depSumSeqProj h n).1 := by
  intro n
  cases n <;> simp [depSumSeqProj] -- surprised how this works?

lemma dep_sum_seq_proj_leq
    {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
    {Q : (a : α) → β a → β a → Prop}
    (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1,
      ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2)) :
    ∀ n, n ≤ (depSumSeqProj h n).2 := by
  intro n
  induction n
  case zero => simp
  case succ n ih =>
    simp [depSumSeqProj]
    grind

open Classical in
lemma fst_same_in_range {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
    {Q : (a : α) → β a → β a → Prop}
    (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1,
      ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2)) :
    ∀ n, ∀ m, n ≤ Nat.find (h (depSumSeqProj h m).2) →
      n ≥ (depSumSeqProj h m).2 → (f (depSumSeqProj h m).2).1 = (f n).1 := by
  intro n m n_lt n_ge
  have n_le_m := dep_sum_seq_proj_leq h n
  induction n
  case zero =>
    have n_ge := by simpa using n_ge
    simp [n_ge]
  case succ n ih =>
    have neq := Nat.find_spec (h (n + 1))
    by_cases eq : n + 1 = (depSumSeqProj h m).2
    case pos => simp [eq]
    case neg =>
      have := ih (by grind) (by grind) (dep_sum_seq_proj_leq h n)
      rw [this]
      by_contra eq
      have :
          ∀ h : (f n).1 = (f (n + 1)).1,
            ¬ Q (f n).1 (f n).2 (h ▸ (f (n + 1)).2) := by
        intro h
        exfalso
        exact eq h
      have := @Nat.find_le _ _ _ (h n) ⟨by grind, this⟩
      have : Nat.find (h (depSumSeqProj h m).2) ≤ Nat.find (h n) := by
        have g : ∀ n, ∀ m, n ≤ m → Nat.find (h n) ≤ Nat.find (h m) :=
          fun n m n_lt_m ↦ @Nat.find_le _ _ _ (h n) ⟨by grind, (Nat.find_spec (h m)).2⟩
        apply g
        grind
      linarith

open Classical in
lemma infinite_dep_sum_chain
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {R : α → α → Prop} {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1,
    ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  (f_chain : ∀ n, Sigma.Lex R Q (f n) (f (n + 1))) :
    ∀ n, R (depSumSeqProj h n).1 (depSumSeqProj h (n + 1)).1 := by
  intro n
  rw [←infinite_dep_sum_sequence_proj_eq h n,
    ←infinite_dep_sum_sequence_proj_eq h (n + 1)]
  simp only [depSumSeqProj, ge_iff_le]
  have n_le_m := dep_sum_seq_proj_leq h n
  have h1 := fst_same_in_range h (Nat.find (h (depSumSeqProj h n).2)) n
    (by simp) (by grind)
  rw [h1]
  rcases Sigma.lex_iff.1 (f_chain (Nat.find (h (depSumSeqProj h n).2))) with
    R_rel | ⟨eq, Q_rel⟩
  · exact R_rel
  · exfalso
    apply (Nat.find_spec (h (depSumSeqProj h n).2)).2 eq
    convert Q_rel <;> simp

open Classical in
/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def infiniteDepSumChainFiniteSubchain
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1,
    ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  (m : ℕ) :
    Fin ((Nat.find (h (depSumSeqProj h m).2) - (depSumSeqProj h m).2) + 1) →
      β (depSumSeqProj h m).1 :=
    fun ⟨n, n_prop⟩ ↦
    have eq : (f ((depSumSeqProj h m).2 + n)).fst = (depSumSeqProj h m).1 := by
      rw [←infinite_dep_sum_sequence_proj_eq h m]
      apply Eq.symm <|
        fst_same_in_range h ((depSumSeqProj h m).2 + n) m ?_ ?_ <;> grind
    eq ▸ (f ((depSumSeqProj h m).2 + n)).2

open Classical in
lemma infinite_dep_sum_chain_finite_subchain_prop
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1,
    ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  (m : ℕ) :
    ∀ k : Fin (Nat.find (h (depSumSeqProj h m).2) - (depSumSeqProj h m).2),
      Q (depSumSeqProj h m).1
        (infiniteDepSumChainFiniteSubchain h m k.castSucc)
        (infiniteDepSumChainFiniteSubchain h m k.succ) := by
    intro ⟨k, k_prop⟩
    unfold infiniteDepSumChainFiniteSubchain
    dsimp
    have := @Nat.find_min _ _ (h (depSumSeqProj h m).2)
      ((depSumSeqProj h m).2 + k) (by grind)
    have this := by simpa using this
    convert this.2 using 1
    · rw [←infinite_dep_sum_sequence_proj_eq]
      apply fst_same_in_range h ((depSumSeqProj h m).2 + k) m ?_ ?_ <;> grind
    · simp
    · grind

lemma infinite_dep_sum_chain_inf
  {α : Type} {β : α → Type} {f : ℕ → (a : α) × β a}
  {Q : (a : α) → β a → β a → Prop}
  (h : ∀ n, ∃ m ≥ n, ∀ h : (f m).1 = (f (m + 1)).1,
    ¬ Q (f m).1 (f m).2 (h ▸ (f (m + 1)).2))
  (p : α → Prop) (q : (a : α) × β a → Prop)
  (inf : ∀ n, ∃ m, p (depSumSeqProj h (n + m)).1)
  (conv : ∀ n, p (depSumSeqProj h n).1 → ∃ m, q (f ((depSumSeqProj h n).2 + m))) :
    ∀ n, ∃ m, q (f (n + m)) := by
  intro n
  have ⟨m, m_prop⟩ := inf n
  have ⟨l, l_prop⟩ := conv (n + m) m_prop
  use (depSumSeqProj h (n + m)).2 - n + l
  convert l_prop using 2
  have := dep_sum_seq_proj_leq h (n + m)
  omega

-- The dependent path proof performs a large case split over transformed proof rules.
/-- Step obligation for `proofTransformation`. -/
private def proofTransformationStepType {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ) : Prop :=
  let α := proofTransformationMap partialProof
  ∀ y_zy : (y : 𝕏.X) × (partialProof y).X,
    match ExtSkip.r α y_zy with
    | ExtSkip.RuleApp.skp _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [ExtSkip.f (ExtSkip.r α y_zy)]
    | ExtSkip.RuleApp.cutₗ _ A =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)).filterRight ∪ {Sum.inl A},
            (ExtSkip.fₙ (ExtSkip.r α y_zy)).filterLeft ∪ {Sum.inr (~A)}]
    | ExtSkip.RuleApp.cutᵣ _ A =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)).filterLeft ∪ {Sum.inr A},
            (ExtSkip.fₙ (ExtSkip.r α y_zy)).filterRight ∪ {Sum.inl (~A)}]
    | ExtSkip.RuleApp.wkₗ _ _ _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [ExtSkip.fₙ (ExtSkip.r α y_zy)]
    | ExtSkip.RuleApp.wkᵣ _ _ _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [ExtSkip.fₙ (ExtSkip.r α y_zy)]
    | ExtSkip.RuleApp.topₗ _ _ => ExtSkip.p α y_zy = ∅
    | ExtSkip.RuleApp.topᵣ _ _ => ExtSkip.p α y_zy = ∅
    | ExtSkip.RuleApp.axₗₗ _ _ _ => ExtSkip.p α y_zy = ∅
    | ExtSkip.RuleApp.axₗᵣ _ _ _ => ExtSkip.p α y_zy = ∅
    | ExtSkip.RuleApp.axᵣₗ _ _ _ => ExtSkip.p α y_zy = ∅
    | ExtSkip.RuleApp.axᵣᵣ _ _ _ => ExtSkip.p α y_zy = ∅
    | ExtSkip.RuleApp.andₗ _ A B _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)) ∪ {Sum.inl A},
            (ExtSkip.fₙ (ExtSkip.r α y_zy)) ∪ {Sum.inl B}]
    | ExtSkip.RuleApp.andᵣ _ A B _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)) ∪ {Sum.inr A},
            (ExtSkip.fₙ (ExtSkip.r α y_zy)) ∪ {Sum.inr B}]
    | ExtSkip.RuleApp.orₗ _ A B _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)) ∪ {Sum.inl A, Sum.inl B}]
    | ExtSkip.RuleApp.orᵣ _ A B _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)) ∪ {Sum.inr A, Sum.inr B}]
    | ExtSkip.RuleApp.boxₗ _ A _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)).D ∪ {Sum.inl A}]
    | ExtSkip.RuleApp.boxᵣ _ A _ =>
        (ExtSkip.p α y_zy).map (fun x ↦ ExtSkip.f (ExtSkip.r α x)) =
          [(ExtSkip.fₙ (ExtSkip.r α y_zy)).D ∪ {Sum.inr A}]

/-- Path obligation for `proofTransformation`. -/
private def proofTransformationPathType {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ) : Prop :=
  let α := proofTransformationMap partialProof
  ∀ x, ∀ f : {f : ℕ → ((y : 𝕏.X) × (partialProof y).X) //
      f 0 = x ∧ ∀ n, ExtSkip.edge α (f n) (f (n + 1))},
    ∀ n, ∃ m, (ExtSkip.r α (f.1 (n + m))).isBox

open Classical in
/-- Step proof for `proofTransformation`. -/
private theorem proofTransformation_step {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ)
    (root_prop : ∀ x, Ext.Proves x (partialProof x) (σ x)) :
    proofTransformationStepType partialProof := by
  unfold proofTransformationStepType
  dsimp
  /- The repeated `ptm_eq` steps keep simplification from collapsing dependent proof
     obligations into a harder form. -/
  intro y_zy
  have h2 := (partialProof y_zy.1).step y_zy.2
  let children : List ((y : 𝕏.X) × (partialProof y).X) :=
    (Ext.p (partialProof y_zy.1).α y_zy.2).map
    (fun z ↦ ⟨y_zy.1, z⟩)
  cases r_def : (@Ext.r _ _ _ _ (partialProof y_zy.1).α y_zy.2) <;>
    simp only [r_def, Ext.fₙ_alternate, SplitSequent.filterLeft, SplitSequent.filterRight,
      List.map_eq_singleton_iff, Bool.false_eq_true, Finset.union_singleton, Finset.union_insert,
      List.empty_eq] at h2
  case pre z _ =>
    have ptm_r_eq :
        ExtSkip.r (proofTransformationMap partialProof) y_zy =
          ExtSkip.RuleApp.skp (σ z) := by
      simp [ExtSkip.r, proofTransformationMap, r_def]
    have ptm_p_eq :
        ExtSkip.p (proofTransformationMap partialProof) y_zy =
          [⟨z, (partialProof z).root⟩] := by
      simp [ExtSkip.p, proofTransformationMap, r_def]
    simp only [ptm_r_eq, ptm_p_eq, List.map_cons, proofTransformation_f, List.map_nil,
      List.cons.injEq, and_true]
    simp only [ExtSkip.f]
    exact root_prop z
  case cutₗ Δ φ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.cutₗ Δ φ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, ←h2]
  case cutᵣ Δ φ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.cutᵣ Δ φ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, ←h2]
  case wkₗ Δ φ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.wkₗ Δ φ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, h2]
  case wkᵣ Δ φ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.wkᵣ Δ φ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, h2]
  case topₗ Δ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.topₗ Δ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ←h2]
  case topᵣ Δ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.topᵣ Δ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ←h2]
  case axₗₗ Δ n in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.axₗₗ Δ n in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ←h2]
  case axₗᵣ Δ n in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.axₗᵣ Δ n in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ←h2]
  case axᵣₗ Δ n in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.axᵣₗ Δ n in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ←h2]
  case axᵣᵣ Δ n in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.axᵣᵣ Δ n in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ←h2]
  case orₗ Δ φ ψ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.orₗ Δ φ ψ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, h2]
  case orᵣ Δ φ ψ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.orᵣ Δ φ ψ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, h2]
  case andₗ Δ φ ψ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.andₗ Δ φ ψ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, ←h2]
  case andᵣ Δ φ ψ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.andᵣ Δ φ ψ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, ←h2]
  case boxₗ Δ φ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.boxₗ Δ φ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, h2]
  case boxᵣ Δ φ in_Δ =>
    have ptm_eq :
        proofTransformationMap partialProof y_zy =
          ⟨ExtSkip.RuleApp.boxᵣ Δ φ in_Δ, children⟩ := by
      simp [proofTransformationMap, r_def, children]
    simp only [ExtSkip.p, ptm_eq, List.map_map, List.map_eq_singleton_iff, Function.comp_apply,
      proofTransformation_f, Bool.false_eq_true, Finset.union_singleton, List.map_eq_nil_iff,
      Finset.union_insert, children]
    rw [ExtSkip.r]
    simp [ptm_eq, ExtSkip.fₙ_alternate, h2]

open Classical in
/-- Path proof for `proofTransformation`. -/
private theorem proofTransformation_path {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ)
    (box_prop : ∀ x, (r 𝕏.α x).isBox →
      (∀ n, ∀ f : Fin (n + 1) → (partialProof x).X,
        f 0 = (partialProof x).root →
        (Ext.r (partialProof x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
        (∀ m : Fin n, Ext.edge (partialProof x).α (f m.castSucc) (f m.succ)) →
        ∃ m : Fin (n + 1), (Ext.r (partialProof x).α (f m)).isBox)) :
    proofTransformationPathType partialProof := by
  unfold proofTransformationPathType
  dsimp
  intro ⟨y, z_y⟩ ⟨f, ⟨f_zero, f_succ⟩⟩
  have lex_chain :
      ∀ n, Sigma.Lex (edge 𝕏.α) (fun x ↦ Ext.edge (partialProof x).α)
        (f n) (f (n + 1)) := by
    intro n
    have := f_succ n
    unfold proofTransformationMap ExtSkip.edge at this
    have this := by simpa [ExtSkip.p] using this
    rcases r_def : Ext.r (partialProof (f n).1).α (f n).2 <;>
      simp only [r_def, List.mem_map, List.mem_singleton] at this
    case pre z z_in =>
      apply Sigma.Lex.left
      convert z_in
      simp [this]
    all_goals
      have ⟨z, z_prop, eq⟩ := this
      apply Sigma.lex_iff.2 (Or.inr ⟨?_, ?_⟩)
      · grind
      · simp only [Ext.edge]
        have eq1 : (f n).1 = (f (n + 1)).1 := by grind
        have eq2 : (f (n + 1)).2 = eq1 ▸ z := by grind
        convert z_prop
        grind
  by_cases h :
      ∀ n, ∃ m ≥ n, ∀ (h : (f m).1 = (f (m + 1)).1),
        ¬ Ext.edge (partialProof (f m).1).α (f m).2
          (h ▸ (f (m + 1)).2)
  case neg =>
    have h := by simpa using h
    intro l
    have ⟨n, n_prop⟩ := h
    have h : ∀ m ≥ n, (f n).1 = (f m).1 := by
      intro m m_ge
      induction m
      case zero =>
        have m_ge := by simpa using m_ge
        subst m_ge
        rfl
      case succ k ih =>
        by_cases eq : n = k + 1
        · subst eq
          rfl
        · rw [ih (by omega)]
          exact (n_prop k (by omega)).choose
    let g : ℕ → (partialProof (f n).1).X :=
      fun m ↦ h (n + m) (by grind) ▸ (f (n + m)).2
    have g_prop :
        ∀ m, Ext.edge (partialProof (f n).fst).α (g m) (g (m + 1)) := by
      intro m
      unfold g
      have ⟨eq, edge⟩ := n_prop (n + m) (by omega)
      grind
    have ⟨m, m_prop⟩ :=
      (partialProof (f n).1).path (f n).2 ⟨g, by unfold g; simp, g_prop⟩ l
    use n + m
    unfold g at m_prop
    have cast_isBox :
        ∀ {x y : 𝕏.X} (hxy : x = y) (z : (partialProof y).X),
          (Ext.r (partialProof x).α (hxy ▸ z)).isBox →
            (Ext.r (partialProof y).α z).isBox := by
      intro x y hxy z hz
      cases hxy
      exact hz
    have idx_eq : n + (l + m) = l + (n + m) := by omega
    rw [← idx_eq]
    simp only [proofTransformation_isBox]
    exact (cast_isBox (h (n + (l + m)) (by omega)) (f (n + (l + m))).snd) m_prop
  case pos =>
    simp only [proofTransformation_isBox]
    let g : ℕ → 𝕏.X := fun n ↦
      (@depSumSeqProj 𝕏.X (fun x ↦ (partialProof x).X) f
        (fun x ↦ Ext.edge (partialProof x).α) h n).1
    have g_prop : ∀ n, edge 𝕏.α (g n) (g (n + 1)) := by
      apply @infinite_dep_sum_chain
      exact lex_chain
    intro n
    have ⟨m, m_prop⟩ := inf_path_has_inf_boxes g g_prop
      (@depSumSeqProj 𝕏.X (fun x ↦ (partialProof x).X) f
        (fun x ↦ Ext.edge (partialProof x).α) h n).2
    apply @infinite_dep_sum_chain_inf 𝕏.X (fun x ↦ (partialProof x).X) f
      (fun x ↦ Ext.edge (partialProof x).α) h
      (fun x ↦ (r 𝕏.α x).isBox)
      (fun ⟨x, z⟩ ↦ (Ext.r (partialProof x).α z).isBox)
      (inf_path_has_inf_boxes g g_prop) ?_
    intro n n_is_box
    simp only
    let f_sub := @infiniteDepSumChainFiniteSubchain 𝕏.X
      (fun x ↦ (partialProof x).X) f
      (fun x ↦ Ext.edge (partialProof x).α) h n
    have f_sub_prop := @infinite_dep_sum_chain_finite_subchain_prop 𝕏.X
      (fun x ↦ (partialProof x).X) f
      (fun x ↦ Ext.edge (partialProof x).α) h n
    have ⟨⟨m, m_lt⟩, m_prop⟩ := box_prop _ n_is_box _ f_sub ?_ ?_ f_sub_prop
    · unfold f_sub infiniteDepSumChainFiniteSubchain at m_prop
      dsimp at m_prop
      have m_prop := by simpa using m_prop
      use m
      let d := @depSumSeqProj 𝕏.X (fun x ↦ (partialProof x).X) f
        (fun x ↦ Ext.edge (partialProof x).α) h n
      have first_eq :
          (f (d.2 + m)).fst = d.1 := by
        rw [← @infinite_dep_sum_sequence_proj_eq 𝕏.X (fun x ↦ (partialProof x).X) f
          (fun x ↦ Ext.edge (partialProof x).α) h n]
        apply Eq.symm <|
          @fst_same_in_range 𝕏.X (fun x ↦ (partialProof x).X) f
            (fun x ↦ Ext.edge (partialProof x).α) h _ _ ?_ ?_
        · have d_le_find := (Nat.find_spec (h d.2)).1
          dsimp [d] at *
          omega
        · dsimp [d]
          omega
      exact sigmaPredicateOfEq
        (ρ := fun a b ↦ (Ext.r (partialProof a).α b).isBox)
        (sigmaMkCastEq first_eq rfl).symm
        m_prop
    · unfold f_sub infiniteDepSumChainFiniteSubchain
      cases n <;> dsimp [depSumSeqProj]
      case zero =>
        exact transformedSuccessorRoot f_succ (Nat.find (h 0))
          (Nat.find_spec (h 0)).2
      case succ n =>
        let ih :=
          (@depSumSeqProj 𝕏.X (fun x ↦ (partialProof x).X) f
            (fun x ↦ Ext.edge (partialProof x).α) h n).2
        exact transformedSuccessorRoot f_succ (Nat.find (h ih))
          (Nat.find_spec (h ih)).2
    · unfold f_sub infiniteDepSumChainFiniteSubchain
      let ih :=
        (@depSumSeqProj 𝕏.X (fun x ↦ (partialProof x).X) f
          (fun x ↦ Ext.edge (partialProof x).α) h n).2
      let d :=
        @depSumSeqProj 𝕏.X (fun x ↦ (partialProof x).X) f
          (fun x ↦ Ext.edge (partialProof x).α) h n
      have fst_eq : d.1 = (f (Nat.find (h ih))).fst := by
        have dep_eq :=
          @infinite_dep_sum_sequence_proj_eq 𝕏.X (fun x ↦ (partialProof x).X) f
            (fun x ↦ Ext.edge (partialProof x).α) h n
        rw [←dep_eq]
        exact @fst_same_in_range 𝕏.X (fun x ↦ (partialProof x).X) f
          (fun x ↦ Ext.edge (partialProof x).α) h
          (Nat.find (h ih)) n le_rfl (Nat.find_spec (h ih)).1
      have eq : ih + (Nat.find (h ih) - ih) = Nat.find (h ih) := by
        have find_ge : ih ≤ Nat.find (h ih) := (Nat.find_spec (h ih)).1
        omega
      have idx_eq :
          f (ih + (Nat.find (h ih) - ih)) = f (Nat.find (h ih)) :=
        congrArg f eq
      have hcast :
          (f (ih + (Nat.find (h ih) - ih))).fst =
            d.1 :=
        (congrArg Sigma.fst idx_eq).trans fst_eq.symm
      have known :
          (Ext.r (partialProof (f (Nat.find (h ih))).fst).α
            (f (Nat.find (h ih))).snd).isNonAxLeaf :=
        transformedFinderIsNonAxLeaf f_succ (Nat.find (h ih))
          (Nat.find_spec (h ih)).2
      change (Ext.r (partialProof d.1).α
        (hcast ▸ (f (ih + (Nat.find (h ih) - ih))).snd)).isNonAxLeaf
      exact sigmaPredicateOfEq
        (ρ := fun a b ↦ (Ext.r (partialProof a).α b).isNonAxLeaf)
        (sigmaMkCastEq hcast idx_eq)
        known

/-- Provides the proof transformation from local pre-proofs and its path witnesses. -/
noncomputable def proofTransformation {𝕏 : Proof} {σ}
    (partialProof : (x : 𝕏.X) → Ext.PreProof x σ)
    (root_prop : ∀ x, Ext.Proves x (partialProof x) (σ x))
    (box_prop : ∀ x, (r 𝕏.α x).isBox →
      (∀ n, ∀ f : Fin (n + 1) → (partialProof x).X,
        f 0 = (partialProof x).root →
        (Ext.r (partialProof x).α (f ⟨n, by simp⟩)).isNonAxLeaf →
        (∀ m : Fin n, Ext.edge (partialProof x).α (f m.castSucc) (f m.succ)) →
        ∃ m : Fin (n + 1), (Ext.r (partialProof x).α (f m)).isBox)) :
    ExtSkip.Proof :=
  { X := (y : 𝕏.X) × (partialProof y).X
    α := proofTransformationMap partialProof
    step := proofTransformation_step partialProof root_prop
    path := proofTransformation_path partialProof box_prop }
end Lean4GlCoalgebras
