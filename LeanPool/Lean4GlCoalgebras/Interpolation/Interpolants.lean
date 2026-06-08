/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import Mathlib.Data.Fintype.Defs
import LeanPool.Lean4GlCoalgebras.Logic.FixedPointTheorem
import LeanPool.Lean4GlCoalgebras.Split.Completeness

/-! ## Finding interpolants

Here we show that given a finite GL-split proof, we can always find suitable interpolants.
-/

namespace Lean4GlCoalgebras

open Split

/-- Get the entire underlying sequent of a finite proof. -/
def Split.Proof.Sequent (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Sequent :=
  fin_X.elems.biUnion (fun x ↦ (f (r 𝕏.α x)).image (Sum.elim id id))

/-- Find `n` such that for all `m ≥ n`, `m` is not in an the variables of the proof. -/
def Split.Proof.freeVar (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Nat :=
  Sequent.freshVar (Proof.Sequent 𝕏)

lemma at_in_lt_freeVar {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {n : Nat}
    (h : at n ∈ 𝕏.Sequent) : n < 𝕏.freeVar := by
  have 𝕏_ne : 𝕏.Sequent ≠ ∅ := by aesop
  simp only [Proof.freeVar, Sequent.freshVar, 𝕏_ne, ↓reduceDIte]
  apply Nat.lt_of_succ_le
  apply Finset.le_max'
  simp only [Nat.succ_eq_add_one, Finset.mem_image]
  exact ⟨at n, h, by simp [Formula.freshVar]⟩

/-- For each `x` in a finite proof, find a free variable. -/
noncomputable def encodeVar {𝕏 : Proof} [Fintype 𝕏.X] : 𝕏.X → Nat :=
  fun x ↦ 𝕏.freeVar + Fintype.equivFin 𝕏.X x

/-- Given `n` in the range of the free variables, unencode it back to its proof node. -/
noncomputable def unencodeVar {𝕏 : Proof} [Fintype 𝕏.X] (n : Nat)
    (h1 : n - 𝕏.freeVar < Fintype.card 𝕏.X) : 𝕏.X :=
  (Fintype.equivFin 𝕏.X).symm ⟨n - 𝕏.freeVar, h1⟩

/-- The encodeVar function is injective. -/
lemma encodeVar_inj (𝕏 : Proof) [Fintype 𝕏.X] : Function.Injective (@encodeVar 𝕏 _) := by
  simp only [Function.Injective]
  intro x y hyp
  exact (Fintype.equivFin 𝕏.X).injective (Fin.ext (Nat.add_left_cancel hyp))

/-- The encodeVar function is injective.
This version works better with simp than `encodeVar_inj`. -/
@[simp]
lemma encodeVar_inj' (𝕏 : Proof) [Fintype 𝕏.X] (x y : 𝕏.X) :
    @encodeVar 𝕏 _ x = @encodeVar 𝕏 _ y ↔ x = y := by
  simp [encodeVar, Fin.val_eq_val]

/-- unencodeVar is a left inverse of encodeVar. -/
lemma encodeVar_inv (𝕏 : Proof) [Fintype 𝕏.X] (x : 𝕏.X) :
    unencodeVar (encodeVar x) (by simp [encodeVar]) = x := by
  simp [unencodeVar, encodeVar]

/-- encodeVar is a left inverse of unencodeVar. -/
lemma unencodeVar_inv (𝕏 : Proof) [Fintype 𝕏.X] (n : ℕ) (h1)
    (h2 : n ≥ 𝕏.freeVar) : encodeVar (@unencodeVar 𝕏 _ n h1) = n := by
  simp [unencodeVar, encodeVar]
  omega

lemma at_in_not_encodeVar {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {n : Nat}
    (h : at n ∈ 𝕏.Sequent) (x : 𝕏.X) : ¬ encodeVar x = n := by
  have := at_in_lt_freeVar h
  intro con
  subst con
  simp_all [encodeVar]

lemma encodeVar_eq {𝕏 : Proof} {Fin_X : Fintype 𝕏.X} {x : 𝕏.X} {n : ℕ} {h1}
    {h2 : n ≥ 𝕏.freeVar} : encodeVar x = n ↔ x = unencodeVar n h1 := by
  constructor
  · intro mp
    subst mp
    simp [encodeVar_inv]
  · intro mpp
    subst mpp
    apply unencodeVar_inv
    exact h2

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def equation {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
    Formula := match r : r 𝕏.α x with
  | RuleApp.topₗ _ _ => ⊥
  | RuleApp.topᵣ _ _ => ⊤
  | RuleApp.axₗₗ _ _ _ => ⊥
  | RuleApp.axₗᵣ _ k _ => na k
  | RuleApp.axᵣₗ _ k _ => at k
  | RuleApp.axᵣᵣ _ _ _ => ⊤
  | RuleApp.orₗ _ _ _ _ =>
      at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.step x; simp only [r] at this; aesop)))
  | RuleApp.orᵣ _ _ _ _ =>
      at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.step x; simp only [r] at this; aesop)))
  | RuleApp.andₗ _ _ _ _ =>
      at (encodeVar ((p 𝕏.α x)[0]'(by
        have := 𝕏.step x
        simp only [r] at this
        apply congrArg List.length at this
        simp_all [List.length_map]))) v
        at (encodeVar ((p 𝕏.α x)[1]'(by
          have := 𝕏.step x
          simp only [r] at this
          apply congrArg List.length at this
          simp_all [List.length_map])))
  | RuleApp.andᵣ _ _ _ _ =>
      at (encodeVar ((p 𝕏.α x)[0]'(by
        have := 𝕏.step x
        simp only [r] at this
        apply congrArg List.length at this
        simp_all [List.length_map]))) &
        at (encodeVar ((p 𝕏.α x)[1]'(by
          have := 𝕏.step x
          simp only [r] at this
          apply congrArg List.length at this
          simp_all [List.length_map])))
  | RuleApp.boxₗ _ _ _ =>
      ◇ at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.step x; simp [r] at this; aesop)))
  | RuleApp.boxᵣ _ _ _ =>
      □ at (encodeVar ((p 𝕏.α x)[0]'(by have := 𝕏.step x; simp [r] at this; aesop)))

lemma encodeVar_helper₁ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} {n : ℕ}
    (h : n ∈ Finset.image encodeVar Y) : n - 𝕏.freeVar < Fintype.card 𝕏.X := by
  simp only [Finset.mem_image, encodeVar] at h
  have ⟨y, y_in, y_eq⟩ := h
  rw [←y_eq]
  simp

lemma encodeVar_helper₂ {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X} {n : ℕ}
    (h : n ∈ Finset.image encodeVar Y) : unencodeVar n (encodeVar_helper₁ h) ∈ Y := by
  simp only [Finset.mem_image, encodeVar] at h
  have ⟨y, y_in, y_eq⟩ := h
  simp [←y_eq, unencodeVar, y_in]

/-- Extend a substitution specific to encoded variables to all formulas. -/
noncomputable def extend {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X}
    (Y_sub : Y ⊆ fin_X.elems) (σ : {x : 𝕏.X // x ∈ Y} → Formula) :
    Formula → Formula
  | ⊥ => ⊥
  | ⊤ => ⊤
  | at n =>
      if h : n ∈ Y.image encodeVar then
        σ ⟨unencodeVar n (encodeVar_helper₁ h), encodeVar_helper₂ h⟩
      else at n
  | na n =>
      if h : n ∈ Y.image encodeVar then
        ~ σ ⟨unencodeVar n (encodeVar_helper₁ h), encodeVar_helper₂ h⟩
      else na n
  | A & B => (extend Y_sub σ A) & (extend Y_sub σ B)
  | A v B => (extend Y_sub σ A) v (extend Y_sub σ B)
  | □ A => □ (extend Y_sub σ A)
  | ◇ A => ◇ (extend Y_sub σ A)

lemma partial_const {p : Nat → Prop} [DecidablePred p] (σ : Subtype p → Formula)
    (A : Formula) : (∀ n ∈ Formula.vocab A, ¬ p n) → (A = partial_ σ A) := by
  intro h
  induction A with
  | bottom => rfl
  | top => rfl
  | atom n =>
      rw [partial_]
      rw [dif_neg (h n (by simp only [Formula.vocab, Finset.mem_singleton]))]
  | negAtom n =>
      rw [partial_]
      rw [dif_neg (h n (by simp only [Formula.vocab, Finset.mem_singleton]))]
  | and A B ihA ihB =>
      rw [partial_]
      have hA : A = partial_ σ A := ihA (by
        intro n hn
        exact h n (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inl hn))
      have hB : B = partial_ σ B := ihB (by
        intro n hn
        exact h n (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inr hn))
      rw [←hA, ←hB]
  | or A B ihA ihB =>
      rw [partial_]
      have hA : A = partial_ σ A := ihA (by
        intro n hn
        exact h n (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inl hn))
      have hB : B = partial_ σ B := ihB (by
        intro n hn
        exact h n (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inr hn))
      rw [←hA, ←hB]
  | box A ihA =>
      rw [partial_]
      have hA : A = partial_ σ A := ihA (by
        intro n hn
        exact h n (by
          simp only [Formula.vocab]
          exact hn))
      rw [←hA]
  | diamond A ihA =>
      rw [partial_]
      have hA : A = partial_ σ A := ihA (by
        intro n hn
        exact h n (by
          simp only [Formula.vocab]
          exact hn))
      rw [←hA]

@[simp]
lemma Finset.doubleton_subset_iff {α : Type} [DecidableEq α] {s : Finset α} {a b : α} :
    {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  simp [Finset.subset_iff]

lemma extend_in {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {Y : Finset 𝕏.X}
    (Y_sub : Y ⊆ fin_X.elems) (σ : {x : 𝕏.X // x ∈ Y} → Formula)
    (A : Formula) :
    (∀ y ∈ Y, encodeVar y ∉ Formula.vocab A) → (A = extend Y_sub σ A) := by
  intro h
  induction A with
  | bottom => rfl
  | top => rfl
  | atom n =>
      rw [extend]
      by_cases hn : n ∈ Y.image encodeVar
      · have ⟨y, hy, hy_eq⟩ := Finset.mem_image.mp hn
        exact False.elim (h y hy (by
          simp only [Formula.vocab, Finset.mem_singleton]
          exact hy_eq))
      · rw [dif_neg hn]
  | negAtom n =>
      rw [extend]
      by_cases hn : n ∈ Y.image encodeVar
      · have ⟨y, hy, hy_eq⟩ := Finset.mem_image.mp hn
        exact False.elim (h y hy (by
          simp only [Formula.vocab, Finset.mem_singleton]
          exact hy_eq))
      · rw [dif_neg hn]
  | and A B ihA ihB =>
      rw [extend]
      have hA : A = extend Y_sub σ A := ihA (by
        intro y hy hyv
        exact h y hy (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inl hyv))
      have hB : B = extend Y_sub σ B := ihB (by
        intro y hy hyv
        exact h y hy (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inr hyv))
      rw [←hA, ←hB]
  | or A B ihA ihB =>
      rw [extend]
      have hA : A = extend Y_sub σ A := ihA (by
        intro y hy hyv
        exact h y hy (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inl hyv))
      have hB : B = extend Y_sub σ B := ihB (by
        intro y hy hyv
        exact h y hy (by
          simp only [Formula.vocab, Finset.mem_union]
          exact Or.inr hyv))
      rw [←hA, ←hB]
  | box A ihA =>
      rw [extend]
      have hA : A = extend Y_sub σ A := ihA (by
        intro y hy hyv
        exact h y hy (by
          simp only [Formula.vocab]
          exact hyv))
      rw [←hA]
  | diamond A ihA =>
      rw [extend]
      have hA : A = extend Y_sub σ A := ihA (by
        intro y hy hyv
        exact h y hy (by
          simp only [Formula.vocab]
          exact hyv))
      rw [←hA]

/-- From the paper: If py ∈ χx then x ◁ y. -/
lemma encodeVar_in_equation_imp_edge {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {x y : 𝕏.X} :
  encodeVar y ∈ (equation x).vocab → (edge 𝕏.α) x y := by
  unfold equation
  split <;> simp only [Formula.vocab, Finset.mem_singleton, Finset.mem_union,
    encodeVar_inj', edge]
  case h_4 Δ n in_Δ r =>  -- this is a contradiction because it cannot be = n
    have h : n < 𝕏.freeVar := by
      apply at_in_lt_freeVar
      simp only [Proof.Sequent, Finset.mem_biUnion]
      exact ⟨x, fin_X.complete x, by simp [r, f, in_Δ]⟩
    intro con
    have lower : 𝕏.freeVar ≤ encodeVar y := by
      unfold encodeVar
      omega
    omega
  case h_5 Δ n in_Δ r =>
    have h : n < 𝕏.freeVar := by
      apply at_in_lt_freeVar
      simp only [Proof.Sequent, Finset.mem_biUnion]
      exact ⟨x, fin_X.complete x, by simp [r, f, in_Δ]⟩
    intro con
    have lower : 𝕏.freeVar ≤ encodeVar y := by
      unfold encodeVar
      omega
    omega
  all_goals
    aesop

/-- From the paper: If p ∈ χx then p ∈ Voc(fˡ(x)) ∩ Voc(fʳ(x)) or p = py and x ◁ y. -/
lemma var_in_equation {𝕏 : Proof} [fin_X : Fintype 𝕏.X] {x : 𝕏.X} (n : ℕ) :
  n ∈ (equation x).vocab →
  n ∈ (SplitSequent.left (f (r 𝕏.α x))).vocab ∩
      (SplitSequent.right (f (r 𝕏.α x))).vocab
  ∨ ∃ y, encodeVar y = n ∧ (edge 𝕏.α) x y := by
  unfold equation
  split <;> simp [Formula.vocab, encodeVar, edge] <;> try grind
  case h_4 Δ n in_Δ r =>  -- this is a contradiction because it cannot be = n
    simp [r, f, SplitSequent.left, SplitSequent.right, Sequent.vocab]
    grind [Formula.vocab]
  case h_5 Δ n in_Δ r =>
    simp [r, f, SplitSequent.left, SplitSequent.right, Sequent.vocab]
    grind [Formula.vocab]

/-- Helper for Solution strong, gives interaction between single substitution and
partial substitution. -/
lemma interpolant_strong_helper {p : Nat → Prop} [DecidablePred p]
    (σ : Subtype p → Formula) (n : ℕ) {B A : Formula} :
    single n B (partial_ σ A) =
      @partial_ (fun m ↦ p m ∨ m = n) _
        (fun m ↦ single n B (if h : p m then σ ⟨m, h⟩ else at m)) A := by
  induction A
  case top => simp only [partial_, single]
  case bottom => simp only [partial_, single]
  case atom m =>
    simp only [partial_]
    by_cases p m
    case pos pm =>
      simp [pm, ↓reduceDIte]
    case neg not_pm =>
      by_cases m = n
      case pos n_eq_m => simp [n_eq_m, ↓reduceDIte]
      case neg n_ne_m => simp [not_pm, n_ne_m, single]
  case negAtom m =>
    simp only [partial_]
    by_cases p m
    case pos pm =>
      simp [pm, ↓reduceDIte, single_neg]
    case neg not_pm =>
      by_cases m = n
      case pos n_eq_m =>
        by_cases p n
        case pos pn => simp only [n_eq_m, or_true, ↓reduceDIte, pn, single_neg]
        case neg not_pn =>
          simp only [n_eq_m, or_true, ↓reduceDIte, not_pn, single, BEq.rfl,
            ↓reduceIte]
      case neg n_ne_m => simp [not_pm, n_ne_m, single]
  case or A B ih1 ih2 => simp [partial_, single, ih1, ih2]
  case and A B ih1 ih2 => simp [partial_, single, ih1, ih2]
  case box A ih => simp [partial_, single, ih]
  case diamond A ih => simp [partial_, single, ih]

open Classical in
/-- Strong solution towards finding interpolants. -/
noncomputable def interpolantStrong {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  {Y : Finset 𝕏.X} (Y_sub : Y ⊆ fin_X.elems) :
    {n // n ∈ Y.image encodeVar} → Formula :=
    if em_con : Y = ∅ then (fun ⟨n, n_prop⟩ ↦ False.elim (by simp_all)) else
    if loop_con : ∃ y, Relation.TransGen (edgeRestr (fun x ↦ x ∈ Y)) y y then
      have box_in_Y :=
        exists_box_on_restr_loop loop_con.choose (fun x ↦ x ∈ Y) loop_con.choose_spec
      let box := box_in_Y.choose
      have τ := @interpolantStrong _ _ (Y \ {box}) (by
        intro x x_in
        exact Y_sub (Finset.mem_sdiff.mp x_in).1)
      have box_or_dia :
          (partial_ τ (equation box)).isBox ∨
            (partial_ τ (equation box)).isDiamond := by
        unfold box
        have isBox := box_in_Y.choose_spec.1
        cases r_def : r 𝕏.α box_in_Y.choose <;>
          simp [r_def] at isBox <;>
          simp [RuleApp.isBox] at isBox
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isDiamond]
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isBox]
      have ψ :=
        (fixed_point_theorem_modal (partial_ τ (equation box)) (encodeVar box)
          box_or_dia).choose
      fun n ↦ (single (encodeVar box) ψ) (partial_ τ (at n))
    else
      have y_in_Y : ∃ y, y ∈ Y := by
        by_contra h
        apply em_con
        apply Finset.eq_empty_of_forall_notMem
        simp_all
      have leaf_in_Y :=
        finite_and_no_loop_implies_exists_leaf (fun x ↦ x ∈ Y) y_in_Y.choose
          y_in_Y.choose_spec loop_con
      let leaf := leaf_in_Y.choose
      let τ := @interpolantStrong _ _ (Y \ {leaf}) (by
        intro x x_in
        exact Y_sub (Finset.mem_sdiff.mp x_in).1)
      fun n ↦ (single (encodeVar leaf) (equation leaf)) (partial_ τ (at n))
termination_by Finset.card Y
decreasing_by
  · have box_in : box ∈ Y := box_in_Y.choose_spec.2.1
    simp [←Finset.card_sdiff_add_card_inter Y {box}, box_in]
    linarith
  · have leaf_in : leaf ∈ Y := leaf_in_Y.choose_spec.1
    simp [←Finset.card_sdiff_add_card_inter Y {leaf}, leaf_in]
    linarith

open Classical in
private theorem interpolant_strong_prop_loop_other {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  {Y : Finset 𝕏.X} {n : ℕ} (n_in : n ∈ Y.image encodeVar)
  {box_in_Y : ∃ z,
      (r 𝕏.α z).isBox ∧ (fun x ↦ x ∈ Y) z ∧
        Relation.TransGen (edgeRestr (fun x ↦ x ∈ Y)) z z}
  (Z_sub : Y \ {box_in_Y.choose} ⊆ fin_X.elems)
  (τ_prop : ∀ n : {n // n ∈ (Y \ {box_in_Y.choose}).image encodeVar},
      ((interpolantStrong Z_sub n =
        partial_ (interpolantStrong Z_sub)
          (equation (unencodeVar n (encodeVar_helper₁ n.2))))
       ∨ (interpolantStrong Z_sub n ≅
        partial_ (interpolantStrong Z_sub)
          (equation (unencodeVar n (encodeVar_helper₁ n.2)))))
    ∧ (∀ m ∈ (interpolantStrong Z_sub n).vocab,
        m ∈ ((SplitSequent.left (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n.2))))).vocab ∩
             (SplitSequent.right (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n.2))))).vocab) ∪
             (fin_X.elems.image encodeVar \ (Y \ {box_in_Y.choose}).image encodeVar))
    ∧ (∀ y : 𝕏.X, encodeVar y ∈ (partial_ (interpolantStrong Z_sub) (at n)).vocab →
          Relation.ReflTransGen (edge 𝕏.α) (unencodeVar n (encodeVar_helper₁ n.2)) y))
  (ψ : Formula)
  (ψ_not_box : encodeVar box_in_Y.choose ∉ Formula.vocab ψ)
  (ψ_vocab :
    Formula.vocab ψ ⊆
      Formula.vocab (partial_ (interpolantStrong Z_sub) (equation box_in_Y.choose)))
  {z : 𝕏.X} (z_in : z ∈ Y) (box_z : z ∈ p 𝕏.α box_in_Y.choose)
  (equation_eq :
    equation box_in_Y.choose = □ (at (encodeVar z)) ∨
      equation box_in_Y.choose = ◇ (at (encodeVar z)))
  (y_ne_box : n ≠ encodeVar box_in_Y.choose) :
      (single (encodeVar box_in_Y.choose) ψ (partial_ (interpolantStrong Z_sub) (at n)) =
          partial_ (fun q : {q // q ∈ Y.image encodeVar} ↦
            single (encodeVar box_in_Y.choose) ψ
            (partial_ (interpolantStrong Z_sub) (at (q : ℕ))))
            (equation (unencodeVar n (encodeVar_helper₁ n_in))) ∨
        (single (encodeVar box_in_Y.choose) ψ
          (partial_ (interpolantStrong Z_sub) (at n)) ≅
          partial_ (fun q : {q // q ∈ Y.image encodeVar} ↦
            single (encodeVar box_in_Y.choose) ψ
            (partial_ (interpolantStrong Z_sub) (at (q : ℕ))))
            (equation (unencodeVar n (encodeVar_helper₁ n_in))))) ∧
      (∀ m ∈ (single (encodeVar box_in_Y.choose) ψ
          (partial_ (interpolantStrong Z_sub) (at n))).vocab,
        m ∈ ((SplitSequent.left (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n_in))))).vocab ∩
             (SplitSequent.right (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n_in))))).vocab) ∪
             (fin_X.elems.image encodeVar \ Y.image encodeVar)) ∧
      (∀ y : 𝕏.X,
        encodeVar y ∈ (partial_ (fun q : {q // q ∈ Y.image encodeVar} ↦
            single (encodeVar box_in_Y.choose) ψ
            (partial_ (interpolantStrong Z_sub) (at (q : ℕ)))) (at n)).vocab →
          Relation.ReflTransGen (edge 𝕏.α) (unencodeVar n (encodeVar_helper₁ n_in)) y) := by
  have n_in' : n ∈ Finset.image encodeVar (Y \ {box_in_Y.choose}) := by
    simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨unencodeVar n (encodeVar_helper₁ n_in), ⟨encodeVar_helper₂ n_in, ?_⟩, ?_⟩
    · intro con
      apply y_ne_box
      simp [←con, encodeVar, unencodeVar]
      have := encodeVar_helper₁ n_in
      simp only [Finset.mem_image] at n_in
      have ⟨y, y_in, y_eq⟩ := n_in
      subst y_eq
      simp [encodeVar]
    · apply unencodeVar_inv
      simp only [Finset.mem_image] at n_in
      have ⟨y, y_in, y_eq⟩ := n_in
      subst y_eq
      simp [encodeVar]
  have ⟨eq_or_equiv, vocab, path⟩ := τ_prop ⟨n, n_in'⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases eq_or_equiv with eq | equiv
    · left
      simp only [partial_, n_in', ↓reduceDIte, eq, Finset.mem_image, Finset.mem_sdiff,
        Finset.mem_singleton]
      convert @interpolant_strong_helper _ _ (interpolantStrong Z_sub)
        (encodeVar box_in_Y.choose) ψ (equation (unencodeVar n (encodeVar_helper₁ n_in)))
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro ⟨y, y_in, y_eq⟩
          subst y_eq
          by_cases y_is_box : y = box_in_Y.choose
          · subst y_is_box
            right
            rfl
          · left
            use y
        · intro mpp
          rcases mpp with ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ | x_eq
          · subst y_eq
            use y
          · subst x_eq
            exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, rfl⟩
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        rename_i heq
        constructor
        · intro mpp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
          · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · intro mp
              rcases mp with l | r
              · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
              · exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, Eq.symm r⟩
            · intro mpp
              have ⟨y, y_in_Y, y_eq⟩ := mpp
              subst y_eq
              by_cases h : y = box_in_Y.choose
              · right
                subst h
                rfl
              · left
                use y
          · exact HEq.symm heq
        · intro mp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
    · right
      simp only [partial_, n_in', ↓reduceDIte, Finset.mem_image, Finset.mem_sdiff,
        Finset.mem_singleton]
      have := single_preserves_equiv (encodeVar box_in_Y.choose) _ _ ψ equiv
      have equiv_help {C D E : Formula} (h : C ≅ D) (g : D = E) : (C ≅ E) := by aesop
      apply equiv_help this
      convert @interpolant_strong_helper _ _ (interpolantStrong Z_sub)
        (encodeVar box_in_Y.choose) ψ (equation (unencodeVar n (encodeVar_helper₁ n_in)))
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro mp
          have ⟨y, y_in_Y, y_eq⟩ := mp
          subst y_eq
          by_cases h : y = box_in_Y.choose
          · right
            subst h
            rfl
          · left
            use y
        · intro mpp
          rcases mpp with l | r
          · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
          · exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, Eq.symm r⟩
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        rename_i heq
        constructor
        · intro mpp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
          · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · intro mp
              rcases mp with l | r
              · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
              · exact ⟨box_in_Y.choose, box_in_Y.choose_spec.2.1, Eq.symm r⟩
            · intro mpp
              have ⟨y, y_in_Y, y_eq⟩ := mpp
              subst y_eq
              by_cases h : y = box_in_Y.choose
              · right
                subst h
                rfl
              · left
                use y
          · exact HEq.symm heq
        · intro mp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
  · intro m m_in
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_image, not_exists, not_and]
    rcases in_single_voc' m_in with ⟨m_in_fpt, box_in_τ⟩ | ⟨m_in_τ, m_not_box⟩
    · have m_in_eq := ψ_vocab m_in_fpt
      rcases equation_eq with c | c
      all_goals
      by_cases z_is_box : z = box_in_Y.choose
      · exfalso
        simp only [c, z_is_box, partial_, Finset.mem_image, Finset.mem_sdiff,
          Finset.mem_singleton, encodeVar_inj', exists_eq_right, not_true_eq_false,
          and_false, ↓reduceDIte, Formula.vocab] at m_in_eq
        subst m_in_eq
        apply ψ_not_box
        exact m_in_fpt
      · simp only [partial_, n_in', ↓reduceDIte] at m_in
        simp only [c, partial_, Finset.mem_image, Finset.mem_sdiff,
          Finset.mem_singleton, encodeVar_inj', exists_eq_right, z_in, z_is_box,
          not_false_eq_true, and_self, ↓reduceDIte, Formula.vocab] at m_in_eq
        have m_in := (τ_prop ⟨encodeVar z, by simp [z_in, z_is_box]⟩).2.1 m m_in_eq
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
          Finset.mem_image, Finset.mem_singleton, not_exists, not_and, and_imp] at m_in
        rcases m_in with m_in_seq | m_in_var
        · refine Or.inl ⟨?_, ?_⟩
          · refine @in_vocab_of_path_left 𝕏 (unencodeVar n (encodeVar_helper₁ n_in))
              z ?_ m ?_
            · exact Relation.ReflTransGen.tail (path box_in_Y.choose box_in_τ) box_z
            · convert m_in_seq.1
              simp [encodeVar_inv]
          · refine @in_vocab_of_path_right 𝕏 (unencodeVar n (encodeVar_helper₁ n_in))
              z ?_ m ?_
            · exact Relation.ReflTransGen.tail (path box_in_Y.choose box_in_τ) box_z
            · convert m_in_seq.2
              simp [encodeVar_inv]
        · refine Or.inr ⟨m_in_var.1, ?_⟩
          · intro x x_in con
            subst con
            apply m_in_var.2 x x_in
            intro con
            subst con
            apply ψ_not_box m_in_fpt
            rfl
    · simp only [partial_, n_in', ↓reduceDIte] at m_in_τ
      have ih := vocab m m_in_τ
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_image, Finset.mem_singleton, not_exists, not_and, and_imp] at ih
      rcases ih with ih1 | ih2
      · exact Or.inl ih1
      · refine Or.inr ⟨ih2.1, ?_⟩
        intro x x_in con
        apply ih2.2 x x_in ?_ con
        intro eq
        subst eq
        subst con
        apply m_not_box
        rfl
  · simp only [partial_, n_in, ↓reduceDIte, n_in']
    simp only [partial_, n_in', ↓reduceDIte] at path
    intro y mp
    rcases in_single_voc' mp with ⟨y_in_fpt, box_in_τ⟩ | ⟨y_in_τ, y_not_box⟩
    · have y_in_eq := ψ_vocab y_in_fpt
      rcases equation_eq with c | c
      all_goals
        simp only [c, partial_, Finset.mem_image, Finset.mem_sdiff,
          Finset.mem_singleton, encodeVar_inj', exists_eq_right, z_in, true_and,
          dite_not, Formula.vocab] at y_in_eq
        by_cases z_is_box : z = box_in_Y.choose
        · subst z_is_box
          simp only [↓reduceDIte, Formula.vocab, Finset.mem_singleton, encodeVar_inj'] at y_in_eq
          subst y_in_eq
          exact path box_in_Y.choose box_in_τ
        · simp only [z_is_box, ↓reduceDIte] at y_in_eq
          have := (τ_prop ⟨encodeVar z, by simp [z_in, z_is_box]⟩).2.2
          simp only [partial_, Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton,
            encodeVar_inj', exists_eq_right, z_in, z_is_box, not_false_eq_true, and_self,
            ↓reduceDIte, encodeVar_inv] at this
          apply Relation.ReflTransGen.trans ?_ (this y y_in_eq)
          exact Relation.ReflTransGen.tail (path box_in_Y.choose box_in_τ)
            (show edge 𝕏.α box_in_Y.choose z from box_z)
    · exact path y y_in_τ

open Classical in
private theorem interpolant_strong_prop_leaf_other {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  {Y : Finset 𝕏.X} {n : ℕ} (n_in : n ∈ Y.image encodeVar)
  {leaf_in_Y :
      ∃ y : 𝕏.X, (fun x ↦ x ∈ Y) y ∧ ∀ z ∈ p 𝕏.α y, ¬(fun x ↦ x ∈ Y) z}
  (Z_sub : Y \ {leaf_in_Y.choose} ⊆ fin_X.elems)
  (τ_prop : ∀ n : {n // n ∈ (Y \ {leaf_in_Y.choose}).image encodeVar},
      ((interpolantStrong Z_sub n =
        partial_ (interpolantStrong Z_sub)
          (equation (unencodeVar n (encodeVar_helper₁ n.2))))
       ∨ (interpolantStrong Z_sub n ≅
        partial_ (interpolantStrong Z_sub)
          (equation (unencodeVar n (encodeVar_helper₁ n.2)))))
    ∧ (∀ m ∈ (interpolantStrong Z_sub n).vocab,
        m ∈ ((SplitSequent.left (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n.2))))).vocab ∩
             (SplitSequent.right (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n.2))))).vocab) ∪
             (fin_X.elems.image encodeVar \ (Y \ {leaf_in_Y.choose}).image encodeVar))
    ∧ (∀ y : 𝕏.X, encodeVar y ∈ (partial_ (interpolantStrong Z_sub) (at n)).vocab →
          Relation.ReflTransGen (edge 𝕏.α) (unencodeVar n (encodeVar_helper₁ n.2)) y))
  (y_ne_box : n ≠ encodeVar leaf_in_Y.choose) :
      (single (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
          (partial_ (interpolantStrong Z_sub) (at n)) =
          partial_ (fun q : {q // q ∈ Y.image encodeVar} ↦
            single (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
              (partial_ (interpolantStrong Z_sub) (at (q : ℕ))))
            (equation (unencodeVar n (encodeVar_helper₁ n_in))) ∨
        (single (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
          (partial_ (interpolantStrong Z_sub) (at n)) ≅
          partial_ (fun q : {q // q ∈ Y.image encodeVar} ↦
            single (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
              (partial_ (interpolantStrong Z_sub) (at (q : ℕ))))
            (equation (unencodeVar n (encodeVar_helper₁ n_in))))) ∧
      (∀ m ∈ (single (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
          (partial_ (interpolantStrong Z_sub) (at n))).vocab,
        m ∈ ((SplitSequent.left (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n_in))))).vocab ∩
             (SplitSequent.right (f (r 𝕏.α
              (unencodeVar n (encodeVar_helper₁ n_in))))).vocab) ∪
             (fin_X.elems.image encodeVar \ Y.image encodeVar)) ∧
      (∀ y : 𝕏.X,
        encodeVar y ∈ (partial_ (fun q : {q // q ∈ Y.image encodeVar} ↦
            single (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
              (partial_ (interpolantStrong Z_sub) (at (q : ℕ)))) (at n)).vocab →
          Relation.ReflTransGen (edge 𝕏.α) (unencodeVar n (encodeVar_helper₁ n_in)) y) := by
  have n_in' : n ∈ Finset.image encodeVar (Y \ {leaf_in_Y.choose}) := by
    simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨unencodeVar n (encodeVar_helper₁ n_in), ⟨encodeVar_helper₂ n_in, ?_⟩, ?_⟩
    · intro con
      apply y_ne_box
      simp [←con, encodeVar, unencodeVar]
      have := encodeVar_helper₁ n_in
      simp only [Finset.mem_image] at n_in
      have ⟨y, y_in, y_eq⟩ := n_in
      subst y_eq
      simp [encodeVar]
    · apply unencodeVar_inv
      simp only [Finset.mem_image] at n_in
      have ⟨y, y_in, y_eq⟩ := n_in
      subst y_eq
      simp [encodeVar]
  have ⟨eq_or_equiv, vocab, path⟩ := τ_prop ⟨n, n_in'⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases eq_or_equiv with eq | equiv
    · left
      simp only [partial_, n_in', ↓reduceDIte, eq, Finset.mem_image, Finset.mem_sdiff,
        Finset.mem_singleton]
      convert @interpolant_strong_helper _ _ (interpolantStrong Z_sub)
        (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
        (equation (unencodeVar n (encodeVar_helper₁ n_in)))
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro mp
          have ⟨y, y_in_Y, y_eq⟩ := mp
          subst y_eq
          by_cases h : y = leaf_in_Y.choose
          · right
            subst h
            rfl
          · left
            use y
        · intro mpp
          rcases mpp with l | r
          · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
          · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        rename_i heq
        constructor
        · intro mpp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
          · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · intro mp
              rcases mp with l | r
              · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
              · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
            · intro mpp
              have ⟨y, y_in_Y, y_eq⟩ := mpp
              subst y_eq
              by_cases h : y = leaf_in_Y.choose
              · right
                subst h
                rfl
              · left
                use y
          · exact HEq.symm heq
        · intro mp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
    · right
      simp only [partial_, n_in', ↓reduceDIte, Finset.mem_image, Finset.mem_sdiff,
        Finset.mem_singleton]
      have :=
        single_preserves_equiv (encodeVar leaf_in_Y.choose) _ _
          (equation leaf_in_Y.choose) equiv
      have equiv_help {C D E : Formula} (h : C ≅ D) (g : D = E) : (C ≅ E) := by aesop
      apply equiv_help this
      convert @interpolant_strong_helper _ _ (interpolantStrong Z_sub)
        (encodeVar leaf_in_Y.choose) (equation leaf_in_Y.choose)
        (equation (unencodeVar n (encodeVar_helper₁ n_in)))
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro mp
          have ⟨y, y_in_Y, y_eq⟩ := mp
          subst y_eq
          by_cases h : y = leaf_in_Y.choose
          · right
            subst h
            rfl
          · left
            use y
        · intro mpp
          rcases mpp with l | r
          · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
          · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
      · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
        rename_i heq
        constructor
        · intro mpp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mpp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
          · simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · intro mp
              rcases mp with l | r
              · exact ⟨l.choose, l.choose_spec.1.1, l.choose_spec.2⟩
              · exact ⟨leaf_in_Y.choose, leaf_in_Y.choose_spec.1, Eq.symm r⟩
            · intro mpp
              have ⟨y, y_in_Y, y_eq⟩ := mpp
              subst y_eq
              by_cases h : y = leaf_in_Y.choose
              · right
                subst h
                rfl
              · left
                use y
          · exact HEq.symm heq
        · intro mp
          have ⟨y, ⟨y_in, y_not_box⟩, y_eq⟩ := mp
          refine ⟨y, ⟨y_in, y_not_box⟩, ?_⟩
          convert y_eq
  · intro m m_in
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_image, not_exists, not_and]
    rcases in_single_voc' m_in with ⟨m_in_eq, leaf_in_τ⟩ | ⟨m_in_τ, m_not_box⟩
    · rcases var_in_equation _ m_in_eq with ax_or | desc
      · left
        have un_y := path leaf_in_Y.choose leaf_in_τ
        simp only [Finset.mem_inter] at ax_or
        exact ⟨in_vocab_of_path_left un_y ax_or.1, in_vocab_of_path_right un_y ax_or.2⟩
      · right
        have ⟨y, y_eq, leaf_y⟩ := desc
        subst y_eq
        refine ⟨⟨y, fin_X.complete y, rfl⟩, ?_⟩
        intro x x_in eq
        have := @encodeVar_inj 𝕏 fin_X x y eq
        subst this
        exact leaf_in_Y.choose_spec.2 x leaf_y x_in
    · simp only [partial_, n_in', ↓reduceDIte] at m_in_τ
      have ih := vocab m m_in_τ
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.mem_image, Finset.mem_singleton, not_exists, not_and, and_imp] at ih
      rcases ih with ih1 | ih2
      · exact Or.inl ih1
      · refine Or.inr ⟨ih2.1, ?_⟩
        intro x x_in con
        apply ih2.2 x x_in ?_ con
        intro eq
        subst eq
        subst con
        apply m_not_box
        rfl
  · simp only [partial_, n_in, ↓reduceDIte, n_in']
    simp only [partial_, n_in', ↓reduceDIte] at path
    intro y mp
    rcases in_single_voc' mp with ⟨y_in_eq, leaf_in_τ⟩ | ⟨y_in_τ, y_not_box⟩
    · exact Relation.ReflTransGen.tail (path leaf_in_Y.choose leaf_in_τ)
        (encodeVar_in_equation_imp_edge y_in_eq)
    · exact path y y_in_τ

private theorem box_successor_in_restr_loop {𝕏 : Proof}
    {Y : Finset 𝕏.X} {box : 𝕏.X} (isBox : (r 𝕏.α box).isBox)
    (box_mem : box ∈ Y) (box_loop : Relation.TransGen (edgeRestr fun x ↦ x ∈ Y) box box) :
    ∃ z, p 𝕏.α box = [z] ∧ z ∈ Y ∧ z ∈ p 𝕏.α box := by
  have Xh := 𝕏.step box
  cases r_def : r 𝕏.α box <;>
    simp [r_def] at isBox <;>
    simp [RuleApp.isBox] at isBox <;>
    simp [r_def] at Xh
  all_goals
  refine ⟨Xh.choose, Xh.choose_spec.1, ?_, ?_⟩
  · by_cases box_is_z : box = Xh.choose
    · rw [←box_is_z]
      exact box_mem
    · have ⟨d, box_d⟩ : ∃ d, Relation.TransGen (edgeRestr fun x ↦ x ∈ Y) box d :=
        ⟨box, box_loop⟩
      cases box_d using Relation.TransGen.head_induction_on
      case neg.single box_d =>
        unfold edgeRestr edge at box_d
        convert box_d.2.2
        have := Xh.choose_spec.1
        have d_mem : d ∈ [Xh.choose] := by
          have d_mem' := box_d.1
          change d ∈ p 𝕏.α box at d_mem'
          rw [this] at d_mem'
          exact d_mem'
        exact Eq.symm <| List.mem_singleton.1 d_mem
      case neg.head box_d heq =>
        rename_i c h
        unfold edgeRestr edge at box_d
        convert box_d.2.2
        have := Xh.choose_spec.1
        have c_mem : c ∈ [Xh.choose] := by
          have c_mem' := box_d.1
          change c ∈ p 𝕏.α box at c_mem'
          rw [this] at c_mem'
          exact c_mem'
        exact Eq.symm <| List.mem_singleton.1 c_mem
  · have := Xh.choose_spec.1
    convert List.mem_singleton_self Xh.choose

open Classical in
/-- Proves that `interpolantStrong` satisfies the necessary properties. -/
theorem interpolant_strong_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X]
  (Y : Finset 𝕏.X) (Y_sub : Y ⊆ fin_X.elems) :
      ∀ n : {n // n ∈ Y.image encodeVar},
          ((interpolantStrong Y_sub n =
              partial_ (interpolantStrong Y_sub)
                (equation (unencodeVar n (encodeVar_helper₁ n.2))))
         ∨ (interpolantStrong Y_sub n ≅
              partial_ (interpolantStrong Y_sub)
                (equation (unencodeVar n (encodeVar_helper₁ n.2)))))
       ∧ (∀ m ∈ (interpolantStrong Y_sub n).vocab,
          m ∈
            ((SplitSequent.left
                  (f (r 𝕏.α (unencodeVar n (encodeVar_helper₁ n.2))))).vocab ∩
              (SplitSequent.right
                  (f (r 𝕏.α (unencodeVar n (encodeVar_helper₁ n.2))))).vocab) ∪
                (fin_X.elems.image encodeVar \ Y.image encodeVar))
       ∧ (∀ y : 𝕏.X,
          encodeVar y ∈ (partial_ (interpolantStrong Y_sub) (at n)).vocab →
            (Relation.ReflTransGen (edge 𝕏.α))
              (unencodeVar n (encodeVar_helper₁ n.2)) y)
       := by
  unfold interpolantStrong
  intro ⟨n, n_in⟩
  by_cases em_con : Y = ∅
  · subst em_con
    simp at n_in
  · by_cases loop_con : ∃ y, Relation.TransGen (edgeRestr (fun x ↦ x ∈ Y)) y y
    case pos =>
      simp only [em_con, loop_con, ↓reduceDIte, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff, Finset.mem_image, not_exists, not_and]
      have box_in_Y :=
        exists_box_on_restr_loop loop_con.choose (fun x ↦ x ∈ Y) loop_con.choose_spec
      have Z_sub : Y \ {box_in_Y.choose} ⊆ Fintype.elems := by
        intro x x_in
        exact Y_sub (Finset.mem_sdiff.mp x_in).1
      let τ_prop :=
        @interpolant_strong_prop _ _ (Y \ {box_in_Y.choose}) Z_sub
      have box_or_dia :
          (partial_ (interpolantStrong Z_sub) (equation box_in_Y.choose)).isBox ∨
            (partial_ (interpolantStrong Z_sub) (equation box_in_Y.choose)).isDiamond := by
        have isBox := box_in_Y.choose_spec.1
        cases r_def : r 𝕏.α box_in_Y.choose <;>
          simp [r_def] at isBox <;>
          simp [RuleApp.isBox] at isBox
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isDiamond]
        · unfold equation
          split <;> simp_all
          simp [partial_, Formula.isBox]
      have fpt :=
        fixed_point_theorem_modal
          (partial_ (interpolantStrong Z_sub) (equation box_in_Y.choose))
          (encodeVar box_in_Y.choose) box_or_dia
      have const := partial_const (interpolantStrong Z_sub) (at (encodeVar box_in_Y.choose)) (by
        simp [Formula.vocab, Finset.mem_singleton, forall_eq])
      have ⟨z, p_eq, z_in, box_z⟩ :=
        box_successor_in_restr_loop box_in_Y.choose_spec.1 box_in_Y.choose_spec.2.1
          box_in_Y.choose_spec.2.2
      have equation_eq :
          equation box_in_Y.choose = □ (at (encodeVar z)) ∨
            equation box_in_Y.choose = ◇ (at (encodeVar z)) := by
        have isBox := box_in_Y.choose_spec.1
        unfold equation
        split <;> rename_i r_def <;>
          simp [r_def] at isBox <;>
          simp [RuleApp.isBox] at isBox <;>
          simp [p_eq]
      by_cases n = encodeVar box_in_Y.choose
      case pos y_eq_box =>
        subst y_eq_box
        refine ⟨?_, ?_, ?_⟩
        · right
          simp only [partial_, Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton,
            encodeVar_inj', exists_eq_right, not_true_eq_false, and_false, ↓reduceDIte,
            single, BEq.rfl, ↓reduceIte, encodeVar_inv]
          have h :
              fpt.choose ≅
                single (encodeVar box_in_Y.choose) fpt.choose
                  (partial_ (interpolantStrong Z_sub)
                    (equation box_in_Y.choose)) :=
            equiv_iff_sem_equiv.1 fpt.choose_spec.2.1
          convert h using 1
          rcases equation_eq with c | c
          all_goals
            simp [c, partial_, single, z_in]
        · simp only [←const, single, BEq.rfl, ↓reduceIte]
          intro m m_in_fpt
          have m_in_eq := fpt.choose_spec.2.2 m_in_fpt
          rcases equation_eq with c | c
          all_goals
            simp only [c, partial_, Finset.mem_image, Finset.mem_sdiff,
              Finset.mem_singleton, encodeVar_inj', exists_eq_right, Formula.vocab] at m_in_eq
            by_cases box_is_z : z = box_in_Y.choose
            · exfalso
              subst box_is_z
              simp only [not_true_eq_false, and_false, ↓reduceDIte, Formula.vocab,
                Finset.mem_singleton] at m_in_eq
              subst m_in_eq
              exact fpt.choose_spec.1 m_in_fpt
            · simp only [z_in, box_is_z, not_false_eq_true, and_self, ↓reduceDIte] at m_in_eq
              have m_in_ih := (τ_prop ⟨encodeVar z, by simp [z_in, box_is_z]⟩).2.1 _ m_in_eq
              simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
                Finset.mem_image, Finset.mem_singleton, not_exists, not_and, and_imp] at m_in_ih
              rcases m_in_ih with m_in_seq | m_in_var
              · refine Or.inl ⟨?_, ?_⟩
                · convert @in_vocab_of_path_left 𝕏 box_in_Y.choose z
                    (Relation.ReflTransGen.single box_z) m
                    (by
                      convert m_in_seq.1
                      simp [encodeVar_inv])
                  simp [encodeVar_inv]
                · convert @in_vocab_of_path_right 𝕏 box_in_Y.choose z
                    (Relation.ReflTransGen.single box_z) m
                    (by
                      convert m_in_seq.2
                      simp [encodeVar_inv])
                  simp [encodeVar_inv]
              · refine Or.inr ⟨m_in_var.1, ?_⟩
                · intro x x_in con
                  subst con
                  apply m_in_var.2 x x_in
                  intro con
                  subst con
                  apply fpt.choose_spec.1 m_in_fpt
                  rfl
        · intro y
          simp only [partial_, n_in, ↓reduceDIte, Finset.mem_image, Finset.mem_sdiff,
            Finset.mem_singleton, encodeVar_inj', exists_eq_right, not_true_eq_false,
            and_false, single, BEq.rfl, ↓reduceIte, encodeVar_inv]
          intro mp
          have mp := fpt.choose_spec.2.2 mp
          rcases equation_eq with c | c
          all_goals
            by_cases box_is_z : z = box_in_Y.choose
            · subst box_is_z
              simp only [c, partial_, Finset.mem_image, Finset.mem_sdiff,
                Finset.mem_singleton, encodeVar_inj', exists_eq_right, not_true_eq_false,
                and_false, ↓reduceDIte, Formula.vocab] at mp
              subst mp
              exact Relation.ReflTransGen.refl
            · simp only [c, partial_, Finset.mem_image, Finset.mem_sdiff,
                Finset.mem_singleton, encodeVar_inj', exists_eq_right, z_in, box_is_z,
                not_false_eq_true, and_self, ↓reduceDIte, Formula.vocab] at mp
              have z_y := (τ_prop ⟨encodeVar z, by simp_all⟩).2.2 y (by
                convert mp
                simp [partial_, z_in, box_is_z])
              simp only [encodeVar_inv] at z_y
              apply Relation.ReflTransGen.head box_z z_y
      case neg y_ne_box =>
        simpa using interpolant_strong_prop_loop_other n_in Z_sub τ_prop fpt.choose
          fpt.choose_spec.1 fpt.choose_spec.2.2 z_in box_z equation_eq y_ne_box
    case neg =>
      simp only [em_con, loop_con, ↓reduceDIte, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff, Finset.mem_image, not_exists, not_and]
      have y_in_Y : ∃ y, y ∈ Y := by
        by_contra h
        apply em_con
        apply Finset.eq_empty_of_forall_notMem
        simp_all
      have leaf_in_Y :=
        finite_and_no_loop_implies_exists_leaf (fun x ↦ x ∈ Y) y_in_Y.choose
          y_in_Y.choose_spec loop_con
      have Z_sub : Y \ {leaf_in_Y.choose} ⊆ Fintype.elems := by
        intro x x_in
        exact Y_sub (Finset.mem_sdiff.mp x_in).1
      let τ_prop :=
        @interpolant_strong_prop _ _ (Y \ {leaf_in_Y.choose}) Z_sub
      have const := partial_const (interpolantStrong Z_sub) (at (encodeVar leaf_in_Y.choose)) (by
        simp [Formula.vocab, Finset.mem_singleton, forall_eq])
      by_cases n = encodeVar leaf_in_Y.choose
      case pos y_eq_box =>
        subst y_eq_box
        refine ⟨?_, ?_, ?_⟩
        · left
          simp only [partial_, Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton,
            encodeVar_inj', exists_eq_right, not_true_eq_false, and_false, ↓reduceDIte,
            single, BEq.rfl, ↓reduceIte, encodeVar_inv]
          apply partial_const
          intro n n_in
          by_contra h
          simp only [Finset.mem_image] at h
          have ⟨z, z_prop⟩ := h
          rw [←z_prop.2] at n_in
          have y_z := encodeVar_in_equation_imp_edge n_in
          exact leaf_in_Y.choose_spec.2 _ y_z z_prop.1
        · simp only [←const, single, BEq.rfl, ↓reduceIte]
          intro m m_in_eq
          rcases var_in_equation _ m_in_eq with ax_or | desc
          · left
            simp only [Finset.mem_inter] at ax_or
            have convert_helper := encodeVar_inv 𝕏 leaf_in_Y.choose
            convert ax_or
          · right
            have ⟨y, y_eq, box_y⟩ := desc
            subst y_eq
            refine ⟨⟨y, fin_X.complete y, rfl⟩, ?_⟩
            intro x x_in eq
            have := @encodeVar_inj 𝕏 fin_X x y eq
            subst this
            exact leaf_in_Y.choose_spec.2 x box_y x_in
        · intro y
          simp only [partial_, n_in, ↓reduceDIte, Finset.mem_image, Finset.mem_sdiff,
            Finset.mem_singleton, encodeVar_inj', exists_eq_right, not_true_eq_false,
            and_false, single, BEq.rfl, ↓reduceIte]
          intro mp
          convert Relation.ReflTransGen.single (encodeVar_in_equation_imp_edge mp)
          simp [encodeVar_inv]
      case neg y_ne_box =>
        simpa using interpolant_strong_prop_leaf_other n_in Z_sub τ_prop y_ne_box
termination_by Finset.card Y
decreasing_by
  · have box_in : box_in_Y.choose ∈ Y := box_in_Y.choose_spec.2.1
    simp [←Finset.card_sdiff_add_card_inter Y {box_in_Y.choose}, box_in]
  · have leaf_in : leaf_in_Y.choose ∈ Y := leaf_in_Y.choose_spec.1
    simp [←Finset.card_sdiff_add_card_inter Y {leaf_in_Y.choose}, leaf_in]

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def interpolant (𝕏 : Proof) [fin_X : Fintype 𝕏.X] : Formula → Formula
  := partial_ <| @interpolantStrong 𝕏 _ fin_X.elems (by aesop)

theorem interpolant_prop {𝕏 : Proof} [fin_X : Fintype 𝕏.X] (x : 𝕏.X) :
    (interpolant 𝕏 (at (encodeVar x)) = interpolant 𝕏 (equation x)
  ∨ (interpolant 𝕏 (at (encodeVar x)) ≅ interpolant 𝕏 (equation x)))
  ∧ (interpolant 𝕏 (at (encodeVar x))).vocab ⊆
    ((SplitSequent.left (f (r 𝕏.α x))).vocab ∩
      (SplitSequent.right (f (r 𝕏.α x))).vocab)
 := by
  unfold interpolant
  have h : ∀ y : 𝕏.X, encodeVar y ∈ Finset.image encodeVar fin_X.elems := by
    intro y
    simp only [Finset.mem_image, encodeVar_inj', exists_eq_right]
    exact fin_X.complete y
  have := @interpolant_strong_prop 𝕏 _ fin_X.elems (by aesop) ⟨encodeVar x, by simp [h]⟩
  have eq_chain :
      ∀ α, ∀ a b c d : α, ∀ r : α → α → Prop,
        r a c → a = b → c = d → r b d := by
    grind
  refine ⟨?_, ?_⟩
  · rcases this.1 with l | r
    · left
      refine eq_chain _ _ _ _ _ _ l ?_ ?_
      · simp [partial_, h]
      · apply congrArg₂
        · rfl
        · simp [encodeVar_inv]
    · right
      refine eq_chain _ _ _ _ _ _ r ?_ ?_
      · simp [partial_, h]
      · apply congrArg₂
        · rfl
        · simp [encodeVar_inv]
  · have h : encodeVar x ∈ Finset.image encodeVar fin_X.elems := by
      simp only [Finset.mem_image, encodeVar_inj', exists_eq_right]
      exact fin_X.complete _
    simp only [partial_, h, ↓reduceDIte]
    intro m m_in
    have := this.2.1 m m_in
    simp only [sdiff_self, Finset.bot_eq_empty, Finset.union_empty, Finset.mem_inter] at this
    convert this
    simp [encodeVar_inv]
end Lean4GlCoalgebras
