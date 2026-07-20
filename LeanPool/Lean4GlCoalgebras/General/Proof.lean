/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.Logic.Syntax
import Mathlib.Data.Set.Defs
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Aesop
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Finset.Lattice.Basic

/-! ## Defining GL-proof systems.

Here we define the GL-proof system along with finitization and basic properties.
-/

namespace Lean4GlCoalgebras

/-! # Basic components of the GL-proof system.-/

/-- Rule applications for the GL-proof system. -/
inductive RuleApp
  | top : (Δ : Sequent) → ⊤ ∈ Δ → RuleApp
  | ax : (Δ : Sequent) → (n : Nat) → (at n ∈ Δ ∧ na n ∈ Δ) → RuleApp
  | and : (Δ : Sequent) → (φ : Formula) → (ψ : Formula) → (φ & ψ) ∈ Δ → RuleApp
  | or : (Δ : Sequent) → (φ : Formula) → (ψ : Formula) → (φ v ψ) ∈ Δ → RuleApp
  | box : (Δ : Sequent) → (φ : Formula) → (□ φ) ∈ Δ → RuleApp

/-- Endofunctor for the GL-proof system. -/
@[simp] def T : (CategoryTheory.Functor Type Type) where
  obj := fun X ↦ (RuleApp × List X)
  map := fun {X Y} f ↦
    TypeCat.ofHom fun x ↦
      match x with
      | (r, A) => (r, A.map (CategoryTheory.ConcreteCategory.hom f))
  map_id := by aesop_cat
  map_comp := by aesop_cat

/-- Given a RuleApp, obtain the principal formulas. -/
def fₚ : RuleApp → Sequent
  | RuleApp.top _ _ => {⊤}
  | RuleApp.ax _ n _ => {at n, na n}
  | RuleApp.and _ A B _ => {A & B}
  | RuleApp.or _ A B _ => {A v B}
  | RuleApp.box _ A _ => {□ A}

/-- Given a RuleApp, obtain the sequent. -/
def f : RuleApp → Sequent
  | RuleApp.top Δ _ => Δ
  | RuleApp.ax Δ _ _ => Δ
  | RuleApp.and Δ _ _ _ => Δ
  | RuleApp.or Δ _ _ _ => Δ
  | RuleApp.box Δ _ _ => Δ

/-- Given a RuleApp, obtain the non-principal formulas. -/
def fₙ : RuleApp → Sequent := fun r ↦ f r \ fₚ r

/-- Relating principal formulas, non-principal formulas, and sequent. -/
lemma fₙ_alternate (r : RuleApp) : fₙ r = match r with
  | RuleApp.top Δ _ => Δ \ {⊤}
  | RuleApp.ax Δ n _ => Δ \ {at n, na n}
  | RuleApp.and Δ A B _ => Δ \ {A & B}
  | RuleApp.or Δ A B _ => Δ \ {A v B}
  | RuleApp.box Δ A _ => Δ \ {□ A} := by cases r <;> simp [fₙ, f, fₚ]

lemma fₚ_sub_f {r : RuleApp} : fₚ r ⊆ f r := by
  cases r <;> grind [fₚ, f]

lemma fₙ_sub_f {r : RuleApp} : fₙ r ⊆ f r := by
  cases r <;> simp_all [fₙ, f]

/-- Auxiliary declaration used in the GL coalgebra development. -/
def RuleApp.isBox : RuleApp → Bool
  | RuleApp.box _ _ _ => true
  | _ => false

/-- Get RuleApp of a node (first projection). -/
def r {X : Type} (α : X → T.obj X) (x : X) := (α x).1

/-- Get premises of a node (second projection). -/
def p {X : Type} (α : X → T.obj X) (x : X) := (α x).2

/-- Edge relation induced by `p`. -/
def edge {X : Type} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

/-- Definition of GL-proof. -/
structure Proof where
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  X : Type
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  α : X → T.obj X
  step : ∀ (x : X), match r α x with
    | RuleApp.top _ _ => p α x = []
    | RuleApp.ax _ _ _ => p α x = []
    | RuleApp.and _ φ ψ _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {φ}, (fₙ (r α x)) ∪ {ψ}]
    | RuleApp.or _ φ ψ _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)) ∪ {φ, ψ}]
    | RuleApp.box _ φ _ => (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {φ}]

/-- GL-proofs are coalgebras. Note: we can do this the other way around, i.e. Proof extends
    CategoryTheory.Endofunctor.Coalgebra T, however I find X and α more explicative than V and str
-/
def Proof.toCoalgebra (𝕏 : Proof) : CategoryTheory.Endofunctor.Coalgebra T where
  V := 𝕏.X
  str := TypeCat.ofHom 𝕏.α

/-- A proof `𝕏` proves sequent `Δ` if some node of `𝕏` has sequent `Δ` as its sequent. -/
def proves (𝕏 : Proof) (Δ : Sequent) : Prop := ∃ x : 𝕏.X, f (r 𝕏.α x) = Δ
/-- A sequent is provable if there exists a GL-proof of it. -/
def Sequent.isTrue (Δ : Sequent) : Prop := ∃ 𝕏 : Proof, proves 𝕏 Δ

/-- Auxiliary declaration used in the GL coalgebra development. -/
infixr:6 "⊢" => proves
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:40 "⊢" => Sequent.isTrue

lemma not_prove_empty : ¬ ∃ 𝕏, 𝕏 ⊢ {} := by
  by_contra con
  have ⟨𝕏, x, x_em⟩ := con
  cases rule : r 𝕏.α x <;> simp_all [f, r] <;> aesop

/-! # Fischer-Ladner properties of GL-proofs -/

/-- Every edge is contained in FL closure. -/
lemma edge_in_FL {𝕏 : Proof} {x y : 𝕏.X} (x_y : (edge 𝕏.α) x y) :
    f (r 𝕏.α y) ⊆ Sequent.FL (f (r 𝕏.α x)) := by
  unfold edge at x_y
  have := 𝕏.step x
  cases rule : r 𝕏.α x <;> simp only [rule] at this
  · exfalso; simp_all
  · exfalso; simp_all
  case and Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_cons, List.not_mem_nil, or_false] at x_y
    rcases x_y with h|h <;> rw [h] <;>
      simp only [Sequent.FL, Finset.subset_iff,
        Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] <;>
      intro χ χ_cases <;>
      rcases χ_cases with h|_ <;> subst_eqs
    · exact ⟨χ, fₙ_sub_f h, Formula.FL_refl⟩
    · exact ⟨φ & ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, Formula.FL_refl⟩
    · exact ⟨φ & ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
  case or Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Finset.union_insert, Sequent.FL, Finset.subset_iff, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with _|h|_ <;> subst_eqs
    · exact ⟨φ v ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, Formula.FL_refl⟩
    · exact ⟨φ v ψ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩
  case box Δ φ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Sequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with h|_ <;> subst_eqs
    · simp only [Sequent.D, Finset.mem_union, Finset.mem_filter, Finset.mem_filterMap,
        Formula.opUnDi_eq, exists_eq_right] at h
      rcases h with ⟨h,_⟩|h
      · refine ⟨χ, fₙ_sub_f h, by simp [Formula.FL_refl]⟩
      · refine ⟨◇χ, ?_, by simp [Formula.FL, Formula.FL_refl]⟩
        exact fₙ_sub_f h
    · exact ⟨□ φ, by simp [f, in_Δ], by simp [Formula.FL, Formula.FL_refl]⟩

/-- Every path is contained in FL closure. -/
lemma path_in_FL {𝕏 : Proof} {x y : 𝕏.X}
    (x_y : Relation.ReflTransGen (edge 𝕏.α) x y) :
    f (r 𝕏.α y) ⊆ Sequent.FL (f (r 𝕏.α x)) := by
  induction x_y
  case refl => exact Sequent.FL_refl
  case tail y z x_y y_z fy_fx =>
    apply Finset.Subset.trans (edge_in_FL y_z)
    apply Sequent.FL_mon at fy_fx
    simp only [Sequent.FL_idem] at fy_fx
    exact fy_fx


/-! # Point Generated GL-Proofs -/

/-- Structure morphism for Point Generation. -/
@[simp] def αPoint (𝕐 : Proof) (x : 𝕐.X) :
    {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} →
      T.obj {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} :=
  fun y ↦ ⟨(𝕐.α y.1).1,
    List.pmap (fun x y ↦ ⟨x, y⟩) (𝕐.α y.1).2 (fun _ z_in ↦ Relation.ReflTransGen.tail y.2 z_in)⟩

/-- Point Generated Proof. -/
def pointGeneratedProof (𝕐 : Proof) (x : 𝕐.X) : Proof where
  X := {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y }
  α := αPoint 𝕐 x
  step := by
    intro ⟨y, y_in⟩
    have h := 𝕐.step y
    simp_all only [r, αPoint]
    cases r_def : (𝕐.α y).1 <;>
      simp_all only [p, αPoint, List.pmap, List.map_pmap, List.pmap_eq_map]

lemma node_in_pg_sequent_in_FL (𝕏 : Proof) (x : 𝕏.X) :
  ∀ y : (pointGeneratedProof 𝕏 x).X, f (r (αPoint 𝕏 x) y) ⊆ Sequent.FL (f (r 𝕏.α x)) := by
  intro y
  exact path_in_FL y.2

/-! # Filtration of GL-Proofs -/

/-- Equivalence relation used for Filtration. -/
instance fEqEquiRel (𝕏 : Proof) : Setoid 𝕏.X where
  r x y := f (r 𝕏.α x) = f (r 𝕏.α y)
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

/-- Structure morphism for Filtration. -/
@[simp] noncomputable def αQuot 𝕐 (x : Quotient (fEqEquiRel 𝕐)) :=
  let structureMap := 𝕐.α (Quotient.out x)
  (structureMap.1, structureMap.2.map (Quotient.mk (fEqEquiRel 𝕐)))

/-- Filtration of a GL-Proof is a GL-proof. -/
noncomputable def filtration (𝕐 : Proof) : Proof where
  X := Quotient (fEqEquiRel 𝕐)
  α := αQuot 𝕐
  step := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (fEqEquiRel 𝕐) x
      have h := 𝕐.step (@Quotient.out _ (fEqEquiRel 𝕐) ⟦x⟧)
      simp only [r, p, αQuot] at *
      convert h <;>
        simp_all only [List.map_map, List.map_inj_left, Function.comp_apply,
          List.map_eq_nil_iff]
      all_goals
        intro x x_in
        exact hyp x

/-! # Finite Proof Property -/

/-- Given a proof of `Δ` there exists a finite proof of `Δ`. -/
theorem finite_proof_of_proof (𝕏 : Proof) (Δ : Sequent) : (𝕏 ⊢ Δ) → ∃ 𝕐, Finite 𝕐.X ∧ (𝕐 ⊢ Δ) := by
  intro X_proves_Δ
  have ⟨x, f_Δ⟩ := X_proves_Δ
  use pointGeneratedProof (filtration 𝕏) (Quotient.mk (fEqEquiRel 𝕏) x)
  constructor
  · have h : Finite (Sequent.FL Δ).powerset := by
      apply Set.finite_coe_iff.1
      apply Finset.finite_toSet
    apply @Finite.of_injective _ _ h (fun y ↦
      ⟨f (r ((pointGeneratedProof (filtration 𝕏) ⟦x⟧).α) y), by
      simp only [Finset.mem_powerset]
      have in_fl := node_in_pg_sequent_in_FL (filtration 𝕏) ⟦x⟧ y
      have hΔ : Δ = f (r (filtration 𝕏).α ⟦x⟧) := by
        simp only [←f_Δ, filtration, r, αQuot]
        exact Eq.symm <| Quotient.mk_out x
      rw [hΔ]
      exact in_fl⟩)
    intro z1 z2 f_z_eq
    have f_z_eq := by simpa [pointGeneratedProof, filtration, r] using f_z_eq
    apply Subtype.ext
    apply Quotient.out_equiv_out.1
    exact f_z_eq
  · use ⟨Quotient.mk (fEqEquiRel 𝕏) x, Relation.ReflTransGen.refl⟩
    rw [←f_Δ]
    simp only [r, filtration, pointGeneratedProof, αPoint, αQuot]
    exact Quotient.mk_out x

/-! # Properties of (infinite) paths -/

/-- Auxiliary declaration used in the GL coalgebra development. -/
def nbEdge {X : Type} (α : X → T.obj X) (x y : X) := y ∈ p α x ∧ ¬ (r α x).isBox

lemma lt_if_not_box_edge {𝕏 : Proof} {x y : 𝕏.X} :
  (x_y : nbEdge 𝕏.α x y) → Sequent.length (f (r 𝕏.α y)) < Sequent.length (f (r 𝕏.α x)) := by
  intro ⟨x_y, not_box⟩
  have h := 𝕏.step x
  cases r_def : (r 𝕏.α x) <;> simp_all only [RuleApp.isBox, List.not_mem_nil, not_true_eq_false]
  case and Δ A B and_in =>
    have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) x_y
    have this := by simpa [h, -Finset.union_singleton] using this
    rcases this with l | l
    · rw [l, fₙ_alternate, f]
      simp only [Sequent.length]
      exact @Finset.sum_diff_singleton_lt _ _ Δ {A} (A & B) _ and_in (by grind [Formula.length])
    · rw [l, fₙ_alternate, f]
      simp only [Sequent.length]
      exact @Finset.sum_diff_singleton_lt _ _ Δ {B} (A & B) _ and_in (by grind [Formula.length])
  case or Δ A B or_in =>
    have l := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) x_y
    have l := by simpa [h, -Finset.union_insert] using l
    · rw [l, fₙ_alternate, f]
      simp only [Sequent.length]
      exact @Finset.sum_diff_singleton_lt _ _ Δ {A, B} (A v B) _ or_in (by grind [Formula.length])

/-- Every infinite path has an infinite number of nodes which are box rule applications. -/
lemma inf_path_has_inf_boxes {𝕏 : Proof} (g : ℕ → 𝕏.X) (h : ∀ n, edge 𝕏.α (g n) (g (n + 1))) :
  ∀ n, ∃ m, (r 𝕏.α (g (n + m))).isBox := by
    intro n
    by_contra h2
    have h2 := by simpa using h2
    apply (wellFounded_iff_isEmpty_descending_chain.1 (@wellFounded_lt ℕ _ _)).false
    use fun m ↦ Sequent.length (f (r 𝕏.α (g (n + m))))
    exact fun m ↦ lt_if_not_box_edge ⟨h (n + m), by simp_all⟩
end Lean4GlCoalgebras
