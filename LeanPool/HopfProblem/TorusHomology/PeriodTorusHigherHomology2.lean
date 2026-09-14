/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1

/-!
# Hopf problem: torus homology · period torus higher homology 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem PeriodTorusHigherHomology.splitExactPair_injective_mo1973_4431 {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) : Function.Injective (p.prod d) := by
  intro b b' h
  have hp : p b = p b' := congrArg Prod.fst h
  have hd : d b = d b' := congrArg Prod.snd h
  have hb : b - b' ∈ LinearMap.ker d := by
    change d (b - b') = 0
    rw [map_sub, hd, sub_self]
  rw [← hex] at hb
  obtain ⟨a, ha⟩ := hb
  have hpa : p (i a) = a := LinearMap.congr_fun hpi a
  have ha0 : a = 0 := by
    calc
      a = p (i a) := hpa.symm
      _ = p (b - b') := (congrArg p ha)
      _ = 0 := by rw [map_sub, hp, sub_self]
  have hdiff : b - b' = 0 := by rw [← ha, ha0, map_zero]
  exact sub_eq_zero.mp hdiff

private theorem PeriodTorusHigherHomology.splitExactPair_surjective_mo1973_4432 {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) (hsurj : Function.Surjective d) :
    Function.Surjective (p.prod d) := by
  rintro ⟨a, c⟩
  obtain ⟨b, hb⟩ := hsurj c
  refine ⟨b + i (a - p b), ?_⟩
  apply Prod.ext
  · change p (b + i (a - p b)) = a
    have hpa : p (i (a - p b)) = a - p b := LinearMap.congr_fun hpi (a - p b)
    rw [map_add, hpa, ← add_sub_assoc, add_comm (p b) a, add_sub_cancel_right]
  · change d (b + i (a - p b)) = c
    have hi : i (a - p b) ∈ LinearMap.range i := ⟨a - p b, rfl⟩
    rw [hex] at hi
    have hdi : d (i (a - p b)) = 0 := hi
    rw [map_add, hdi, add_zero, hb]

private def
    PeriodTorusHigherHomology.splitExactEquiv {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A)
    (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id) (hex : LinearMap.range i = LinearMap.ker d)
    (hsurj : Function.Surjective d) : B ≃ₗ[ℤ] (A × C) :=
  ({
        Equiv.ofBijective (fun b : B => (p b, d b))
          ⟨splitExactPair_injective_mo1973_4431 i p d hpi hex,
            splitExactPair_surjective_mo1973_4432 i p d hpi hex hsurj⟩ with
        map_add' b b' := Prod.ext (map_add p b b') (map_add d b b') } :
      B ≃+ (A × C)).toIntLinearEquiv

@[simp]
private theorem PeriodTorusHigherHomology.splitExactEquiv_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) (hsurj : Function.Surjective d) (b : B) :
    splitExactEquiv i p d hpi hex hsurj b = (p b, d b) :=
  rfl

private theorem
    PeriodTorusHigherHomology.splitExactEquiv_apply_inclusion {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) (hsurj : Function.Surjective d) (a : A) :
    splitExactEquiv i p d hpi hex hsurj (i a) = (a, 0) := by
  have hpa : p (i a) = a := LinearMap.congr_fun hpi a
  have hi : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hex] at hi
  have hdi : d (i a) = 0 := hi
  rw [splitExactEquiv_apply, hpa, hdi]

private def
    PeriodTorusHigherHomology.intLinearMapOfAddHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {modA : Module ℤ A} {modB : Module ℤ B} (f : A →+ B) : A →ₗ[ℤ] B
    where
  toFun := f
  map_add' := f.map_add
  map_smul' n
    a := by
    change f (modA.smul n a) = modB.smul n (f a)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact f.map_zsmul n a

private def PeriodTorusHigherHomology.pairSumMap (A : Type*) [AddCommGroup A] [Module ℤ A] :
    (A × A) →ₗ[ℤ] A :=
  intLinearMapOfAddHom
    { toFun ac := ac.1 + ac.2
      map_zero' := add_zero 0
      map_add' ac bd := add_add_add_comm ac.1 bd.1 ac.2 bd.2 }

private def PeriodTorusHigherHomology.negativeFirstMap (A : Type*) [AddCommGroup A] [Module ℤ A] :
    (A × A) →ₗ[ℤ] A :=
  intLinearMapOfAddHom
    { toFun ac := -ac.1
      map_zero' := neg_zero
      map_add' ac bd := neg_add ac.1 bd.1 }

@[simp]
private theorem PeriodTorusHigherHomology.pairSumMap_apply (A : Type*) [AddCommGroup A] [Module ℤ A]
    (ac : A × A) : pairSumMap A ac = ac.1 + ac.2 :=
  rfl

private theorem PeriodTorusHigherHomology.circleBoundary_sum_eq_zero {A : Type*} [AddCommGroup A]
    [Module ℤ A] {B : Type*} [AddCommGroup B] [Module ℤ B] (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) (b : B) : (δ b).1 + (δ b).2 = 0 :=
  by
  have hb : δ b ∈ LinearMap.range δ := ⟨b, rfl⟩
  rw [hrange] at hb
  exact hb

private theorem
    PeriodTorusHigherHomology.circleBoundary_negativeFirst_ker {A : Type*} [AddCommGroup A]
    [Module ℤ A] {B : Type*} [AddCommGroup B] [Module ℤ B] (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) :
    LinearMap.ker ((negativeFirstMap A).comp δ) = LinearMap.ker δ := by
  ext b
  change -(δ b).1 = 0 ↔ δ b = 0
  constructor
  · intro hb
    have hfst : (δ b).1 = 0 := neg_eq_zero.mp hb
    have hsnd := circleBoundary_sum_eq_zero δ hrange b
    rw [hfst, zero_add] at hsnd
    exact Prod.ext hfst hsnd
  · intro hb
    rw [hb]
    exact neg_zero

private theorem PeriodTorusHigherHomology.circleBoundary_negativeFirst_surjective {A : Type*}
    [AddCommGroup A] [Module ℤ A] {B : Type*} [AddCommGroup B] [Module ℤ B] (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) :
    Function.Surjective ((negativeFirstMap A).comp δ) := by
  intro a
  have ha : (-a, a) ∈ LinearMap.ker (pairSumMap A) := neg_add_cancel a
  rw [← hrange] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, ?_⟩
  change -(δ b).1 = a
  rw [hb]
  exact neg_neg a

private def
    PeriodTorusHigherHomology.circleSplitExactEquiv {A : Type*} [AddCommGroup A] [Module ℤ A]
    {B P : Type*} [AddCommGroup B] [AddCommGroup P] [Module ℤ B] [Module ℤ P] (i : P →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] P) (δ : B →ₗ[ℤ] (A × A)) (hpi : p.comp i = LinearMap.id)
    (hker : LinearMap.range i = LinearMap.ker δ)
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) : B ≃ₗ[ℤ] (P × A) :=
  splitExactEquiv i p ((negativeFirstMap A).comp δ) hpi
    (hker.trans (circleBoundary_negativeFirst_ker δ hrange).symm)
    (circleBoundary_negativeFirst_surjective δ hrange)

@[simp]
private theorem PeriodTorusHigherHomology.circleSplitExactEquiv_apply_inclusion {A : Type*}
    [AddCommGroup A] [Module ℤ A] {B P : Type*} [AddCommGroup B] [AddCommGroup P] [Module ℤ B]
    [Module ℤ P] (i : P →ₗ[ℤ] B) (p : B →ₗ[ℤ] P) (δ : B →ₗ[ℤ] (A × A))
    (hpi : p.comp i = LinearMap.id) (hker : LinearMap.range i = LinearMap.ker δ)
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) (a : P) :
    circleSplitExactEquiv i p δ hpi hker hrange (i a) = (a, 0) :=
  splitExactEquiv_apply_inclusion i p ((negativeFirstMap A).comp δ) hpi
    (hker.trans (circleBoundary_negativeFirst_ker δ hrange).symm)
    (circleBoundary_negativeFirst_surjective δ hrange) a

private def
    PeriodTorusHigherHomology.sumInlMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    C(X, X ⊕ Y) :=
  ⟨Sum.inl, continuous_inl⟩

private def
    PeriodTorusHigherHomology.sumInrMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    C(Y, X ⊕ Y) :=
  ⟨Sum.inr, continuous_inr⟩

private def
    PeriodTorusHigherHomology.sumElimMap {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Z)) (g : C(Y, Z)) : C(X ⊕ Y, Z) :=
  ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩

private theorem
    PeriodTorusHigherHomology.singularSimplex_sum_split (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex (X ⊕ Y) n) :
    (∃ τ : FirstHurewicz.SingularSimplex X n, σ = (sumInlMap X Y).comp τ) ∨
      (∃ τ : FirstHurewicz.SingularSimplex Y n, σ = (sumInrMap X Y).comp τ) := by
  rcases Sum.isConnected_iff.mp (isConnected_range σ.continuous) with ⟨s, _, hs⟩ | ⟨s, _, hs⟩
  · have hr : Set.range σ ⊆ Set.range (Sum.inl : X → X ⊕ Y) :=
      hs.trans_subset (Set.image_subset_range _ _)
    obtain ⟨g, hg⟩ := Set.range_subset_range_iff_exists_comp.mp hr
    have hc : Continuous g := Topology.IsEmbedding.inl.continuous_iff.mpr (hg ▸ σ.continuous)
    exact Or.inl ⟨⟨g, hc⟩, ContinuousMap.ext (congrFun hg)⟩
  · have hr : Set.range σ ⊆ Set.range (Sum.inr : Y → X ⊕ Y) :=
      hs.trans_subset (Set.image_subset_range _ _)
    obtain ⟨g, hg⟩ := Set.range_subset_range_iff_exists_comp.mp hr
    have hc : Continuous g := Topology.IsEmbedding.inr.continuous_iff.mpr (hg ▸ σ.continuous)
    exact Or.inr ⟨⟨g, hc⟩, ContinuousMap.ext (congrFun hg)⟩

private def
    PeriodTorusHigherHomology.sumSimplexMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) :
    FirstHurewicz.SingularSimplex X n ⊕ FirstHurewicz.SingularSimplex Y n →
      FirstHurewicz.SingularSimplex (X ⊕ Y) n :=
  Sum.elim ((sumInlMap X Y).comp) ((sumInrMap X Y).comp)

private theorem PeriodTorusHigherHomology.sumSimplexMap_injective (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) : Function.Injective (sumSimplexMap X Y n) := by
  classical
  let z : stdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  intro σ τ h
  cases σ with
  | inl σ =>
    cases τ with
    | inl τ =>
      congr 1
      exact ContinuousMap.ext fun t => Sum.inl.inj (congrArg (fun f => f t) h)
    | inr τ => exact False.elim (Sum.inl_ne_inr (congrArg (fun f => f z) h))
  | inr σ =>
    cases τ with
    | inl τ => exact False.elim (Sum.inr_ne_inl (congrArg (fun f => f z) h))
    | inr τ =>
      congr 1
      exact ContinuousMap.ext fun t => Sum.inr.inj (congrArg (fun f => f t) h)

private theorem PeriodTorusHigherHomology.sumSimplexMap_surjective (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) : Function.Surjective (sumSimplexMap X Y n) := by
  intro σ
  rcases singularSimplex_sum_split X Y n σ with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
  · exact ⟨Sum.inl τ, hτ.symm⟩
  · exact ⟨Sum.inr τ, hτ.symm⟩

private def PeriodTorusHigherHomology.sumSimplexEquiv (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    FirstHurewicz.SingularSimplex X n ⊕ FirstHurewicz.SingularSimplex Y n ≃
      FirstHurewicz.SingularSimplex (X ⊕ Y) n :=
  Equiv.ofBijective (sumSimplexMap X Y n)
    ⟨sumSimplexMap_injective X Y n, sumSimplexMap_surjective X Y n⟩

@[simp]
private theorem PeriodTorusHigherHomology.sumSimplexEquiv_symm_inl (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex X n) :
    (sumSimplexEquiv X Y n).symm ((sumInlMap X Y).comp σ) = Sum.inl σ :=
  (sumSimplexEquiv X Y n).symm_apply_apply (Sum.inl σ)

@[simp]
private theorem PeriodTorusHigherHomology.sumSimplexEquiv_symm_inr (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex Y n) :
    (sumSimplexEquiv X Y n).symm ((sumInrMap X Y).comp σ) = Sum.inr σ :=
  (sumSimplexEquiv X Y n).symm_apply_apply (Sum.inr σ)

private def PeriodTorusHigherHomology.sumChainComplexMap (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y ⟶
      FirstHurewicz.singularComplex (X ⊕ Y) :=
  CategoryTheory.Limits.biprod.desc (FirstHurewicz.singularChainMap (sumInlMap X Y))
    (FirstHurewicz.singularChainMap (sumInrMap X Y))

private def PeriodTorusHigherHomology.sumChainInverseDegree_mo1973_4506 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    FirstHurewicz.Chains (X ⊕ Y) n →ₗ[ℤ]
      (FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).X n :=
  FirstHurewicz.chainLift (X ⊕ Y) n fun σ =>
    Sum.elim
      (fun τ =>
        (CategoryTheory.Limits.biprod.inl :
                FirstHurewicz.singularComplex X ⟶
                  FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).f
            n |>.hom
          (FirstHurewicz.simplexChain X n τ))
      (fun τ =>
        (CategoryTheory.Limits.biprod.inr :
                FirstHurewicz.singularComplex Y ⟶
                  FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).f
            n |>.hom
          (FirstHurewicz.simplexChain Y n τ))
      ((sumSimplexEquiv X Y n).symm σ)

private theorem PeriodTorusHigherHomology.sumChainInverseDegree_inl_mo1973_4507 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex X n) :
    sumChainInverseDegree_mo1973_4506 X Y n
        (FirstHurewicz.simplexChain (X ⊕ Y) n ((sumInlMap X Y).comp σ)) =
      ((CategoryTheory.Limits.biprod.inl :
                FirstHurewicz.singularComplex X ⟶
                  FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).f
            n).hom
        (FirstHurewicz.simplexChain X n σ) := by
  simp only [sumChainInverseDegree_mo1973_4506, FirstHurewicz.chainLift_simplex,
    sumSimplexEquiv_symm_inl, Sum.elim_inl]

private theorem PeriodTorusHigherHomology.sumChainInverseDegree_inr_mo1973_4508 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex Y n) :
    sumChainInverseDegree_mo1973_4506 X Y n
        (FirstHurewicz.simplexChain (X ⊕ Y) n ((sumInrMap X Y).comp σ)) =
      ((CategoryTheory.Limits.biprod.inr :
                FirstHurewicz.singularComplex Y ⟶
                  FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).f
            n).hom
        (FirstHurewicz.simplexChain Y n σ) := by
  simp only [sumChainInverseDegree_mo1973_4506, FirstHurewicz.chainLift_simplex,
    sumSimplexEquiv_symm_inr, Sum.elim_inr]

private theorem PeriodTorusHigherHomology.sumChainComplexMap_comp_inverse_mo1973_4509 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    (sumChainComplexMap X Y).f n ≫ ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) =
      𝟙 ((FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).X n) := by
  apply HomologicalComplex.biprodX_ext_from
  · calc
      _ =
          ((CategoryTheory.Limits.biprod.inl :
                    FirstHurewicz.singularComplex X ⟶
                      FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).f
                n ≫
              (sumChainComplexMap X Y).f n) ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          (FirstHurewicz.singularChainMap (sumInlMap X Y)).f n ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (congrArg
          (fun f : FirstHurewicz.Chains X n ⟶ FirstHurewicz.Chains (X ⊕ Y) n =>
            f ≫ ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n))
          (HomologicalComplex.biprod_inl_desc_f (FirstHurewicz.singularChainMap (sumInlMap X Y))
            (FirstHurewicz.singularChainMap (sumInrMap X Y)) n))
      _ = _ := by
        apply ModuleCat.hom_ext
        apply FirstHurewicz.chainMap_ext X n
        intro σ
        change
          sumChainInverseDegree_mo1973_4506 X Y n
              (FirstHurewicz.inducedChain (sumInlMap X Y) n (FirstHurewicz.simplexChain X n σ)) =
            _
        rw [FirstHurewicz.inducedChain_simplex, sumChainInverseDegree_inl_mo1973_4507,
          CategoryTheory.Category.comp_id]
  · calc
      _ =
          ((CategoryTheory.Limits.biprod.inr :
                    FirstHurewicz.singularComplex Y ⟶
                      FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y).f
                n ≫
              (sumChainComplexMap X Y).f n) ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (CategoryTheory.Category.assoc _ _ _).symm
      _ =
          (FirstHurewicz.singularChainMap (sumInrMap X Y)).f n ≫
            ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) :=
        (congrArg
          (fun f : FirstHurewicz.Chains Y n ⟶ FirstHurewicz.Chains (X ⊕ Y) n =>
            f ≫ ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n))
          (HomologicalComplex.biprod_inr_desc_f (FirstHurewicz.singularChainMap (sumInlMap X Y))
            (FirstHurewicz.singularChainMap (sumInrMap X Y)) n))
      _ = _ := by
        apply ModuleCat.hom_ext
        apply FirstHurewicz.chainMap_ext Y n
        intro σ
        change
          sumChainInverseDegree_mo1973_4506 X Y n
              (FirstHurewicz.inducedChain (sumInrMap X Y) n (FirstHurewicz.simplexChain Y n σ)) =
            _
        rw [FirstHurewicz.inducedChain_simplex, sumChainInverseDegree_inr_mo1973_4508,
          CategoryTheory.Category.comp_id]

private theorem PeriodTorusHigherHomology.sumChainInverse_comp_map_mo1973_4510 (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n) ≫ (sumChainComplexMap X Y).f n =
      𝟙 (FirstHurewicz.Chains (X ⊕ Y) n) := by
  apply ModuleCat.hom_ext
  apply FirstHurewicz.chainMap_ext (X ⊕ Y) n
  intro σ
  rcases singularSimplex_sum_split X Y n σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · change
      ((sumChainComplexMap X Y).f n).hom
          (sumChainInverseDegree_mo1973_4506 X Y n
            (FirstHurewicz.simplexChain (X ⊕ Y) n ((sumInlMap X Y).comp τ))) =
        _
    rw [sumChainInverseDegree_inl_mo1973_4507]
    exact
      (congrArg (fun f => f.hom (FirstHurewicz.simplexChain X n τ))
            (HomologicalComplex.biprod_inl_desc_f (FirstHurewicz.singularChainMap (sumInlMap X Y))
              (FirstHurewicz.singularChainMap (sumInrMap X Y)) n)).trans
        (FirstHurewicz.inducedChain_simplex (sumInlMap X Y) n τ)
  · change
      ((sumChainComplexMap X Y).f n).hom
          (sumChainInverseDegree_mo1973_4506 X Y n
            (FirstHurewicz.simplexChain (X ⊕ Y) n ((sumInrMap X Y).comp τ))) =
        _
    rw [sumChainInverseDegree_inr_mo1973_4508]
    exact
      (congrArg (fun f => f.hom (FirstHurewicz.simplexChain Y n τ))
            (HomologicalComplex.biprod_inr_desc_f (FirstHurewicz.singularChainMap (sumInlMap X Y))
              (FirstHurewicz.singularChainMap (sumInrMap X Y)) n)).trans
        (FirstHurewicz.inducedChain_simplex (sumInrMap X Y) n τ)

private theorem PeriodTorusHigherHomology.sumChainComplexMap_component_isIso_mo1973_4511
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    CategoryTheory.IsIso ((sumChainComplexMap X Y).f n) :=
  ⟨⟨ModuleCat.ofHom (sumChainInverseDegree_mo1973_4506 X Y n),
      sumChainComplexMap_comp_inverse_mo1973_4509 X Y n,
      sumChainInverse_comp_map_mo1973_4510 X Y n⟩⟩

private def PeriodTorusHigherHomology.sumChainComplexIso (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    FirstHurewicz.singularComplex X ⊞ FirstHurewicz.singularComplex Y ≅
      FirstHurewicz.singularComplex (X ⊕ Y) := by
  letI (n : ℕ) : CategoryTheory.IsIso ((sumChainComplexMap X Y).f n) :=
    sumChainComplexMap_component_isIso_mo1973_4511 X Y n
  letI : CategoryTheory.IsIso (sumChainComplexMap X Y) :=
    HomologicalComplex.Hom.isIso_of_components (sumChainComplexMap X Y)
  exact CategoryTheory.asIso (sumChainComplexMap X Y)

private def PeriodTorusHigherHomology.sumHomologyEquiv (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.SingularHomology (X ⊕ Y) n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology Y n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (sumChainComplexIso X Y)).symm.toLinearEquiv.trans
    (SingularMayerVietoris.homologyBiprodEquiv (FirstHurewicz.singularComplex X)
      (FirstHurewicz.singularComplex Y) n)

private theorem
    PeriodTorusHigherHomology.sumHomologyEquiv_symm_apply (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology Y n) :
    (sumHomologyEquiv X Y n).symm a =
      SingularMayerVietoris.singularHomologyMap (sumInlMap X Y) n a.1 +
        SingularMayerVietoris.singularHomologyMap (sumInrMap X Y) n a.2 := by
  change
    (HomologicalComplex.homologyMap (sumChainComplexMap X Y) n).hom
        ((SingularMayerVietoris.homologyBiprodEquiv (FirstHurewicz.singularComplex X)
              (FirstHurewicz.singularComplex Y) n).symm
          a) =
      _
  exact
    SingularMayerVietoris.homologyBiprodEquiv_desc n
      (FirstHurewicz.singularChainMap (sumInlMap X Y))
      (FirstHurewicz.singularChainMap (sumInrMap X Y)) a

@[simp]
private theorem PeriodTorusHigherHomology.sumHomologyEquiv_inl (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    sumHomologyEquiv X Y n (SingularMayerVietoris.singularHomologyMap (sumInlMap X Y) n a) =
      (a, 0) := by
  apply (sumHomologyEquiv X Y n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sumHomologyEquiv_symm_apply, map_zero, add_zero]

@[simp]
private theorem PeriodTorusHigherHomology.sumHomologyEquiv_inr (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology Y n) :
    sumHomologyEquiv X Y n (SingularMayerVietoris.singularHomologyMap (sumInrMap X Y) n a) =
      (0, a) := by
  apply (sumHomologyEquiv X Y n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sumHomologyEquiv_symm_apply, map_zero, zero_add]

private theorem PeriodTorusHigherHomology.sumElim_homology_inl_mo1973_4520 {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n
        (SingularMayerVietoris.singularHomologyMap (sumInlMap X Y) n a) =
      SingularMayerVietoris.singularHomologyMap f n a := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (sumInlMap X Y)) (TopCat.ofHom (sumElimMap f g))
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a).symm

private theorem PeriodTorusHigherHomology.sumElim_homology_inr_mo1973_4521 {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n
        (SingularMayerVietoris.singularHomologyMap (sumInrMap X Y) n a) =
      SingularMayerVietoris.singularHomologyMap g n a := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (sumInrMap X Y)) (TopCat.ofHom (sumElimMap f g))
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a).symm

private theorem PeriodTorusHigherHomology.disjointHomology_id_apply_mo1973_4522 {X : Type}
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n a = a := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_id
      (TopCat.of X)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a

private theorem PeriodTorusHigherHomology.sumHomologyEquiv_sumElim_symm {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n
        ((sumHomologyEquiv X Y n).symm a) =
      SingularMayerVietoris.singularHomologyMap f n a.1 +
        SingularMayerVietoris.singularHomologyMap g n a.2 := by
  rw [sumHomologyEquiv_symm_apply, map_add, sumElim_homology_inl_mo1973_4520,
    sumElim_homology_inr_mo1973_4521]

private theorem PeriodTorusHigherHomology.sumHomologyEquiv_sumElim {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Z))
    (g : C(Y, Z)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology (X ⊕ Y) n) :
    SingularMayerVietoris.singularHomologyMap (sumElimMap f g) n a =
      SingularMayerVietoris.singularHomologyMap f n (sumHomologyEquiv X Y n a).1 +
        SingularMayerVietoris.singularHomologyMap g n (sumHomologyEquiv X Y n a).2 := by
  have h := sumHomologyEquiv_sumElim_symm f g n (sumHomologyEquiv X Y n a)
  rwa [LinearEquiv.symm_apply_apply] at h

private theorem
    PeriodTorusHigherHomology.sumHomologyEquiv_fold {X : Type} [TopologicalSpace X] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X ⊕ X) n) :
    SingularMayerVietoris.singularHomologyMap
        (sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)) n a =
      (sumHomologyEquiv X X n a).1 + (sumHomologyEquiv X X n a).2 := by
  rw [sumHomologyEquiv_sumElim, disjointHomology_id_apply_mo1973_4522,
    disjointHomology_id_apply_mo1973_4522]

private theorem
    PeriodTorusHigherHomology.CircleTopology.intervalContractible (a b : ℝ) (hab : a < b) :
    ContractibleSpace (Set.Ioo a b) :=
  (convex_Ioo a b).contractibleSpace ⟨(a + b) / 2, by constructor <;> linarith⟩

private def
    PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInl (t : Set.Ioo (0 : ℝ) (1 / 2)) :
    { s : Set.Ioo (0 : ℝ) 1 // (s : ℝ) ≠ 1 / 2 } :=
  ⟨⟨t, t.property.1, t.property.2.trans (by norm_num)⟩, ne_of_lt t.property.2⟩

private def
    PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInr (t : Set.Ioo (1 / 2 : ℝ) 1) :
    { s : Set.Ioo (0 : ℝ) 1 // (s : ℝ) ≠ 1 / 2 } :=
  ⟨⟨t, (by norm_num : (0 : ℝ) < 1 / 2).trans t.property.1, t.property.2⟩, ne_of_gt t.property.1⟩

private theorem PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInl_continuous :
    Continuous puncturedIntervalInl :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInr_continuous :
    Continuous puncturedIntervalInr :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInl_isOpenMap :
    IsOpenMap puncturedIntervalInl :=
  (isOpen_Ioo.isOpenMap_subtype_val.subtype_mk _).subtype_mk _

private theorem PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInr_isOpenMap :
    IsOpenMap puncturedIntervalInr :=
  (isOpen_Ioo.isOpenMap_subtype_val.subtype_mk _).subtype_mk _

private def PeriodTorusHigherHomology.CircleTopology.puncturedIntervalSumEquiv_mo1973_4536 :
    (Set.Ioo (0 : ℝ) (1 / 2) ⊕ Set.Ioo (1 / 2 : ℝ) 1) ≃
      { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } :=
  Equiv.ofBijective (Sum.elim puncturedIntervalInl puncturedIntervalInr)
    (by
      constructor
      · intro s t h
        have hcoord :=
          congrArg (fun u : { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } => (u.val : ℝ)) h
        rcases s with s | s <;> rcases t with t | t
        · exact congrArg Sum.inl (Subtype.ext hcoord)
        · change (s : ℝ) = (t : ℝ) at hcoord
          linarith [s.property.2, t.property.1]
        · change (s : ℝ) = (t : ℝ) at hcoord
          linarith [s.property.1, t.property.2]
        · exact congrArg Sum.inr (Subtype.ext hcoord)
      · intro t
        rcases lt_or_gt_of_ne t.property with ht | ht
        · exact ⟨Sum.inl ⟨t.val, t.val.property.1, ht⟩, rfl⟩
        · exact ⟨Sum.inr ⟨t.val, ht, t.val.property.2⟩, rfl⟩)

private def PeriodTorusHigherHomology.CircleTopology.puncturedIntervalHomeomorph :
    { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } ≃ₜ
      (Set.Ioo (0 : ℝ) (1 / 2) ⊕ Set.Ioo (1 / 2 : ℝ) 1) :=
  (puncturedIntervalSumEquiv_mo1973_4536.toHomeomorphOfContinuousOpen
      (puncturedIntervalInl_continuous.sumElim puncturedIntervalInr_continuous)
      (puncturedIntervalInl_isOpenMap.sumElim puncturedIntervalInr_isOpenMap)).symm

/-- The additive circle of circumference one. -/
public
abbrev PeriodTorusHigherHomology.CircleTopology.Circle :=
  AddCircle (1 : ℝ)

private def PeriodTorusHigherHomology.CircleTopology.halfPoint :
    PeriodTorusHigherHomology.CircleTopology.Circle :=
  ((1 / 2 : ℝ) : PeriodTorusHigherHomology.CircleTopology.Circle)

private theorem PeriodTorusHigherHomology.CircleTopology.halfPoint_ne_zero : halfPoint ≠ 0 := by
  intro h
  have he :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) (a := (1 / 2 : ℝ)) (by norm_num)).mp h
  norm_num at he

private def PeriodTorusHigherHomology.CircleTopology.arcU :
    Set PeriodTorusHigherHomology.CircleTopology.Circle :=
  ({0} : Set PeriodTorusHigherHomology.CircleTopology.Circle)ᶜ

private def PeriodTorusHigherHomology.CircleTopology.arcV :
    Set PeriodTorusHigherHomology.CircleTopology.Circle :=
  ({ halfPoint } : Set PeriodTorusHigherHomology.CircleTopology.Circle)ᶜ

@[simp]
private theorem PeriodTorusHigherHomology.CircleTopology.mem_arcU
    (x : PeriodTorusHigherHomology.CircleTopology.Circle) : x ∈ arcU ↔ x ≠ 0 :=
  Iff.rfl

@[simp]
private theorem PeriodTorusHigherHomology.CircleTopology.mem_arcV
    (x : PeriodTorusHigherHomology.CircleTopology.Circle) : x ∈ arcV ↔ x ≠ halfPoint :=
  Iff.rfl

private theorem PeriodTorusHigherHomology.CircleTopology.arcU_open : IsOpen arcU :=
  isOpen_compl_singleton

private theorem PeriodTorusHigherHomology.CircleTopology.arcV_open : IsOpen arcV :=
  isOpen_compl_singleton

private theorem PeriodTorusHigherHomology.CircleTopology.arc_cover : arcU ∪ arcV = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_arcU, mem_arcV, Set.mem_univ, iff_true]
  by_cases hx : x = 0
  · right
    rw [hx]
    exact Ne.symm halfPoint_ne_zero
  · exact Or.inl hx

private def PeriodTorusHigherHomology.CircleTopology.puncturedCircleHomeomorph (a : ℝ) :
    ({(a : PeriodTorusHigherHomology.CircleTopology.Circle)}ᶜ :
        Set PeriodTorusHigherHomology.CircleTopology.Circle) ≃ₜ
      Set.Ioo a (a + 1) :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).toHomeomorphSourceTarget.symm

private def PeriodTorusHigherHomology.CircleTopology.arcUHomeomorph : arcU ≃ₜ Set.Ioo (0 : ℝ) 1 :=
  (puncturedCircleHomeomorph 0).trans (Homeomorph.setCongr (by simp))

private def PeriodTorusHigherHomology.CircleTopology.arcVHomeomorph :
    arcV ≃ₜ Set.Ioo (1 / 2 : ℝ) (3 / 2) :=
  (puncturedCircleHomeomorph (1 / 2)).trans (Homeomorph.setCongr (by norm_num))

@[simp]
private theorem PeriodTorusHigherHomology.CircleTopology.arcUHomeomorph_coe (x : arcU) :
    (((arcUHomeomorph x : Set.Ioo (0 : ℝ) 1) : ℝ) :
        PeriodTorusHigherHomology.CircleTopology.Circle) =
      (x : PeriodTorusHigherHomology.CircleTopology.Circle) :=
  congrArg Subtype.val (arcUHomeomorph.symm_apply_apply x)

@[simp]
private theorem PeriodTorusHigherHomology.CircleTopology.arcVHomeomorph_coe (x : arcV) :
    (((arcVHomeomorph x : Set.Ioo (1 / 2 : ℝ) (3 / 2)) : ℝ) :
        PeriodTorusHigherHomology.CircleTopology.Circle) =
      (x : PeriodTorusHigherHomology.CircleTopology.Circle) :=
  congrArg Subtype.val (arcVHomeomorph.symm_apply_apply x)

private instance
    PeriodTorusHigherHomology.CircleTopology.arcUContractible : ContractibleSpace arcU := by
  let : ContractibleSpace (Set.Ioo (0 : ℝ) 1) := intervalContractible 0 1 zero_lt_one
  exact arcUHomeomorph.contractibleSpace

private instance
    PeriodTorusHigherHomology.CircleTopology.arcVContractible : ContractibleSpace arcV := by
  let : ContractibleSpace (Set.Ioo (1 / 2 : ℝ) (3 / 2)) :=
    intervalContractible (1 / 2) (3 / 2) (by norm_num)
  exact arcVHomeomorph.contractibleSpace

private instance PeriodTorusHigherHomology.CircleTopology.leftIntervalContractible :
    ContractibleSpace (Set.Ioo (0 : ℝ) (1 / 2)) :=
  intervalContractible 0 (1 / 2) (by norm_num)

private instance PeriodTorusHigherHomology.CircleTopology.rightIntervalContractible :
    ContractibleSpace (Set.Ioo (1 / 2 : ℝ) 1) :=
  intervalContractible (1 / 2) 1 (by norm_num)

private def PeriodTorusHigherHomology.CircleTopology.intersectionSubtypeHomeomorph {T : Type*}
    [TopologicalSpace T] (U V : Set T) : ↥(U ∩ V) ≃ₜ { x : U // (x : T) ∈ V }
    where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private theorem PeriodTorusHigherHomology.CircleTopology.arcU_mem_arcV_iff (x : arcU) :
    (x : PeriodTorusHigherHomology.CircleTopology.Circle) ∈ arcV ↔
      (arcUHomeomorph x : ℝ) ≠ 1 / 2 := by
  change (x : PeriodTorusHigherHomology.CircleTopology.Circle) ≠ halfPoint ↔ _
  let m : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  have hm :
    (arcUHomeomorph.symm m : PeriodTorusHigherHomology.CircleTopology.Circle) = halfPoint := rfl
  constructor
  · intro hx ht
    have ht' : arcUHomeomorph x = m := Subtype.ext ht
    have hx' : x = arcUHomeomorph.symm m :=
      (arcUHomeomorph.symm_apply_apply x).symm.trans (congrArg arcUHomeomorph.symm ht')
    exact hx ((congrArg Subtype.val hx').trans hm)
  · intro hx ht
    have hx' : x = arcUHomeomorph.symm m := Subtype.ext (ht.trans hm.symm)
    apply hx
    change (arcUHomeomorph x : ℝ) = (m : ℝ)
    rw [hx', Homeomorph.apply_symm_apply]

private def PeriodTorusHigherHomology.CircleTopology.intersectionPuncturedHomeomorph :
    ↥(arcU ∩ arcV) ≃ₜ { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } :=
  (intersectionSubtypeHomeomorph arcU arcV).trans (arcUHomeomorph.subtype arcU_mem_arcV_iff)

private def PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph :
    ↥(arcU ∩ arcV) ≃ₜ (Set.Ioo (0 : ℝ) (1 / 2) ⊕ Set.Ioo (1 / 2 : ℝ) 1) :=
  intersectionPuncturedHomeomorph.trans puncturedIntervalHomeomorph

private def
    PeriodTorusHigherHomology.CircleTopology.contractionPoint (S : Type*) [TopologicalSpace S]
    [ContractibleSpace S] : S :=
  Classical.choose (id_nullhomotopic S)

private theorem PeriodTorusHigherHomology.CircleTopology.contractionPoint_homotopic (S : Type*)
    [TopologicalSpace S] [ContractibleSpace S] :
    (ContinuousMap.const S (contractionPoint S)).Homotopic (ContinuousMap.id S) :=
  (Classical.choose_spec (id_nullhomotopic S)).symm

private def PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv (S X : Type*)
    [TopologicalSpace S] [TopologicalSpace X] [ContractibleSpace S] : (S × X) ≃ₕ X
    where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const X (contractionPoint S)).prodMk (ContinuousMap.id X)
  left_inv := (contractionPoint_homotopic S).prodMap (.refl (ContinuousMap.id X))
  right_inv := .refl (ContinuousMap.id X)

private def PeriodTorusHigherHomology.CircleTopology.sumContinuousMap {A A' B B' : Type*}
    [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']
    (f : C(A, A')) (g : C(B, B')) : C(A ⊕ B, A' ⊕ B') :=
  ⟨Sum.map f g, f.continuous.sumMap g.continuous⟩

private def
    PeriodTorusHigherHomology.CircleTopology.sumHomotopy {A A' B B' : Type*} [TopologicalSpace A]
    [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B'] {f₀ f₁ : C(A, A')}
    {g₀ g₁ : C(B, B')} (F : f₀.Homotopy f₁) (G : g₀.Homotopy g₁) :
    (sumContinuousMap f₀ g₀).Homotopy (sumContinuousMap f₁ g₁)
    where
  toFun := Sum.elim (fun p => Sum.inl (F p)) (fun p => Sum.inr (G p)) ∘ Homeomorph.prodSumDistrib
  continuous_toFun :=
    ((continuous_inl.comp F.continuous).sumElim (continuous_inr.comp G.continuous)).comp
      Homeomorph.prodSumDistrib.continuous
  map_zero_left := by
    intro x
    cases x with
    | inl a => exact congrArg Sum.inl (F.map_zero_left a)
    | inr b => exact congrArg Sum.inr (G.map_zero_left b)
  map_one_left := by
    intro x
    cases x with
    | inl a => exact congrArg Sum.inl (F.map_one_left a)
    | inr b => exact congrArg Sum.inr (G.map_one_left b)

private def PeriodTorusHigherHomology.CircleTopology.sumHomotopyEquiv {A A' B B' : Type*}
    [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']
    (eA : A ≃ₕ A') (eB : B ≃ₕ B') : (A ⊕ B) ≃ₕ (A' ⊕ B')
    where
  toFun := sumContinuousMap eA.toFun eB.toFun
  invFun := sumContinuousMap eA.invFun eB.invFun
  left_inv := by
    rcases eA.left_inv with ⟨F⟩
    rcases eB.left_inv with ⟨G⟩
    refine ⟨(sumHomotopy F G).cast ?_ ?_⟩
    · ext x
      cases x <;> rfl
    · ext x
      cases x <;> rfl
  right_inv := by
    rcases eA.right_inv with ⟨F⟩
    rcases eB.right_inv with ⟨G⟩
    refine ⟨(sumHomotopy F G).cast ?_ ?_⟩
    · ext x
      cases x <;> rfl
    · ext x
      cases x <;> rfl

private def PeriodTorusHigherHomology.CircleTopology.circleLiftContraction {S : Type*}
    [TopologicalSpace S] (f : C(S, AddCircle (1 : ℝ))) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = f s) : f.Homotopy (ContinuousMap.const S 0)
    where
  toFun p := (((1 - (p.1 : ℝ)) * l p.2 : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (l.continuous.comp continuous_snd))
  map_zero_left s := by simpa using hlift s
  map_one_left s := by simp

private def PeriodTorusHigherHomology.CircleTopology.circleProductLiftContraction {S X : Type*}
    [TopologicalSpace S] [TopologicalSpace X] (f : C(S, AddCircle (1 : ℝ) × X)) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = (f s).1) :
    f.Homotopy ⟨fun s => (0, (f s).2), continuous_const.prodMk f.continuous.snd⟩
    where
  toFun p := ((((1 - (p.1 : ℝ)) * l p.2 : ℝ) : AddCircle (1 : ℝ)), (f p.2).2)
  continuous_toFun :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            (l.continuous.comp continuous_snd))).prodMk
      (f.continuous.snd.comp continuous_snd)
  map_zero_left
    s := by
    apply Prod.ext
    · simpa using hlift s
    · rfl
  map_one_left s := by simp

private def PeriodTorusHigherHomology.CircleTopology.productU (X : Type*) :
    Set (PeriodTorusHigherHomology.CircleTopology.Circle × X) :=
  Prod.fst ⁻¹' arcU

private def PeriodTorusHigherHomology.CircleTopology.productV (X : Type*) :
    Set (PeriodTorusHigherHomology.CircleTopology.Circle × X) :=
  Prod.fst ⁻¹' arcV

private theorem
    PeriodTorusHigherHomology.CircleTopology.productU_open (X : Type*) [TopologicalSpace X] :
    IsOpen (productU X) :=
  arcU_open.preimage continuous_fst

private theorem
    PeriodTorusHigherHomology.CircleTopology.productV_open (X : Type*) [TopologicalSpace X] :
    IsOpen (productV X) :=
  arcV_open.preimage continuous_fst

private theorem PeriodTorusHigherHomology.CircleTopology.product_cover (X : Type*) :
    productU X ∪ productV X = Set.univ := by
  change
    Prod.fst ⁻¹' arcU ∪ Prod.fst ⁻¹' arcV =
      (Set.univ : Set (PeriodTorusHigherHomology.CircleTopology.Circle × X))
  rw [← Set.preimage_union, arc_cover, Set.preimage_univ]

private def
    PeriodTorusHigherHomology.CircleTopology.productProjection (X : Type*) [TopologicalSpace X] :
    C(PeriodTorusHigherHomology.CircleTopology.Circle × X, X) :=
  ContinuousMap.snd

private def
    PeriodTorusHigherHomology.CircleTopology.productSection (X : Type*) [TopologicalSpace X] :
    C(X, PeriodTorusHigherHomology.CircleTopology.Circle × X) :=
  (ContinuousMap.const X (0 : PeriodTorusHigherHomology.CircleTopology.Circle)).prodMk
    (ContinuousMap.id X)

@[simp]
private theorem
    PeriodTorusHigherHomology.CircleTopology.productProjection_comp_productSection (X : Type*)
    [TopologicalSpace X] : (productProjection X).comp (productSection X) = ContinuousMap.id X :=
  rfl

private def
    PeriodTorusHigherHomology.CircleTopology.productUInclusion (X : Type*) [TopologicalSpace X] :
    C(productU X, PeriodTorusHigherHomology.CircleTopology.Circle × X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def
    PeriodTorusHigherHomology.CircleTopology.productVInclusion (X : Type*) [TopologicalSpace X] :
    C(productV X, PeriodTorusHigherHomology.CircleTopology.Circle × X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def PeriodTorusHigherHomology.CircleTopology.productIntersectionToU (X : Type*)
    [TopologicalSpace X] : C(↥(productU X ∩ productV X), productU X) :=
  ⟨fun z => ⟨z.val, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

private def PeriodTorusHigherHomology.CircleTopology.productIntersectionToV (X : Type*)
    [TopologicalSpace X] : C(↥(productU X ∩ productV X), productV X) :=
  ⟨fun z => ⟨z.val, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩

private def PeriodTorusHigherHomology.CircleTopology.foldMap (X : Type*) [TopologicalSpace X] :
    C(X ⊕ X, X) :=
  ⟨Sum.elim id id, continuous_id.sumElim continuous_id⟩

private def
    PeriodTorusHigherHomology.CircleTopology.productArcHomeomorph (X : Type*) [TopologicalSpace X]
    (S : Set PeriodTorusHigherHomology.CircleTopology.Circle) :
    ↥(Prod.fst ⁻¹' S : Set (PeriodTorusHigherHomology.CircleTopology.Circle × X)) ≃ₜ S × X
    where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

private def
    PeriodTorusHigherHomology.CircleTopology.productUHomeomorph (X : Type*) [TopologicalSpace X] :
    productU X ≃ₜ arcU × X :=
  productArcHomeomorph X arcU

private def
    PeriodTorusHigherHomology.CircleTopology.productVHomeomorph (X : Type*) [TopologicalSpace X] :
    productV X ≃ₜ arcV × X :=
  productArcHomeomorph X arcV

private def PeriodTorusHigherHomology.CircleTopology.productIntersectionArcHomeomorph (X : Type*)
    [TopologicalSpace X] : ↥(productU X ∩ productV X) ≃ₜ ↥(arcU ∩ arcV) × X :=
  productArcHomeomorph X (arcU ∩ arcV)

private def PeriodTorusHigherHomology.CircleTopology.productIntersectionHomeomorph (X : Type*)
    [TopologicalSpace X] :
    ↥(productU X ∩ productV X) ≃ₜ (Set.Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Set.Ioo (1 / 2 : ℝ) 1 × X) :=
  ((productIntersectionArcHomeomorph X).trans
        (intersectionHomeomorph.prodCongr (Homeomorph.refl X))).trans
    Homeomorph.sumProdDistrib

private def PeriodTorusHigherHomology.CircleTopology.productUHomotopyEquiv (X : Type*)
    [TopologicalSpace X] : productU X ≃ₕ X :=
  (productUHomeomorph X).toHomotopyEquiv.trans (contractibleProdHomotopyEquiv arcU X)

private def PeriodTorusHigherHomology.CircleTopology.productVHomotopyEquiv (X : Type*)
    [TopologicalSpace X] : productV X ≃ₕ X :=
  (productVHomeomorph X).toHomotopyEquiv.trans (contractibleProdHomotopyEquiv arcV X)

private def PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv (X : Type*)
    [TopologicalSpace X] : ↥(productU X ∩ productV X) ≃ₕ X ⊕ X :=
  (productIntersectionHomeomorph X).toHomotopyEquiv.trans
    (sumHomotopyEquiv (contractibleProdHomotopyEquiv (Set.Ioo (0 : ℝ) (1 / 2)) X)
      (contractibleProdHomotopyEquiv (Set.Ioo (1 / 2 : ℝ) 1) X))

@[simp]
private theorem
    PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv_fold (X : Type*)
    [TopologicalSpace X] (z : ↥(productU X ∩ productV X)) :
    foldMap X (productIntersectionHomotopyEquiv X z) = z.val.2 := by
  let c : ↥(arcU ∩ arcV) := ⟨z.val.1, z.property⟩
  change
    Sum.elim id id
        (Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
          (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
          (Homeomorph.sumProdDistrib (intersectionHomeomorph c, z.val.2))) =
      z.val.2
  cases h : intersectionHomeomorph c <;> rfl

private theorem PeriodTorusHigherHomology.CircleTopology.productIntersectionToU_fold (X : Type*)
    [TopologicalSpace X] :
    (productUHomotopyEquiv X).toFun.comp (productIntersectionToU X) =
      (foldMap X).comp (productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  exact (productIntersectionHomotopyEquiv_fold X z).symm

private theorem PeriodTorusHigherHomology.CircleTopology.productIntersectionToV_fold (X : Type*)
    [TopologicalSpace X] :
    (productVHomotopyEquiv X).toFun.comp (productIntersectionToV X) =
      (foldMap X).comp (productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  exact (productIntersectionHomotopyEquiv_fold X z).symm

private def
    PeriodTorusHigherHomology.CircleTopology.productUCoordinate (X : Type*) [TopologicalSpace X] :
    C(productU X, ℝ) :=
  ⟨fun z => (arcUHomeomorph ((productUHomeomorph X z).1) : ℝ),
    continuous_subtype_val.comp
      (arcUHomeomorph.continuous.comp (productUHomeomorph X).continuous.fst)⟩

private def
    PeriodTorusHigherHomology.CircleTopology.productVCoordinate (X : Type*) [TopologicalSpace X] :
    C(productV X, ℝ) :=
  ⟨fun z => (arcVHomeomorph ((productVHomeomorph X z).1) : ℝ),
    continuous_subtype_val.comp
      (arcVHomeomorph.continuous.comp (productVHomeomorph X).continuous.fst)⟩

@[simp]
private theorem PeriodTorusHigherHomology.CircleTopology.productUCoordinate_coe (X : Type*)
    [TopologicalSpace X] (z : productU X) :
    ((productUCoordinate X z : ℝ) : PeriodTorusHigherHomology.CircleTopology.Circle) = z.val.1 :=
  arcUHomeomorph_coe _

@[simp]
private theorem PeriodTorusHigherHomology.CircleTopology.productVCoordinate_coe (X : Type*)
    [TopologicalSpace X] (z : productV X) :
    ((productVCoordinate X z : ℝ) : PeriodTorusHigherHomology.CircleTopology.Circle) = z.val.1 :=
  arcVHomeomorph_coe _

private def PeriodTorusHigherHomology.CircleTopology.productUInclusionHomotopy (X : Type*)
    [TopologicalSpace X] :
    (productUInclusion X).Homotopy ((productSection X).comp (productUHomotopyEquiv X).toFun) :=
  circleProductLiftContraction (productUInclusion X) (productUCoordinate X)
    (productUCoordinate_coe X)

private def PeriodTorusHigherHomology.CircleTopology.productVInclusionHomotopy (X : Type*)
    [TopologicalSpace X] :
    (productVInclusion X).Homotopy ((productSection X).comp (productVHomotopyEquiv X).toFun) :=
  circleProductLiftContraction (productVInclusion X) (productVCoordinate X)
    (productVCoordinate_coe X)

private def
    PeriodTorusHigherHomology.productArcHomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularMayerVietoris.SingularHomology (CircleTopology.productU X) n ×
        SingularMayerVietoris.SingularHomology (CircleTopology.productV X) n) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  ((homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n).toAddEquiv.prodCongr
      (homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X)
          n).toAddEquiv).toIntLinearEquiv

private def
    PeriodTorusHigherHomology.productIntersectionHomologyEquiv (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (homotopyEquivHomologyEquiv (CircleTopology.productIntersectionHomotopyEquiv X) n).trans
    (sumHomologyEquiv X X n)

@[simp]
private theorem PeriodTorusHigherHomology.productIntersectionHomologyEquiv_apply (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    productIntersectionHomologyEquiv X n a =
      sumHomologyEquiv X X n
        (SingularMayerVietoris.singularHomologyMap
          (CircleTopology.productIntersectionHomotopyEquiv X).toFun n a) :=
  rfl

private abbrev
    PeriodTorusHigherHomology.circleSectionHomology (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) n :=
  SingularMayerVietoris.singularHomologyMap (CircleTopology.productSection X) n

private abbrev PeriodTorusHigherHomology.circleProjectionHomology (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)
        n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (CircleTopology.productProjection X) n

@[simp]
private theorem PeriodTorusHigherHomology.circleProjection_section (X : Type) [TopologicalSpace X]
    (n : ℕ) : (circleProjectionHomology X n).comp (circleSectionHomology X n) = LinearMap.id := by
  rw [← singularHomologyMap_comp, CircleTopology.productProjection_comp_productSection,
    singularHomologyMap_id]

private theorem PeriodTorusHigherHomology.productUInclusion_homology (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productUInclusion X) n =
      (circleSectionHomology X n).comp
        (homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n).toLinearMap := by
  rw [homotopy_homologyMap (CircleTopology.productUInclusionHomotopy X) n,
    singularHomologyMap_comp]
  rfl

private theorem PeriodTorusHigherHomology.productVInclusion_homology (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productVInclusion X) n =
      (circleSectionHomology X n).comp
        (homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X) n).toLinearMap := by
  rw [homotopy_homologyMap (CircleTopology.productVInclusionHomotopy X) n,
    singularHomologyMap_comp]
  rfl

private theorem
    PeriodTorusHigherHomology.productFold_homology (X : Type) [TopologicalSpace X] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X ⊕ X) n) :
    SingularMayerVietoris.singularHomologyMap (CircleTopology.foldMap X) n a =
      (sumHomologyEquiv X X n a).1 + (sumHomologyEquiv X X n a).2 :=
  sumHomologyEquiv_fold n a

private theorem
    PeriodTorusHigherHomology.productIntersectionToU_homology (X : Type) [TopologicalSpace X]
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToU X) n
          a) =
      (productIntersectionHomologyEquiv X n a).1 + (productIntersectionHomologyEquiv X n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productUHomotopyEquiv X).toFun n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToU X) n
          a) =
      _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CircleTopology.productIntersectionToU_fold, singularHomologyMap_comp]
  exact productFold_homology X n _

private theorem
    PeriodTorusHigherHomology.productIntersectionToV_homology (X : Type) [TopologicalSpace X]
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X) n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToV X) n
          a) =
      (productIntersectionHomologyEquiv X n a).1 + (productIntersectionHomologyEquiv X n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productVHomotopyEquiv X).toFun n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToV X) n
          a) =
      _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CircleTopology.productIntersectionToV_fold, singularHomologyMap_comp]
  exact productFold_homology X n _

private theorem PeriodTorusHigherHomology.circleProductLeftHomologyMap_apply (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    productArcHomologyEquiv X n
        (SingularMayerVietoris.leftHomologyMap (CircleTopology.productU X)
          (CircleTopology.productV X) n a) =
      ((productIntersectionHomologyEquiv X n a).1 + (productIntersectionHomologyEquiv X n a).2,
        -((productIntersectionHomologyEquiv X n a).1 +
            (productIntersectionHomologyEquiv X n a).2)) := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    (homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n
          (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToU X) n
            a),
        homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X) n
          (-SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToV X) n
              a)) =
      _
  rw [map_neg, productIntersectionToU_homology, productIntersectionToV_homology]

private theorem PeriodTorusHigherHomology.circleProductRightHomologyMap_apply (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (CircleTopology.productU X) n ×
        SingularMayerVietoris.SingularHomology (CircleTopology.productV X) n) :
    SingularMayerVietoris.rightHomologyMap (CircleTopology.productU X) (CircleTopology.productV X)
        n a =
      circleSectionHomology X n
        ((productArcHomologyEquiv X n a).1 + (productArcHomologyEquiv X n a).2) := by
  rw [SingularMayerVietoris.rightHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productUInclusion X) n a.1 +
        SingularMayerVietoris.singularHomologyMap (CircleTopology.productVInclusion X) n a.2 =
      _
  rw [productUInclusion_homology, productVInclusion_homology]
  exact (map_add (circleSectionHomology X n) _ _).symm

private abbrev
    PeriodTorusHigherHomology.circleMayerVietorisConnecting (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)
        (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n :=
  SingularMayerVietoris.connectingHomomorphism (CircleTopology.productU X)
    (CircleTopology.productV X) (CircleTopology.productU_open X) (CircleTopology.productV_open X)
    (CircleTopology.product_cover X) n

private def
    PeriodTorusHigherHomology.circleBoundaryCoordinates (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)
        (n + 1) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (productIntersectionHomologyEquiv X n).toLinearMap.comp (circleMayerVietorisConnecting X n)

private theorem
    PeriodTorusHigherHomology.circleBoundaryCoordinates_range (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    LinearMap.range (circleBoundaryCoordinates X n) =
      LinearMap.ker (pairSumMap (SingularMayerVietoris.SingularHomology X n)) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hb :
      circleMayerVietorisConnecting X n b ∈ LinearMap.range (circleMayerVietorisConnecting X n) :=
      ⟨b, rfl⟩
    rw [SingularMayerVietoris.exact_at_intersection (CircleTopology.productU X)
        (CircleTopology.productV X) (CircleTopology.productU_open X)
        (CircleTopology.productV_open X) (CircleTopology.product_cover X)] at hb
    have he := congrArg (productArcHomologyEquiv X n) hb
    rw [circleProductLeftHomologyMap_apply, map_zero] at he
    exact congrArg Prod.fst he
  · intro ha
    have ha' : a.1 + a.2 = 0 := ha
    have hleft :
      SingularMayerVietoris.leftHomologyMap (CircleTopology.productU X)
          (CircleTopology.productV X) n ((productIntersectionHomologyEquiv X n).symm a) =
        0 := by
      apply (productArcHomologyEquiv X n).injective
      rw [circleProductLeftHomologyMap_apply, LinearEquiv.apply_symm_apply, map_zero]
      exact Prod.ext ha' (ha' ▸ neg_zero)
    have hi :
      (productIntersectionHomologyEquiv X n).symm a ∈
        LinearMap.range (circleMayerVietorisConnecting X n) := by
      rw [SingularMayerVietoris.exact_at_intersection (CircleTopology.productU X)
          (CircleTopology.productV X) (CircleTopology.productU_open X)
          (CircleTopology.productV_open X) (CircleTopology.product_cover X)]
      exact hleft
    obtain ⟨b, hb⟩ := hi
    refine ⟨b, ?_⟩
    change productIntersectionHomologyEquiv X n (circleMayerVietorisConnecting X n b) = a
    rw [hb, LinearEquiv.apply_symm_apply]

private theorem PeriodTorusHigherHomology.circleProductRightHomologyMap_range (X : Type)
    [TopologicalSpace X] (n : ℕ) :
    LinearMap.range
        (SingularMayerVietoris.rightHomologyMap (CircleTopology.productU X)
          (CircleTopology.productV X) n) =
      LinearMap.range (circleSectionHomology X n) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact
      ⟨(productArcHomologyEquiv X n a).1 + (productArcHomologyEquiv X n a).2,
        (circleProductRightHomologyMap_apply X n a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(productArcHomologyEquiv X n).symm (a, 0), ?_⟩
    rw [circleProductRightHomologyMap_apply, LinearEquiv.apply_symm_apply]
    exact congrArg (circleSectionHomology X n) (add_zero a)

private theorem
    PeriodTorusHigherHomology.circleBoundaryCoordinates_ker (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    LinearMap.range (circleSectionHomology X (n + 1)) =
      LinearMap.ker (circleBoundaryCoordinates X n) := by
  rw [circleBoundaryCoordinates, SingularMayerVietoris.rightTransport_second_ker]
  rw [←
    SingularMayerVietoris.exact_at_ambient (CircleTopology.productU X) (CircleTopology.productV X)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X)]
  exact (circleProductRightHomologyMap_range X (n + 1)).symm

private def PeriodTorusHigherHomology.circleBoundary (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)
        (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  (negativeFirstMap (SingularMayerVietoris.SingularHomology X n)).comp
    (circleBoundaryCoordinates X n)

@[simp]
private theorem
    PeriodTorusHigherHomology.circleBoundary_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundary X n a = -(circleBoundaryCoordinates X n a).1 :=
  rfl

private theorem PeriodTorusHigherHomology.circleBoundary_surjective (X : Type) [TopologicalSpace X]
    (n : ℕ) : Function.Surjective (circleBoundary X n) :=
  circleBoundary_negativeFirst_surjective (circleBoundaryCoordinates X n)
    (circleBoundaryCoordinates_range X n)

private theorem
    PeriodTorusHigherHomology.circleBoundary_exact (X : Type) [TopologicalSpace X] (n : ℕ) :
    LinearMap.range (circleSectionHomology X (n + 1)) = LinearMap.ker (circleBoundary X n) :=
  (circleBoundaryCoordinates_ker X n).trans
    (circleBoundary_negativeFirst_ker (circleBoundaryCoordinates X n)
        (circleBoundaryCoordinates_range X n)).symm

private def
    PeriodTorusHigherHomology.circleProductHomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)
        (n + 1) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :=
  circleSplitExactEquiv (circleSectionHomology X (n + 1)) (circleProjectionHomology X (n + 1))
    (circleBoundaryCoordinates X n) (circleProjection_section X (n + 1))
    (circleBoundaryCoordinates_ker X n) (circleBoundaryCoordinates_range X n)

@[simp]
private theorem
    PeriodTorusHigherHomology.circleProductHomologyEquiv_apply (X : Type) [TopologicalSpace X]
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleProductHomologyEquiv X n a =
      (circleProjectionHomology X (n + 1) a, circleBoundary X n a) :=
  rfl

private theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_section (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    circleProductHomologyEquiv X n (circleSectionHomology X (n + 1) a) = (a, 0) :=
  circleSplitExactEquiv_apply_inclusion _ _ _ _ _ _ a

private theorem PeriodTorusHigherHomology.circleSectionHomology_zero_surjective (X : Type)
    [TopologicalSpace X] : Function.Surjective (circleSectionHomology X 0) := by
  intro b
  obtain ⟨a, ha⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective (CircleTopology.productU X)
      (CircleTopology.productV X) (CircleTopology.productU_open X)
      (CircleTopology.productV_open X) (CircleTopology.product_cover X) b
  exact
    ⟨(productArcHomologyEquiv X 0 a).1 + (productArcHomologyEquiv X 0 a).2,
      (circleProductRightHomologyMap_apply X 0 a).symm.trans ha⟩

private def
    PeriodTorusHigherHomology.circleProductHomologyZeroEquiv (X : Type) [TopologicalSpace X] :
    SingularMayerVietoris.SingularHomology ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)
        0 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X 0
    where
  toLinearMap := circleProjectionHomology X 0
  invFun := circleSectionHomology X 0
  left_inv
    b := by
    obtain ⟨a, rfl⟩ := circleSectionHomology_zero_surjective X b
    exact
      congrArg (circleSectionHomology X 0) (LinearMap.congr_fun (circleProjection_section X 0) a)
  right_inv a := LinearMap.congr_fun (circleProjection_section X 0) a

end Mathoverflow1973

end
