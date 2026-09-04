/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
public import LeanPool.HopfProblem.Threefold.SpecialPeriods5
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.PeriodFamily.PeriodDomain
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.Threefold.SpecialPeriods5

/-!
# Hopf problem: torus homology · period torus higher homology 7

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

private def
    PeriodTorusHigherHomology.torusMatrixLinearMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ProductTorus n →ₗ[ℤ] ProductTorus m
    where
  toFun x i := ∑ j, A i j • x j
  map_add' x
    y := by
    ext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r
    x := by
    ext i
    change (∑ j, A i j • (r • x j)) = r • ∑ j, A i j • x j
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact SMulCommClass.smul_comm (A i j) r (x j)

private theorem PeriodTorusHigherHomology.torusMatrixLinearMap_continuous {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) : Continuous (torusMatrixLinearMap A) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : ProductTorus n => ∑ j, A i j • x j)
  exact continuous_finsetSum Finset.univ (fun j _ => (continuous_apply j).zsmul (A i j))

private def PeriodTorusHigherHomology.torusMatrixMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    C(ProductTorus n, ProductTorus m) :=
  ⟨torusMatrixLinearMap A, torusMatrixLinearMap_continuous A⟩

@[simp]
private theorem
    PeriodTorusHigherHomology.torusMatrixMap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x : ProductTorus n) (i : Fin m) : torusMatrixMap A x i = ∑ j, A i j • x j :=
  rfl

private theorem PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℝ) :
    torusMatrixMap A (coordinateProjection n x) =
      coordinateProjection m (A.map (Int.castRingHom ℝ) *ᵥ x) := by
  ext i
  change
    (∑ j, A i j • (x j : AddCircle (1 : ℝ))) = ((∑ j, (A i j : ℝ) * x j : ℝ) : AddCircle (1 : ℝ))
  have h :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (fun j : Fin n => A i j • x j)
      Finset.univ
  calc
    _ = ((∑ j, A i j • x j : ℝ) : AddCircle (1 : ℝ)) := h.symm
    _ = _ := congrArg (fun y : ℝ => (y : AddCircle (1 : ℝ))) (by simp only [zsmul_eq_mul])

@[simp]
private theorem PeriodTorusHigherHomology.torusMatrixMap_one (n : ℕ) :
    torusMatrixMap (1 : Matrix (Fin n) (Fin n) ℤ) = ContinuousMap.id (ProductTorus n) := by
  apply ContinuousMap.ext
  intro x
  ext i
  simp [torusMatrixMap_apply, Matrix.one_apply]

private theorem
    PeriodTorusHigherHomology.torusMatrixMap_mul {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin r) ℤ) :
    torusMatrixMap (A * B) = (torusMatrixMap A).comp (torusMatrixMap B) := by
  apply ContinuousMap.ext
  intro x
  ext i
  change (∑ j, (A * B) i j • x j) = ∑ k, A i k • ∑ j, B k j • x j
  simp only [Matrix.mul_apply, Finset.sum_smul, SemigroupAction.mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

private def PeriodTorusHigherHomologyPontryagin.cyclicMap (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] : C(Y × (Z × X), X × (Y × Z)) :=
  ⟨fun p => (p.2.2, (p.1, p.2.1)), by fun_prop⟩

private def PeriodTorusHigherHomologyPontryagin.additionMap (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] : C(G × G, G) :=
  ⟨fun p => p.1 + p.2, continuous_fst.add continuous_snd⟩

private def PeriodTorusHigherHomologyPontryagin.rightAdditionMap (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] : C(G × (G × G), G) :=
  (additionMap G).comp ((ContinuousMap.id G).prodMap (additionMap G))

@[simp]
private theorem PeriodTorusHigherHomologyPontryagin.rightAdditionMap_comp_cyclic (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] :
    (rightAdditionMap G).comp (cyclicMap G G G) = rightAdditionMap G := by
  ext p
  change p.2.2 + (p.1 + p.2.1) = p.1 + (p.2.1 + p.2.2)
  abel

private theorem PeriodTorusHigherHomologyPontryagin.rightAddition_homology_cyclic (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) n).comp
        (SingularMayerVietoris.singularHomologyMap (cyclicMap G G G) n) =
      SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) n := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, rightAdditionMap_comp_cyclic]

private theorem
    PeriodTorusHigherHomologyPontryagin.additionMap_natural {G : Type} [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] {H : Type} [TopologicalSpace H] [AddCommGroup H]
    [IsTopologicalAddGroup H] (f : C(G, H)) (hf : ∀ x y, f (x + y) = f x + f y) :
    f.comp (additionMap G) = (additionMap H).comp (f.prodMap f) := by
  ext p
  exact hf p.1 p.2

private theorem PeriodTorusHigherHomologyPontryagin.addition_homology_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap f n).comp
        (SingularMayerVietoris.singularHomologyMap (additionMap G) n) =
      (SingularMayerVietoris.singularHomologyMap (additionMap H) n).comp
        (SingularMayerVietoris.singularHomologyMap (f.prodMap f) n) := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, additionMap_natural f hf,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomologyPontryagin.product (G : Type) [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (n : ℕ) :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G n →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G (n + 1) :=
  PeriodTorusHigherHomology.integerBilinearPostcompose
    (PeriodTorusHigherHomology.crossProductHomology G G n)
    (SingularMayerVietoris.singularHomologyMap (additionMap G) (n + 1))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomologyPontryagin.product_apply (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology G 1)
    (b : SingularMayerVietoris.SingularHomology G n) :
    product G n a b =
      SingularMayerVietoris.singularHomologyMap (additionMap G) (n + 1)
        (PeriodTorusHigherHomology.crossProductHomology G G n a b) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private abbrev PeriodTorusHigherHomologyPontryagin.product11 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 2 :=
  product G 1

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private abbrev PeriodTorusHigherHomologyPontryagin.product12 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 2 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 3 :=
  product G 2

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomologyPontryagin.tripleProduct (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
          SingularMayerVietoris.SingularHomology G 3
    where
  toFun a := PeriodTorusHigherHomology.integerBilinearPostcompose (product11 G) (product12 G a)
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.SingularHomology G 2 →ₗ[ℤ]
              SingularMayerVietoris.SingularHomology G 3 =>
          f (product11 G c d))
        ((product12 G).map_add a b)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.SingularHomology G 2 →ₗ[ℤ]
              SingularMayerVietoris.SingularHomology G 3 =>
          f (product11 G c d))
        ((product12 G).map_smul r a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomologyPontryagin.tripleProduct_apply (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c = product12 G a (product11 G b c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomologyPontryagin.product_natural {G H : Type} [TopologicalSpace G]
    [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H] [IsTopologicalAddGroup G]
    [IsTopologicalAddGroup H] (f : C(G, H)) (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology G 1)
    (b : SingularMayerVietoris.SingularHomology G n) :
    SingularMayerVietoris.singularHomologyMap f (n + 1) (product G n a b) =
      product H n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f n b) :=
  (LinearMap.congr_fun (addition_homology_natural f hf (n + 1))
        (PeriodTorusHigherHomology.crossProductHomology G G n a b)).trans
    (congrArg (SingularMayerVietoris.singularHomologyMap (additionMap H) (n + 1))
      (PeriodTorusHigherHomology.crossProductHomology_natural f f n a b))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_natural {G H : Type}
    [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (a b c : SingularMayerVietoris.SingularHomology G 1) :
    SingularMayerVietoris.singularHomologyMap f 3 (tripleProduct G a b c) =
      tripleProduct H (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f 1 b)
        (SingularMayerVietoris.singularHomologyMap f 1 c) := by
  change
    SingularMayerVietoris.singularHomologyMap f 3 (product G 2 a (product G 1 b c)) =
      product H 2 (SingularMayerVietoris.singularHomologyMap f 1 a)
        (product H 1 (SingularMayerVietoris.singularHomologyMap f 1 b)
          (SingularMayerVietoris.singularHomologyMap f 1 c))
  rw [product_natural f hf 2, product_natural f hf 1]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomologyPontryagin.tripleProduct_eq_cross (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c =
      SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) 3
        (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
          (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)) := by
  have h :=
    PeriodTorusHigherHomology.crossProductHomology_natural (ContinuousMap.id G) (additionMap G) 2
      a (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)
  change
    SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id G).prodMap (additionMap G)) 3
        (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
          (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)) =
      PeriodTorusHigherHomology.crossProductHomology G G 2
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id G) 1 a)
        (SingularMayerVietoris.singularHomologyMap (additionMap G) 2
          (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)) at h
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h
  calc
    tripleProduct G a b c =
        SingularMayerVietoris.singularHomologyMap (additionMap G) 3
          (PeriodTorusHigherHomology.crossProductHomology G G 2 a
            (SingularMayerVietoris.singularHomologyMap (additionMap G) 2
              (PeriodTorusHigherHomology.crossProductHomology G G 1 b c))) :=
      rfl
    _ =
        SingularMayerVietoris.singularHomologyMap (additionMap G) 3
          (SingularMayerVietoris.singularHomologyMap
            ((ContinuousMap.id G).prodMap (additionMap G)) 3
            (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
              (PeriodTorusHigherHomology.crossProductHomology G G 1 b c))) :=
      (congrArg (SingularMayerVietoris.singularHomologyMap (additionMap G) 3) h.symm)
    _ = _ :=
      (LinearMap.congr_fun
          (PeriodTorusHigherHomology.singularHomologyMap_comp
            ((ContinuousMap.id G).prodMap (additionMap G)) (additionMap G) 3)
          (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
            (PeriodTorusHigherHomology.crossProductHomology G G 1 b c))).symm

private def PeriodTorusHigherHomology.binomialCoordinateBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (binomialModule r n) :=
  Pi.basisFun ℤ (Fin (r.choose n))

@[simp]
private theorem
    PeriodTorusHigherHomology.binomialCoordinateBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    binomialCoordinateBasis r n i = Pi.single i 1 :=
  Pi.basisFun_apply ℤ (Fin (r.choose n)) i

@[simp]
private theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_single_inl (r n : ℕ)
    (i : Fin (r.choose (n + 1))) :
    binomialModuleSuccEquiv r n (Pi.single ((binomialPascalIndexEquiv r n).symm (Sum.inl i)) 1) =
      (Pi.single i 1, 0) := by
  apply Prod.ext
  · funext j
    simp only [binomialModuleSuccEquiv_apply_fst, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq]
  · funext j
    simp only [binomialModuleSuccEquiv_apply_snd, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inr_ne_inl, ite_false, Pi.zero_apply]

@[simp]
private theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_single_inr (r n : ℕ)
    (i : Fin (r.choose n)) :
    binomialModuleSuccEquiv r n (Pi.single ((binomialPascalIndexEquiv r n).symm (Sum.inr i)) 1) =
      (0, Pi.single i 1) := by
  apply Prod.ext
  · funext j
    simp only [binomialModuleSuccEquiv_apply_fst, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inl_ne_inr, ite_false, Pi.zero_apply]
  · funext j
    simp only [binomialModuleSuccEquiv_apply_snd, Pi.single_apply, Equiv.apply_eq_iff_eq,
      Sum.inr.injEq]

private theorem PeriodTorusHigherHomology.integerBinomialZeroEquiv_one_single (r : ℕ)
    (i : Fin (r.choose 0)) : integerBinomialZeroEquiv r 1 = Pi.single i 1 := by
  have hsingle : Subsingleton (Fin (r.choose 0)) := by
    rw [Nat.choose_zero_right]
    infer_instance
  funext j
  have hij : i = j := hsingle.elim i j
  subst j
  simp [integerBinomialZeroEquiv]

private theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_top (n : ℕ) :
    binomialModuleSuccEquiv n n (fun _ => 1) = (0, fun _ => 1) := by
  apply Prod.ext
  · exact binomialModule_eq_zero_of_lt (Nat.lt_succ_self n) _
  · rfl

private def PeriodTorusHigherHomology.productTorusTopClass (n : ℕ) :
    SingularMayerVietoris.SingularHomology (ProductTorus n) n :=
  (productTorusHomologyEquiv n n).symm (fun _ => (1 : ℤ))

@[simp]
private theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_topClass (n : ℕ) :
    productTorusHomologyEquiv n n (productTorusTopClass n) = fun _ => (1 : ℤ) :=
  (productTorusHomologyEquiv n n).apply_symm_apply _

@[simp]
private theorem PeriodTorusHigherHomology.productTorusTopClass_zero :
    productTorusTopClass 0 = pointClass (0 : ProductTorus 0) := by
  apply (productTorusHomologyEquiv 0 0).injective
  rw [productTorusHomologyEquiv_topClass, productTorusHomologyEquiv_zero]
  simp only [LinearEquiv.trans_apply, connectedHomologyZeroEquiv_pointClass]
  rfl

private theorem PeriodTorusHigherHomology.productTorusTopClass_succ_coordinates (n : ℕ) :
    circleProductHomologyEquiv (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) =
      (0, productTorusTopClass n) := by
  apply Prod.ext
  · exact
      @Subsingleton.elim (SingularMayerVietoris.SingularHomology (ProductTorus n) (n + 1))
        (productTorus_homology_subsingleton_of_lt (Nat.lt_succ_self n)) _ _
  · apply (productTorusHomologyEquiv n n).injective
    have h :=
      congrArg Prod.snd (productTorusHomologyEquiv_succ_apply n n (productTorusTopClass (n + 1)))
    rw [productTorusHomologyEquiv_topClass, binomialModuleSuccEquiv_top] at h
    exact h.symm.trans (productTorusHomologyEquiv_topClass n).symm

private theorem PeriodTorusHigherHomology.productTorusTopClass_succ_boundary (n : ℕ) :
    circleBoundary (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) =
      productTorusTopClass n :=
  congrArg Prod.snd (productTorusTopClass_succ_coordinates n)

@[simp]
private theorem PeriodTorusHigherHomology.flatTorusCircleHomeomorph_add (x y : RealTorus₄) :
    flatTorusCircleHomeomorph (x + y) =
      flatTorusCircleHomeomorph x + flatTorusCircleHomeomorph y :=
  flatTorusCircleMap.map_add x y

private theorem
    PeriodTorusHigherHomology.periodTorusCircle_inducedHomology_periodLoop (p : PeriodDomain)
    (v : Lattice) :
    FirstHurewicz.inducedHomology (periodTorusCircleHomeomorph p : C(_, _))
        (FirstHurewicz.loopHomologyClass (p.periodLoop v)) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 v) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, periodTorusCircleHomeomorph_periodLoop]
  rfl

private def PeriodTorusHigherHomology.coordinateCircleMap {n : ℕ} (v : Fin n → ℤ) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle), ProductTorus n)
    where
  toFun z i := v i • z
  continuous_toFun := continuous_pi fun i => continuous_id.zsmul (v i)

@[simp]
private theorem PeriodTorusHigherHomology.coordinateCircleMap_apply {n : ℕ} (v : Fin n → ℤ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) (i : Fin n) :
    coordinateCircleMap v z i = v i • z :=
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.coordinateCircleMap_zero {n : ℕ} (v : Fin n → ℤ) :
    coordinateCircleMap v 0 = 0 := by
  ext i
  exact smul_zero (v i)

private theorem PeriodTorusHigherHomology.coordinateCircleMap_add {n : ℕ} (v : Fin n → ℤ)
    (x y : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    coordinateCircleMap v (x + y) = coordinateCircleMap v x + coordinateCircleMap v y := by
  ext i
  exact smul_add (v i) x y

private theorem
    PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop_apply {n : ℕ} (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinateCircleMap v (CirclePaths.positiveLoop t) = coordinatePeriodLoop n v t := by
  ext i
  rw [coordinateCircleMap_apply, CirclePaths.positiveLoop_apply, coordinatePeriodLoop_apply]
  change
    ((v i • (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      (((t : ℝ) * (v i : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

private theorem PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop {n : ℕ} (v : Fin n → ℤ) :
    CirclePaths.positiveLoop.map (coordinateCircleMap v).continuous =
      (coordinatePeriodLoop n v).cast (coordinateCircleMap_zero v) (coordinateCircleMap_zero v) :=
  by
  apply Path.ext
  funext t
  exact coordinateCircleMap_positiveLoop_apply v t

private theorem
    PeriodTorusHigherHomology.coordinateCircleMap_positiveHomology {n : ℕ} (v : Fin n → ℤ) :
    FirstHurewicz.inducedHomology (coordinateCircleMap v)
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n v) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, coordinateCircleMap_positiveLoop]
  rfl

private theorem PeriodTorusHigherHomology.coordinatePeriodLoop_eq_projection (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinatePeriodLoop n v t = coordinateProjection n ((t : ℝ) • (fun i => (v i : ℝ))) := by
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

private theorem PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) (t : unitInterval) :
    torusMatrixMap A (coordinatePeriodLoop n v t) = coordinatePeriodLoop m (A *ᵥ v) t := by
  rw [coordinatePeriodLoop_eq_projection, torusMatrixMap_coordinateProjection,
    coordinatePeriodLoop_eq_projection, Matrix.mulVec_smul]
  congr 2
  ext i
  exact ((Int.castRingHom ℝ).map_mulVec A v i).symm

@[simp]
private theorem
    PeriodTorusHigherHomology.torusMatrixMap_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    torusMatrixMap A 0 = 0 :=
  (torusMatrixLinearMap A).map_zero

private theorem PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (torusMatrixMap A).continuous =
      (coordinatePeriodLoop m (A *ᵥ v)).cast (torusMatrixMap_zero A) (torusMatrixMap_zero A) := by
  apply Path.ext
  funext t
  exact torusMatrixMap_coordinatePeriodLoop_apply A v t

private theorem PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    FirstHurewicz.inducedHomology (torusMatrixMap A)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n v)) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop m (A *ᵥ v)) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, torusMatrixMap_coordinatePeriodLoop]
  rfl

private def PeriodTorusHigherHomology.torusHeadCircleMap (n : ℕ) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle), ProductTorus (n + 1)) :=
  coordinateCircleMap (Pi.single (0 : Fin (n + 1)) 1)

@[simp]
private theorem PeriodTorusHigherHomology.torusHeadCircleMap_apply (n : ℕ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    torusHeadCircleMap n z = Fin.cons z 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]

private def
    PeriodTorusHigherHomology.torusTailMap (n : ℕ) : C(ProductTorus n, ProductTorus (n + 1)) :=
  ((productTorusSuccHomeomorph n).symm : C(_, _)).comp
    (CircleTopology.productSection (ProductTorus n))

@[simp]
private theorem PeriodTorusHigherHomology.torusTailMap_apply (n : ℕ) (x : ProductTorus n) :
    torusTailMap n x = Fin.cons 0 x :=
  rfl

private theorem PeriodTorusHigherHomology.torusTailMap_add (n : ℕ) (x y : ProductTorus n) :
    torusTailMap n (x + y) = torusTailMap n x + torusTailMap n y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

private theorem PeriodTorusHigherHomology.torusTailMap_zero (n : ℕ) : torusTailMap n 0 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

private theorem
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (torusTailMap n).continuous =
      (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)).cast (torusTailMap_zero n)
        (torusTailMap_zero n) := by
  apply Path.ext
  funext t
  apply funext
  intro i
  change
    torusTailMap n (coordinatePeriodLoop n v t) i =
      coordinatePeriodLoop (n + 1) (Fin.cons 0 v) t i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]

private theorem
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology (n : ℕ) (v : Fin n → ℤ) :
    SingularMayerVietoris.singularHomologyMap (torusTailMap n) 1
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n v)) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)) := by
  rw [SingularMayerVietoris.singularHomologyMap_one,
    FirstHurewicz.inducedHomology_loopHomologyClass, torusTailMap_coordinatePeriodLoop]
  rfl

private theorem PeriodTorusHigherHomology.productTorusSucc_inverse_eq_add (n : ℕ) :
    ((productTorusSuccHomeomorph n).symm :
        C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus n,
          ProductTorus (n + 1))) =
      (PeriodTorusHigherHomologyPontryagin.additionMap (ProductTorus (n + 1))).comp
        ((torusHeadCircleMap n).prodMap (torusTailMap n)) := by
  apply ContinuousMap.ext
  rintro ⟨z, x⟩
  change Fin.cons z x = torusHeadCircleMap n z + torusTailMap n x
  rw [torusHeadCircleMap_apply, torusTailMap_apply]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem PeriodTorusHigherHomology.torusSplit_positiveCircleCross (r n : ℕ)
    (b : SingularMayerVietoris.SingularHomology (ProductTorus r) n) :
    SingularMayerVietoris.singularHomologyMap ((productTorusSuccHomeomorph r).symm : C(_, _))
        (n + 1) (positiveCircleCross (ProductTorus r) n b) =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus (r + 1)) n
        (SingularMayerVietoris.singularHomologyMap (torusHeadCircleMap r) 1
          (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop))
        (SingularMayerVietoris.singularHomologyMap (torusTailMap r) n b) := by
  rw [PeriodTorusHigherHomologyPontryagin.product_apply]
  have h :=
    crossProductHomology_natural (torusHeadCircleMap r) (torusTailMap r) n
      (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) b
  rw [← h]
  rw [productTorusSucc_inverse_eq_add, singularHomologyMap_comp]
  rfl

private theorem PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (torusHeadCircleMap n) 1
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop (n + 1) (Pi.single 0 1)) :=
  coordinateCircleMap_positiveHomology (Pi.single (0 : Fin (n + 1)) 1)

private theorem PeriodTorusHigherHomology.productTorusTopClass_succ_cross (n : ℕ) :
    productTorusTopClass (n + 1) =
      SingularMayerVietoris.singularHomologyMap ((productTorusSuccHomeomorph n).symm : C(_, _))
        (n + 1) (positiveCircleCross (ProductTorus n) n (productTorusTopClass n)) := by
  apply (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).injective
  apply (circleProductHomologyEquiv (ProductTorus n) n).injective
  rw [productTorusTopClass_succ_coordinates]
  change
    (0, productTorusTopClass n) =
      circleProductHomologyEquiv (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          ((homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).symm
            (positiveCircleCross (ProductTorus n) n (productTorusTopClass n))))
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_positiveCircleCross]

private theorem PeriodTorusHigherHomology.productTorusTopClass_succ_product (n : ℕ) :
    productTorusTopClass (n + 1) =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus (n + 1)) n
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop (n + 1) (Pi.single 0 1)))
        (SingularMayerVietoris.singularHomologyMap (torusTailMap n) n (productTorusTopClass n)) :=
  by
  rw [productTorusTopClass_succ_cross, torusSplit_positiveCircleCross,
    torusHeadCircleMap_positiveHomology]

private theorem PeriodTorusHigherHomology.productTorusTopClass_one :
    productTorusTopClass 1 =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 1 (Pi.single 0 1)) := by
  rw [productTorusTopClass_succ_cross, productTorusTopClass_zero, positiveCircleCross,
    crossProductHomology_pointClass_right]
  have hmap :
    ((productTorusSuccHomeomorph 0).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus 0,
              ProductTorus 1)).comp
        (crossInsertRight (0 : ProductTorus 0)) =
      torusHeadCircleMap 0 := by
    apply ContinuousMap.ext
    intro z
    rw [torusHeadCircleMap_apply]
    rfl
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hmap]
  exact torusHeadCircleMap_positiveHomology 0

private theorem PeriodTorusHigherHomology.productTorusTopClass_two :
    productTorusTopClass 2 =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus 2) 1
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1))) := by
  rw [productTorusTopClass_succ_product, productTorusTopClass_one,
    torusTailMap_coordinatePeriodHomology]
  congr 3
  decide

private theorem PeriodTorusHigherHomology.productTorusTopClass_three :
    productTorusTopClass 3 =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 3)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 1 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 2 1))) := by
  rw [productTorusTopClass_succ_product, productTorusTopClass_two,
    PeriodTorusHigherHomologyPontryagin.product_natural (torusTailMap 2) (torusTailMap_add 2),
    torusTailMap_coordinatePeriodHomology, torusTailMap_coordinatePeriodHomology]
  have h₁ : Fin.cons 0 (Pi.single 0 1 : Fin 2 → ℤ) = (Pi.single 1 1 : Fin 3 → ℤ) := by decide
  have h₂ : Fin.cons 0 (Pi.single 1 1 : Fin 2 → ℤ) = (Pi.single 2 1 : Fin 3 → ℤ) := by decide
  rw [h₁, h₂]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule in
private def PeriodTorusHigherHomologyPontryagin.multilinearOfBilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (β : M →ₗ[ℤ] M →ₗ[ℤ] N) :
    MultilinearMap ℤ (fun _ : Fin 2 => M) N
    where
  toFun v := β (v 0) (v 1)
  map_update_add' {hDecEq} v i x
    y := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp
  map_update_smul' {hDecEq} v i r
    x := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule in
private def PeriodTorusHigherHomologyPontryagin.alternatingOfBilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hdiag : ∀ x : M, β x x = 0) : AlternatingMap ℤ M N (Fin 2)
    where
  toMultilinearMap := multilinearOfBilinear β
  map_eq_zero_of_eq' v i j hij
    hne := by
    have h : v 0 = v 1 := by fin_cases i <;> fin_cases j <;> simp_all
    change β (v 0) (v 1) = 0
    rw [h]
    exact hdiag _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule in
private theorem PeriodTorusHigherHomologyPontryagin.skewBilinear_diagonal_zero {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] [Module.IsTorsionFree ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hskew : ∀ x y : M, β x y = -β y x) (x : M) : β x x = 0 := by
  apply (smul_eq_zero_iff_right (show (2 : ℤ) ≠ 0 by decide)).mp
  rw [two_smul ℤ]
  exact add_eq_zero_iff_eq_neg.mpr (hskew x x)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule in
private def
    PeriodTorusHigherHomologyPontryagin.multilinearOfTrilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N) :
    MultilinearMap ℤ (fun _ : Fin 3 => M) N
    where
  toFun v := g (v 0) (v 1) (v 2)
  map_update_add' {hDecEq} v i x
    y := by
    have heq : hDecEq = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp
  map_update_smul' {hDecEq} v i r
    x := by
    have heq : hDecEq = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule in
private def
    PeriodTorusHigherHomologyPontryagin.alternatingOfTrilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (h01 : ∀ x z : M, g x x z = 0) (h02 : ∀ x y : M, g x y x = 0) (h12 : ∀ x y : M, g x y y = 0) :
    AlternatingMap ℤ M N (Fin 3)
    where
  toMultilinearMap := multilinearOfTrilinear g
  map_eq_zero_of_eq' v i j hij
    hne := by
    have h : v 0 = v 1 ∨ v 0 = v 2 ∨ v 1 = v 2 := by fin_cases i <;> fin_cases j <;> simp_all
    change g (v 0) (v 1) (v 2) = 0
    rcases h with h | h | h
    · rw [h]
      exact h01 _ _
    · rw [h]
      exact h02 _ _
    · rw [h]
      exact h12 _ _

private theorem
    PeriodTorusHigherHomology.formalMap_comp {V W Z : Type*} (f : W → Z) (g : V → W) (n : ℕ)
    (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap f n (SingularMayerVietoris.formalMap g n c) =
      SingularMayerVietoris.formalMap (f ∘ g) n c := by
  have h :
    (SingularMayerVietoris.formalMap f n).comp (SingularMayerVietoris.formalMap g n) =
      SingularMayerVietoris.formalMap (f ∘ g) n := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c

private theorem PeriodTorusHigherHomology.formalMap_prod_swap {V W V' W' : Type*} (f : V → V')
    (g : W → W') (n : ℕ) (c : SingularMayerVietoris.FormalChains (W × V) n) :
    SingularMayerVietoris.formalMap (Prod.map f g) n
        (SingularMayerVietoris.formalMap Prod.swap n c) =
      SingularMayerVietoris.formalMap Prod.swap n
        (SingularMayerVietoris.formalMap (Prod.map g f) n c) := by
  rw [formalMap_comp, formalMap_comp]
  rfl

private theorem PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_one {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap Prod.swap 2 (formalPointCrossProduct 1 c d) =
      formalEdgeCrossProduct 0 d c := by
  have h :
    (formalPointCrossProduct (V := V) (W := W) 1).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 2) =
      (formalEdgeCrossProduct 0).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 2
          (formalPointCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 2
            (SingularMayerVietoris.formalMap (fun z => (v 0, z)) 2
              (SingularMayerVietoris.formalSimplex w)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 2)
          (formalPointCrossProduct_simplex_left 1 v (SingularMayerVietoris.formalSimplex w))
      _ =
          SingularMayerVietoris.formalMap (fun z => (z, v 0)) 2
            (SingularMayerVietoris.formalSimplex w) := by
        rw [formalMap_comp]
        rfl
      _ = _ :=
        (formalEdgeCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w) v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private theorem PeriodTorusHigherHomology.formalMap_swap_edgeCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalMap Prod.swap 2 (formalEdgeCrossProduct 0 c d) =
      formalPointCrossProduct 1 d c := by
  have h :
    (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 2) =
      (formalPointCrossProduct 1).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 2
          (formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        formalPointCrossProduct 1 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 2
            (SingularMayerVietoris.formalMap (fun z => (z, w 0)) 2
              (SingularMayerVietoris.formalSimplex v)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 2)
          (formalEdgeCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex v) w)
      _ =
          SingularMayerVietoris.formalMap (fun z => (w 0, z)) 2
            (SingularMayerVietoris.formalSimplex v) := by
        rw [formalMap_comp]
        rfl
      _ = _ :=
        (formalPointCrossProduct_simplex_left 1 w (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private def PeriodTorusHigherHomology.formalEdgeSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 3 :=
  formalEdgeCrossProduct 1 +
    (formalEdgeCrossProduct 1).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 3)

@[simp]
private theorem PeriodTorusHigherHomology.formalEdgeSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    formalEdgeSwapDefect c d =
      formalEdgeCrossProduct 1 c d +
        SingularMayerVietoris.formalMap Prod.swap 3 (formalEdgeCrossProduct 1 d c) :=
  rfl

private theorem PeriodTorusHigherHomology.formalBoundary_edgeSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 2 (formalEdgeSwapDefect c d) = 0 := by
  rw [formalEdgeSwapDefect_apply, map_add, formalBoundary_edgeCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, formalBoundary_edgeCrossProduct, map_sub,
    formalMap_swap_pointCrossProduct_one, formalMap_swap_edgeCrossProduct_zero]
  abel

private theorem PeriodTorusHigherHomology.formalMap_edgeSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 3 (formalEdgeSwapDefect c d) =
      formalEdgeSwapDefect (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [formalEdgeSwapDefect_apply, map_add, formalMap_edgeCrossProduct, formalMap_prod_swap,
    formalMap_edgeCrossProduct, formalEdgeSwapDefect_apply]

private def PeriodTorusHigherHomology.formalEdgeSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 3
      (formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w))

@[simp]
private theorem
    PeriodTorusHigherHomology.formalEdgeSwapHomotopy_simplex {V W : Type*} (v : Fin 2 → V)
    (w : Fin 2 → W) :
    formalEdgeSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 3
        (formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)) :=
  formalBilinearLift_simplex _ _ _

private theorem PeriodTorusHigherHomology.formalEdgeSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (formalEdgeSwapHomotopy c d) =
      formalEdgeSwapDefect c d := by
  have h :
    (formalEdgeSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 3) =
      formalEdgeSwapDefect := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, formalEdgeSwapHomotopy_simplex,
      SingularMayerVietoris.formalBoundary_cone, formalBoundary_edgeSwapDefect, map_zero,
      sub_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private theorem
    PeriodTorusHigherHomology.formalMap_edgeSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (formalEdgeSwapHomotopy c d) =
      formalEdgeSwapHomotopy (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have h :
    (formalEdgeSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 4) =
      ((formalEdgeSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 2) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, formalEdgeSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone, formalMap_edgeSwapDefect,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.prodSwap_productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :
    (ContinuousMap.prodSwap :
            C(FirstHurewicz.Simplex p × FirstHurewicz.Simplex q,
              FirstHurewicz.Simplex q × FirstHurewicz.Simplex p)).comp
        (productAffineSimplex v) =
      productAffineSimplex (Prod.swap ∘ v) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.inducedChain_swap_productAffineChainMap (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
        (n + 1)) :
    FirstHurewicz.inducedChain
        (ContinuousMap.prodSwap :
          C(FirstHurewicz.Simplex p × FirstHurewicz.Simplex q,
            FirstHurewicz.Simplex q × FirstHurewicz.Simplex p))
        n (productAffineChainMap p q n c) =
      productAffineChainMap q p n (SingularMayerVietoris.formalMap Prod.swap (n + 1) c) := by
  have h :
    (FirstHurewicz.inducedChain
            (ContinuousMap.prodSwap :
              C(FirstHurewicz.Simplex p × FirstHurewicz.Simplex q,
                FirstHurewicz.Simplex q × FirstHurewicz.Simplex p))
            n).comp
        (productAffineChainMap p q n) =
      (productAffineChainMap q p n).comp (SingularMayerVietoris.formalMap Prod.swap (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      prodSwap_productAffineSimplex]
  exact LinearMap.congr_fun h c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.inducedChain_prodMap_swap {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (c : FirstHurewicz.Chains (Y × X) n) :
    FirstHurewicz.inducedChain (f.prodMap g) n
        (FirstHurewicz.inducedChain ContinuousMap.prodSwap n c) =
      FirstHurewicz.inducedChain ContinuousMap.prodSwap n
        (FirstHurewicz.inducedChain (g.prodMap f) n c) := by
  calc
    _ = FirstHurewicz.inducedChain ((f.prodMap g).comp ContinuousMap.prodSwap) n c :=
      (LinearMap.congr_fun (FirstHurewicz.inducedChain_comp _ _ n) c).symm
    _ = FirstHurewicz.inducedChain (ContinuousMap.prodSwap.comp (g.prodMap f)) n c := rfl
    _ = _ := LinearMap.congr_fun (FirstHurewicz.inducedChain_comp _ _ n) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    FirstHurewicz.Chains X 1 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 3 :=
  chainBilinearLift X Y 1 1 fun σ τ =>
    FirstHurewicz.inducedChain (σ.prodMap τ) 3
      (productAffineChainMap 1 1 3
        (formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : FirstHurewicz.SingularSimplex X 1)
    (τ : FirstHurewicz.SingularSimplex Y 1) :
    crossProductSwapHomotopy X Y (FirstHurewicz.simplexChain X 1 σ)
        (FirstHurewicz.simplexChain Y 1 τ) =
      FirstHurewicz.inducedChain (σ.prodMap τ) 3
        (productAffineChainMap 1 1 3
          (formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  chainBilinearLift_simplex X Y 1 1 _ σ τ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1) :
    FirstHurewicz.inducedChain (f.prodMap g) 3 (crossProductSwapHomotopy X Y a b) =
      crossProductSwapHomotopy X' Y' (FirstHurewicz.inducedChain f 1 a)
        (FirstHurewicz.inducedChain g 1 b) := by
  have h :
    integerBilinearPostcompose (crossProductSwapHomotopy X Y)
        (FirstHurewicz.inducedChain (f.prodMap g) 3) =
      integerBilinearPrecompose (crossProductSwapHomotopy X' Y') (FirstHurewicz.inducedChain f 1)
        (FirstHurewicz.inducedChain g 1) := by
    apply chainBilinearMap_ext X Y 1 1
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      productAffineChainMap p q 3 (formalEdgeSwapHomotopy a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q))
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1) =
      integerBilinearPostcompose formalEdgeSwapHomotopy (productAffineChainMap p q 3) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductSwapHomotopy_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q 3
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            4
            (formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [formalMap_edgeSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d 3
            2).hom
        (crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)) =
      crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 1
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b) +
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 2
          (crossProductEdge (FirstHurewicz.Simplex q) (FirstHurewicz.Simplex p) 1
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap p 1 a)) := by
  rw [crossProductSwapHomotopy_affineChainMap, productAffineChainMap_boundary,
    formalEdgeSwapHomotopy_boundary, formalEdgeSwapDefect_apply, map_add,
    crossProductEdge_affineChainMap, crossProductEdge_affineChainMap,
    inducedChain_swap_productAffineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) :
    ((FirstHurewicz.singularComplex (X × Y)).d 3 2).hom (crossProductSwapHomotopy X Y a b) =
      crossProductEdge X Y 1 a b +
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 2 (crossProductEdge Y X 1 b a) := by
  have h :
    integerBilinearPostcompose (crossProductSwapHomotopy X Y)
        ((FirstHurewicz.singularComplex (X × Y)).d 3 2).hom =
      crossProductEdge X Y 1 +
        integerBilinearPostcompose (integerBilinearFlip (crossProductEdge Y X 1))
          (FirstHurewicz.inducedChain ContinuousMap.prodSwap 2) := by
    apply chainBilinearMap_ext X Y 1 1
    intro σ τ
    have hstd :=
      crossProductSwapHomotopy_boundary_affine 1 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) 2) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearFlip_apply, LinearMap.add_apply,
      map_add, FirstHurewicz.inducedChain_boundary, crossProductSwapHomotopy_natural,
      inducedChain_prodMap_swap, crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductCycleClasses_add_swap_eq_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1) :
    crossProductCycleClasses X Y 1 a b +
        SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
          (crossProductCycleClasses Y X 1 b a) =
      0 := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (X × Y)) 2
          (crossProductCycles X Y 1 a b) +
        (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap ContinuousMap.prodSwap)
              2).hom
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (Y × X))
            2 (crossProductCycles Y X 1 b a)) =
      0
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, ← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (FirstHurewicz.singularComplex (X × Y)) 2 _).mpr
  refine ⟨crossProductSwapHomotopy X Y a.1 b.1, ?_⟩
  rw [Submodule.coe_add, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact crossProductSwapHomotopy_boundary a.1 b.1

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductHomology_add_swap_eq_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    crossProductHomology X Y 1 a b +
        SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
          (crossProductHomology Y X 1 b a) =
      0 := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Y) 1
      b
  rw [crossProductHomology_cycleClass, crossProductHomology_cycleClass]
  exact crossProductCycleClasses_add_swap_eq_zero a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductHomology_swap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
        (crossProductHomology X Y 1 a b) =
      -crossProductHomology Y X 1 b a := by
  have h := crossProductHomology_add_swap_eq_zero b a
  exact eq_neg_of_add_eq_zero_right h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductHomology_pushforward_anticommute {X Z : Type}
    [TopologicalSpace X] [TopologicalSpace Z] (f : C(X × X, Z))
    (hf : f.comp ContinuousMap.prodSwap = f) (a b : SingularMayerVietoris.SingularHomology X 1) :
    SingularMayerVietoris.singularHomologyMap f 2 (crossProductHomology X X 1 a b) =
      -SingularMayerVietoris.singularHomologyMap f 2 (crossProductHomology X X 1 b a) := by
  have h :=
    congrArg (SingularMayerVietoris.singularHomologyMap f 2) (crossProductHomology_swap a b)
  rw [map_neg] at h
  have hc :=
    LinearMap.congr_fun (singularHomologyMap_comp (ContinuousMap.prodSwap : C(X × X, X × X)) f 2)
      (crossProductHomology X X 1 a b)
  rw [hf] at hc
  exact hc.trans h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomologyPontryagin.product11_skew (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b : SingularMayerVietoris.SingularHomology G 1) : product11 G a b = -product11 G b a :=
  PeriodTorusHigherHomology.crossProductHomology_pushforward_anticommute (additionMap G)
    (by ext p; exact add_comm p.2 p.1) a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomologyPontryagin.product11_self (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a : SingularMayerVietoris.SingularHomology G 1) : product11 G a a = 0 :=
  skewBilinear_diagonal_zero (product11 G) (product11_skew G) a

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomologyPontryagin.homologyAlternatingTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 2) (Fin 2) :=
  alternatingOfBilinear (product11 G) (product11_self G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^2 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 2 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingTwo G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 2 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeTwo G (exteriorPower.ιMulti ℤ 2 v) = product11 G (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 2 :=
  (homologyWedgeTwo G).comp (exteriorPower.map 2 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (v : Fin 2 → Lattice) :
    latticeWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v) = product11 G (c (v 0)) (c (v 1)) := by
  change homologyWedgeTwo G (exteriorPower.map 2 c (exteriorPower.ιMulti ℤ 2 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeTwo_apply_ιMulti]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 2).comp (latticeWedgeTwo G c) =
      (latticeWedgeTwo H d).comp (exteriorPower.map 2 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    SingularMayerVietoris.singularHomologyMap f 2
        (latticeWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v)) =
      latticeWedgeTwo H d (exteriorPower.map 2 A (exteriorPower.ιMulti ℤ 2 v))
  rw [exteriorPower.map_apply_ιMulti, latticeWedgeTwo_apply_ιMulti, latticeWedgeTwo_apply_ιMulti]
  rw [product_natural f hf 1, hmark, hmark]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomology.integerTrilinearPostcompose {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := integerBilinearPostcompose (F a) g
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => g (l b c)) (F.map_smul r a)).trans
        (g.map_smul r (F a b c))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.integerTrilinearPostcompose_apply {A B C D E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) (a : A) (b : B) (c : C) :
    integerTrilinearPostcompose F g a b c = g (F a b c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.integerTrilinearPrecompose {A B C D A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
    [Module ℤ A'] [Module ℤ B'] [Module ℤ C'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C) : A' →ₗ[ℤ] B' →ₗ[ℤ] C' →ₗ[ℤ] D
    where
  toFun a := integerBilinearPrecompose (F (f a)) g h
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPrecompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun x => F x (g b) (h c)) (f.map_smul r a)).trans
        (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => l (g b) (h c)) (F.map_smul r (f a)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.integerTrilinearPrecompose_apply {A B C D A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
    [Module ℤ A'] [Module ℤ B'] [Module ℤ C'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C) (a : A') (b : B') (c : C') :
    integerTrilinearPrecompose F f g h a b c = F (f a) (g b) (h c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomology.integerTrilinearLeftAssociated {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] B →ₗ[ℤ] D) (G : D →ₗ[ℤ] C →ₗ[ℤ] E) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := integerBilinearPrecompose G (F a) LinearMap.id
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPrecompose_apply, LinearMap.id_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun l : B →ₗ[ℤ] D => G (l b) c) (F.map_smul r a)).trans
        (congrArg (fun l : C →ₗ[ℤ] E => l c) (G.map_smul r (F a b)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomology.integerTrilinearRightAssociated {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] D →ₗ[ℤ] E) (G : B →ₗ[ℤ] C →ₗ[ℤ] D) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := integerBilinearPostcompose G (F a)
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact congrArg (fun l : D →ₗ[ℤ] E => l (G b c)) (F.map_smul r a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.chainTrilinearLift (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f :
      FirstHurewicz.SingularSimplex X p →
        FirstHurewicz.SingularSimplex Y q → FirstHurewicz.SingularSimplex Z r → M) :
    FirstHurewicz.Chains X p →ₗ[ℤ]
      FirstHurewicz.Chains Y q →ₗ[ℤ] FirstHurewicz.Chains Z r →ₗ[ℤ] M :=
  FirstHurewicz.chainLift X p fun σ => chainBilinearLift Y Z q r (f σ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.chainTrilinearLift_simplex (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f :
      FirstHurewicz.SingularSimplex X p →
        FirstHurewicz.SingularSimplex Y q → FirstHurewicz.SingularSimplex Z r → M)
    (σ : FirstHurewicz.SingularSimplex X p) (τ : FirstHurewicz.SingularSimplex Y q)
    (υ : FirstHurewicz.SingularSimplex Z r) :
    chainTrilinearLift X Y Z p q r f (FirstHurewicz.simplexChain X p σ)
        (FirstHurewicz.simplexChain Y q τ) (FirstHurewicz.simplexChain Z r υ) =
      f σ τ υ := by
  rw [chainTrilinearLift, FirstHurewicz.chainLift_simplex, chainBilinearLift_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.chainTrilinearMap_ext (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    {F G :
      FirstHurewicz.Chains X p →ₗ[ℤ]
        FirstHurewicz.Chains Y q →ₗ[ℤ] FirstHurewicz.Chains Z r →ₗ[ℤ] M}
    (h :
      ∀ σ τ υ,
        F (FirstHurewicz.simplexChain X p σ) (FirstHurewicz.simplexChain Y q τ)
            (FirstHurewicz.simplexChain Z r υ) =
          G (FirstHurewicz.simplexChain X p σ) (FirstHurewicz.simplexChain Y q τ)
            (FirstHurewicz.simplexChain Z r υ)) :
    F = G := by
  apply FirstHurewicz.chainMap_ext X p
  intro σ
  apply chainBilinearMap_ext Y Z q r
  exact h σ

private theorem
    PeriodTorusHigherHomology.formalMap_comp_apply {V W Z : Type*} (f : W → Z) (g : V → W)
    (n : ℕ) (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap f n (SingularMayerVietoris.formalMap g n c) =
      SingularMayerVietoris.formalMap (f ∘ g) n c := by
  have h :
    (SingularMayerVietoris.formalMap f n).comp (SingularMayerVietoris.formalMap g n) =
      SingularMayerVietoris.formalMap (f ∘ g) n := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c

private theorem PeriodTorusHigherHomology.formalMap_id_apply {V : Type*} (n : ℕ)
    (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap (id : V → V) n c = c := by
  have h : SingularMayerVietoris.formalMap (id : V → V) n = LinearMap.id := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [SingularMayerVietoris.formalMap_simplex, LinearMap.id_apply]
    rfl
  exact LinearMap.congr_fun h c

private theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_point_left {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 1) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (formalEdgeCrossProduct q (formalPointCrossProduct 1 a b) c) =
      formalPointCrossProduct (q + 1) a (formalEdgeCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((formalEdgeCrossProduct q).flip c).comp ((formalPointCrossProduct 1).flip b)) =
      (formalPointCrossProduct (q + 1)).flip (formalEdgeCrossProduct q b c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, formalPointCrossProduct_simplex_left]
    have hn := formalMap_edgeCrossProduct (fun w : W => (v 0, w)) (id : Z → Z) q b c
    rw [formalMap_id_apply] at hn
    rw [← hn, formalMap_comp_apply]
    rfl
  exact LinearMap.congr_fun h a

private theorem
    PeriodTorusHigherHomology.formalEdgeCrossProduct_point_middle {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 1)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (formalEdgeCrossProduct q (formalEdgeCrossProduct 0 a b) c) =
      formalEdgeCrossProduct q a (formalPointCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((formalEdgeCrossProduct q).flip c).comp (formalEdgeCrossProduct 0 a)) =
      (formalEdgeCrossProduct q a).comp ((formalPointCrossProduct q).flip c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [formalEdgeCrossProduct_zero_simplex_right, formalPointCrossProduct_simplex_left]
    have hl := formalMap_edgeCrossProduct (fun v : V => (v, w 0)) (id : Z → Z) q a c
    have hr := formalMap_edgeCrossProduct (id : V → V) (fun z : Z => (w 0, z)) q a c
    rw [formalMap_id_apply] at hl hr
    rw [← hl, formalMap_comp_apply, ← hr]
    rfl
  exact LinearMap.congr_fun h b

private theorem PeriodTorusHigherHomology.formalTriangleCrossProduct_point_right {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3
        (formalTriangleCrossProduct 0 (formalEdgeCrossProduct 1 a b) c) =
      formalEdgeCrossProduct 1 a (formalEdgeCrossProduct 0 b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3).comp
        (formalTriangleCrossProduct 0 (formalEdgeCrossProduct 1 a b)) =
      (formalEdgeCrossProduct 1 a).comp (formalEdgeCrossProduct 0 b) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, formalTriangleCrossProduct_zero_simplex_right,
      formalEdgeCrossProduct_zero_simplex_right, formalMap_comp_apply]
    have hn := formalMap_edgeCrossProduct (id : V → V) (fun w : W => (w, z 0)) 1 a b
    rw [formalMap_id_apply] at hn
    exact hn
  exact LinearMap.congr_fun h c

private theorem PeriodTorusHigherHomology.formalChains_trilinear_ext {V W Z M : Type*} {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M]
    {f g :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] M}
    (h :
      ∀ v w z,
        f (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalSimplex z) =
          g (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalSimplex z)) :
    f = g := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  apply formalChains_bilinear_ext
  exact h v

private def
    PeriodTorusHigherHomology.formalTrilinearLift {V W Z M : Type*} {n m l : ℕ} [AddCommGroup M]
    [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] M :=
  SingularMayerVietoris.formalLift fun v => formalBilinearLift (f v)

@[simp]
private theorem PeriodTorusHigherHomology.formalTrilinearLift_simplex {V W Z M : Type*} {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M)
    (v : Fin n → V) (w : Fin m → W) (z : Fin l → Z) :
    formalTrilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      f v w z := by simp [formalTrilinearLift]

private def PeriodTorusHigherHomology.formalAssociatorDefect {V W Z : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3) :=
  (formalEdgeCrossProduct 1).compr₂
      ((formalTriangleCrossProduct q).compr₂
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2)))
          (q + 3))) -
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z (q + 1))
              (SingularMayerVietoris.FormalChains (W × Z) (q + 2))
              (SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3))).compl₂
          (formalEdgeCrossProduct q)).comp
      (formalEdgeCrossProduct (q + 1))

@[simp]
private theorem PeriodTorusHigherHomology.formalAssociatorDefect_apply {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    formalAssociatorDefect q a b c =
      SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 3)
          (formalTriangleCrossProduct q (formalEdgeCrossProduct 1 a b) c) -
        formalEdgeCrossProduct (q + 1) a (formalEdgeCrossProduct q b c) :=
  rfl

private theorem PeriodTorusHigherHomology.formalAssociatorDefect_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : formalAssociatorDefect 0 a b c = 0 := by
  rw [formalAssociatorDefect_apply, formalTriangleCrossProduct_point_right, sub_self]

private theorem PeriodTorusHigherHomology.formalBoundary_associatorDefect {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 2)) :
    SingularMayerVietoris.formalBoundary (q + 3) (formalAssociatorDefect (q + 1) a b c) =
      formalAssociatorDefect q a b (SingularMayerVietoris.formalBoundary (q + 1) c) := by
  simp only [formalAssociatorDefect_apply, map_sub, ← SingularMayerVietoris.formalMap_boundary,
    formalBoundary_triangleCrossProduct, formalBoundary_edgeCrossProduct, map_add,
    LinearMap.sub_apply, formalEdgeCrossProduct_point_middle]
  rw [formalEdgeCrossProduct_point_left (q + 1) (SingularMayerVietoris.formalBoundary 1 a) b c]
  abel

private theorem PeriodTorusHigherHomology.formalMap_prodAssoc_naturality {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') (n : ℕ)
    (c : SingularMayerVietoris.FormalChains ((V × W) × Z) n) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n c) =
      SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n c) := by
  have heq :
    (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n).comp
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n) =
      (SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n).comp
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun heq c

private theorem
    PeriodTorusHigherHomology.formalMap_associatorDefect {V W Z V' W' Z' : Type*} (f : V → V')
    (g : W → W') (h : Z → Z') (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
    (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 3)
        (formalAssociatorDefect q a b c) =
      formalAssociatorDefect q (SingularMayerVietoris.formalMap f 2 a)
        (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) := by
  rw [formalAssociatorDefect_apply, map_sub, formalMap_prodAssoc_naturality,
    formalMap_triangleCrossProduct, formalMap_edgeCrossProduct, formalMap_edgeCrossProduct,
    formalMap_edgeCrossProduct]
  rfl

private def PeriodTorusHigherHomology.triplePostcomp_mo1973_13949 {V W Z U U' : Type*}
    {n m l r s : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains U r →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s :=
  F.compr₂
    (LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z l)
      (SingularMayerVietoris.FormalChains U r) (SingularMayerVietoris.FormalChains U' s) f)

private def PeriodTorusHigherHomology.triplePrecompLast_mo1973_13950 {V W Z Z' U : Type*}
    {n m l l' r : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains Z l) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains U r :=
  F.compr₂
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z' l')
          (SingularMayerVietoris.FormalChains Z l) (SingularMayerVietoris.FormalChains U r)).flip
      f)

private def PeriodTorusHigherHomology.formalAssociatorHomotopy {V W Z : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
            SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 4)
  | 0 => 0
  | q + 1 =>
    formalTrilinearLift fun v w z =>
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z)))

@[simp]
private theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : formalAssociatorHomotopy 0 a b c = 0 :=
  rfl

@[simp]
private theorem
    PeriodTorusHigherHomology.formalAssociatorHomotopy_simplex_succ {V W Z : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin 2 → W) (z : Fin (q + 2) → Z) :
    formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z))) :=
  formalTrilinearLift_simplex _ _ _ _

private theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalBoundary 3 (formalAssociatorHomotopy 0 a b c) =
      formalAssociatorDefect 0 a b c := by
  rw [formalAssociatorHomotopy_zero, map_zero, formalAssociatorDefect_zero]

private theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary {V W Z : Type*} :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 4) (formalAssociatorHomotopy (q + 1) a b c) +
          formalAssociatorHomotopy q a b (SingularMayerVietoris.formalBoundary (q + 1) c) =
        formalAssociatorDefect (q + 1) a b c := by
  intro q
  induction q with
  | zero =>
    intro a b c
    have heq :
      triplePostcomp_mo1973_13949 (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) 1)
            (SingularMayerVietoris.formalBoundary 4) +
          triplePrecompLast_mo1973_13950 (formalAssociatorHomotopy 0)
            (SingularMayerVietoris.formalBoundary 1) =
        formalAssociatorDefect 1 := by
      apply formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary 4
              (formalAssociatorHomotopy 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex z)) =
          formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hz :
        SingularMayerVietoris.formalBoundary 3
            (formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by
        rw [map_sub, formalBoundary_associatorDefect, formalAssociatorDefect_zero,
          formalAssociatorHomotopy_zero, map_zero, sub_self]
      rw [formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c
  | succ q ih =>
    intro a b c
    have heq :
      triplePostcomp_mo1973_13949 (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 2))
            (SingularMayerVietoris.formalBoundary (q + 5)) +
          triplePrecompLast_mo1973_13950 (formalAssociatorHomotopy (q + 1))
            (SingularMayerVietoris.formalBoundary (q + 2)) =
        formalAssociatorDefect (q + 2) := by
      apply formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary (q + 5)
              (formalAssociatorHomotopy (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z)) =
          formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hp :
        SingularMayerVietoris.formalBoundary (q + 4)
            (formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z))) =
          formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2)
              (SingularMayerVietoris.formalSimplex z)) := by
        simpa only [SingularMayerVietoris.formalBoundary_boundary, map_zero, add_zero] using
          ih (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2) (SingularMayerVietoris.formalSimplex z))
      have hz :
        SingularMayerVietoris.formalBoundary (q + 4)
            (formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by rw [map_sub, formalBoundary_associatorDefect, hp, sub_self]
      rw [formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

private theorem PeriodTorusHigherHomology.formalMap_associatorHomotopy {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 4)
          (formalAssociatorHomotopy q a b c) =
        formalAssociatorHomotopy q (SingularMayerVietoris.formalMap f 2 a)
          (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) :=
  by
  intro q
  induction q with
  | zero =>
    intro a b c
    simp only [formalAssociatorHomotopy_zero, map_zero]
  | succ q ih =>
    intro a b c
    have heq :
      triplePostcomp_mo1973_13949 (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 1))
          (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)) =
        ((triplePrecompLast_mo1973_13950 (formalAssociatorHomotopy (q + 1))
                  (SingularMayerVietoris.formalMap h (q + 2))).compl₂
              (SingularMayerVietoris.formalMap g 2)).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)
            (formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) =
          formalAssociatorHomotopy (q + 1)
            (SingularMayerVietoris.formalMap f 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalMap g 2 (SingularMayerVietoris.formalSimplex w))
            (SingularMayerVietoris.formalMap h (q + 2) (SingularMayerVietoris.formalSimplex z))
      simp only [SingularMayerVietoris.formalMap_simplex, formalAssociatorHomotopy_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_sub, formalMap_associatorDefect, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

private def PeriodTorusHigherHomology.tripleAffineSimplex {n p q r : ℕ}
    (v :
      Fin (n + 1) →
        FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :
    C(FirstHurewicz.Simplex n,
      FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (productAffineSimplex (fun i => (v i).2))

private theorem PeriodTorusHigherHomology.tripleAffineSimplex_face {n p q r : ℕ}
    (v :
      Fin (n + 2) → FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))
    (i : Fin (n + 2)) :
    (tripleAffineSimplex v).comp (FirstHurewicz.simplexFace n i) =
      tripleAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).1) i)
  · exact
      congrArg
        (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex q × FirstHurewicz.Simplex r) =>
          f t)
        (productAffineSimplex_face (fun j => (v j).2) i)

private def PeriodTorusHigherHomology.tripleAffineChainMap (p q r n : ℕ) :
    SingularMayerVietoris.FormalChains
        (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))
        (n + 1) →ₗ[ℤ]
      FirstHurewicz.Chains
        (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) n :=
  SingularMayerVietoris.formalLift fun v => FirstHurewicz.simplexChain _ n (tripleAffineSimplex v)

@[simp]
private theorem PeriodTorusHigherHomology.tripleAffineChainMap_simplex (p q r n : ℕ)
    (v :
      Fin (n + 1) →
        FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :
    tripleAffineChainMap p q r n (SingularMayerVietoris.formalSimplex v) =
      FirstHurewicz.simplexChain _ n (tripleAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

private theorem PeriodTorusHigherHomology.tripleAffineChainMap_boundary (p q r n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains
        (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) (n + 2)) :
    ((FirstHurewicz.singularComplex
                (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
            (n + 1) n).hom
        (tripleAffineChainMap p q r (n + 1) c) =
      tripleAffineChainMap p q r n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((FirstHurewicz.singularComplex
                  (FirstHurewicz.Simplex p ×
                    (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
              (n + 1) n).hom).comp
        (tripleAffineChainMap p q r (n + 1)) =
      (tripleAffineChainMap p q r n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((FirstHurewicz.singularComplex
                  (FirstHurewicz.Simplex p ×
                    (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
              (n + 1) n).hom
          (tripleAffineChainMap p q r (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [tripleAffineChainMap_simplex, FirstHurewicz.boundary_simplex]
    change
      _ =
        tripleAffineChainMap p q r n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, tripleAffineChainMap_simplex, tripleAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

private def PeriodTorusHigherHomology.affineProductLeft {a b p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
    (w : Fin (b + 1) → FirstHurewicz.Simplex r) :
    C(FirstHurewicz.Simplex a × FirstHurewicz.Simplex b,
      FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :=
  (Homeomorph.prodAssoc (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) :
        C(_, _)).comp
    ((productAffineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w))

private def PeriodTorusHigherHomology.affineProductRight {a b p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p)
    (w : Fin (b + 1) → FirstHurewicz.Simplex q × FirstHurewicz.Simplex r) :
    C(FirstHurewicz.Simplex a × FirstHurewicz.Simplex b,
      FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex v).prodMap (productAffineSimplex w)

private theorem PeriodTorusHigherHomology.affineProductLeft_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
    (w : Fin (b + 1) → FirstHurewicz.Simplex r)
    (z : Fin (m + 1) → FirstHurewicz.Simplex a × FirstHurewicz.Simplex b) :
    (affineProductLeft v w).comp (productAffineSimplex z) =
      tripleAffineSimplex (fun j => affineProductLeft v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).1) (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).2) (fun j => (z j).1))
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (z j).2))

private theorem PeriodTorusHigherHomology.affineProductRight_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p)
    (w : Fin (b + 1) → FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
    (z : Fin (m + 1) → FirstHurewicz.Simplex a × FirstHurewicz.Simplex b) :
    (affineProductRight v w).comp (productAffineSimplex z) =
      tripleAffineSimplex (fun j => affineProductRight v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).1) (fun j => (z j).2))
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).2) (fun j => (z j).2))

private theorem PeriodTorusHigherHomology.inducedChain_affineProductLeft {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
    (w : Fin (b + 1) → FirstHurewicz.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex a × FirstHurewicz.Simplex b)
        (m + 1)) :
    FirstHurewicz.inducedChain (affineProductLeft v w) m (productAffineChainMap a b m c) =
      tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (affineProductLeft v w) (m + 1) c) := by
  have h :
    (FirstHurewicz.inducedChain (affineProductLeft v w) m).comp (productAffineChainMap a b m) =
      (tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (affineProductLeft v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      tripleAffineChainMap_simplex, affineProductLeft_comp]
    rfl
  exact LinearMap.congr_fun h c

private theorem PeriodTorusHigherHomology.inducedChain_affineProductRight {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p)
    (w : Fin (b + 1) → FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex a × FirstHurewicz.Simplex b)
        (m + 1)) :
    FirstHurewicz.inducedChain (affineProductRight v w) m (productAffineChainMap a b m c) =
      tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (affineProductRight v w) (m + 1) c) := by
  have h :
    (FirstHurewicz.inducedChain (affineProductRight v w) m).comp (productAffineChainMap a b m) =
      (tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (affineProductRight v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      tripleAffineChainMap_simplex, affineProductRight_comp]
    rfl
  exact LinearMap.congr_fun h c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomology.crossProductAssociatorDefect (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    FirstHurewicz.Chains X 1 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ]
        FirstHurewicz.Chains Z n →ₗ[ℤ] FirstHurewicz.Chains (X × (Y × Z)) (n + 2) :=
  integerTrilinearPostcompose
      (integerTrilinearLeftAssociated (crossProductEdge X Y 1) (crossProductTriangle (X × Y) Z n))
      (FirstHurewicz.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)) -
    integerTrilinearRightAssociated (crossProductEdge X (Y × Z) (n + 1)) (crossProductEdge Y Z n)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_apply (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n) :
    crossProductAssociatorDefect X Y Z n a b c =
      FirstHurewicz.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)
          (crossProductTriangle (X × Y) Z n (crossProductEdge X Y 1 a b) c) -
        crossProductEdge X (Y × Z) (n + 1) a (crossProductEdge Y Z n b c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    FirstHurewicz.Chains X 1 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ]
        FirstHurewicz.Chains Z n →ₗ[ℤ] FirstHurewicz.Chains (X × (Y × Z)) (n + 3) :=
  chainTrilinearLift X Y Z 1 1 n fun σ τ υ =>
    FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
      (tripleAffineChainMap 1 1 n (n + 3)
        (formalAssociatorHomotopy n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_simplex (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (σ : FirstHurewicz.SingularSimplex X 1) (τ : FirstHurewicz.SingularSimplex Y 1)
    (υ : FirstHurewicz.SingularSimplex Z n) :
    crossProductAssociatorHomotopy X Y Z n (FirstHurewicz.simplexChain X 1 σ)
        (FirstHurewicz.simplexChain Y 1 τ) (FirstHurewicz.simplexChain Z n υ) =
      FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
        (tripleAffineChainMap 1 1 n (n + 3)
          (formalAssociatorHomotopy n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  chainTrilinearLift_simplex X Y Z 1 1 n _ σ τ υ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n) :
    FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) (n + 3)
        (crossProductAssociatorHomotopy X Y Z n a b c) =
      crossProductAssociatorHomotopy X' Y' Z' n (FirstHurewicz.inducedChain f 1 a)
        (FirstHurewicz.inducedChain g 1 b) (FirstHurewicz.inducedChain h n c) := by
  have heq :
    integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z n)
        (FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) (n + 3)) =
      integerTrilinearPrecompose (crossProductAssociatorHomotopy X' Y' Z' n)
        (FirstHurewicz.inducedChain f 1) (FirstHurewicz.inducedChain g 1)
        (FirstHurewicz.inducedChain h n) := by
    apply chainTrilinearMap_ext X Y Z 1 1 n
    intro σ τ υ
    simp only [integerTrilinearPostcompose_apply, integerTrilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductAssociatorHomotopy_simplex]
    have hc :
      (f.comp σ).prodMap ((g.comp τ).prodMap (h.comp υ)) =
        (f.prodMap (g.prodMap h)).comp (σ.prodMap (τ.prodMap υ)) :=
      rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.inducedChain_prodAssoc_natural {X : Type} {Y : Type} {Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (c : FirstHurewicz.Chains ((X × Y) × Z) n) :
    FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) n
        (FirstHurewicz.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) n c) =
      FirstHurewicz.inducedChain (Homeomorph.prodAssoc X' Y' Z' : C(_, _)) n
        (FirstHurewicz.inducedChain ((f.prodMap g).prodMap h) n c) := by
  have hc :
    (f.prodMap (g.prodMap h)).comp (Homeomorph.prodAssoc X Y Z : C(_, _)) =
      (Homeomorph.prodAssoc X' Y' Z' : C(_, _)).comp ((f.prodMap g).prodMap h) :=
    rfl
  have heq := congrArg (fun k => FirstHurewicz.inducedChain k n c) hc
  simpa only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply] using heq

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n) :
    FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) (n + 2)
        (crossProductAssociatorDefect X Y Z n a b c) =
      crossProductAssociatorDefect X' Y' Z' n (FirstHurewicz.inducedChain f 1 a)
        (FirstHurewicz.inducedChain g 1 b) (FirstHurewicz.inducedChain h n c) := by
  simp only [crossProductAssociatorDefect_apply, map_sub, inducedChain_prodAssoc_natural,
    crossProductTriangle_natural, crossProductEdge_natural]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.productAffineSimplex_stdVertices_image {n p q : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :
    productAffineSimplex v ∘ SingularMayerVietoris.stdVertices n = v := by
  funext i
  exact productAffineSimplex_vertex v i

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.prodMap_tripleAffineSimplex {a b c m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p) (w : Fin (b + 1) → FirstHurewicz.Simplex q)
    (z : Fin (c + 1) → FirstHurewicz.Simplex r)
    (t :
      Fin (m + 1) →
        FirstHurewicz.Simplex a × (FirstHurewicz.Simplex b × FirstHurewicz.Simplex c)) :
    ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z))).comp
        (tripleAffineSimplex t) =
      tripleAffineSimplex
        (fun j =>
          (SingularMayerVietoris.affineSimplex v (t j).1,
            (SingularMayerVietoris.affineSimplex w (t j).2.1,
              SingularMayerVietoris.affineSimplex z (t j).2.2))) := by
  apply ContinuousMap.ext
  intro s
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex p) => f s)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (t j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex q) => f s)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (t j).2.1))
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex r) => f s)
          (SingularMayerVietoris.affineSimplex_comp z (fun j => (t j).2.2))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.inducedChain_tripleAffineChainMap {a b c m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p) (w : Fin (b + 1) → FirstHurewicz.Simplex q)
    (z : Fin (c + 1) → FirstHurewicz.Simplex r)
    (t :
      SingularMayerVietoris.FormalChains
        (FirstHurewicz.Simplex a × (FirstHurewicz.Simplex b × FirstHurewicz.Simplex c)) (m + 1)) :
    FirstHurewicz.inducedChain
        ((SingularMayerVietoris.affineSimplex v).prodMap
          ((SingularMayerVietoris.affineSimplex w).prodMap
            (SingularMayerVietoris.affineSimplex z)))
        m (tripleAffineChainMap a b c m t) =
      tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1) t) := by
  have h :
    (FirstHurewicz.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              ((SingularMayerVietoris.affineSimplex w).prodMap
                (SingularMayerVietoris.affineSimplex z)))
            m).comp
        (tripleAffineChainMap a b c m) =
      (tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro s
    simp only [LinearMap.comp_apply, tripleAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      prodMap_tripleAffineSimplex]
    rfl
  exact LinearMap.congr_fun h t

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductTriangle_productAffineChainMap_left (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 1)) :
    FirstHurewicz.inducedChain
        (Homeomorph.prodAssoc (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
            (FirstHurewicz.Simplex r) :
          C(_, _))
        (n + 2)
        (crossProductTriangle (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) n (productAffineChainMap p q 2 a)
          (SingularMayerVietoris.affineChainMap r n b)) =
      tripleAffineChainMap p q r (n + 2)
        (SingularMayerVietoris.formalMap
          (fun x :
              (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) × FirstHurewicz.Simplex r =>
            (x.1.1, (x.1.2, x.2)))
          (n + 3) (formalTriangleCrossProduct n a b)) := by
  have h :
    integerBilinearPostcompose
        (integerBilinearPrecompose
          (crossProductTriangle (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
            (FirstHurewicz.Simplex r) n)
          (productAffineChainMap p q 2) (SingularMayerVietoris.affineChainMap r n))
        (FirstHurewicz.inducedChain
          (Homeomorph.prodAssoc (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
              (FirstHurewicz.Simplex r) :
            C(_, _))
          (n + 2)) =
      integerBilinearPostcompose (formalTriangleCrossProduct n)
        ((tripleAffineChainMap p q r (n + 2)).comp
          (SingularMayerVietoris.formalMap
            (fun x :
                (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) × FirstHurewicz.Simplex r =>
              (x.1.1, (x.1.2, x.2)))
            (n + 3))) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      productAffineChainMap_simplex, SingularMayerVietoris.affineChainMap_simplex,
      crossProductTriangle_simplex, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply, ← FirstHurewicz.inducedChain_comp]
    change
      FirstHurewicz.inducedChain (affineProductLeft v w) (n + 2)
          (productAffineChainMap 2 n (n + 2)
            (formalTriangleCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [inducedChain_affineProductLeft]
    apply congrArg (tripleAffineChainMap p q r (n + 2))
    change
      SingularMayerVietoris.formalMap
          ((fun x :
                (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) × FirstHurewicz.Simplex r =>
              (x.1.1, (x.1.2, x.2))) ∘
            Prod.map (productAffineSimplex v) (SingularMayerVietoris.affineSimplex w))
          (n + 3)
          (formalTriangleCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))) =
        _
    rw [← formalMap_comp_apply, formalMap_triangleCrossProduct,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      productAffineSimplex_stdVertices_image, affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_productAffineChainMap_right (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
        (n + 1)) :
    crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
        n (SingularMayerVietoris.affineChainMap p 1 a) (productAffineChainMap q r n b) =
      tripleAffineChainMap p q r (n + 1) (formalEdgeCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductEdge (FirstHurewicz.Simplex p)
          (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (productAffineChainMap q r n) =
      integerBilinearPostcompose (formalEdgeCrossProduct n)
        (tripleAffineChainMap p q r (n + 1)) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, productAffineChainMap_simplex,
      crossProductEdge_simplex]
    change
      FirstHurewicz.inducedChain (affineProductRight v w) (n + 1)
          (productAffineChainMap 1 n (n + 1)
            (formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [inducedChain_affineProductRight]
    change
      tripleAffineChainMap p q r (n + 1)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v) (productAffineSimplex w)) (n + 2)
            (formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_edgeCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      productAffineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 1)) :
    crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      tripleAffineChainMap p q r (n + 3) (formalAssociatorHomotopy n a b c) := by
  have heq :
    integerTrilinearPrecompose
        (crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1)
        (SingularMayerVietoris.affineChainMap r n) =
      integerTrilinearPostcompose (formalAssociatorHomotopy n)
        (tripleAffineChainMap p q r (n + 3)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    apply SingularMayerVietoris.formalChains_ext
    intro w
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [integerTrilinearPrecompose_apply, integerTrilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductAssociatorHomotopy_simplex]
    rw [inducedChain_tripleAffineChainMap]
    change
      tripleAffineChainMap p q r (n + 3)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (Prod.map (SingularMayerVietoris.affineSimplex w)
                (SingularMayerVietoris.affineSimplex z)))
            (n + 4)
            (formalAssociatorHomotopy n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_associatorHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      affineSimplex_stdVertices_image, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 1)) :
    crossProductAssociatorDefect (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      tripleAffineChainMap p q r (n + 2) (formalAssociatorDefect n a b c) := by
  simp only [crossProductAssociatorDefect_apply, crossProductEdge_affineChainMap, Nat.reduceAdd,
    crossProductTriangle_productAffineChainMap_left, crossProductEdge_productAffineChainMap_right,
    formalAssociatorDefect_apply, map_sub]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero_affine (p q r : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) 1) :
    ((FirstHurewicz.singularComplex
                (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
            3 2).hom
        (crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (SingularMayerVietoris.affineChainMap r 0 c)) =
      crossProductAssociatorDefect (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r 0 c) := by
  rw [crossProductAssociatorHomotopy_affineChainMap, tripleAffineChainMap_boundary,
    formalAssociatorHomotopy_boundary_zero, crossProductAssociatorDefect_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_affine (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 2)) :
    ((FirstHurewicz.singularComplex
                  (FirstHurewicz.Simplex p ×
                    (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
              (n + 4) (n + 3)).hom
          (crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
            (FirstHurewicz.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) +
        crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex r)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) =
      crossProductAssociatorDefect (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r (n + 1) c) := by
  rw [crossProductAssociatorHomotopy_affineChainMap, tripleAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductAssociatorHomotopy_affineChainMap,
    ← map_add, formalAssociatorHomotopy_boundary, crossProductAssociatorDefect_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z 0) :
    ((FirstHurewicz.singularComplex (X × (Y × Z))).d 3 2).hom
        (crossProductAssociatorHomotopy X Y Z 0 a b c) =
      crossProductAssociatorDefect X Y Z 0 a b c := by
  have heq :
    integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z 0)
        ((FirstHurewicz.singularComplex (X × (Y × Z))).d 3 2).hom =
      crossProductAssociatorDefect X Y Z 0 := by
    apply chainTrilinearMap_ext X Y Z 1 1 0
    intro σ τ υ
    have hstd :=
      crossProductAssociatorHomotopy_boundary_zero_affine 1 1 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστυ := congrArg (FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) 2) hstd
    simpa only [integerTrilinearPostcompose_apply, FirstHurewicz.inducedChain_boundary,
      crossProductAssociatorHomotopy_natural, crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1)
    (c : FirstHurewicz.Chains Z (n + 1)) :
    ((FirstHurewicz.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom
          (crossProductAssociatorHomotopy X Y Z (n + 1) a b c) +
        crossProductAssociatorHomotopy X Y Z n a b
          (((FirstHurewicz.singularComplex Z).d (n + 1) n).hom c) =
      crossProductAssociatorDefect X Y Z (n + 1) a b c := by
  have heq :
    integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z (n + 1))
          ((FirstHurewicz.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom +
        integerTrilinearPrecompose (crossProductAssociatorHomotopy X Y Z n) LinearMap.id
          LinearMap.id ((FirstHurewicz.singularComplex Z).d (n + 1) n).hom =
      crossProductAssociatorDefect X Y Z (n + 1) := by
    apply chainTrilinearMap_ext X Y Z 1 1 (n + 1)
    intro σ τ υ
    have hstd :=
      crossProductAssociatorHomotopy_boundary_affine 1 1 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστυ := congrArg (FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)) hstd
    simpa only [integerTrilinearPostcompose_apply, integerTrilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, FirstHurewicz.inducedChain_boundary,
      crossProductAssociatorHomotopy_natural, crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_of_cycle {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n)
    (hc : ((FirstHurewicz.singularComplex Z).d n (n - 1)).hom c = 0) :
    ((FirstHurewicz.singularComplex (X × (Y × Z))).d (n + 3) (n + 2)).hom
        (crossProductAssociatorHomotopy X Y Z n a b c) =
      crossProductAssociatorDefect X Y Z n a b c := by
  cases n with
  | zero => exact crossProductAssociatorHomotopy_boundary_zero a b c
  | succ
    n =>
    have hc' : ((FirstHurewicz.singularComplex Z).d (n + 1) n).hom c = 0 := by
      simpa only [Nat.succ_sub_one] using hc
    simpa only [hc', map_zero, add_zero] using crossProductAssociatorHomotopy_boundary n a b c

private theorem PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_two {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (d : SingularMayerVietoris.FormalChains W 3) :
    SingularMayerVietoris.formalMap Prod.swap 3 (formalPointCrossProduct 2 c d) =
      formalTriangleCrossProduct 0 d c := by
  have heq :
    (formalPointCrossProduct (V := V) (W := W) 2).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 3) =
      (formalTriangleCrossProduct 0).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 3
          (formalPointCrossProduct 2 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        formalTriangleCrossProduct 0 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 3
            (SingularMayerVietoris.formalMap (fun z => (v 0, z)) 3
              (SingularMayerVietoris.formalSimplex w)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 3)
          (formalPointCrossProduct_simplex_left 2 v (SingularMayerVietoris.formalSimplex w))
      _ =
          SingularMayerVietoris.formalMap (fun z => (z, v 0)) 3
            (SingularMayerVietoris.formalSimplex w) := by
        rw [formalMap_comp]
        rfl
      _ = _ :=
        (formalTriangleCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w)
            v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

private def PeriodTorusHigherHomology.formalMixedSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  formalTriangleCrossProduct 1 -
    (formalEdgeCrossProduct 2).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 4)

@[simp]
private theorem PeriodTorusHigherHomology.formalMixedSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    formalMixedSwapDefect c d =
      formalTriangleCrossProduct 1 c d -
        SingularMayerVietoris.formalMap Prod.swap 4 (formalEdgeCrossProduct 2 d c) :=
  rfl

private theorem PeriodTorusHigherHomology.formalBoundary_mixedSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (formalMixedSwapDefect c d) =
      formalEdgeSwapDefect (SingularMayerVietoris.formalBoundary 2 c) d := by
  rw [formalMixedSwapDefect_apply, map_sub, formalBoundary_triangleCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, formalBoundary_edgeCrossProduct, map_sub,
    formalMap_swap_pointCrossProduct_two, formalEdgeSwapDefect_apply]
  abel

private theorem PeriodTorusHigherHomology.formalMap_mixedSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (formalMixedSwapDefect c d) =
      formalMixedSwapDefect (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [formalMixedSwapDefect_apply, map_sub, formalMap_triangleCrossProduct, formalMap_prod_swap,
    formalMap_edgeCrossProduct, formalMixedSwapDefect_apply]

private def PeriodTorusHigherHomology.formalMixedSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 5 :=
  formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 4
      (formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w) -
        formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
          (SingularMayerVietoris.formalSimplex w))

@[simp]
private theorem
    PeriodTorusHigherHomology.formalMixedSwapHomotopy_simplex {V W : Type*} (v : Fin 3 → V)
    (w : Fin 2 → W) :
    formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 4
        (formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) -
          formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w)) :=
  formalBilinearLift_simplex _ _ _

private theorem PeriodTorusHigherHomology.formalMixedSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 4 (formalMixedSwapHomotopy c d) +
        formalEdgeSwapHomotopy (SingularMayerVietoris.formalBoundary 2 c) d =
      formalMixedSwapDefect c d := by
  have heq :
    (formalMixedSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 4) +
        (formalEdgeSwapHomotopy).comp (SingularMayerVietoris.formalBoundary 2) =
      formalMixedSwapDefect := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalBoundary 4
            (formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) +
          formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) =
        formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)
    have hz :
      SingularMayerVietoris.formalBoundary 3
          (formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) -
            formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
              (SingularMayerVietoris.formalSimplex w)) =
        0 := by
      rw [map_sub, formalBoundary_mixedSwapDefect, formalEdgeSwapHomotopy_boundary, sub_self]
    rw [formalMixedSwapHomotopy_simplex, SingularMayerVietoris.formalBoundary_cone, hz, map_zero,
      sub_zero, sub_add_cancel]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

private theorem
    PeriodTorusHigherHomology.formalMap_mixedSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 5 (formalMixedSwapHomotopy c d) =
      formalMixedSwapHomotopy (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have heq :
    (formalMixedSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 5) =
      ((formalMixedSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 3) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, formalMixedSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone]
    congr 1
    rw [map_sub, formalMap_mixedSwapDefect, formalMap_edgeSwapHomotopy,
      SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomology.crossProductMixedSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    FirstHurewicz.Chains X 2 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 4 :=
  chainBilinearLift X Y 2 1 fun σ τ =>
    FirstHurewicz.inducedChain (σ.prodMap τ) 4
      (productAffineChainMap 2 1 4
        (formalMixedSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : FirstHurewicz.SingularSimplex X 2)
    (τ : FirstHurewicz.SingularSimplex Y 1) :
    crossProductMixedSwapHomotopy X Y (FirstHurewicz.simplexChain X 2 σ)
        (FirstHurewicz.simplexChain Y 1 τ) =
      FirstHurewicz.inducedChain (σ.prodMap τ) 4
        (productAffineChainMap 2 1 4
          (formalMixedSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  chainBilinearLift_simplex X Y 2 1 _ σ τ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : FirstHurewicz.Chains X 2) (b : FirstHurewicz.Chains Y 1) :
    FirstHurewicz.inducedChain (f.prodMap g) 4 (crossProductMixedSwapHomotopy X Y a b) =
      crossProductMixedSwapHomotopy X' Y' (FirstHurewicz.inducedChain f 2 a)
        (FirstHurewicz.inducedChain g 1 b) := by
  have h :
    integerBilinearPostcompose (crossProductMixedSwapHomotopy X Y)
        (FirstHurewicz.inducedChain (f.prodMap g) 4) =
      integerBilinearPrecompose (crossProductMixedSwapHomotopy X' Y')
        (FirstHurewicz.inducedChain f 2) (FirstHurewicz.inducedChain g 1) := by
    apply chainBilinearMap_ext X Y 2 1
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductMixedSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    crossProductMixedSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (SingularMayerVietoris.affineChainMap p 2 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      productAffineChainMap p q 4 (formalMixedSwapHomotopy a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductMixedSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q))
        (SingularMayerVietoris.affineChainMap p 2) (SingularMayerVietoris.affineChainMap q 1) =
      integerBilinearPostcompose formalMixedSwapHomotopy (productAffineChainMap p q 4) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductMixedSwapHomotopy_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q 4
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            5
            (formalMixedSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [formalMap_mixedSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d 4
              3).hom
          (crossProductMixedSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
            (SingularMayerVietoris.affineChainMap p 2 a)
            (SingularMayerVietoris.affineChainMap q 1 b)) +
        crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p)).d 2 1).hom
            (SingularMayerVietoris.affineChainMap p 2 a))
          (SingularMayerVietoris.affineChainMap q 1 b) =
      crossProductTriangle (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 1
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q 1 b) -
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 3
          (crossProductEdge (FirstHurewicz.Simplex q) (FirstHurewicz.Simplex p) 2
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap p 2 a)) := by
  rw [crossProductMixedSwapHomotopy_affineChainMap, productAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductSwapHomotopy_affineChainMap,
    crossProductTriangle_affineChainMap, crossProductEdge_affineChainMap,
    inducedChain_swap_productAffineChainMap, ← map_add, formalMixedSwapHomotopy_boundary,
    formalMixedSwapDefect_apply, map_sub]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 2)
    (b : FirstHurewicz.Chains Y 1) :
    ((FirstHurewicz.singularComplex (X × Y)).d 4 3).hom (crossProductMixedSwapHomotopy X Y a b) +
        crossProductSwapHomotopy X Y (((FirstHurewicz.singularComplex X).d 2 1).hom a) b =
      crossProductTriangle X Y 1 a b -
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) := by
  have h :
    integerBilinearPostcompose (crossProductMixedSwapHomotopy X Y)
          ((FirstHurewicz.singularComplex (X × Y)).d 4 3).hom +
        integerBilinearPrecompose (crossProductSwapHomotopy X Y)
          ((FirstHurewicz.singularComplex X).d 2 1).hom LinearMap.id =
      crossProductTriangle X Y 1 -
        integerBilinearPostcompose (integerBilinearFlip (crossProductEdge Y X 2))
          (FirstHurewicz.inducedChain ContinuousMap.prodSwap 3) := by
    apply chainBilinearMap_ext X Y 2 1
    intro σ τ
    have hstd :=
      crossProductMixedSwapHomotopy_boundary_affine 2 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) 3) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      integerBilinearFlip_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, FirstHurewicz.inducedChain_boundary,
      crossProductMixedSwapHomotopy_natural, crossProductSwapHomotopy_natural,
      inducedChain_prodMap_swap, crossProductTriangle_natural, crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_of_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 2)
    (ha : ((FirstHurewicz.singularComplex X).d 2 1).hom a = 0) (b : FirstHurewicz.Chains Y 1) :
    ((FirstHurewicz.singularComplex (X × Y)).d 4 3).hom (crossProductMixedSwapHomotopy X Y a b) =
      crossProductTriangle X Y 1 a b -
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) := by
  simpa only [ha, map_zero, LinearMap.zero_apply, add_zero] using
    crossProductMixedSwapHomotopy_boundary a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductTwoOneCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1 →ₗ[ℤ]
        SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (X × Y)) 3
    where
  toFun
    a :=
    { toFun
        b :=
        SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex (X × Y)) 3
          (crossProductTriangle X Y 1 a.1 b.1)
          (by
            change
              ((FirstHurewicz.singularComplex (X × Y)).d 3 2).hom
                  (crossProductTriangle X Y 1 a.1 b.1) =
                0
            simp only [crossProductTriangle_boundary,
              SingularMayerVietoris.ModuleHomology.cycle_condition
                  (FirstHurewicz.singularComplex X) 2 a,
              SingularMayerVietoris.ModuleHomology.cycle_condition
                  (FirstHurewicz.singularComplex Y) 1 b,
              map_zero, LinearMap.zero_apply, zero_add])
      map_add' b
        c := by
        apply Subtype.ext
        exact (crossProductTriangle X Y 1 a.1).map_add b.1 c.1
      map_smul' r
        b := by
        apply Subtype.ext
        exact (crossProductTriangle X Y 1 a.1).map_smul r b.1 }
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 3 => f c.1)
        ((crossProductTriangle X Y 1).map_add a.1 b.1)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 3 => f c.1)
        ((crossProductTriangle X Y 1).map_smul r a.1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.crossProductTwoOneCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1) :
    (crossProductTwoOneCycles X Y a b).1 = crossProductTriangle X Y 1 a.1 b.1 :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductHomologyTwoOne (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Y 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology (X × Y) 3 :=
  integerBilinearPostcompose (integerBilinearFlip (crossProductHomology Y X 2))
    (SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductHomologyTwoOne_apply (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 2)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    crossProductHomologyTwoOne X Y a b =
      SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3
        (crossProductHomology Y X 2 b a) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductHomologyTwoOne_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1) :
    crossProductHomologyTwoOne X Y
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) 1 b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (X × Y)) 3
        (crossProductTwoOneCycles X Y a b) := by
  rw [crossProductHomologyTwoOne_apply, crossProductHomology_cycleClass]
  change
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap ContinuousMap.prodSwap) 3).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (Y × X)) 3
          (crossProductCycles Y X 2 b a)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply Eq.symm
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (FirstHurewicz.singularComplex (X × Y)) 3 _ _).mpr
  refine ⟨crossProductMixedSwapHomotopy X Y a.1 b.1, ?_⟩
  simp only [crossProductTwoOneCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val,
    crossProductCycles_val]
  exact
    crossProductMixedSwapHomotopy_boundary_of_cycle a.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2 a)
      b.1

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductCycleClasses_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Z) 1) :
    (HomologicalComplex.homologyMap
            (FirstHurewicz.singularChainMap (Homeomorph.prodAssoc X Y Z : C(_, _))) 3).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex ((X × Y) × Z)) 3
          (crossProductTwoOneCycles (X × Y) Z (crossProductCycles X Y 1 a b) c)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (X × (Y × Z))) 3
        (crossProductCycles X (Y × Z) 2 a (crossProductCycles Y Z 1 b c)) := by
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (FirstHurewicz.singularComplex (X × (Y × Z))) 3 _ _).mpr
  refine ⟨crossProductAssociatorHomotopy X Y Z 1 a.1 b.1 c.1, ?_⟩
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, crossProductTwoOneCycles_val,
    crossProductCycles_val]
  exact
    crossProductAssociatorHomotopy_boundary_of_cycle 1 a.1 b.1 c.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex Z) 1 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductHomology_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc X Y Z : C(_, _)) 3
        (crossProductHomologyTwoOne (X × Y) Z (crossProductHomology X Y 1 a b) c) =
      crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Y) 1
      b
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Z) 1
      c
  rw [crossProductHomology_cycleClass, crossProductHomologyTwoOne_cycleClass,
    crossProductHomology_cycleClass, crossProductHomology_cycleClass]
  exact crossProductCycleClasses_associative a b c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductCyclicMap (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] : C(Y × (Z × X), X × (Y × Z)) :=
  ContinuousMap.prodSwap.comp ((Homeomorph.prodAssoc Y Z X).symm : C(_, _))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductCyclicMap_assoc_swap {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    (crossProductCyclicMap X Y Z).comp
        ((Homeomorph.prodAssoc Y Z X : C(_, _)).comp ContinuousMap.prodSwap) =
      ContinuousMap.id (X × (Y × Z)) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductHomology_cyclic {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c) =
      SingularMayerVietoris.singularHomologyMap (crossProductCyclicMap X Y Z) 3
        (crossProductHomology Y (Z × X) 2 b (crossProductHomology Z X 1 c a)) := by
  have h := crossProductHomology_associative b c a
  rw [crossProductHomologyTwoOne_apply] at h
  have h' :=
    congrArg (SingularMayerVietoris.singularHomologyMap (crossProductCyclicMap X Y Z) 3) h
  have hmap :
    (SingularMayerVietoris.singularHomologyMap (crossProductCyclicMap X Y Z) 3).comp
        ((SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc Y Z X : C(_, _)) 3).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.prodSwap : C(X × (Y × Z), (Y × Z) × X)) 3)) =
      LinearMap.id := by
    rw [← singularHomologyMap_comp, ← singularHomologyMap_comp, crossProductCyclicMap_assoc_swap,
      singularHomologyMap_id]
  exact
    (LinearMap.congr_fun hmap
          (crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c))).symm.trans
      h'

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomologyPontryagin.tripleProduct_cyclic (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c = tripleProduct G b c a := by
  rw [tripleProduct_eq_cross G a b c, tripleProduct_eq_cross G b c a,
    PeriodTorusHigherHomology.crossProductHomology_cyclic]
  have he : PeriodTorusHigherHomology.crossProductCyclicMap G G G = cyclicMap G G G := by
    apply ContinuousMap.ext
    intro p
    rfl
  rw [he]
  exact
    LinearMap.congr_fun (rightAddition_homology_cyclic G 3)
      (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 b
        (PeriodTorusHigherHomology.crossProductHomology G G 1 c a))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomologyPontryagin.tripleProduct_self12 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a b b = 0 := by
  rw [tripleProduct_apply, product11_self, map_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomologyPontryagin.tripleProduct_self02 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a b a = 0 :=
  (tripleProduct_cyclic G a b a).trans (tripleProduct_self12 G b a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomologyPontryagin.tripleProduct_self01 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a a b = 0 :=
  (tripleProduct_cyclic G a a b).trans (tripleProduct_self02 G a b)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomologyPontryagin.homologyAlternatingThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 3) (Fin 3) :=
  alternatingOfTrilinear (tripleProduct G) (tripleProduct_self01 G) (tripleProduct_self02 G)
    (tripleProduct_self12 G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomologyPontryagin.homologyWedgeThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^3 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 3 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingThree G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeThree_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 3 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeThree G (exteriorPower.ιMulti ℤ 3 v) = tripleProduct G (v 0) (v 1) (v 2) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomologyPontryagin.latticeWedgeThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 3 :=
  (homologyWedgeThree G).comp (exteriorPower.map 3 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (v : Fin 3 → Lattice) :
    latticeWedgeThree G c (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct G (c (v 0)) (c (v 1)) (c (v 2)) := by
  change homologyWedgeThree G (exteriorPower.map 3 c (exteriorPower.ιMulti ℤ 3 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeThree_apply_ιMulti]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 3).comp (latticeWedgeThree G c) =
      (latticeWedgeThree H d).comp (exteriorPower.map 3 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    SingularMayerVietoris.singularHomologyMap f 3
        (latticeWedgeThree G c (exteriorPower.ιMulti ℤ 3 v)) =
      latticeWedgeThree H d (exteriorPower.map 3 A (exteriorPower.ιMulti ℤ 3 v))
  rw [exteriorPower.map_apply_ιMulti, latticeWedgeThree_apply_ιMulti,
    latticeWedgeThree_apply_ιMulti]
  rw [tripleProduct_natural f hf, hmark, hmark, hmark]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomologyPontryagin.product11_mem_range_latticeWedgeTwo (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (a b : SingularMayerVietoris.SingularHomology G 1) :
    product11 G a b ∈ LinearMap.range (latticeWedgeTwo G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  refine ⟨exteriorPower.ιMulti ℤ 2 ![v, w], ?_⟩
  simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomologyPontryagin.tripleProduct_mem_range_latticeWedgeThree (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (a b d : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b d ∈ LinearMap.range (latticeWedgeThree G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  obtain ⟨u, rfl⟩ := hc d
  refine ⟨exteriorPower.ιMulti ℤ 3 ![v, w, u], ?_⟩
  simp

private theorem PeriodTorusHigherHomology.productTorusTopClass_two_is_product :
    ∃ a b : SingularMayerVietoris.SingularHomology (ProductTorus 2) 1,
      productTorusTopClass 2 =
        PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus 2) a b := by
  refine
    ⟨FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)),
      SingularMayerVietoris.singularHomologyMap (torusTailMap 1) 1 (productTorusTopClass 1), ?_⟩
  exact productTorusTopClass_succ_product 1

private theorem PeriodTorusHigherHomology.productTorusTopClass_three_is_tripleProduct :
    ∃ a b c : SingularMayerVietoris.SingularHomology (ProductTorus 3) 1,
      productTorusTopClass 3 =
        PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 3) a b c := by
  obtain ⟨a, b, hab⟩ := productTorusTopClass_two_is_product
  refine
    ⟨FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)),
      SingularMayerVietoris.singularHomologyMap (torusTailMap 2) 1 a,
      SingularMayerVietoris.singularHomologyMap (torusTailMap 2) 1 b, ?_⟩
  rw [PeriodTorusHigherHomologyPontryagin.tripleProduct_apply,
    productTorusTopClass_succ_product 2, hab,
    PeriodTorusHigherHomologyPontryagin.product_natural (torusTailMap 2) (torusTailMap_add 2) 1]

private theorem PeriodTorusHigherHomology.map_topClass_two_mem_range_latticeWedgeTwo {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 2, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 2 (productTorusTopClass 2) ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c) := by
  obtain ⟨a, b, hab⟩ := productTorusTopClass_two_is_product
  rw [hab, PeriodTorusHigherHomologyPontryagin.product_natural f hf 1]
  exact PeriodTorusHigherHomologyPontryagin.product11_mem_range_latticeWedgeTwo G c hc _ _

private theorem PeriodTorusHigherHomology.map_topClass_three_mem_range_latticeWedgeThree {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 3, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 3 (productTorusTopClass 3) ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c) := by
  obtain ⟨a, b, d, habd⟩ := productTorusTopClass_three_is_tripleProduct
  rw [habd, PeriodTorusHigherHomologyPontryagin.tripleProduct_natural f hf]
  exact PeriodTorusHigherHomologyPontryagin.tripleProduct_mem_range_latticeWedgeThree G c hc _ _ _

private def PeriodTorusHigherHomology.omitHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin n) ℤ :=
  Fin.cons 0 A

private def PeriodTorusHigherHomology.takeHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i))

private theorem PeriodTorusHigherHomology.torusMatrixMap_omitHeadMatrix {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (x : ProductTorus n) :
    torusMatrixMap (omitHeadMatrix A) x = Fin.cons 0 (torusMatrixMap A x) := by
  have hzero (j : Fin n) : omitHeadMatrix A 0 j = 0 := rfl
  have hsucc (i : Fin r) (j : Fin n) : omitHeadMatrix A i.succ j = A i j := rfl
  funext i
  change (∑ j, omitHeadMatrix A i j • x j) = _
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [hzero]
  · simp [hsucc]

private theorem PeriodTorusHigherHomology.torusMatrixMap_takeHeadMatrix {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (x : ProductTorus (n + 1)) :
    torusMatrixMap (takeHeadMatrix A) x = Fin.cons (x 0) (torusMatrixMap A (fun k => x k.succ)) :=
  by
  funext i
  change (∑ j, takeHeadMatrix A i j • x j) = _
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [takeHeadMatrix, Fin.sum_univ_succ]
  · simp [takeHeadMatrix, Fin.sum_univ_succ]

@[simp]
private theorem PeriodTorusHigherHomology.torusMatrixMap_zero_source {r : ℕ}
    (A : Matrix (Fin r) (Fin 0) ℤ) : torusMatrixMap A = ContinuousMap.const (ProductTorus 0) 0 := by
  apply ContinuousMap.ext
  intro x
  funext i
  simp

private def PeriodTorusHigherHomology.coordinateTorusMap :
    (r n : ℕ) → Fin (r.choose n) → C(ProductTorus n, ProductTorus r)
  | 0, 0, _ => ContinuousMap.const _ 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => ContinuousMap.const _ 0
  | r + 1, n + 1, i =>
    match binomialPascalIndexEquiv r n i with
    | Sum.inl j =>
      ((productTorusSuccHomeomorph r).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r,
              ProductTorus (r + 1))).comp
        ((CircleTopology.productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j))
    | Sum.inr j =>
      ((productTorusSuccHomeomorph r).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r,
              ProductTorus (r + 1))).comp
        ((circleProductMap (coordinateTorusMap r n j)).comp
          (productTorusSuccHomeomorph n :
            C(ProductTorus (n + 1),
              (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus n)))

@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateTorusMap_degree_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusMap r 0 i = ContinuousMap.const _ 0 := by cases r <;> rfl

@[simp]
private theorem PeriodTorusHigherHomology.coordinateTorusMap_omit_apply (r n : ℕ)
    (j : Fin (r.choose (n + 1))) (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x =
      Fin.cons 0 (coordinateTorusMap r (n + 1) j x) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateTorusMap_take_apply (r n : ℕ) (j : Fin (r.choose n))
    (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x =
      Fin.cons (x 0) (coordinateTorusMap r n j (fun k => x k.succ)) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

private theorem
    PeriodTorusHigherHomology.coordinateTorusMap_omit (r n : ℕ) (j : Fin (r.choose (n + 1))) :
    (productTorusSuccHomeomorph r :
            C(ProductTorus (r + 1),
              (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j))) =
      (CircleTopology.productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j) := by
  apply ContinuousMap.ext
  intro x
  change
    productTorusSuccHomeomorph r
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x) =
      _
  rw [coordinateTorusMap_omit_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

private theorem PeriodTorusHigherHomology.coordinateTorusMap_take (r n : ℕ) (j : Fin (r.choose n)) :
    (productTorusSuccHomeomorph r :
            C(ProductTorus (r + 1),
              (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j))) =
      (circleProductMap (coordinateTorusMap r n j)).comp
        (productTorusSuccHomeomorph n :
          C(ProductTorus (n + 1),
            (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus n)) := by
  apply ContinuousMap.ext
  intro x
  change
    productTorusSuccHomeomorph r
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x) =
      _
  rw [coordinateTorusMap_take_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

private def PeriodTorusHigherHomology.coordinateTorusMatrix :
    (r n : ℕ) → Fin (r.choose n) → Matrix (Fin r) (Fin n) ℤ
  | 0, 0, _ => 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => 0
  | r + 1, n + 1, i =>
    match binomialPascalIndexEquiv r n i with
    | Sum.inl j => omitHeadMatrix (coordinateTorusMatrix r (n + 1) j)
    | Sum.inr j => takeHeadMatrix (coordinateTorusMatrix r n j)

@[simp]
private theorem PeriodTorusHigherHomology.coordinateTorusMatrix_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) =
      omitHeadMatrix (coordinateTorusMatrix r (n + 1) j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateTorusMatrix_take (r n : ℕ) (j : Fin (r.choose n)) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) =
      takeHeadMatrix (coordinateTorusMatrix r n j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

private theorem PeriodTorusHigherHomology.coordinateTorusMap_eq_torusMatrixMap (r n : ℕ)
    (i : Fin (r.choose n)) :
    coordinateTorusMap r n i = torusMatrixMap (coordinateTorusMatrix r n i) := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => rw [coordinateTorusMap_degree_zero, torusMatrixMap_zero_source]
    | succ n => exact Fin.elim0 i
  | succ r ih =>
    cases n with
    | zero => rw [coordinateTorusMap_degree_zero, torusMatrixMap_zero_source]
    | succ n =>
      obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
      cases j with
      | inl j =>
        apply ContinuousMap.ext
        intro x
        rw [coordinateTorusMap_omit_apply, coordinateTorusMatrix_omit,
          torusMatrixMap_omitHeadMatrix, ih (n + 1) j]
      | inr j =>
        apply ContinuousMap.ext
        intro x
        rw [coordinateTorusMap_take_apply, coordinateTorusMatrix_take,
          torusMatrixMap_takeHeadMatrix, ih n j]

private def PeriodTorusHigherHomology.coordinateTorusClass (r n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r n i) n (productTorusTopClass n)

@[simp]
private theorem PeriodTorusHigherHomology.coordinateTorusClass_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusClass r 0 i = pointClass (0 : ProductTorus r) := by
  rw [coordinateTorusClass, productTorusTopClass_zero, singularHomologyMap_pointClass,
    coordinateTorusMap_degree_zero]
  rfl

private theorem PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1)))
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))
          (n + 1) a) =
      circleSectionHomology (ProductTorus r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r (n + 1) j) (n + 1) a) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (productTorusSuccHomeomorph r :
                C(ProductTorus (r + 1),
                  (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r))
              (n + 1)).comp
          (SingularMayerVietoris.singularHomologyMap
            (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))
            (n + 1)))
        a =
      _
  rw [← singularHomologyMap_comp, coordinateTorusMap_omit, singularHomologyMap_comp]
  rfl

private theorem PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_take (r n : ℕ)
    (j : Fin (r.choose n))
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))
          (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap (circleProductMap (coordinateTorusMap r n j))
        (n + 1) (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1) a) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (productTorusSuccHomeomorph r :
                C(ProductTorus (r + 1),
                  (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r))
              (n + 1)).comp
          (SingularMayerVietoris.singularHomologyMap
            (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))
            (n + 1)))
        a =
      _
  rw [← singularHomologyMap_comp, coordinateTorusMap_take, singularHomologyMap_comp]
  rfl

private theorem PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))) =
      (coordinateTorusClass r (n + 1) j, 0) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_omit, circleProductHomologyEquiv_section]

private theorem PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_take (r n : ℕ)
    (j : Fin (r.choose n)) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))) =
      (0, coordinateTorusClass r n j) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_take, circleProductHomologyEquiv_naturality,
    productTorusTopClass_succ_coordinates, map_zero]

private theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_pair (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      ((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
          (productTorusHomologyEquiv r n).toAddEquiv)
        (circleProductHomologyEquiv (ProductTorus r) n
          (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)) :=
  productTorusHomologyEquiv_succ_apply r n a

private theorem
    PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass_zero (r : ℕ)
    (i : Fin (r.choose 0)) :
    productTorusHomologyEquiv r 0 (coordinateTorusClass r 0 i) = Pi.single i 1 := by
  rw [coordinateTorusClass_zero, productTorusHomologyEquiv_zero]
  change
    integerBinomialZeroEquiv r
        (connectedHomologyZeroEquiv (ProductTorus r) (pointClass (0 : ProductTorus r))) =
      _
  rw [connectedHomologyZeroEquiv_pointClass]
  exact integerBinomialZeroEquiv_one_single r i

private theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass (r n : ℕ)
    (i : Fin (r.choose n)) :
    productTorusHomologyEquiv r n (coordinateTorusClass r n i) = Pi.single i 1 := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero 0 i
    | succ n => exact Fin.elim0 i
  | succ r ih =>
    cases n with
    | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero (r + 1) i
    | succ n =>
      obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
      cases j with
      | inl j =>
        apply (binomialModuleSuccEquiv r n).injective
        rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_omit,
          binomialModuleSuccEquiv_single_inl]
        change
          (productTorusHomologyEquiv r (n + 1) (coordinateTorusClass r (n + 1) j),
              productTorusHomologyEquiv r n 0) =
            (Pi.single j 1, 0)
        rw [ih (n + 1) j, map_zero]
      | inr j =>
        apply (binomialModuleSuccEquiv r n).injective
        rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_take,
          binomialModuleSuccEquiv_single_inr]
        change
          (productTorusHomologyEquiv r (n + 1) 0,
              productTorusHomologyEquiv r n (coordinateTorusClass r n j)) =
            (0, Pi.single j 1)
        rw [map_zero, ih n j]

private def PeriodTorusHigherHomology.coordinateTorusBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ
      (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  (binomialCoordinateBasis r n).map (productTorusHomologyEquiv r n).symm

@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateTorusBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasis r n i = coordinateTorusClass r n i := by
  apply (productTorusHomologyEquiv r n).injective
  rw [coordinateTorusBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    binomialCoordinateBasis_apply, productTorusHomologyEquiv_coordinateTorusClass]

private def PeriodTorusHigherHomology.realTorusHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n ≃ₗ[ℤ] binomialModule 4 n :=
  (homeomorphHomologyEquiv flatTorusCircleHomeomorph n).trans (productTorusHomologyEquiv 4 n)

private def PeriodTorusHigherHomology.periodTorusHomologyEquiv (p : PeriodDomain) (n : ℕ) :
    SingularMayerVietoris.SingularHomology p.Torus n ≃ₗ[ℤ] binomialModule 4 n :=
  (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) n).trans
    (productTorusHomologyEquiv 4 n)

@[simp]
private theorem PeriodTorusHigherHomology.realTorusHomologyEquiv_apply (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    realTorusHomologyEquiv n a =
      productTorusHomologyEquiv 4 n
        (SingularMayerVietoris.singularHomologyMap
          (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n a) :=
  rfl

private theorem PeriodTorusHigherHomology.realTorus_homology_free (n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) :=
  Module.Free.of_equiv (realTorusHomologyEquiv n).symm

private theorem PeriodTorusHigherHomology.realTorus_homology_finite (n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) :=
  Module.Finite.of_surjective (realTorusHomologyEquiv n).symm.toLinearMap
    (realTorusHomologyEquiv n).symm.surjective

private theorem PeriodTorusHigherHomology.realTorus_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) = Nat.choose 4 n := by
  rw [(realTorusHomologyEquiv n).finrank_eq]
  exact binomialModule_finrank 4 n

private theorem PeriodTorusHigherHomology.realTorus_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) := by
  let := realTorus_homology_free n
  infer_instance

public
theorem PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology RealTorus₄ n) := by
  let := binomialModule_subsingleton_of_lt hn
  exact (realTorusHomologyEquiv n).injective.subsingleton

private theorem PeriodTorusHigherHomology.periodTorus_homology_subsingleton_of_lt (p : PeriodDomain)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularMayerVietoris.SingularHomology p.Torus n) := by
  let := binomialModule_subsingleton_of_lt hn
  exact (periodTorusHomologyEquiv p n).injective.subsingleton

private def PeriodTorusHigherHomology.realTorusH4Equiv :
    SingularMayerVietoris.SingularHomology RealTorus₄ 4 ≃ₗ[ℤ] ℤ :=
  (realTorusHomologyEquiv 4).trans (integerBinomialZeroEquiv 4).symm

private def
    PeriodTorusHigherHomology.coordinateTorusMapAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) : C(ProductTorus n, X) :=
  (e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)

private def
    PeriodTorusHigherHomology.coordinateTorusClassAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMapAlong e n i) n
    (productTorusTopClass n)

private def
    PeriodTorusHigherHomology.coordinateTorusBasisAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (SingularMayerVietoris.SingularHomology X n) :=
  (coordinateTorusBasis r n).map (homeomorphHomologyEquiv e n).symm

@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateTorusBasisAlong_apply {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasisAlong e n i = coordinateTorusClassAlong e n i := by
  rw [coordinateTorusBasisAlong, Module.Basis.map_apply, coordinateTorusBasis_apply,
    homeomorphHomologyEquiv_symm_apply]
  change
    SingularMayerVietoris.singularHomologyMap (e.symm : C(ProductTorus r, X)) n
        (SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r n i) n
          (productTorusTopClass n)) =
      SingularMayerVietoris.singularHomologyMap
        ((e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)) n
        (productTorusTopClass n)
  rw [singularHomologyMap_comp]
  rfl

private theorem
    PeriodTorusHigherHomology.coordinateTorusBasisAlong_coe {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    ⇑(coordinateTorusBasisAlong e n) = coordinateTorusClassAlong e n :=
  funext (coordinateTorusBasisAlong_apply e n)

private theorem
    PeriodTorusHigherHomology.coordinateTorusClassAlong_span {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Submodule.span ℤ (Set.range (coordinateTorusClassAlong e n)) = ⊤ := by
  simpa only [coordinateTorusBasisAlong_coe] using (coordinateTorusBasisAlong e n).span_eq

private theorem
    PeriodTorusHigherHomology.surjective_of_coordinateTorusClassAlong_mem_range {X : Type}
    [TopologicalSpace X] {r : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (f : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hf : ∀ i : Fin (r.choose n), coordinateTorusClassAlong e n i ∈ LinearMap.range f) :
    Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← coordinateTorusClassAlong_span e n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hf i

@[simp]
private theorem
    PeriodTorusHigherHomology.torusMatrixMap_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x y : ProductTorus n) : torusMatrixMap A (x + y) = torusMatrixMap A x + torusMatrixMap A y :=
  (torusMatrixLinearMap A).map_add x y

@[simp]
private theorem PeriodTorusHigherHomology.coordinateTorusMap_add (r n : ℕ) (i : Fin (r.choose n))
    (x y : ProductTorus n) :
    coordinateTorusMap r n i (x + y) = coordinateTorusMap r n i x + coordinateTorusMap r n i y := by
  simpa only [coordinateTorusMap_eq_torusMatrixMap] using
    torusMatrixMap_add (coordinateTorusMatrix r n i) x y

private theorem
    PeriodTorusHigherHomology.homeomorph_symm_add_of_add {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Add X] [Add Y] (e : X ≃ₜ Y) (he : ∀ x y, e (x + y) = e x + e y)
    (x y : Y) : e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

private theorem
    PeriodTorusHigherHomology.coordinateTorusMapAlong_add {X : Type} [TopologicalSpace X]
    [Add X] {r : ℕ} (e : X ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y) (n : ℕ)
    (i : Fin (r.choose n)) (x y : ProductTorus n) :
    coordinateTorusMapAlong e n i (x + y) =
      coordinateTorusMapAlong e n i x + coordinateTorusMapAlong e n i y := by
  change
    e.symm (coordinateTorusMap r n i (x + y)) =
      e.symm (coordinateTorusMap r n i x) + e.symm (coordinateTorusMap r n i y)
  rw [coordinateTorusMap_add]
  exact homeomorph_symm_add_of_add e he _ _

private def PeriodTorusHigherHomologyExterior.standardExteriorBasis (m n : ℕ) :
    Module.Basis (Set.powersetCard (Fin m) n) ℤ (⋀[ℤ]^n (Fin m → ℤ)) :=
  (Pi.basisFun ℤ (Fin m)).exteriorPower n

private theorem PeriodTorusHigherHomologyExterior.standardExterior_map_coefficient (m n : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) (s t : Set.powersetCard (Fin m) n) :
    (standardExteriorBasis m n).repr
        (exteriorPower.map n A.mulVecLin (standardExteriorBasis m n t)) s =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  unfold standardExteriorBasis
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti]
  have hmatrix :
    (Matrix.of fun i j =>
        (Pi.basisFun ℤ (Fin m)).coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
          ((A.mulVecLin ∘ ((Pi.basisFun ℤ (Fin m)) ∘ Set.powersetCard.ofFinEmbEquiv.symm t)) i)) =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).transpose := by
    ext i j
    simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr, Function.comp_apply,
      Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [hmatrix, Matrix.det_transpose]

private abbrev PeriodTorusHigherHomologyExterior.latticeExterior (n : ℕ) :=
  ⋀[ℤ]^n Lattice

private def PeriodTorusHigherHomologyExterior.latticeBasis : Module.Basis (Fin 4) ℤ Lattice :=
  Pi.basisFun ℤ (Fin 4)

private def PeriodTorusHigherHomologyExterior.latticeExteriorBasis (n : ℕ) :
    Module.Basis (Set.powersetCard (Fin 4) n) ℤ (latticeExterior n) :=
  standardExteriorBasis 4 n

private theorem PeriodTorusHigherHomologyExterior.pairIndices_strictMono (i : Fin 6) :
    StrictMono (LocalSystemMatrices.pairIndices i) := by fin_cases i <;> decide

private theorem PeriodTorusHigherHomologyExterior.tripleIndices_strictMono (i : Fin 4) :
    StrictMono (LocalSystemMatrices.tripleIndices i) := by fin_cases i <;> decide

private theorem PeriodTorusHigherHomologyExterior.pairIndices_injective :
    Function.Injective LocalSystemMatrices.pairIndices := by decide

private theorem PeriodTorusHigherHomologyExterior.tripleIndices_injective :
    Function.Injective LocalSystemMatrices.tripleIndices := by decide

private def PeriodTorusHigherHomologyExterior.pairEmbedding (i : Fin 6) : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (LocalSystemMatrices.pairIndices i) (pairIndices_strictMono i)

private def PeriodTorusHigherHomologyExterior.tripleEmbedding (i : Fin 4) : Fin 3 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (LocalSystemMatrices.tripleIndices i) (tripleIndices_strictMono i)

private def PeriodTorusHigherHomologyExterior.pairSubset (i : Fin 6) : Set.powersetCard (Fin 4) 2 :=
  Set.powersetCard.ofFinEmbEquiv (pairEmbedding i)

private def
    PeriodTorusHigherHomologyExterior.tripleSubset (i : Fin 4) : Set.powersetCard (Fin 4) 3 :=
  Set.powersetCard.ofFinEmbEquiv (tripleEmbedding i)

@[simp]
private theorem PeriodTorusHigherHomologyExterior.pairSubset_ordered (i : Fin 6) :
    (Set.powersetCard.ofFinEmbEquiv.symm (pairSubset i) : Fin 2 → Fin 4) =
      LocalSystemMatrices.pairIndices i := by
  rw [pairSubset, Equiv.symm_apply_apply]
  rfl

@[simp]
private theorem PeriodTorusHigherHomologyExterior.tripleSubset_ordered (i : Fin 4) :
    (Set.powersetCard.ofFinEmbEquiv.symm (tripleSubset i) : Fin 3 → Fin 4) =
      LocalSystemMatrices.tripleIndices i := by
  rw [tripleSubset, Equiv.symm_apply_apply]
  rfl

private theorem
    PeriodTorusHigherHomologyExterior.pairSubset_injective : Function.Injective pairSubset := by
  intro i j hij
  apply pairIndices_injective
  simpa only [pairSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 2 → Fin 4)) hij

private theorem PeriodTorusHigherHomologyExterior.tripleSubset_injective :
    Function.Injective tripleSubset := by
  intro i j hij
  apply tripleIndices_injective
  simpa only [tripleSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 3 → Fin 4)) hij

private theorem
    PeriodTorusHigherHomologyExterior.pairSubset_bijective : Function.Bijective pairSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨pairSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 4 2 = 6 by decide] using
    (Set.powersetCard.card (Fin 4) 2).symm

private theorem PeriodTorusHigherHomologyExterior.tripleSubset_bijective :
    Function.Bijective tripleSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨tripleSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 4 3 = 4 by decide] using
    (Set.powersetCard.card (Fin 4) 3).symm

private def
    PeriodTorusHigherHomologyExterior.pairSubsetEquiv : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective pairSubset pairSubset_bijective

private def
    PeriodTorusHigherHomologyExterior.tripleSubsetEquiv : Fin 4 ≃ Set.powersetCard (Fin 4) 3 :=
  Equiv.ofBijective tripleSubset tripleSubset_bijective

private def
    PeriodTorusHigherHomologyExterior.squareBasis : Module.Basis (Fin 6) ℤ (latticeExterior 2) :=
  (latticeExteriorBasis 2).reindex pairSubsetEquiv.symm

private def
    PeriodTorusHigherHomologyExterior.cubeBasis : Module.Basis (Fin 4) ℤ (latticeExterior 3) :=
  (latticeExteriorBasis 3).reindex tripleSubsetEquiv.symm

private theorem PeriodTorusHigherHomologyExterior.squareBasis_apply (i : Fin 6) :
    squareBasis i = exteriorPower.ιMulti ℤ 2 (latticeBasis ∘ LocalSystemMatrices.pairIndices i) :=
  by
  rw [squareBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 4)).exteriorPower 2 (pairSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, pairSubset_ordered]
  rfl

private theorem PeriodTorusHigherHomologyExterior.cubeBasis_apply (i : Fin 4) :
    cubeBasis i = exteriorPower.ιMulti ℤ 3 (latticeBasis ∘ LocalSystemMatrices.tripleIndices i) :=
  by
  rw [cubeBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 4)).exteriorPower 3 (tripleSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, tripleSubset_ordered]
  rfl

private def
    PeriodTorusHigherHomologyExterior.squareCoordinates : latticeExterior 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  squareBasis.equivFun

private def
    PeriodTorusHigherHomologyExterior.cubeCoordinates : latticeExterior 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  cubeBasis.equivFun

@[simp]
private theorem PeriodTorusHigherHomologyExterior.squareCoordinates_apply (x : latticeExterior 2)
    (i : Fin 6) : squareCoordinates x i = squareBasis.repr x i :=
  congrFun (squareBasis.equivFun_apply x) i

@[simp]
private theorem PeriodTorusHigherHomologyExterior.cubeCoordinates_apply (x : latticeExterior 3)
    (i : Fin 4) : cubeCoordinates x i = cubeBasis.repr x i :=
  congrFun (cubeBasis.equivFun_apply x) i

private theorem PeriodTorusHigherHomologyExterior.latticeExterior_finrank (n : ℕ) :
    Module.finrank ℤ (latticeExterior n) = Nat.choose 4 n := by
  rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis latticeBasis, Fintype.card_fin]

private theorem
    PeriodTorusHigherHomology.coordinateTorusClassAlong_mem_range_latticeWedgeTwo {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 2)) :
    coordinateTorusClassAlong e 2 i ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c) :=
  map_topClass_two_mem_range_latticeWedgeTwo c hc (coordinateTorusMapAlong e 2 i)
    (coordinateTorusMapAlong_add e he 2 i)

private theorem
    PeriodTorusHigherHomology.coordinateTorusClassAlong_mem_range_latticeWedgeThree {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 3)) :
    coordinateTorusClassAlong e 3 i ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c) :=
  map_topClass_three_mem_range_latticeWedgeThree c hc (coordinateTorusMapAlong e 3 i)
    (coordinateTorusMapAlong_add e he 3 i)

private theorem PeriodTorusHigherHomology.latticeWedgeTwo_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 2
    (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c)
    (coordinateTorusClassAlong_mem_range_latticeWedgeTwo e he c hc)

private theorem PeriodTorusHigherHomology.latticeWedgeThree_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 3
    (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c)
    (coordinateTorusClassAlong_mem_range_latticeWedgeThree e he c hc)

private def PeriodTorusHigherHomologyExterior.exteriorMap (n : ℕ) (T : LatticeMatrix) :
    latticeExterior n →ₗ[ℤ] latticeExterior n :=
  exteriorPower.map n T.mulVecLin

private theorem PeriodTorusHigherHomologyExterior.squareMap_coefficient (T : LatticeMatrix)
    (i j : Fin 6) :
    squareBasis.repr (exteriorMap 2 T (squareBasis j)) i =
      LocalSystemMatrices.exteriorSquare T i j := by
  rw [squareBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change
    (standardExteriorBasis 4 2).repr
        (exteriorPower.map 2 T.mulVecLin (standardExteriorBasis 4 2 (pairSubset j)))
        (pairSubset i) =
      _
  rw [standardExterior_map_coefficient, pairSubset_ordered, pairSubset_ordered]
  rfl

private theorem
    PeriodTorusHigherHomologyExterior.cubeMap_coefficient (T : LatticeMatrix) (i j : Fin 4) :
    cubeBasis.repr (exteriorMap 3 T (cubeBasis j)) i = LocalSystemMatrices.exteriorCube T i j := by
  rw [cubeBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change
    (standardExteriorBasis 4 3).repr
        (exteriorPower.map 3 T.mulVecLin (standardExteriorBasis 4 3 (tripleSubset j)))
        (tripleSubset i) =
      _
  rw [standardExterior_map_coefficient, tripleSubset_ordered, tripleSubset_ordered]
  rfl

private theorem PeriodTorusHigherHomologyExterior.squareMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix squareBasis squareBasis (exteriorMap 2 T) =
      LocalSystemMatrices.exteriorSquare T := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact squareMap_coefficient T i j

private theorem PeriodTorusHigherHomologyExterior.cubeMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix cubeBasis cubeBasis (exteriorMap 3 T) =
      LocalSystemMatrices.exteriorCube T := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact cubeMap_coefficient T i j

private theorem PeriodTorusHigherHomologyExterior.squareCoordinates_map (T : LatticeMatrix)
    (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 T x) =
      LocalSystemMatrices.exteriorSquare T *ᵥ squareCoordinates x := by
  have h := LinearMap.toMatrix_mulVec_repr squareBasis squareBasis (exteriorMap 2 T) x
  rw [squareMap_toMatrix] at h
  simpa only [squareCoordinates, Module.Basis.equivFun_apply] using h.symm

private theorem PeriodTorusHigherHomologyExterior.cubeCoordinates_map (T : LatticeMatrix)
    (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 T x) =
      LocalSystemMatrices.exteriorCube T *ᵥ cubeCoordinates x := by
  have h := LinearMap.toMatrix_mulVec_repr cubeBasis cubeBasis (exteriorMap 3 T) x
  rw [cubeMap_toMatrix] at h
  simpa only [cubeCoordinates, Module.Basis.equivFun_apply] using h.symm

private def PeriodTorusHigherHomology.coordinateH1Add (n : ℕ) :
    (Fin n → ℤ) →+ FirstHurewicz.SingularH1 (ProductTorus n)
    where
  toFun v := ∑ i, v i • FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1))
  map_zero' := by simp only [Pi.zero_apply, zero_zsmul, Finset.sum_const_zero]
  map_add' v w := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

private def PeriodTorusHigherHomology.coordinateH1 (n : ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] FirstHurewicz.SingularH1 (ProductTorus n) :=
  { toFun := coordinateH1Add n
    map_add' := (coordinateH1Add n).map_add
    map_smul' r
      a := by
      convert! (coordinateH1Add n).map_zsmul r a using 1
      exact int_smul_eq_zsmul .. }

private theorem PeriodTorusHigherHomology.coordinateH1_basis (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.basisFun ℤ (Fin n) i) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simp [coordinateH1, coordinateH1Add, Pi.basisFun_apply, Pi.single_apply]

@[simp]
private theorem PeriodTorusHigherHomology.coordinateH1_single (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.single i 1) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simpa only [Pi.basisFun_apply] using coordinateH1_basis n i

private theorem PeriodTorusHigherHomology.coordinateH1_four_eq_periodMarking (p : PeriodDomain) :
    coordinateH1 4 =
      (FirstHurewicz.inducedHomology (periodTorusCircleHomeomorph p : C(_, _))).comp
        p.singularH1Equiv.symm.toLinearMap := by
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro i
  rw [coordinateH1_basis, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [p.singularH1Equiv_symm_apply, periodTorusCircle_inducedHomology_periodLoop]
  simp only [Pi.basisFun_apply]

private theorem PeriodTorusHigherHomology.coordinateH1_four_apply (p : PeriodDomain) (v : Lattice) :
    coordinateH1 4 v = FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 v) := by
  rw [coordinateH1_four_eq_periodMarking p, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [p.singularH1Equiv_symm_apply, periodTorusCircle_inducedHomology_periodLoop]

private theorem PeriodTorusHigherHomology.coordinateH1_four_bijective (p : PeriodDomain) :
    Function.Bijective (coordinateH1 4) := by
  rw [coordinateH1_four_eq_periodMarking p]
  exact
    (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) 1).bijective.comp
      p.singularH1Equiv.symm.bijective

private def PeriodTorusHigherHomology.coordinateH1FourEquiv (p : PeriodDomain) :
    Lattice ≃ₗ[ℤ] FirstHurewicz.SingularH1 (ProductTorus 4) :=
  LinearEquiv.ofBijective (coordinateH1 4) (coordinateH1_four_bijective p)

private theorem PeriodTorusHigherHomology.coordinateH1_matrix_natural (p : PeriodDomain)
    (A : LatticeMatrix) (v : Lattice) :
    FirstHurewicz.inducedHomology (torusMatrixMap A) (coordinateH1 4 v) =
      coordinateH1 4 (A *ᵥ v) := by
  rw [coordinateH1_four_apply p, coordinateH1_four_apply p,
    torusMatrixMap_coordinatePeriodHomology]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.coordinateTorusWedgeTwo :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 := by
  letI := productTorus_homology_torsionFree 4 2
  exact PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo (ProductTorus 4) (coordinateH1 4)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.coordinateTorusWedgeThree :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 := by
  letI := productTorus_homology_torsionFree 4 2
  exact PeriodTorusHigherHomologyPontryagin.latticeWedgeThree (ProductTorus 4) (coordinateH1 4)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti (v : Fin 2 → Lattice) :
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus 4) (coordinateH1 4 (v 0))
        (coordinateH1 4 (v 1)) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_apply_ιMulti (ProductTorus 4)
      (coordinateH1 4) v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateTorusWedgeThree_apply_ιMulti (v : Fin 3 → Lattice) :
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 4) (coordinateH1 4 (v 0))
        (coordinateH1 4 (v 1)) (coordinateH1 4 (v 2)) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_apply_ιMulti (ProductTorus 4)
      (coordinateH1 4) v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti_periodLoops
    (p : PeriodDomain) (v : Fin 2 → Lattice) :
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus 4)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 1))) := by
  rw [coordinateTorusWedgeTwo_apply_ιMulti, coordinateH1_four_apply p, coordinateH1_four_apply p]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_apply_ιMulti_periodLoops
    (p : PeriodDomain) (v : Fin 3 → Lattice) :
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 4)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 2))) := by
  rw [coordinateTorusWedgeThree_apply_ιMulti, coordinateH1_four_apply p,
    coordinateH1_four_apply p, coordinateH1_four_apply p]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_matrix (p : PeriodDomain)
    (A : LatticeMatrix) :
    (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2).comp
        coordinateTorusWedgeTwo =
      coordinateTorusWedgeTwo.comp (exteriorPower.map 2 A.mulVecLin) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_natural (torusMatrixMap A)
      (fun x y => (torusMatrixLinearMap A).map_add x y) (coordinateH1 4) (coordinateH1 4)
      A.mulVecLin (coordinateH1_matrix_natural p A)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_matrix (p : PeriodDomain)
    (A : LatticeMatrix) :
    (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3).comp
        coordinateTorusWedgeThree =
      coordinateTorusWedgeThree.comp (exteriorPower.map 3 A.mulVecLin) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_natural (torusMatrixMap A)
      (fun x y => (torusMatrixLinearMap A).map_add x y) (coordinateH1 4) (coordinateH1 4)
      A.mulVecLin (coordinateH1_matrix_natural p A)

private theorem PeriodTorusHigherHomology.coordinateH1_four_surjective :
    Function.Surjective (coordinateH1 4) :=
  (coordinateH1_four_bijective (Elliptic.examplePeriod .four)).surjective

private theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_surjective :
    Function.Surjective coordinateTorusWedgeTwo := by
  let := productTorus_homology_torsionFree 4 2
  exact
    latticeWedgeTwo_surjective_of_torusHomeomorph (Homeomorph.refl (ProductTorus 4))
      (fun _ _ => rfl) (coordinateH1 4) coordinateH1_four_surjective

private theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_surjective :
    Function.Surjective coordinateTorusWedgeThree := by
  let := productTorus_homology_torsionFree 4 2
  exact
    latticeWedgeThree_surjective_of_torusHomeomorph (Homeomorph.refl (ProductTorus 4))
      (fun _ _ => rfl) (coordinateH1 4) coordinateH1_four_surjective

private theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_bijective :
    Function.Bijective coordinateTorusWedgeTwo := by
  let := productTorus_homology_free 4 2
  let := productTorus_homology_finite 4 2
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le coordinateTorusWedgeTwo
      coordinateTorusWedgeTwo_surjective
  rw [PeriodTorusHigherHomologyExterior.latticeExterior_finrank, productTorus_homology_finrank]

private theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_bijective :
    Function.Bijective coordinateTorusWedgeThree := by
  let := productTorus_homology_free 4 3
  let := productTorus_homology_finite 4 3
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le coordinateTorusWedgeThree
      coordinateTorusWedgeThree_surjective
  rw [PeriodTorusHigherHomologyExterior.latticeExterior_finrank, productTorus_homology_finrank]

private def PeriodTorusHigherHomology.coordinateTorusWedgeTwoEquiv :
    PeriodTorusHigherHomologyExterior.latticeExterior 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 :=
  LinearEquiv.ofBijective coordinateTorusWedgeTwo coordinateTorusWedgeTwo_bijective

private def PeriodTorusHigherHomology.coordinateTorusWedgeThreeEquiv :
    PeriodTorusHigherHomologyExterior.latticeExterior 3 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 :=
  LinearEquiv.ofBijective coordinateTorusWedgeThree coordinateTorusWedgeThree_bijective

private def PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 ≃ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 2 :=
  coordinateTorusWedgeTwoEquiv.symm

private def PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 ≃ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 3 :=
  coordinateTorusWedgeThreeEquiv.symm

@[simp]
private theorem PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_wedge
    (v : PeriodTorusHigherHomologyExterior.latticeExterior 2) :
    coordinateTorusH2ExteriorEquiv (coordinateTorusWedgeTwo v) = v :=
  coordinateTorusWedgeTwoEquiv.symm_apply_apply v

@[simp]
private theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_wedge
    (v : PeriodTorusHigherHomologyExterior.latticeExterior 3) :
    coordinateTorusH3ExteriorEquiv (coordinateTorusWedgeThree v) = v :=
  coordinateTorusWedgeThreeEquiv.symm_apply_apply v

private theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_symm_ιMulti
    (v : Fin 3 → Lattice) :
    coordinateTorusH3ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 4)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 2))) :=
  coordinateTorusWedgeThree_apply_ιMulti_periodLoops (Elliptic.examplePeriod .four) v

private theorem PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a) =
      exteriorPower.map 2 A.mulVecLin (coordinateTorusH2ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := coordinateTorusWedgeTwo_surjective a
  have h :=
    LinearMap.congr_fun (coordinateTorusWedgeTwo_matrix (Elliptic.examplePeriod .four) A) v
  change
    SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 (coordinateTorusWedgeTwo v) =
      coordinateTorusWedgeTwo (exteriorPower.map 2 A.mulVecLin v) at h
  rw [h, coordinateTorusH2ExteriorEquiv_wedge, coordinateTorusH2ExteriorEquiv_wedge]

private theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a) =
      exteriorPower.map 3 A.mulVecLin (coordinateTorusH3ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := coordinateTorusWedgeThree_surjective a
  have h :=
    LinearMap.congr_fun (coordinateTorusWedgeThree_matrix (Elliptic.examplePeriod .four) A) v
  change
    SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 (coordinateTorusWedgeThree v) =
      coordinateTorusWedgeThree (exteriorPower.map 3 A.mulVecLin v) at h
  rw [h, coordinateTorusH3ExteriorEquiv_wedge, coordinateTorusH3ExteriorEquiv_wedge]

private def PeriodTorusHigherHomology.coordinateTorusH2Coordinates :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  coordinateTorusH2ExteriorEquiv.trans PeriodTorusHigherHomologyExterior.squareCoordinates

private def PeriodTorusHigherHomology.coordinateTorusH3Coordinates :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  coordinateTorusH3ExteriorEquiv.trans PeriodTorusHigherHomologyExterior.cubeCoordinates

private theorem PeriodTorusHigherHomology.coordinateTorusH2Coordinates_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a) =
      LocalSystemMatrices.exteriorSquare A *ᵥ coordinateTorusH2Coordinates a := by
  change
    PeriodTorusHigherHomologyExterior.squareCoordinates
        (coordinateTorusH2ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a)) =
      _
  rw [coordinateTorusH2ExteriorEquiv_matrix]
  exact
    PeriodTorusHigherHomologyExterior.squareCoordinates_map A (coordinateTorusH2ExteriorEquiv a)

private theorem PeriodTorusHigherHomology.coordinateTorusH3Coordinates_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a) =
      LocalSystemMatrices.exteriorCube A *ᵥ coordinateTorusH3Coordinates a := by
  change
    PeriodTorusHigherHomologyExterior.cubeCoordinates
        (coordinateTorusH3ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a)) =
      _
  rw [coordinateTorusH3ExteriorEquiv_matrix]
  exact PeriodTorusHigherHomologyExterior.cubeCoordinates_map A (coordinateTorusH3ExteriorEquiv a)

end Mathoverflow1973

end
