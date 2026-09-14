/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris

/-!
# Hopf problem: torus homology · period torus higher homology 1

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

@[simp]
private theorem
    PeriodTorusHigherHomology.singularHomologyMap_id (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n = LinearMap.id := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_id
      (TopCat.of X)
  exact congrArg ModuleCat.Hom.hom h

public
theorem PeriodTorusHigherHomology.singularHomologyMap_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (g.comp f) n =
      (SingularMayerVietoris.singularHomologyMap g n).comp
        (SingularMayerVietoris.singularHomologyMap f n) := by
  have h :=
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g)
  exact congrArg ModuleCat.Hom.hom h

private def PeriodTorusHigherHomology.singularChainHomotopy {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (H : f.Homotopy g) :
    _root_.Homotopy (FirstHurewicz.singularChainMap f) (FirstHurewicz.singularChainMap g) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom f) (g := TopCat.ofHom g) H
    (ModuleCat.of ℤ ℤ)

private theorem PeriodTorusHigherHomology.homotopy_homologyMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap f n =
      SingularMayerVietoris.singularHomologyMap g n :=
  congrArg ModuleCat.Hom.hom ((singularChainHomotopy H).homologyMap_eq n)

private theorem PeriodTorusHigherHomology.homotopic_homologyMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (h : f.Homotopic g) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap f n =
      SingularMayerVietoris.singularHomologyMap g n := by
  obtain ⟨H⟩ := h
  exact homotopy_homologyMap H n

private def PeriodTorusHigherHomology.homotopyInverseHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology Y n
    where
  toLinearMap := SingularMayerVietoris.singularHomologyMap f n
  invFun := SingularMayerVietoris.singularHomologyMap g n
  left_inv
    a := by
    have h := homotopic_homologyMap hgf n
    rw [singularHomologyMap_comp, singularHomologyMap_id] at h
    exact LinearMap.congr_fun h a
  right_inv
    a := by
    have h := homotopic_homologyMap hfg n
    rw [singularHomologyMap_comp, singularHomologyMap_id] at h
    exact LinearMap.congr_fun h a

private def PeriodTorusHigherHomology.homotopyEquivHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology Y n :=
  homotopyInverseHomologyEquiv e.toFun e.invFun e.left_inv e.right_inv n

@[simp]
private theorem PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_toLinearMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ) :
    (homotopyEquivHomologyEquiv e n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap e.toFun n :=
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    homotopyEquivHomologyEquiv e n a = SingularMayerVietoris.singularHomologyMap e.toFun n a :=
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology Y n) :
    (homotopyEquivHomologyEquiv e n).symm a =
      SingularMayerVietoris.singularHomologyMap e.symm.toFun n a :=
  rfl

private def PeriodTorusHigherHomology.homeomorphHomologyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology Y n :=
  homotopyEquivHomologyEquiv e.toHomotopyEquiv n

@[simp]
private theorem PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    (homeomorphHomologyEquiv e n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap (e : C(X, Y)) n :=
  rfl

@[simp]
private theorem
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_apply {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    homeomorphHomologyEquiv e n a = SingularMayerVietoris.singularHomologyMap (e : C(X, Y)) n a :=
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.homeomorphHomologyEquiv_symm_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology Y n) :
    (homeomorphHomologyEquiv e n).symm a =
      SingularMayerVietoris.singularHomologyMap (e.symm : C(Y, X)) n a :=
  rfl

@[simp]
private theorem
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_symm {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ) :
    (homeomorphHomologyEquiv e n).symm = homeomorphHomologyEquiv e.symm n := by
  apply LinearEquiv.ext
  intro a
  rfl

@[simp]
private theorem
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_refl (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    homeomorphHomologyEquiv (Homeomorph.refl X) n =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology X n) := by
  apply LinearEquiv.ext
  intro a
  change SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n a = a
  rw [singularHomologyMap_id]
  rfl

private theorem PeriodTorusHigherHomology.homeomorphHomologyEquiv_trans {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (e : X ≃ₜ Y) (f : Y ≃ₜ Z)
    (n : ℕ) :
    homeomorphHomologyEquiv (e.trans f) n =
      (homeomorphHomologyEquiv e n).trans (homeomorphHomologyEquiv f n) := by
  apply LinearEquiv.ext
  intro a
  change
    SingularMayerVietoris.singularHomologyMap ((f : C(Y, Z)).comp (e : C(X, Y))) n a =
      SingularMayerVietoris.singularHomologyMap (f : C(Y, Z)) n
        (SingularMayerVietoris.singularHomologyMap (e : C(X, Y)) n a)
  rw [singularHomologyMap_comp]
  rfl

private def PeriodTorusHigherHomology.connectedHomologyZeroEquiv (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : SingularMayerVietoris.SingularHomology X 0 ≃ₗ[ℤ] ℤ :=
  (CategoryTheory.asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv

private theorem PeriodTorusHigherHomology.totallyDisconnected_homology_isZero (X : Type)
    [TopologicalSpace X] [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (SingularMayerVietoris.SingularHomology X n) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℤ) n
    (ModuleCat.of ℤ ℤ) (TopCat.of X) hn

private theorem PeriodTorusHigherHomology.totallyDisconnected_homology_subsingleton (X : Type)
    [TopologicalSpace X] [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology X n) :=
  ModuleCat.subsingleton_of_isZero (totallyDisconnected_homology_isZero X n hn)

private abbrev PeriodTorusHigherHomology.pointHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology Unit 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv Unit

private theorem PeriodTorusHigherHomology.point_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology Unit n) :=
  totallyDisconnected_homology_subsingleton Unit n hn

private def PeriodTorusHigherHomology.contractibleHomologyEquivPoint (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Unit n :=
  homotopyEquivHomologyEquiv (Classical.choice (ContractibleSpace.hequiv_unit X)) n

private theorem PeriodTorusHigherHomology.contractible_homology_subsingleton (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology X n) := by
  let := point_homology_subsingleton n hn
  exact (contractibleHomologyEquivPoint X n).injective.subsingleton

end Mathoverflow1973

end
