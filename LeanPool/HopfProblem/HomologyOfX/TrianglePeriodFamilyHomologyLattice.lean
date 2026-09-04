/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.TrianglePeriodFamilyHomologySplitting
public import LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology2
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra
import all LeanPool.HopfProblem.Foundations.TrianglePeriodFamilyHomologySplitting
import all LeanPool.HopfProblem.PeriodFamily.Core4

/-!
# Hopf problem: homology of x · triangle period family homology lattice

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

private theorem ThreefoldHomology.BoundaryFirst.boundaryMonodromy_one_coordinates
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 1
          a) =
      latticeMonodromy i *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a := by
  cases i with
  |
    none =>
    change
      PeriodFamily.FlatTorus.singularH1Equiv
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 : C(RealTorus₄, RealTorus₄)) 1 a) =
        M₀ *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a
    rw [← SpecialPeriods.triangleTorusHomeomorph_cusp_zpow 1]
    change
      PeriodFamily.FlatTorus.singularH1Equiv
          (FirstHurewicz.inducedHomology
            (SpecialPeriods.triangleTorusHomeomorph
                (SpecialPeriods.triangleCuspGenerator ^ (1 : ℤ)) :
              C(RealTorus₄, RealTorus₄))
            a) =
        _
    rw [PeriodFamily.FlatTorus.singularH1Equiv_inducedHomology_triangle,
      SpecialPeriods.triangleDualRepresentation_cusp_zpow_matrix,
      SpecialPeriods.CuspFamily.cuspIntegralMatrix_one]
  | some
    j =>
    change
      PeriodFamily.FlatTorus.singularH1Equiv
          (SingularMayerVietoris.singularHomologyMap
            (Elliptic.flatTorusAffine j j.twist : C(RealTorus₄, RealTorus₄)) 1 a) =
        j.matrix *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a
    rw [PeriodFamily.Boundary.flatTorusAffine_homology_triangle]
    change
      PeriodFamily.FlatTorus.singularH1Equiv
          (FirstHurewicz.inducedHomology
            (SpecialPeriods.triangleTorusHomeomorph
                (SpecialPeriods.Triangle.ellipticGenerator j) :
              C(RealTorus₄, RealTorus₄))
            a) =
        _
    rw [PeriodFamily.FlatTorus.singularH1Equiv_inducedHomology_triangle]
    cases j
    · rw [SpecialPeriods.Triangle.ellipticGenerator,
        SpecialPeriods.triangleDualRepresentation_generator₁_matrix]
      rfl
    · rw [SpecialPeriods.Triangle.ellipticGenerator,
        SpecialPeriods.triangleDualRepresentation_generator₂_matrix]
      rfl

private theorem ThreefoldHomology.BoundaryFirst.boundaryWangDifference_one_coordinates
    (i : SpecialPeriods.Threefold.Puncture)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 1 a) =
      latticeDifference i (PeriodFamily.FlatTorus.singularH1Equiv a) := by
  change
    PeriodFamily.FlatTorus.singularH1Equiv
        (a -
          MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 1
            a) =
      _
  rw [map_sub, boundaryMonodromy_one_coordinates, latticeDifference_apply]

private def ThreefoldHomology.BoundaryFirst.boundaryCokernelOneCoordinatesAddEquiv_mo1973_25077
    (i : SpecialPeriods.Threefold.Puncture) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 1 ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 1)) ≃+
      (Lattice ⧸ LinearMap.range (latticeDifference i)) := by
  letI :=
    Submodule.Quotient.module
      (LinearMap.range
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 1))
  letI := Submodule.Quotient.module (LinearMap.range (latticeDifference i))
  exact
    (PeriodFamily.HomologyDifference.cokernelEquivOfCommuting
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 1)
        (latticeDifference i) PeriodFamily.FlatTorus.singularH1Equiv
        PeriodFamily.FlatTorus.singularH1Equiv
        (boundaryWangDifference_one_coordinates i)).toAddEquiv

private def ThreefoldHomology.BoundaryFirst.boundaryCokernelOneCoordinates
    (i : SpecialPeriods.Threefold.Puncture) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 1 ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i)
            1)) ≃ₗ[ℤ]
      (Lattice ⧸ LinearMap.range (latticeDifference i)) :=
  (boundaryCokernelOneCoordinatesAddEquiv_mo1973_25077 i).toIntLinearEquiv

private def ThreefoldHomology.BoundaryFirst.latticeCokernelAddEquiv_mo1973_25080
    (i : SpecialPeriods.Threefold.Puncture) :
    (Lattice ⧸ LinearMap.range (latticeDifference i)) ≃+ (Fin 2 → ℤ) := by
  letI := Submodule.Quotient.module (LinearMap.range (latticeDifference i))
  exact (latticeCokernelEquiv i).toAddEquiv

private def ThreefoldHomology.BoundaryFirst.boundaryCokernelOneEquiv
    (i : SpecialPeriods.Threefold.Puncture) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 1 ⧸
        LinearMap.range
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i)
            1)) ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  ((boundaryCokernelOneCoordinates i).toAddEquiv.trans
      (latticeCokernelAddEquiv_mo1973_25080 i)).toIntLinearEquiv

private theorem ThreefoldHomology.BoundaryFirst.boundaryMonodromy_zero_identity
    (i : SpecialPeriods.Threefold.Puncture) :
    MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 0 =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄).injective
  exact
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
      (ThreefoldOverlapMappingTorus.monodromy i : C(RealTorus₄, RealTorus₄)) a

private theorem ThreefoldHomology.BoundaryFirst.boundaryWangDifference_zero
    (i : SpecialPeriods.Threefold.Puncture) :
    MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 0 = 0 := by
  apply LinearMap.ext
  intro a
  change
    a - MappingTorusHomology.monodromyHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) 0 a =
      0
  rw [boundaryMonodromy_zero_identity, LinearMap.id_apply, sub_self]

private def ThreefoldHomology.BoundaryFirst.boundaryKernelZeroEquiv
    (i : SpecialPeriods.Threefold.Puncture) :
    LinearMap.ker
        (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 0) ≃ₗ[ℤ]
      ℤ :=
  ({    toFun a := PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄ a.val
        invFun
          z :=
          ⟨(PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄).symm z,
            by
            rw [boundaryWangDifference_zero, LinearMap.ker_zero]
            trivial⟩
        left_inv
          a :=
          Subtype.ext
            ((PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄).symm_apply_apply
              a.val)
        right_inv
          z :=
          (PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄).apply_symm_apply z
        map_add' a
          b :=
          (PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄).map_add a.val
            b.val } :
      LinearMap.ker
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 0) ≃+
        ℤ).toIntLinearEquiv

private def
    ThreefoldHomology.BoundaryFirst.boundaryH1SplitEquiv (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) 1 ≃ₗ[ℤ]
      ((SingularMayerVietoris.SingularHomology RealTorus₄ 1 ⧸
          LinearMap.range
            (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 1)) ×
        LinearMap.ker
          (MappingTorusHomology.wangDifference (ThreefoldOverlapMappingTorus.monodromy i) 0)) := by
  letI := Module.Free.of_equiv (boundaryKernelZeroEquiv i).toAddEquiv.symm.toIntLinearEquiv
  exact
    TrianglePeriodFamilyHomologySplitting.freeRightSplitEquiv
      (MappingTorusHomology.cokernelInclusion (ThreefoldOverlapMappingTorus.monodromy i) 1)
      (MappingTorusHomology.kernelBoundary (ThreefoldOverlapMappingTorus.monodromy i) 0)
      (LinearMap.exact_iff.mpr
        (MappingTorusHomology.cokernelInclusion_range_eq_ker_kernelBoundary
            (ThreefoldOverlapMappingTorus.monodromy i) 0).symm)
      (MappingTorusHomology.cokernelInclusion_injective (ThreefoldOverlapMappingTorus.monodromy i)
        1)
      (MappingTorusHomology.kernelBoundary_surjective (ThreefoldOverlapMappingTorus.monodromy i)
        0)

private def ThreefoldHomology.BoundaryFirst.boundaryH1ProductEquiv
    (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) 1 ≃ₗ[ℤ]
      ((Fin 2 → ℤ) × ℤ) :=
  ((boundaryH1SplitEquiv i).toAddEquiv.trans
      ((boundaryCokernelOneEquiv i).toAddEquiv.prodCongr
        (boundaryKernelZeroEquiv i).toAddEquiv)).toIntLinearEquiv

private def
    ThreefoldHomology.BoundaryFirst.twoFibreOneBaseEquiv : ((Fin 2 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (((AddEquiv.refl (Fin 2 → ℤ)).prodCongr
          (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.toAddEquiv).trans
      (TrianglePeriodFamilyHomologyFreeCoordinates.freeCoordinateSumEquiv 2
          1).toAddEquiv).toIntLinearEquiv

private def
    ThreefoldHomology.BoundaryFirst.boundaryH1Equiv (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology (ThreefoldOverlapMappingTorus.Boundary i) 1 ≃ₗ[ℤ]
      (Fin 3 → ℤ) :=
  (boundaryH1ProductEquiv i).trans twoFibreOneBaseEquiv

private def ThreefoldHomology.BoundaryFirst.overlapH1Equiv (i : SpecialPeriods.Threefold.Puncture) :
    SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1 ≃ₗ[ℤ]
      (Fin 3 → ℤ) :=
  (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i 1).trans (boundaryH1Equiv i)

private theorem
    ThreefoldHomology.BoundaryFirst.overlapH1_free (i : SpecialPeriods.Threefold.Puncture) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1) :=
  Module.Free.of_equiv (overlapH1Equiv i).symm

private theorem
    ThreefoldHomology.BoundaryFirst.overlapH1_finite (i : SpecialPeriods.Threefold.Puncture) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1) :=
  Module.Finite.of_surjective (overlapH1Equiv i).symm.toLinearMap
    (overlapH1Equiv i).symm.surjective

private theorem ThreefoldHomology.BoundaryFirst.overlapH1_finrank
    (i : SpecialPeriods.Threefold.Puncture) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) 1) =
      3 := by
  rw [(overlapH1Equiv i).finrank_eq]
  simp

private theorem ThreefoldHomology.Finiteness.finite_pi_int {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)] [∀ i, Module.Finite ℤ (M i)]
    [piModule : Module ℤ (∀ i, M i)] : Module.Finite ℤ (∀ i, M i) := by
  have h : piModule = Pi.module ι M ℤ := Subsingleton.elim _ _
  cases h
  exact Module.Finite.pi

private theorem ThreefoldHomology.Finiteness.finite_prod_int (M N : Type*) [AddCommGroup M]
    [AddCommGroup N] [Module ℤ M] [Module ℤ N] [Module.Finite ℤ M] [Module.Finite ℤ N]
    [prodModule : Module ℤ (M × N)] : Module.Finite ℤ (M × N) := by
  have h : prodModule = (Prod.instModule : Module ℤ (M × N)) := Subsingleton.elim _ _
  cases h
  exact Module.Finite.prod

private theorem ThreefoldHomologyFreeProducts.free_pi_int {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)] [∀ i, Module.Free ℤ (M i)]
    [piModule : Module ℤ (∀ i, M i)] : Module.Free ℤ (∀ i, M i) := by
  have h : piModule = Pi.module ι M ℤ := Subsingleton.elim _ _
  cases h
  infer_instance

private theorem ThreefoldHomologyFreeProducts.free_prod_int (M N : Type*) [AddCommGroup M]
    [AddCommGroup N] [Module ℤ M] [Module ℤ N] [Module.Free ℤ M] [Module.Free ℤ N]
    [prodModule : Module ℤ (M × N)] : Module.Free ℤ (M × N) := by
  have h : prodModule = (Prod.instModule : Module ℤ (M × N)) := Subsingleton.elim _ _
  cases h
  infer_instance

public
theorem ThreefoldHomologyFreeProducts.finrank_pi_int {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)] [∀ i, Module.Free ℤ (M i)]
    [∀ i, Module.Finite ℤ (M i)] [piModule : Module ℤ (∀ i, M i)] :
    Module.finrank ℤ (∀ i, M i) = ∑ i, Module.finrank ℤ (M i) := by
  have h : piModule = Pi.module ι M ℤ := Subsingleton.elim _ _
  cases h
  exact Module.finrank_pi_fintype ℤ

private theorem ThreefoldHomologyFreeProducts.finrank_prod_int (M N : Type*) [AddCommGroup M]
    [AddCommGroup N] [Module ℤ M] [Module ℤ N] [Module.Free ℤ M] [Module.Free ℤ N]
    [Module.Finite ℤ M] [Module.Finite ℤ N] [prodModule : Module ℤ (M × N)] :
    Module.finrank ℤ (M × N) = Module.finrank ℤ M + Module.finrank ℤ N := by
  have h : prodModule = (Prod.instModule : Module ℤ (M × N)) := Subsingleton.elim _ _
  cases h
  exact Module.finrank_prod

private def TrianglePeriodFamilyHomologyAlgebra.reducedCokernelToMiddle {High Middle : Type u}
    [AddCommGroup High] [AddCommGroup Middle] [Module ℤ High] [Module ℤ Middle]
    (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j) :
    (High ⧸ LinearMap.range (delta P Q)) →ₗ[ℤ] Middle :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    ((cokernelToMiddle (overlapMap P Q) j hj).toAddMonoidHom.comp
      (overlapCokernelEquiv P Q).symm.toAddEquiv.toAddMonoidHom)

@[simp]
private theorem
    TrianglePeriodFamilyHomologyAlgebra.reducedCokernelToMiddle_apply {High Middle : Type u}
    [AddCommGroup High] [AddCommGroup Middle] [Module ℤ High] [Module ℤ Middle]
    (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j) (q : High ⧸ LinearMap.range (delta P Q)) :
    reducedCokernelToMiddle P Q j hj q =
      cokernelToMiddle (overlapMap P Q) j hj ((overlapCokernelEquiv P Q).symm q) :=
  rfl

private theorem
    TrianglePeriodFamilyHomologyAlgebra.reducedCokernelToMiddle_mk {High Middle : Type u}
    [AddCommGroup High] [AddCommGroup Middle] [Module ℤ High] [Module ℤ Middle]
    (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j) (y : High) :
    reducedCokernelToMiddle P Q j hj (Submodule.Quotient.mk y) = j (0, -y) := by
  rw [reducedCokernelToMiddle_apply, overlapCokernelEquiv_symm_mk]
  rfl

private theorem TrianglePeriodFamilyHomologyAlgebra.reducedCokernelToMiddle_injective
    {High Middle : Type u} [AddCommGroup High] [AddCommGroup Middle] [Module ℤ High]
    [Module ℤ Middle] (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j) :
    Function.Injective (reducedCokernelToMiddle P Q j hj) :=
  (cokernelToMiddle_injective (overlapMap P Q) j hj).comp
    (overlapCokernelEquiv P Q).symm.injective

private def TrianglePeriodFamilyHomologyAlgebra.middleToReducedKernel {Low Middle : Type u}
    [AddCommGroup Low] [AddCommGroup Middle] [Module ℤ Low] [Module ℤ Middle]
    (P Q : Low →ₗ[ℤ] Low) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hδ : Function.Exact δ (overlapMap P Q)) : Middle →ₗ[ℤ] LinearMap.ker (delta P Q) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    ((overlapKerEquiv P Q).toAddEquiv.toAddMonoidHom.comp
      (middleToKernel δ (overlapMap P Q) hδ).toAddMonoidHom)

@[simp]
private theorem
    TrianglePeriodFamilyHomologyAlgebra.middleToReducedKernel_apply {Low Middle : Type u}
    [AddCommGroup Low] [AddCommGroup Middle] [Module ℤ Low] [Module ℤ Middle]
    (P Q : Low →ₗ[ℤ] Low) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hδ : Function.Exact δ (overlapMap P Q)) (m : Middle) :
    middleToReducedKernel P Q δ hδ m =
      overlapKerEquiv P Q (middleToKernel δ (overlapMap P Q) hδ m) :=
  rfl

private theorem
    TrianglePeriodFamilyHomologyAlgebra.middleToReducedKernel_surjective {Low Middle : Type u}
    [AddCommGroup Low] [AddCommGroup Middle] [Module ℤ Low] [Module ℤ Middle]
    (P Q : Low →ₗ[ℤ] Low) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hδ : Function.Exact δ (overlapMap P Q)) :
    Function.Surjective (middleToReducedKernel P Q δ hδ) :=
  (overlapKerEquiv P Q).surjective.comp (middleToKernel_surjective δ (overlapMap P Q) hδ)

private theorem
    TrianglePeriodFamilyHomologyAlgebra.reducedExtension_exact {High Low Middle : Type u}
    [AddCommGroup High] [AddCommGroup Low] [AddCommGroup Middle] [Module ℤ High] [Module ℤ Low]
    [Module ℤ Middle] (PHigh QHigh : High →ₗ[ℤ] High) (PLow QLow : Low →ₗ[ℤ] Low)
    (j : (High × High) →ₗ[ℤ] Middle) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hj : Function.Exact (overlapMap PHigh QHigh) j) (hjδ : Function.Exact j δ)
    (hδ : Function.Exact δ (overlapMap PLow QLow)) :
    Function.Exact (reducedCokernelToMiddle PHigh QHigh j hj)
      (middleToReducedKernel PLow QLow δ hδ) := by
  have hex :=
    cokernelToMiddle_middleToKernel_exact (overlapMap PHigh QHigh) j δ (overlapMap PLow QLow) hj
      hjδ hδ
  intro m
  constructor
  · intro hm
    have hzero : middleToKernel δ (overlapMap PLow QLow) hδ m = 0 := by
      apply (overlapKerEquiv PLow QLow).injective
      exact hm.trans (overlapKerEquiv PLow QLow).map_zero.symm
    obtain ⟨q, hq⟩ := (hex m).mp hzero
    refine ⟨overlapCokernelEquiv PHigh QHigh q, ?_⟩
    rw [reducedCokernelToMiddle_apply, LinearEquiv.symm_apply_apply]
    exact hq
  · rintro ⟨q, rfl⟩
    have hzero :
      middleToKernel δ (overlapMap PLow QLow) hδ (reducedCokernelToMiddle PHigh QHigh j hj q) =
        0 :=
      (hex _).mpr ⟨(overlapCokernelEquiv PHigh QHigh).symm q, rfl⟩
    rw [middleToReducedKernel_apply, hzero, map_zero]

private def TrianglePeriodFamilyHomologyLattice.deltaTwo :
    ((Fin 6 → ℤ) × (Fin 6 → ℤ)) →ₗ[ℤ] (Fin 6 → ℤ) :=
  TrianglePeriodFamilyHomologyAlgebra.delta PeriodTorusHigherHomologyExterior.squareA₁.mulVecLin
    PeriodTorusHigherHomologyExterior.squareA₂.mulVecLin

private theorem TrianglePeriodFamilyHomologyLattice.deltaTwo_apply (b c : Fin 6 → ℤ) :
    deltaTwo (b, c) =
      ![-b 0 + b 1 - c 0 - c 1, -b 0 - 2 * b 1 + c 0 - c 1, b 0 + c 1, -6 * b 0 - 6 * c 1,
        6 * b 0 + 2 * b 1 + 6 * b 2 - b 3 - b 4 + b 5 + 3 * c 1 - c 4 - c 5,
        -8 * b 0 - 2 * b 1 - 6 * b 2 + b 3 - b 4 - 2 * b 5 - 3 * c 0 - 6 * c 1 - 6 * c 2 + c 3 +
            c 4 -
          c 5] := by
  change
    (PeriodTorusHigherHomologyExterior.squareA₁.mulVecLin b - b) +
        (PeriodTorusHigherHomologyExterior.squareA₂.mulVecLin c - c) =
      _
  rw [PeriodTorusHigherHomologyExterior.squareA₁_eq,
    PeriodTorusHigherHomologyExterior.squareA₂_eq]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

private def TrianglePeriodFamilyHomologyLattice.functionalTwo : (Fin 6 → ℤ) →ₗ[ℤ] ℤ
    where
  toFun x := 6 * x 2 + x 3
  map_add' x y := by simp; ring
  map_smul' n x := by simp; ring

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.functionalTwo_apply (x : Fin 6 → ℤ) :
    functionalTwo x = 6 * x 2 + x 3 :=
  rfl

private theorem TrianglePeriodFamilyHomologyLattice.functionalTwo_single_three (z : ℤ) :
    functionalTwo ![0, 0, 0, z, 0, 0] = z := by simp

private theorem TrianglePeriodFamilyHomologyLattice.functionalTwo_surjective :
    Function.Surjective functionalTwo := by
  intro z
  exact ⟨![0, 0, 0, z, 0, 0], functionalTwo_single_three z⟩

private def TrianglePeriodFamilyHomologyLattice.deltaTwoLift :
    (Fin 6 → ℤ) →ₗ[ℤ] ((Fin 6 → ℤ) × (Fin 6 → ℤ)) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun
        x :=
        (![0, -x 0 - x 1 - 2 * x 2, 0, -2 * x 0 - 2 * x 1 - x 2 - x 4, 0, 0],
          ![-2 * x 0 - x 1 - 3 * x 2, x 2, 0, -6 * x 0 - 3 * x 1 - 6 * x 2 + x 4 + x 5, 0, 0])
      map_zero' := by apply Prod.ext <;> funext i <;> fin_cases i <;> simp
      map_add' x y := by apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring }

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.deltaTwoLift_apply (x : Fin 6 → ℤ) :
    deltaTwoLift x =
      (![0, -x 0 - x 1 - 2 * x 2, 0, -2 * x 0 - 2 * x 1 - x 2 - x 4, 0, 0],
        ![-2 * x 0 - x 1 - 3 * x 2, x 2, 0, -6 * x 0 - 3 * x 1 - 6 * x 2 + x 4 + x 5, 0, 0]) :=
  rfl

private theorem TrianglePeriodFamilyHomologyLattice.deltaTwo_deltaTwoLift (x : Fin 6 → ℤ) :
    deltaTwo (deltaTwoLift x) = ![x 0, x 1, x 2, -6 * x 2, x 4, x 5] := by
  rw [deltaTwoLift_apply, deltaTwo_apply]
  ext i
  fin_cases i <;> simp <;> ring

private theorem TrianglePeriodFamilyHomologyLattice.deltaTwo_lift (x : Fin 6 → ℤ)
    (hx : functionalTwo x = 0) : deltaTwo (deltaTwoLift x) = x := by
  rw [deltaTwo_deltaTwoLift]
  have hx3 : -6 * x 2 = x 3 := by
    change 6 * x 2 + x 3 = 0 at hx
    omega
  ext i
  fin_cases i <;> simp [hx3]

private theorem TrianglePeriodFamilyHomologyLattice.functionalTwo_deltaTwo
    (x : (Fin 6 → ℤ) × (Fin 6 → ℤ)) : functionalTwo (deltaTwo x) = 0 := by
  rcases x with ⟨b, c⟩
  rw [deltaTwo_apply, functionalTwo_apply]
  simp
  ring

private theorem TrianglePeriodFamilyHomologyLattice.deltaTwo_range_eq_ker :
    LinearMap.range deltaTwo = LinearMap.ker functionalTwo := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact functionalTwo_deltaTwo y
  · intro hx
    exact ⟨deltaTwoLift x, deltaTwo_lift x hx⟩

private def TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv :
    ((Fin 6 → ℤ) ⧸ LinearMap.range deltaTwo) ≃ₗ[ℤ] ℤ :=
  ((Submodule.quotEquivOfEq _ _ deltaTwo_range_eq_ker).toAddEquiv.trans
      (functionalTwo.quotKerEquivOfSurjective
          functionalTwo_surjective).toAddEquiv).toIntLinearEquiv

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv_mk (x : Fin 6 → ℤ) :
    cokernelTwoEquiv (Submodule.Quotient.mk x) = functionalTwo x := by
  change
    functionalTwo.quotKerEquivOfSurjective functionalTwo_surjective
        (Submodule.quotEquivOfEq _ _ deltaTwo_range_eq_ker (Submodule.Quotient.mk x)) =
      _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.det_A₁ : A₁.det = 1 := by
  rw [A₁_eq_transpose_sq, Matrix.det_transpose, Matrix.det_pow, det_T₁, one_pow]

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.det_A₂ : A₂.det = 1 := by
  rw [A₂_eq_transpose_cube, Matrix.det_transpose, Matrix.det_pow, det_T₂, one_pow]

private def TrianglePeriodFamilyHomologyLattice.deltaZero : (ℤ × ℤ) →ₗ[ℤ] ℤ :=
  TrianglePeriodFamilyHomologyAlgebra.delta (LinearMap.id : ℤ →ₗ[ℤ] ℤ) (LinearMap.id : ℤ →ₗ[ℤ] ℤ)

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.deltaZero_eq_zero : deltaZero = 0 := by
  apply LinearMap.ext
  intro x
  simp [deltaZero, TrianglePeriodFamilyHomologyAlgebra.delta_apply]

private def TrianglePeriodFamilyHomologyLattice.deltaFour : (ℤ × ℤ) →ₗ[ℤ] ℤ :=
  TrianglePeriodFamilyHomologyAlgebra.delta (A₁.det • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))
    (A₂.det • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

@[simp]
private theorem TrianglePeriodFamilyHomologyLattice.deltaFour_eq_zero : deltaFour = 0 := by
  rw [deltaFour, det_A₁, det_A₂, one_smul]
  exact deltaZero_eq_zero

private def
    TrianglePeriodFamilyHomologyLattice.kernelZeroEquiv : LinearMap.ker deltaZero ≃ₗ[ℤ] (ℤ × ℤ) :=
  ({    toFun x := x.val
        invFun x := ⟨x, by simp⟩
        left_inv _ := Subtype.ext rfl
        right_inv _ := rfl
        map_add' _ _ := rfl } : LinearMap.ker deltaZero ≃+ (ℤ × ℤ)).toIntLinearEquiv

private def
    TrianglePeriodFamilyHomologyLattice.kernelFourEquiv : LinearMap.ker deltaFour ≃ₗ[ℤ] (ℤ × ℤ) :=
  ({    toFun x := x.val
        invFun x := ⟨x, by simp⟩
        left_inv _ := Subtype.ext rfl
        right_inv _ := rfl
        map_add' _ _ := rfl } : LinearMap.ker deltaFour ≃+ (ℤ × ℤ)).toIntLinearEquiv


private def TrianglePeriodFamilyHomologyLattice.cokernelFourEquiv :
    (ℤ ⧸ LinearMap.range deltaFour) ≃ₗ[ℤ] ℤ :=
  ((LinearMap.range deltaFour).quotEquivOfEqBot (by simp)).toAddEquiv.toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem TrianglePeriodFamilyHomologyLattice.kernel_finite_of_finite {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] [Module.Finite ℤ M]
    (f : M →ₗ[ℤ] N) : Module.Finite ℤ (LinearMap.ker f) :=
  inferInstance

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem TrianglePeriodFamilyHomologyLattice.kernel_free_of_finite_free {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] [Module.Finite ℤ M]
    [Module.Free ℤ M] (f : M →ₗ[ℤ] N) : Module.Free ℤ (LinearMap.ker f) := by
  let := kernel_finite_of_finite f
  infer_instance

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem
    TrianglePeriodFamilyHomologyLattice.kernel_finrank_add_of_cokernelEquiv {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] [Module.Finite ℤ M]
    [Module.Finite ℤ N] (f : M →ₗ[ℤ] N) (e : (N ⧸ LinearMap.range f) ≃ₗ[ℤ] ℤ) :
    Module.finrank ℤ (LinearMap.ker f) + Module.finrank ℤ N = Module.finrank ℤ M + 1 := by
  have hsource := (LinearMap.ker f).finrank_quotient_add_finrank
  have htarget := (LinearMap.range f).finrank_quotient_add_finrank
  have hquot : Module.finrank ℤ (M ⧸ LinearMap.ker f) = Module.finrank ℤ (LinearMap.range f) :=
    f.quotKerEquivRange.finrank_eq
  have hcoker : Module.finrank ℤ (N ⧸ LinearMap.range f) = 1 := by
    rw [e.finrank_eq]
    simp
  omega

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def
    TrianglePeriodFamilyHomologyLattice.kernelEquivOfFinrankEq {M N : Type u} [AddCommGroup M]
    [AddCommGroup N] [Module ℤ M] [Module ℤ N] [Module.Finite ℤ M] [Module.Free ℤ M]
    (f : M →ₗ[ℤ] N) (r : ℕ) (hr : Module.finrank ℤ (LinearMap.ker f) = r) :
    LinearMap.ker f ≃ₗ[ℤ] (Fin r → ℤ) := by
  let := kernel_finite_of_finite f
  let := kernel_free_of_finite_free f
  apply LinearEquiv.ofFinrankEq
  simpa using hr

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem TrianglePeriodFamilyHomologyLattice.kernelOne_finrank :
    Module.finrank ℤ (LinearMap.ker deltaOne) = 5 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaOne cokernelOneEquiv
  norm_num [Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem TrianglePeriodFamilyHomologyLattice.kernelTwo_finrank :
    Module.finrank ℤ (LinearMap.ker deltaTwo) = 7 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaTwo cokernelTwoEquiv
  norm_num [Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem TrianglePeriodFamilyHomologyLattice.kernelThree_finrank :
    Module.finrank ℤ (LinearMap.ker deltaThree) = 5 := by
  have h := kernel_finrank_add_of_cokernelEquiv deltaThree cokernelThreeEquiv
  norm_num [Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def TrianglePeriodFamilyHomologyLattice.kernelOneEquiv :
    LinearMap.ker deltaOne ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  kernelEquivOfFinrankEq deltaOne 5 kernelOne_finrank

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def TrianglePeriodFamilyHomologyLattice.kernelTwoEquiv :
    LinearMap.ker deltaTwo ≃ₗ[ℤ] (Fin 7 → ℤ) :=
  kernelEquivOfFinrankEq deltaTwo 7 kernelTwo_finrank

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def TrianglePeriodFamilyHomologyLattice.kernelThreeEquiv :
    LinearMap.ker deltaThree ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  kernelEquivOfFinrankEq deltaThree 5 kernelThree_finrank

end Mathoverflow1973

end
