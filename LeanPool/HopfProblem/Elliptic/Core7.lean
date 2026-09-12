/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Pi1.MappingTorusHomology
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Pi1.MappingTorusHomology

/-!
# Hopf problem: elliptic · core 7

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

private def Elliptic.HigherHomology.CoverAlgebra.secondMap {M : Type*} [AddCommGroup M] [Module ℤ M]
    (L : M →ₗ[ℤ] (Fin 2 → ℤ)) : M →ₗ[ℤ] ℤ :=
  (LinearMap.proj 1).comp L

private def Elliptic.HigherHomology.fibreIntoPeriodTorus (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : C(PeriodTorusHigherHomology.ProductTorus 3, p.val.Torus)
    where
  toFun x := (splitPeriodTorusHomeomorph j p.val).symm (0, x)
  continuous_toFun :=
    (splitPeriodTorusHomeomorph j p.val).symm.continuous.comp
      (continuous_const.prodMk continuous_id)

private def
    Elliptic.HigherHomology.fibreIntoSurface (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    C(PeriodTorusHigherHomology.ProductTorus 3,
      Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) :=
  (periodCover j p j.twist (Elliptic.mainTwist_admissible j)).comp (fibreIntoPeriodTorus j p)

private theorem Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_comp_fibreIntoSurface
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    (surfaceMappingTorusHomeomorph j p :
            C(Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j),
              mappingTorusModel j)).comp
        (fibreIntoSurface j p) =
      MappingTorus.HomologyCover.fibreInclusion (fibreTorusHomeomorph j).symm := by
  ext x
  change
    surfaceMappingTorusHomeomorph j p
        (Elliptic.surfaceProjection j p j.twist (Elliptic.mainTwist_admissible j)
          ((splitPeriodTorusHomeomorph j p.val).symm (0, x))) =
      MappingTorus.mk (fibreTorusHomeomorph j).symm (0, x)
  simpa only [AddCircle.coe_zero, MulZeroClass.zero_mul] using
    surfaceMappingTorusHomeomorph_splitPeriodTorus j p (0 : ℝ) x

private theorem Elliptic.HigherHomology.surfaceMappingTorusHomology_fibre_map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) n) =
      MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm n := by
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    surfaceMappingTorusHomeomorph_comp_fibreIntoSurface]

private theorem Elliptic.HigherHomology.surfaceMappingTorusHomology_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n
        (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) n a) =
      MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm n a :=
  DFunLike.congr_fun (surfaceMappingTorusHomology_fibre_map j p n) a

private def Elliptic.HigherHomology.mappingTorusProductCover (j : Elliptic.Kind) :
    C(MappingTorus.Circle × PeriodTorusHigherHomology.ProductTorus 3, mappingTorusModel j) :=
  (MappingTorusQuotient.mappingTorusHomeomorph j.order (fibreTorusHomeomorph j)
          (fibreTorusHomeomorph_pow_order j) :
        C(surfaceProductQuotient j, mappingTorusModel j)).comp
    ⟨MappingTorusQuotient.project j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j),
      MappingTorusQuotient.project_continuous j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j)⟩

private theorem
    Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_comp_periodCover (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    (surfaceMappingTorusHomeomorph j p :
            C(Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j),
              mappingTorusModel j)).comp
        (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) =
      (mappingTorusProductCover j).comp
        (splitPeriodTorusHomeomorph j p.val :
          C(p.val.Torus, MappingTorus.Circle × PeriodTorusHigherHomology.ProductTorus 3)) :=
  rfl

private theorem
    Elliptic.HigherHomology.surfaceMappingTorusHomology_periodCover_map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n) =
      (SingularMayerVietoris.singularHomologyMap (mappingTorusProductCover j) n).comp
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
            n).toLinearMap := by
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    surfaceMappingTorusHomeomorph_comp_periodCover,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap]

private theorem Elliptic.HigherHomology.surfaceMappingTorusHomology_periodCover (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n a) =
      SingularMayerVietoris.singularHomologyMap (mappingTorusProductCover j) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n
          a) :=
  DFunLike.congr_fun (surfaceMappingTorusHomology_periodCover_map j p n) a

private theorem Elliptic.HigherHomology.surfaceH2Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    surfaceH2Equiv j p (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 2 a) =
      ![torusH2Coordinates a 0, 0] := by
  change
    mappingTorusH2Equiv j
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 2
          (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 2 a)) =
      _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH2Equiv_fibre]

private theorem Elliptic.HigherHomology.surfaceH3Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    surfaceH3Equiv j p (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 3 a) =
      ![torusH3Coordinates a, 0] := by
  change
    mappingTorusH3Equiv j
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 3
          (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 3 a)) =
      _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH3Equiv_fibre]

private theorem Elliptic.HigherHomology.surfaceH2Equiv_periodCover_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    surfaceH2Equiv j p
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 2 a)) =
      ![torusH2Coordinates a 0, 0] := by
  change
    surfaceH2Equiv j p
        (((SingularMayerVietoris.singularHomologyMap
                (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2).comp
            (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 2))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact surfaceH2Equiv_fibre j p a

private theorem Elliptic.HigherHomology.surfaceH3Equiv_periodCover_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    surfaceH3Equiv j p
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 3 a)) =
      ![torusH3Coordinates a, 0] := by
  change
    surfaceH3Equiv j p
        (((SingularMayerVietoris.singularHomologyMap
                (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3).comp
            (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 3))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact surfaceH3Equiv_fibre j p a

private def Elliptic.HigherHomology.surfacePeriodCoverH2Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology p.val.Torus 2 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH2Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2)

private def Elliptic.HigherHomology.surfacePeriodCoverH3Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology p.val.Torus 3 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH3Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3)

private def Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : SingularMayerVietoris.SingularHomology p.val.Torus 4 →ₗ[ℤ] ℤ :=
  (surfaceH4Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 4)

/-- The index contributed by the norm map for each elliptic fibre type. -/
public
def Elliptic.HigherHomology.fibreNormIndex : Elliptic.Kind → ℕ
  | .three => 1
  | .four => 2

@[simp]
private theorem Elliptic.HigherHomology.fibreNormIndex_three : fibreNormIndex .three = 1 :=
  rfl

@[simp]
private theorem Elliptic.HigherHomology.fibreNormIndex_four : fibreNormIndex .four = 2 :=
  rfl

private theorem
    Elliptic.HigherHomology.fibreNormIndex_pos (j : Elliptic.Kind) : 0 < fibreNormIndex j := by
  cases j <;> decide

public
theorem Elliptic.HigherHomology.fibreNormIndex_int_ne_zero (j : Elliptic.Kind) :
    (fibreNormIndex j : ℤ) ≠ 0 := by exact_mod_cast (fibreNormIndex_pos j).ne'

private def Elliptic.HigherHomology.fibreNormMatrix (j : Elliptic.Kind) : FibreMatrix :=
  ∑ k ∈ Finset.range j.order, (fibreMatrix j) ^ k

private def Elliptic.HigherHomology.fibreSquareNormMatrix (j : Elliptic.Kind) : FibreMatrix :=
  ∑ k ∈ Finset.range j.order, (fibreSquareMatrix j) ^ k

@[simp]
private theorem Elliptic.HigherHomology.fibreNormMatrix_three :
    fibreNormMatrix .three = !![0, 0, 0; 0, 0, 0; 2, 1, 3] := by decide

@[simp]
private theorem Elliptic.HigherHomology.fibreNormMatrix_four :
    fibreNormMatrix .four = !![0, 0, 0; 0, 0, 0; 2, 2, 4] := by decide

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareNormMatrix_three :
    fibreSquareNormMatrix .three = !![3, 0, 0; -1, 0, 0; 2, 0, 0] := by decide

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareNormMatrix_four :
    fibreSquareNormMatrix .four = !![4, 0, 0; -2, 0, 0; 2, 0, 0] := by decide

private def
    Elliptic.HigherHomology.fibreNorm (j : Elliptic.Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreNormMatrix j).mulVecLin

private theorem Elliptic.HigherHomology.fibreNorm_apply (j : Elliptic.Kind) (v : FibreLattice) :
    fibreNorm j v =
      ((fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v) • fibreKernelVector := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [fibreCoinvariantCoordinate, fibreNorm, fibreKernelVector, dotProduct, Fin.sum_univ_succ]
  all_goals ring

@[simp]
private theorem Elliptic.HigherHomology.fibreNorm_apply_two (j : Elliptic.Kind) (v : FibreLattice) :
    fibreNorm j v 2 = (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v := by
  rw [fibreNorm_apply]
  simp [fibreKernelVector]

private def Elliptic.HigherHomology.fibreSquareNorm (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreSquareNormMatrix j).mulVecLin

@[simp]
private theorem
    Elliptic.HigherHomology.fibreSquareNorm_apply (j : Elliptic.Kind) (v : FibreLattice) :
    fibreSquareNorm j v = ((fibreNormIndex j : ℤ) * v 0) • fibreSquareKernelVector j := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [fibreSquareKernelVector, fibreSquareNorm, dotProduct, Fin.sum_univ_succ]
  all_goals ring

private theorem
    Elliptic.HigherHomology.fibreSquareNorm_mem_ker (j : Elliptic.Kind) (v : FibreLattice) :
    fibreSquareNorm j v ∈ LinearMap.ker (fibreSquareDifference j) := by
  rw [LinearMap.mem_ker, fibreSquareNorm_apply, map_smul, fibreSquareDifference_kernelVector,
    smul_zero]

private def Elliptic.HigherHomology.fibreSquareNormToKernel (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] LinearMap.ker (fibreSquareDifference j) :=
  (fibreSquareNorm j).codRestrict _ (fibreSquareNorm_mem_ker j)

private def Elliptic.HigherHomology.fibreSquareNormCoordinate (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] ℤ :=
  (fibreSquareKernelEquivInt j).toLinearMap.comp (fibreSquareNormToKernel j)

private theorem Elliptic.HigherHomology.fibreSquareNormCoordinate_eq_neg_second (j : Elliptic.Kind)
    (v : FibreLattice) : fibreSquareNormCoordinate j v = -(fibreSquareNorm j v) 1 :=
  rfl

@[simp]
private theorem Elliptic.HigherHomology.fibreSquareNormCoordinate_apply (j : Elliptic.Kind)
    (v : FibreLattice) : fibreSquareNormCoordinate j v = (fibreNormIndex j : ℤ) * v 0 := by
  rw [fibreSquareNormCoordinate_eq_neg_second, fibreSquareNorm_apply]
  simp

private theorem Elliptic.HigherHomology.markedLinearPower {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] FibreLattice) (f : M →ₗ[ℤ] M) (A : FibreMatrix) (h : ∀ a, e (f a) = A *ᵥ e a)
    (k : ℕ) (a : M) : e ((f ^ k) a) = A ^ k *ᵥ e a := by
  induction k generalizing a with
  | zero => simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Matrix.mulVec_mulVec]

private def Elliptic.HigherHomology.fibreHomologyNorm (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n :=
  ∑ k ∈ Finset.range j.order,
    (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) n) ^ k

private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_one (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    torusH1Equiv (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 1 a) =
      fibreMatrix j *ᵥ torusH1Equiv a :=
  torusH1Equiv_matrix_natural (fibreMatrix j) a

private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_two (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 2 a) =
      fibreSquareMatrix j *ᵥ torusH2Coordinates a :=
  torusH2Coordinates_fibreMatrix j a

private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_three (j : Elliptic.Kind) :
    MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 3 = 1 := by
  ext a
  apply torusH3Coordinates.injective
  exact torusH3Coordinates_fibreMatrix j a

private theorem Elliptic.HigherHomology.fibreHomologyNorm_one (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    torusH1Equiv (fibreHomologyNorm j 1 a) = fibreNorm j (torusH1Equiv a) := by
  simp only [fibreHomologyNorm, LinearMap.sum_apply, map_sum, fibreNorm, Matrix.mulVecLin_apply,
    fibreNormMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  exact markedLinearPower torusH1Equiv _ _ (fibreHomologyMonodromy_one j) k a

private theorem Elliptic.HigherHomology.fibreHomologyNorm_two (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates (fibreHomologyNorm j 2 a) = fibreSquareNorm j (torusH2Coordinates a) := by
  simp only [fibreHomologyNorm, LinearMap.sum_apply, map_sum, fibreSquareNorm,
    Matrix.mulVecLin_apply, fibreSquareNormMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  exact markedLinearPower torusH2Coordinates _ _ (fibreHomologyMonodromy_two j) k a

private theorem Elliptic.HigherHomology.fibreHomologyNorm_three (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    torusH3Coordinates (fibreHomologyNorm j 3 a) = (j.order : ℤ) * torusH3Coordinates a := by
  simp [fibreHomologyNorm, fibreHomologyMonodromy_three]

private def Elliptic.HigherHomology.fibreHomologyNormOneCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1 →ₗ[ℤ] ℤ :=
  (LinearMap.proj (2 : Fin 3)).comp (torusH1Equiv.toLinearMap.comp (fibreHomologyNorm j 1))

private theorem Elliptic.HigherHomology.fibreHomologyNormOneCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    fibreHomologyNormOneCoordinate j a =
      (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j (torusH1Equiv a) := by
  change torusH1Equiv (fibreHomologyNorm j 1 a) 2 = _
  rw [fibreHomologyNorm_one, fibreNorm_apply_two]

private def Elliptic.HigherHomology.fibreHomologyNormTwoCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 →ₗ[ℤ] ℤ :=
  (-LinearMap.proj (1 : Fin 3)).comp (torusH2Coordinates.toLinearMap.comp (fibreHomologyNorm j 2))

private theorem Elliptic.HigherHomology.fibreHomologyNormTwoCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    fibreHomologyNormTwoCoordinate j a = (fibreNormIndex j : ℤ) * torusH2Coordinates a 0 := by
  change -(torusH2Coordinates (fibreHomologyNorm j 2 a) 1) = _
  rw [fibreHomologyNorm_two]
  exact fibreSquareNormCoordinate_apply j (torusH2Coordinates a)

private def Elliptic.HigherHomology.fibreHomologyNormThreeCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 →ₗ[ℤ] ℤ :=
  torusH3Coordinates.toLinearMap.comp (fibreHomologyNorm j 3)

private theorem Elliptic.HigherHomology.fibreHomologyNormThreeCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    fibreHomologyNormThreeCoordinate j a = (j.order : ℤ) * torusH3Coordinates a :=
  fibreHomologyNorm_three j a

@[simp]
private theorem
    Elliptic.HigherHomology.mappingTorusProductCover_eq_productCover (j : Elliptic.Kind) :
    mappingTorusProductCover j =
      MappingTorusHomology.Covering.productCover j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j) :=
  rfl

private theorem
    Elliptic.HigherHomology.fibreHomologyNorm_eq_homologyNorm (j : Elliptic.Kind) (n : ℕ) :
    fibreHomologyNorm j n =
      MappingTorusHomology.Covering.homologyNorm j.order (fibreTorusHomeomorph j) n :=
  (MappingTorusHomology.Covering.homologyNorm_eq_sum_powers j.order (fibreTorusHomeomorph j)
      n).symm

private def Elliptic.HigherHomology.surfacePeriodCoverCircleBoundary (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    SingularMayerVietoris.SingularHomology p.val.Torus (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n :=
  (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) n).comp
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
        (n + 1)).toLinearMap

@[simp]
private theorem Elliptic.HigherHomology.surfacePeriodCoverCircleBoundary_apply (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus (n + 1)) :
    surfacePeriodCoverCircleBoundary j p n a =
      PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
          (n + 1) a) :=
  rfl

private theorem Elliptic.HigherHomology.surfacePeriodCover_wangBoundary (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus (n + 1)) :
    MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm n
        (surfaceMappingTorusHomologyEquiv j p (n + 1)
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) (n + 1) a)) =
      fibreHomologyNorm j n (surfacePeriodCoverCircleBoundary j p n a) := by
  change
    MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p)
          (n + 1)
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) (n + 1) a)) =
      _
  rw [surfaceMappingTorusHomology_periodCover, mappingTorusProductCover_eq_productCover]
  change
    MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm n
        (MappingTorusHomology.Covering.productCoverHomology j.order (fibreTorusHomeomorph j)
          (fibreTorusHomeomorph_pow_order j) (n + 1)
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
            (n + 1) a)) =
      _
  rw [MappingTorusHomology.Covering.wangBoundary_productCover_apply, ←
    fibreHomologyNorm_eq_homologyNorm]
  rfl

private theorem
    Elliptic.HigherHomology.surfacePeriodCoverH2Coordinates_secondMap (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH2Coordinates j p) =
      (fibreHomologyNormOneCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 1) := by
  ext a
  change
    mappingTorusH2Equiv j
        (surfaceMappingTorusHomologyEquiv j p 2
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2 a))
        1 =
      _
  rw [mappingTorusH2Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl

private theorem
    Elliptic.HigherHomology.surfacePeriodCoverH3Coordinates_secondMap (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH3Coordinates j p) =
      (fibreHomologyNormTwoCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 2) := by
  ext a
  change
    mappingTorusH3Equiv j
        (surfaceMappingTorusHomologyEquiv j p 3
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3 a))
        1 =
      _
  rw [mappingTorusH3Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl

private theorem Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates_eq_norm (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    surfacePeriodCoverH4Coordinates j p =
      (fibreHomologyNormThreeCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 3) := by
  ext a
  change
    mappingTorusH4Equiv j
        (surfaceMappingTorusHomologyEquiv j p 4
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 4 a)) =
      torusH3Coordinates (fibreHomologyNorm j 3 (surfacePeriodCoverCircleBoundary j p 3 a))
  rw [mappingTorusH4Equiv_boundary, surfacePeriodCover_wangBoundary]

private theorem Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates_apply (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : SingularMayerVietoris.SingularHomology p.val.Torus 4) :
    surfacePeriodCoverH4Coordinates j p a =
      (j.order : ℤ) * torusH3Coordinates (surfacePeriodCoverCircleBoundary j p 3 a) := by
  rw [surfacePeriodCoverH4Coordinates_eq_norm, LinearMap.comp_apply,
    fibreHomologyNormThreeCoordinate_apply]


private def
    Elliptic.HigherHomology.surfaceH1Equiv (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) 1 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p 1).trans (mappingTorusH1Equiv j)

private theorem Elliptic.HigherHomology.surfaceH1Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    surfaceH1Equiv j p (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 1 a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change
    mappingTorusH1Equiv j
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 1
          (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 1 a)) =
      _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH1Equiv_fibre]

private theorem Elliptic.HigherHomology.surfaceH1Equiv_periodCover_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    surfaceH1Equiv j p
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 1 a)) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change
    surfaceH1Equiv j p
        (((SingularMayerVietoris.singularHomologyMap
                (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1).comp
            (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 1))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact surfaceH1Equiv_fibre j p a

private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_zero (j : Elliptic.Kind) :
    MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 0 = 1 := by
  ext a
  apply torusH0Coordinates.injective
  exact
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
      (fibreTorusHomeomorph j :
        C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
      a

private theorem Elliptic.HigherHomology.fibreHomologyNorm_zero (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0) :
    torusH0Coordinates (fibreHomologyNorm j 0 a) = (j.order : ℤ) * torusH0Coordinates a := by
  simp [fibreHomologyNorm, fibreHomologyMonodromy_zero]

private def Elliptic.HigherHomology.fibreHomologyNormZeroCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0 →ₗ[ℤ] ℤ :=
  torusH0Coordinates.toLinearMap.comp (fibreHomologyNorm j 0)

private theorem Elliptic.HigherHomology.fibreHomologyNormZeroCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0) :
    fibreHomologyNormZeroCoordinate j a = (j.order : ℤ) * torusH0Coordinates a :=
  fibreHomologyNorm_zero j a

private def Elliptic.HigherHomology.surfacePeriodCoverH1Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology p.val.Torus 1 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH1Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1)

private theorem
    Elliptic.HigherHomology.surfacePeriodCoverH1Coordinates_secondMap (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH1Coordinates j p) =
      (fibreHomologyNormZeroCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 0) := by
  ext a
  change
    mappingTorusH1Equiv j
        (surfaceMappingTorusHomologyEquiv j p 1
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1 a))
        1 =
      _
  rw [mappingTorusH1Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl

end Mathoverflow1973

end
