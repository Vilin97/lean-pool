/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Toric.DiagonalQuotient4
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.PeriodFamily.PeriodDomain
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods10
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology9
import all LeanPool.HopfProblem.Foundations.TrianglePeriodFamilyHomologySplitting
import all LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyLattice
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods9
import all LeanPool.HopfProblem.Pi1.TwistGroup
import all LeanPool.HopfProblem.Toric.DiagonalQuotient4

/-!
# Hopf problem: period family · core 5

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

private def PeriodFamily.Homology.slitCoinvariantInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
        LinearMap.range (slitDifference b n)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.Space n :=
  TrianglePeriodFamilyHomologyAlgebra.reducedCokernelToMiddle (overlapHomologyAction b 0 n)
    (overlapHomologyAction b 2 n) (familyMarkedRight D b n) (familyMarked_exact_at_pair D b n)

@[simp]
private theorem PeriodFamily.Homology.slitCoinvariantInclusion_mk
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    slitCoinvariantInclusion D b n (Submodule.Quotient.mk a) = familyMarkedRight D b n (0, -a) :=
  TrianglePeriodFamilyHomologyAlgebra.reducedCokernelToMiddle_mk (overlapHomologyAction b 0 n)
    (overlapHomologyAction b 2 n) (familyMarkedRight D b n) (familyMarked_exact_at_pair D b n) a

private theorem PeriodFamily.Homology.slitCoinvariantInclusion_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    Function.Injective (slitCoinvariantInclusion D b n) :=
  TrianglePeriodFamilyHomologyAlgebra.reducedCokernelToMiddle_injective
    (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n) (familyMarkedRight D b n)
    (familyMarked_exact_at_pair D b n)

private def PeriodFamily.Homology.slitKernelProjection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    SingularMayerVietoris.SingularHomology D.Space (n + 1) →ₗ[ℤ]
      LinearMap.ker (slitDifference b n) :=
  TrianglePeriodFamilyHomologyAlgebra.middleToReducedKernel (overlapHomologyAction b 0 n)
    (overlapHomologyAction b 2 n) (familyMarkedConnecting D b n)
    (familyMarked_exact_at_intersection D b n)

private theorem PeriodFamily.Homology.slitKernelProjection_surjective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    Function.Surjective (slitKernelProjection D b n) :=
  TrianglePeriodFamilyHomologyAlgebra.middleToReducedKernel_surjective
    (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n) (familyMarkedConnecting D b n)
    (familyMarked_exact_at_intersection D b n)

private theorem PeriodFamily.Homology.slitCoinvariantInclusion_kernelProjection_exact
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    Function.Exact (slitCoinvariantInclusion D b (n + 1)) (slitKernelProjection D b n) :=
  TrianglePeriodFamilyHomologyAlgebra.reducedExtension_exact (overlapHomologyAction b 0 (n + 1))
    (overlapHomologyAction b 2 (n + 1)) (overlapHomologyAction b 0 n)
    (overlapHomologyAction b 2 n) (familyMarkedRight D b (n + 1)) (familyMarkedConnecting D b n)
    (familyMarked_exact_at_pair D b (n + 1)) (familyMarked_exact_at_ambient D b n)
    (familyMarked_exact_at_intersection D b n)

private def PeriodFamily.Homology.familyFibreInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) :
    C(RealTorus₄, D.Space) :=
  ⟨fun f => D.quotient (b.val, f),
    D.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩

private def PeriodFamily.Homology.upperFamilyInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : C(upperFamily D, D.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def PeriodFamily.Homology.lowerFamilyInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) : C(lowerFamily D, D.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def PeriodFamily.Homology.upperContractionToBasepoint :
    Path (PeriodTorusHigherHomology.CircleTopology.contractionPoint upperBase) upperBasePoint :=
  PathConnectedSpace.somePath
    (PeriodTorusHigherHomology.CircleTopology.contractionPoint upperBase) upperBasePoint

private def PeriodFamily.Homology.lowerContractionToBasepoint :
    Path (PeriodTorusHigherHomology.CircleTopology.contractionPoint lowerBase) lowerBasePoint :=
  PathConnectedSpace.somePath
    (PeriodTorusHigherHomology.CircleTopology.contractionPoint lowerBase) lowerBasePoint

private def PeriodFamily.Homology.upperFamilyFibreHomotopy
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) :
    ((upperFamilyInclusion D).comp (upperHomotopyEquiv D b).invFun).Homotopy
      (familyFibreInclusion D b)
    where
  toFun x := D.quotient (upperLift b (upperContractionToBasepoint x.1), x.2)
  continuous_toFun :=
    D.quotient_continuous.comp
      (((upperLift b).continuous.comp
            (upperContractionToBasepoint.continuous.comp continuous_fst)).prodMk
        continuous_snd)
  map_zero_left
    f := by
    change
      D.quotient (upperLift b (upperContractionToBasepoint 0), f) =
        D.quotient
          (upperLift b (PeriodTorusHigherHomology.CircleTopology.contractionPoint upperBase), f)
    rw [upperContractionToBasepoint.source]
  map_one_left
    f := by
    change D.quotient (upperLift b (upperContractionToBasepoint 1), f) = D.quotient (b.val, f)
    rw [upperContractionToBasepoint.target, upperLift_basepoint]

private def PeriodFamily.Homology.lowerFamilyFibreHomotopy
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) :
    ((lowerFamilyInclusion D).comp (lowerHomotopyEquiv D b).invFun).Homotopy
      (familyFibreInclusion D b)
    where
  toFun x := D.quotient (lowerLift b (lowerContractionToBasepoint x.1), x.2)
  continuous_toFun :=
    D.quotient_continuous.comp
      (((lowerLift b).continuous.comp
            (lowerContractionToBasepoint.continuous.comp continuous_fst)).prodMk
        continuous_snd)
  map_zero_left
    f := by
    change
      D.quotient (lowerLift b (lowerContractionToBasepoint 0), f) =
        D.quotient
          (lowerLift b (PeriodTorusHigherHomology.CircleTopology.contractionPoint lowerBase), f)
    rw [lowerContractionToBasepoint.source]
  map_one_left
    f := by
    change D.quotient (lowerLift b (lowerContractionToBasepoint 1), f) = D.quotient (b.val, f)
    rw [lowerContractionToBasepoint.target, lowerLift_basepoint]

private theorem PeriodFamily.Homology.upperFamilyInclusion_homology_symm
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap (upperFamilyInclusion D) n
        ((upperHomologyEquiv D b n).symm a) =
      SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) n a := by
  change
    SingularMayerVietoris.singularHomologyMap (upperFamilyInclusion D) n
        (SingularMayerVietoris.singularHomologyMap (upperHomotopyEquiv D b).invFun n a) =
      _
  exact
    LinearMap.congr_fun
      ((PeriodTorusHigherHomology.singularHomologyMap_comp (upperHomotopyEquiv D b).invFun
            (upperFamilyInclusion D) n).symm.trans
        (PeriodTorusHigherHomology.homotopy_homologyMap (upperFamilyFibreHomotopy D b) n))
      a

private theorem PeriodFamily.Homology.lowerFamilyInclusion_homology_symm
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap (lowerFamilyInclusion D) n
        ((lowerHomologyEquiv D b n).symm a) =
      SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) n a := by
  change
    SingularMayerVietoris.singularHomologyMap (lowerFamilyInclusion D) n
        (SingularMayerVietoris.singularHomologyMap (lowerHomotopyEquiv D b).invFun n a) =
      _
  exact
    LinearMap.congr_fun
      ((PeriodTorusHigherHomology.singularHomologyMap_comp (lowerHomotopyEquiv D b).invFun
            (lowerFamilyInclusion D) n).symm.trans
        (PeriodTorusHigherHomology.homotopy_homologyMap (lowerFamilyFibreHomotopy D b) n))
      a

private theorem PeriodFamily.Homology.familyRightHomologyMap_pair_symm
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    familyRightHomologyMap D n ((pairHomologyEquiv D b n).symm a) =
      SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) n (a.1 + a.2) := by
  refine
    (SingularMayerVietoris.rightHomologyMap_apply (upperFamily D : Set D.Space) (lowerFamily D) n
          ((pairHomologyEquiv D b n).symm a)).trans
      ?_
  change
    SingularMayerVietoris.singularHomologyMap (upperFamilyInclusion D) n
          ((upperHomologyEquiv D b n).symm a.1) +
        SingularMayerVietoris.singularHomologyMap (lowerFamilyInclusion D) n
          ((lowerHomologyEquiv D b n).symm a.2) =
      _
  rw [upperFamilyInclusion_homology_symm, lowerFamilyInclusion_homology_symm, map_add]

private theorem PeriodFamily.Homology.familyRightHomologyMap_pair
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (upperFamily D) n ×
        SingularMayerVietoris.SingularHomology (lowerFamily D) n) :
    familyRightHomologyMap D n a =
      SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) n
        ((pairHomologyEquiv D b n a).1 + (pairHomologyEquiv D b n a).2) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    familyRightHomologyMap_pair_symm D b n (pairHomologyEquiv D b n a)

private theorem PeriodFamily.Homology.familyRightHomologyMap_range_eq_fibre
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    LinearMap.range (familyRightHomologyMap D n) =
      LinearMap.range (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) n) := by
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    refine ⟨(pairHomologyEquiv D b n a).1 + (pairHomologyEquiv D b n a).2, ?_⟩
    exact (familyRightHomologyMap_pair D b n a).symm
  · rintro y ⟨a, rfl⟩
    refine ⟨(pairHomologyEquiv D b n).symm (a, 0), ?_⟩
    simpa only [add_zero] using familyRightHomologyMap_pair_symm D b n (a, 0)

private theorem PeriodFamily.Homology.familyConnectingHomomorphism_ker_eq_fibre
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ) :
    LinearMap.ker (familyConnectingHomomorphism D n) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) (n + 1)) :=
  (LinearMap.exact_iff.mp (family_exact_at_ambient D n)).trans
    (familyRightHomologyMap_range_eq_fibre D b (n + 1))

@[simp]
private theorem PeriodFamily.Homology.normalizedSlitCokernelEquiv_symm_mk (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    (normalizedSlitCokernelEquiv n).symm (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := by
  apply (normalizedSlitCokernelEquiv n).injective
  rw [LinearEquiv.apply_symm_apply, normalizedSlitCokernelEquiv_mk]

private theorem PeriodFamily.Homology.familyMarkedRight_eq_fibre
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    familyMarkedRight D b n a =
      SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) n (a.1 + a.2) :=
  familyRightHomologyMap_pair_symm D b n a

private def PeriodFamily.Homology.sourceCoinvariantInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
        LinearMap.range (sourceDifference n)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.Space n :=
  -((slitCoinvariantInclusion D normalizedSlitBaseLift n).comp
      (normalizedSlitCokernelEquiv n).symm.toLinearMap)

@[simp]
private theorem PeriodFamily.Homology.sourceCoinvariantInclusion_apply
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
        LinearMap.range (sourceDifference n)) :
    sourceCoinvariantInclusion D n a =
      -slitCoinvariantInclusion D normalizedSlitBaseLift n
          ((normalizedSlitCokernelEquiv n).symm a) :=
  rfl

private theorem PeriodFamily.Homology.sourceCoinvariantInclusion_mk
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    sourceCoinvariantInclusion D n (Submodule.Quotient.mk a) =
      SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) n
        a := by
  rw [sourceCoinvariantInclusion_apply, normalizedSlitCokernelEquiv_symm_mk,
    slitCoinvariantInclusion_mk, familyMarkedRight_eq_fibre]
  simp only [zero_add, map_neg, neg_neg]

private theorem PeriodFamily.Homology.sourceCoinvariantInclusion_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Function.Injective (sourceCoinvariantInclusion D n) := by
  intro a b hab
  have hneg :
    -slitCoinvariantInclusion D normalizedSlitBaseLift n
          ((normalizedSlitCokernelEquiv n).symm a) =
      -slitCoinvariantInclusion D normalizedSlitBaseLift n
          ((normalizedSlitCokernelEquiv n).symm b) :=
    hab
  exact
    (normalizedSlitCokernelEquiv n).symm.injective
      (slitCoinvariantInclusion_injective D normalizedSlitBaseLift n (neg_injective hneg))

private def PeriodFamily.Homology.sourceKernelProjection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.SingularHomology D.Space (n + 1) →ₗ[ℤ]
      LinearMap.ker (sourceDifference n) :=
  (normalizedSlitKernelEquiv n).toLinearMap.comp (slitKernelProjection D normalizedSlitBaseLift n)

@[simp]
private theorem PeriodFamily.Homology.sourceKernelProjection_apply
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology D.Space (n + 1)) :
    sourceKernelProjection D n a =
      normalizedSlitKernelEquiv n (slitKernelProjection D normalizedSlitBaseLift n a) :=
  rfl

private theorem PeriodFamily.Homology.sourceKernelProjection_surjective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Function.Surjective (sourceKernelProjection D n) :=
  (normalizedSlitKernelEquiv n).surjective.comp
    (slitKernelProjection_surjective D normalizedSlitBaseLift n)

private theorem PeriodFamily.Homology.sourceCoinvariantInclusion_kernelProjection_exact
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Function.Exact (sourceCoinvariantInclusion D (n + 1)) (sourceKernelProjection D n) := by
  intro a
  constructor
  · intro ha
    have hzero : slitKernelProjection D normalizedSlitBaseLift n a = 0 := by
      apply (normalizedSlitKernelEquiv n).injective
      exact ha.trans (normalizedSlitKernelEquiv n).map_zero.symm
    obtain ⟨q, hq⟩ :=
      (slitCoinvariantInclusion_kernelProjection_exact D normalizedSlitBaseLift n a).mp hzero
    refine ⟨-normalizedSlitCokernelEquiv (n + 1) q, ?_⟩
    rw [sourceCoinvariantInclusion_apply, map_neg, LinearEquiv.symm_apply_apply, map_neg, neg_neg]
    exact hq
  · rintro ⟨q, rfl⟩
    have hex := slitCoinvariantInclusion_kernelProjection_exact D normalizedSlitBaseLift n
    rw [sourceKernelProjection_apply, sourceCoinvariantInclusion_apply, map_neg,
      hex.apply_apply_eq_zero, neg_zero, map_zero]

private theorem PeriodFamily.Homology.familyFibreInclusion_kernel
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift)
          n) =
      LinearMap.range (sourceDifference n) := by
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) n
          a =
        0 ↔
      _
  rw [← sourceCoinvariantInclusion_mk]
  constructor
  · intro ha
    have hq :
      (Submodule.Quotient.mk a :
          SingularMayerVietoris.SingularHomology RealTorus₄ n ⧸
            LinearMap.range (sourceDifference n)) =
        0 :=
      sourceCoinvariantInclusion_injective D n (ha.trans (map_zero _).symm)
    exact
      (Submodule.Quotient.mk_eq_zero (p := LinearMap.range (sourceDifference n)) (x := a)).mp hq
  · intro ha
    rw [(Submodule.Quotient.mk_eq_zero (p := LinearMap.range (sourceDifference n)) (x := a)).mpr
        ha,
      map_zero]

private theorem PeriodFamily.Homology.sourceCoinvariantInclusion_range
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    LinearMap.range (sourceCoinvariantInclusion D n) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift)
          n) := by
  apply le_antisymm
  · rintro a ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨x, (sourceCoinvariantInclusion_mk D n x).symm⟩
  · rintro a ⟨x, rfl⟩
    exact ⟨Submodule.Quotient.mk x, sourceCoinvariantInclusion_mk D n x⟩

private theorem PeriodFamily.Homology.sourceKernelProjection_kernel
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    LinearMap.ker (sourceKernelProjection D n) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift)
          (n + 1)) :=
  (LinearMap.exact_iff.mp (sourceCoinvariantInclusion_kernelProjection_exact D n)).trans
    (sourceCoinvariantInclusion_range D (n + 1))

private def PeriodFamily.Homology.familyHomologySplitEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ)
    [Module.Free ℤ (LinearMap.ker (sourceDifference n))] :
    SingularMayerVietoris.SingularHomology D.Space (n + 1) ≃ₗ[ℤ]
      ((SingularMayerVietoris.SingularHomology RealTorus₄ (n + 1) ⧸
          LinearMap.range (sourceDifference (n + 1))) ×
        LinearMap.ker (sourceDifference n)) :=
  TrianglePeriodFamilyHomologySplitting.freeRightSplitEquiv (sourceCoinvariantInclusion D (n + 1))
    (sourceKernelProjection D n) (sourceCoinvariantInclusion_kernelProjection_exact D n)
    (sourceCoinvariantInclusion_injective D (n + 1)) (sourceKernelProjection_surjective D n)

private def PeriodFamily.Homology.familyHomologyMarkedEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) {L K : Type*}
    [AddCommGroup L] [AddCommGroup K] [Module ℤ K]
    (ec :
      (SingularMayerVietoris.SingularHomology RealTorus₄ (n + 1) ⧸
          LinearMap.range (sourceDifference (n + 1))) ≃+
        L)
    (ek : LinearMap.ker (sourceDifference n) ≃+ K) [Module.Free ℤ K] :
    SingularMayerVietoris.SingularHomology D.Space (n + 1) ≃ₗ[ℤ] (L × K) := by
  letI := Module.Free.of_equiv ek.toIntLinearEquiv.symm
  exact ((familyHomologySplitEquiv D n).toAddEquiv.trans (ec.prodCongr ek)).toIntLinearEquiv

private theorem PeriodFamily.FlatTorus.flatTorusCircleHomeomorph_triangle
    (g : SpecialPeriods.TriangleGroup) (x : RealTorus₄) :
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph
        (SpecialPeriods.triangleTorusHomeomorph g x) =
      PeriodTorusHigherHomology.torusMatrixMap
        (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix)
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph x) := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  simp only [SpecialPeriods.triangleTorusHomeomorph_mkQ,
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ,
    PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection,
    SpecialPeriods.triangleRealEquiv_apply]

private theorem PeriodFamily.FlatTorus.flatTorusCircleHomeomorph_triangle_comp
    (g : SpecialPeriods.TriangleGroup) :
    (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)).comp
        (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) =
      (PeriodTorusHigherHomology.torusMatrixMap
            (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix)).comp
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)) := by
  apply ContinuousMap.ext
  intro x
  exact flatTorusCircleHomeomorph_triangle g x

@[simp]
private theorem PeriodFamily.FlatTorus.flatTorusCircleHomeomorph_zero :
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph (0 : RealTorus₄) = 0 :=
  PeriodTorusHigherHomology.flatTorusCircleMap.map_zero

private theorem PeriodFamily.FlatTorus.flatTorusCircleHomeomorph_periodLoop_apply (c : Lattice)
    (t : unitInterval) :
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph (periodLoop c t) =
      PeriodTorusHigherHomology.coordinatePeriodLoop 4 c t := by
  rw [periodLoop_apply, PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ]
  ext i
  rw [PeriodTorusHigherHomology.coordinatePeriodLoop_apply]
  rfl

private theorem PeriodFamily.FlatTorus.flatTorusCircleHomeomorph_periodLoop (c : Lattice) :
    (periodLoop c).map PeriodTorusHigherHomology.flatTorusCircleHomeomorph.continuous =
      (PeriodTorusHigherHomology.coordinatePeriodLoop 4 c).cast flatTorusCircleHomeomorph_zero
        flatTorusCircleHomeomorph_zero := by
  apply Path.ext
  funext t
  exact flatTorusCircleHomeomorph_periodLoop_apply c t

private theorem PeriodFamily.FlatTorus.inducedHomology_periodLoop_circle (c : Lattice) :
    FirstHurewicz.inducedHomology
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        (FirstHurewicz.loopHomologyClass (periodLoop c)) =
      FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 4 c) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, flatTorusCircleHomeomorph_periodLoop]
  rfl

private theorem PeriodFamily.FlatTorus.inducedHomology_singularH1Equiv_symm_circle (c : Lattice) :
    FirstHurewicz.inducedHomology
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        (singularH1Equiv.symm c) =
      FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 4 c) := by
  rw [singularH1Equiv_symm_apply, inducedHomology_periodLoop_circle]

private theorem PeriodFamily.FlatTorus.coordinateH1_eq_flatMarking :
    PeriodTorusHigherHomology.coordinateH1 4 =
      (FirstHurewicz.inducedHomology
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
              C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))).comp
        singularH1Equiv.symm.toLinearMap := by
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro i
  change
    PeriodTorusHigherHomology.coordinateH1 4 (Pi.basisFun ℤ (Fin 4) i) =
      FirstHurewicz.inducedHomology
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        (singularH1Equiv.symm (Pi.basisFun ℤ (Fin 4) i))
  rw [PeriodTorusHigherHomology.coordinateH1_basis, inducedHomology_singularH1Equiv_symm_circle]
  simp only [Pi.basisFun_apply]

private theorem PeriodFamily.FlatTorus.coordinateH1_flatMarking (c : Lattice) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        1 (singularH1Equiv.symm c) =
      PeriodTorusHigherHomology.coordinateH1 4 c :=
  (LinearMap.congr_fun coordinateH1_eq_flatMarking c).symm

private def PeriodFamily.FlatTorus.singularH2Equiv :
    SingularMayerVietoris.SingularHomology RealTorus₄ 2 ≃ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 2 :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        PeriodTorusHigherHomology.flatTorusCircleHomeomorph 2).trans
    PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv

private def PeriodFamily.FlatTorus.singularH3Equiv :
    SingularMayerVietoris.SingularHomology RealTorus₄ 3 ≃ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 3 :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        PeriodTorusHigherHomology.flatTorusCircleHomeomorph 3).trans
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv

@[simp]
private theorem PeriodFamily.FlatTorus.singularH2Equiv_apply
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    singularH2Equiv a =
      PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          2 a) :=
  rfl

@[simp]
private theorem PeriodFamily.FlatTorus.singularH3Equiv_apply
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    singularH3Equiv a =
      PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          3 a) :=
  rfl

private def PeriodFamily.FlatTorus.singularH2Coordinates :
    SingularMayerVietoris.SingularHomology RealTorus₄ 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  singularH2Equiv.trans PeriodTorusHigherHomologyExterior.squareCoordinates

private def PeriodFamily.FlatTorus.singularH3Coordinates :
    SingularMayerVietoris.SingularHomology RealTorus₄ 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  singularH3Equiv.trans PeriodTorusHigherHomologyExterior.cubeCoordinates

@[simp]
private theorem PeriodFamily.FlatTorus.singularH2Coordinates_apply
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    singularH2Coordinates a =
      PeriodTorusHigherHomologyExterior.squareCoordinates (singularH2Equiv a) :=
  rfl

@[simp]
private theorem PeriodFamily.FlatTorus.singularH3Coordinates_apply
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    singularH3Coordinates a =
      PeriodTorusHigherHomologyExterior.cubeCoordinates (singularH3Equiv a) :=
  rfl

private theorem
    PeriodFamily.FlatTorus.flatTorusCircleHomology_triangle (g : SpecialPeriods.TriangleGroup)
    (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
              C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
            n).comp
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) n) =
      (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.torusMatrixMap
              (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix))
            n).comp
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          n) := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, flatTorusCircleHomeomorph_triangle_comp]

private theorem PeriodFamily.FlatTorus.flatTorusCircleHomology_triangle_apply
    (g : SpecialPeriods.TriangleGroup) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        n
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) n a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap
          (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix))
        n
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          n a) :=
  LinearMap.congr_fun (flatTorusCircleHomology_triangle g n) a

private theorem PeriodFamily.FlatTorus.singularH2Equiv_inducedHomology_triangle
    (g : SpecialPeriods.TriangleGroup) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    singularH2Equiv
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2 a) =
      exteriorPower.map 2 (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (singularH2Equiv a) := by
  change
    PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          2
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2 a)) =
      exteriorPower.map 2 (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
              C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
            2 a))
  rw [flatTorusCircleHomology_triangle_apply,
    PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_matrix]

private theorem PeriodFamily.FlatTorus.singularH3Equiv_inducedHomology_triangle
    (g : SpecialPeriods.TriangleGroup) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    singularH3Equiv
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3 a) =
      exteriorPower.map 3 (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (singularH3Equiv a) := by
  change
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          3
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3 a)) =
      exteriorPower.map 3 (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
              C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
            3 a))
  rw [flatTorusCircleHomology_triangle_apply,
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_matrix]

private theorem PeriodFamily.FlatTorus.singularH2Coordinates_inducedHomology_triangle
    (g : SpecialPeriods.TriangleGroup) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    singularH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 2 a) =
      LocalSystemMatrices.exteriorSquare
          (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) *ᵥ
        singularH2Coordinates a := by
  rw [singularH2Coordinates_apply, singularH2Equiv_inducedHomology_triangle]
  exact
    PeriodTorusHigherHomologyExterior.squareCoordinates_map
      (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) (singularH2Equiv a)

private theorem PeriodFamily.FlatTorus.singularH3Coordinates_inducedHomology_triangle
    (g : SpecialPeriods.TriangleGroup) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 3 a) =
      LocalSystemMatrices.exteriorCube
          (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) *ᵥ
        singularH3Coordinates a := by
  rw [singularH3Coordinates_apply, singularH3Equiv_inducedHomology_triangle]
  exact
    PeriodTorusHigherHomologyExterior.cubeCoordinates_map
      (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) (singularH3Equiv a)

private theorem PeriodFamily.HomologyDifference.generatorHomologyTwo_coordinates (j : Bool)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (PeriodFamily.Homology.generatorHomologyEquiv j 2 a) =
      (if j then PeriodTorusHigherHomologyExterior.squareA₂
        else PeriodTorusHigherHomologyExterior.squareA₁) *ᵥ
        PeriodFamily.FlatTorus.singularH2Coordinates a := by
  cases j
  · change
      PeriodFamily.FlatTorus.singularH2Coordinates
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleGenerator₁ :
              C(RealTorus₄, RealTorus₄))
            2 a) =
        _
    rw [PeriodFamily.FlatTorus.singularH2Coordinates_inducedHomology_triangle,
      SpecialPeriods.triangleDualRepresentation_generator₁_matrix]
    rfl
  · change
      PeriodFamily.FlatTorus.singularH2Coordinates
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleGenerator₂ :
              C(RealTorus₄, RealTorus₄))
            2 a) =
        _
    rw [PeriodFamily.FlatTorus.singularH2Coordinates_inducedHomology_triangle,
      SpecialPeriods.triangleDualRepresentation_generator₂_matrix]
    rfl

private theorem PeriodFamily.HomologyDifference.sourceDifferenceTwo_coordinates
    (x :
      SingularMayerVietoris.SingularHomology RealTorus₄ 2 ×
        SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    PeriodFamily.FlatTorus.singularH2Coordinates (PeriodFamily.Homology.sourceDifference 2 x) =
      TrianglePeriodFamilyHomologyLattice.deltaTwo
        (PeriodFamily.FlatTorus.singularH2Coordinates x.1,
          PeriodFamily.FlatTorus.singularH2Coordinates x.2) := by
  change
    PeriodFamily.FlatTorus.singularH2Coordinates
        ((PeriodFamily.Homology.generatorHomologyEquiv Bool.false 2 x.1 - x.1) +
          (PeriodFamily.Homology.generatorHomologyEquiv Bool.true 2 x.2 - x.2)) =
      (PeriodTorusHigherHomologyExterior.squareA₁ *ᵥ
            PeriodFamily.FlatTorus.singularH2Coordinates x.1 -
          PeriodFamily.FlatTorus.singularH2Coordinates x.1) +
        (PeriodTorusHigherHomologyExterior.squareA₂ *ᵥ
            PeriodFamily.FlatTorus.singularH2Coordinates x.2 -
          PeriodFamily.FlatTorus.singularH2Coordinates x.2)
  rw [map_add, map_sub, map_sub, generatorHomologyTwo_coordinates,
    generatorHomologyTwo_coordinates]
  rfl

private theorem PeriodFamily.HomologyDifference.generatorHomologyThree_coordinates (j : Bool)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (PeriodFamily.Homology.generatorHomologyEquiv j 3 a) =
      (if j then PeriodTorusHigherHomologyExterior.cubeA₂
        else PeriodTorusHigherHomologyExterior.cubeA₁) *ᵥ
        PeriodFamily.FlatTorus.singularH3Coordinates a := by
  cases j
  · change
      PeriodFamily.FlatTorus.singularH3Coordinates
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleGenerator₁ :
              C(RealTorus₄, RealTorus₄))
            3 a) =
        _
    rw [PeriodFamily.FlatTorus.singularH3Coordinates_inducedHomology_triangle,
      SpecialPeriods.triangleDualRepresentation_generator₁_matrix]
    rfl
  · change
      PeriodFamily.FlatTorus.singularH3Coordinates
          (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleGenerator₂ :
              C(RealTorus₄, RealTorus₄))
            3 a) =
        _
    rw [PeriodFamily.FlatTorus.singularH3Coordinates_inducedHomology_triangle,
      SpecialPeriods.triangleDualRepresentation_generator₂_matrix]
    rfl

private theorem PeriodFamily.HomologyDifference.sourceDifferenceThree_coordinates
    (x :
      SingularMayerVietoris.SingularHomology RealTorus₄ 3 ×
        SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates (PeriodFamily.Homology.sourceDifference 3 x) =
      TrianglePeriodFamilyHomologyLattice.deltaThree
        (PeriodFamily.FlatTorus.singularH3Coordinates x.1,
          PeriodFamily.FlatTorus.singularH3Coordinates x.2) := by
  change
    PeriodFamily.FlatTorus.singularH3Coordinates
        ((PeriodFamily.Homology.generatorHomologyEquiv Bool.false 3 x.1 - x.1) +
          (PeriodFamily.Homology.generatorHomologyEquiv Bool.true 3 x.2 - x.2)) =
      (PeriodTorusHigherHomologyExterior.cubeA₁ *ᵥ
            PeriodFamily.FlatTorus.singularH3Coordinates x.1 -
          PeriodFamily.FlatTorus.singularH3Coordinates x.1) +
        (PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ
            PeriodFamily.FlatTorus.singularH3Coordinates x.2 -
          PeriodFamily.FlatTorus.singularH3Coordinates x.2)
  rw [map_add, map_sub, map_sub, generatorHomologyThree_coordinates,
    generatorHomologyThree_coordinates]
  rfl

private theorem PeriodFamily.HomologyDifference.generatorHomologyOne_false_coordinates
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (PeriodFamily.Homology.generatorHomologyEquiv Bool.false 1 a) =
      A₁ *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a := by
  change
    PeriodFamily.FlatTorus.singularH1Equiv
        (FirstHurewicz.inducedHomology
          (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleGenerator₁ :
            C(RealTorus₄, RealTorus₄))
          a) =
      _
  rw [PeriodFamily.FlatTorus.singularH1Equiv_inducedHomology_triangle,
    SpecialPeriods.triangleDualRepresentation_generator₁_matrix]

private theorem PeriodFamily.HomologyDifference.generatorHomologyOne_true_coordinates
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (PeriodFamily.Homology.generatorHomologyEquiv Bool.true 1 a) =
      A₂ *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a := by
  change
    PeriodFamily.FlatTorus.singularH1Equiv
        (FirstHurewicz.inducedHomology
          (SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleGenerator₂ :
            C(RealTorus₄, RealTorus₄))
          a) =
      _
  rw [PeriodFamily.FlatTorus.singularH1Equiv_inducedHomology_triangle,
    SpecialPeriods.triangleDualRepresentation_generator₂_matrix]

private theorem PeriodFamily.HomologyDifference.sourceDifferenceOne_coordinates
    (x :
      SingularMayerVietoris.SingularHomology RealTorus₄ 1 ×
        SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv (PeriodFamily.Homology.sourceDifference 1 x) =
      TrianglePeriodFamilyHomologyLattice.deltaOne
        (PeriodFamily.FlatTorus.singularH1Equiv x.1,
          PeriodFamily.FlatTorus.singularH1Equiv x.2) := by
  change
    PeriodFamily.FlatTorus.singularH1Equiv
        ((PeriodFamily.Homology.generatorHomologyEquiv Bool.false 1 x.1 - x.1) +
          (PeriodFamily.Homology.generatorHomologyEquiv Bool.true 1 x.2 - x.2)) =
      (A₁ *ᵥ PeriodFamily.FlatTorus.singularH1Equiv x.1 -
          PeriodFamily.FlatTorus.singularH1Equiv x.1) +
        (A₂ *ᵥ PeriodFamily.FlatTorus.singularH1Equiv x.2 -
          PeriodFamily.FlatTorus.singularH1Equiv x.2)
  rw [map_add, map_sub, map_sub, generatorHomologyOne_false_coordinates,
    generatorHomologyOne_true_coordinates]

private theorem PeriodFamily.HomologyDifference.sourceDifferenceZero_coordinates
    (x :
      SingularMayerVietoris.SingularHomology RealTorus₄ 0 ×
        SingularMayerVietoris.SingularHomology RealTorus₄ 0) :
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄
        (PeriodFamily.Homology.sourceDifference 0 x) =
      TrianglePeriodFamilyHomologyLattice.deltaZero
        (PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄ x.1,
          PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄ x.2) := by
  rw [PeriodFamily.Homology.sourceDifference_zero,
    TrianglePeriodFamilyHomologyLattice.deltaZero_eq_zero]
  simp only [LinearMap.zero_apply, map_zero]

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelZeroCoordinates :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 0) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaZero :=
  kernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 0)
    TrianglePeriodFamilyHomologyLattice.deltaZero
    ((PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄).toAddEquiv.prodCongr
        (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
            RealTorus₄).toAddEquiv).toIntLinearEquiv
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄)
    sourceDifferenceZero_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelZeroEquiv :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 0) ≃ₗ[ℤ] (ℤ × ℤ) :=
  (kernelZeroCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.kernelZeroEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelOneCoordinates :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 1) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaOne :=
  kernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 1)
    TrianglePeriodFamilyHomologyLattice.deltaOne
    (PeriodFamily.FlatTorus.singularH1Equiv.toAddEquiv.prodCongr
        PeriodFamily.FlatTorus.singularH1Equiv.toAddEquiv).toIntLinearEquiv
    PeriodFamily.FlatTorus.singularH1Equiv sourceDifferenceOne_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelOneEquiv :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 1) ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  (kernelOneCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.kernelOneEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelOneCoordinates :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 1 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 1)) ≃ₗ[ℤ]
      (Lattice ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaOne) :=
  cokernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 1)
    TrianglePeriodFamilyHomologyLattice.deltaOne
    (PeriodFamily.FlatTorus.singularH1Equiv.toAddEquiv.prodCongr
        PeriodFamily.FlatTorus.singularH1Equiv.toAddEquiv).toIntLinearEquiv
    PeriodFamily.FlatTorus.singularH1Equiv sourceDifferenceOne_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelOneEquiv :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 1 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 1)) ≃ₗ[ℤ]
      ℤ :=
  (cokernelOneCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.cokernelOneEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelTwoCoordinates :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 2) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaTwo :=
  kernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 2)
    TrianglePeriodFamilyHomologyLattice.deltaTwo
    (PeriodFamily.FlatTorus.singularH2Coordinates.toAddEquiv.prodCongr
        PeriodFamily.FlatTorus.singularH2Coordinates.toAddEquiv).toIntLinearEquiv
    PeriodFamily.FlatTorus.singularH2Coordinates sourceDifferenceTwo_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelTwoEquiv :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 2) ≃ₗ[ℤ] (Fin 7 → ℤ) :=
  (kernelTwoCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.kernelTwoEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelTwoCoordinates :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 2 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 2)) ≃ₗ[ℤ]
      ((Fin 6 → ℤ) ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaTwo) :=
  cokernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 2)
    TrianglePeriodFamilyHomologyLattice.deltaTwo
    (PeriodFamily.FlatTorus.singularH2Coordinates.toAddEquiv.prodCongr
        PeriodFamily.FlatTorus.singularH2Coordinates.toAddEquiv).toIntLinearEquiv
    PeriodFamily.FlatTorus.singularH2Coordinates sourceDifferenceTwo_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
@[simp]
private theorem PeriodFamily.HomologyDifference.cokernelTwoCoordinates_mk
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    cokernelTwoCoordinates (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (PeriodFamily.FlatTorus.singularH2Coordinates a) :=
  rfl

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelTwoEquiv :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 2 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 2)) ≃ₗ[ℤ]
      ℤ :=
  (cokernelTwoCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
@[simp]
private theorem PeriodFamily.HomologyDifference.cokernelTwoEquiv_mk
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    cokernelTwoEquiv (Submodule.Quotient.mk a) =
      6 * PeriodFamily.FlatTorus.singularH2Coordinates a 2 +
        PeriodFamily.FlatTorus.singularH2Coordinates a 3 := by
  change
    TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv
        (cokernelTwoCoordinates (Submodule.Quotient.mk a)) =
      _
  rw [cokernelTwoCoordinates_mk]
  exact TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv_mk _

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelThreeCoordinates :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 3) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaThree :=
  kernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 3)
    TrianglePeriodFamilyHomologyLattice.deltaThree
    (PeriodFamily.FlatTorus.singularH3Coordinates.toAddEquiv.prodCongr
        PeriodFamily.FlatTorus.singularH3Coordinates.toAddEquiv).toIntLinearEquiv
    PeriodFamily.FlatTorus.singularH3Coordinates sourceDifferenceThree_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelThreeEquiv :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 3) ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  (kernelThreeCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.kernelThreeEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelThreeCoordinates :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 3 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 3)) ≃ₗ[ℤ]
      (Lattice ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaThree) :=
  cokernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 3)
    TrianglePeriodFamilyHomologyLattice.deltaThree
    (PeriodFamily.FlatTorus.singularH3Coordinates.toAddEquiv.prodCongr
        PeriodFamily.FlatTorus.singularH3Coordinates.toAddEquiv).toIntLinearEquiv
    PeriodFamily.FlatTorus.singularH3Coordinates sourceDifferenceThree_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
@[simp]
private theorem PeriodFamily.HomologyDifference.cokernelThreeCoordinates_mk
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    cokernelThreeCoordinates (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (PeriodFamily.FlatTorus.singularH3Coordinates a) :=
  rfl

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelThreeEquiv :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 3 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 3)) ≃ₗ[ℤ]
      ℤ :=
  (cokernelThreeCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
@[simp]
private theorem PeriodFamily.HomologyDifference.cokernelThreeEquiv_mk
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    cokernelThreeEquiv (Submodule.Quotient.mk a) =
      PeriodFamily.FlatTorus.singularH3Coordinates a 0 := by
  change
    TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv
        (cokernelThreeCoordinates (Submodule.Quotient.mk a)) =
      _
  rw [cokernelThreeCoordinates_mk]
  exact TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv_mk _

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
@[simp]
private theorem PeriodFamily.HomologyDifference.cokernelThreeEquiv_symm_apply (z : ℤ) :
    cokernelThreeEquiv.symm z =
      Submodule.Quotient.mk (PeriodFamily.FlatTorus.singularH3Coordinates.symm ![z, 0, 0, 0]) := by
  apply cokernelThreeEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelThreeEquiv_mk]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

private def
    PeriodFamily.Homology.headMapFibre {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) : C(X, Y) :=
  (PeriodTorusHigherHomology.CircleTopology.productProjection Y).comp
    (F.comp ((ContinuousMap.const X z).prodMk (ContinuousMap.id X)))

private theorem PeriodFamily.Homology.headMap_mapsToU {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    Set.MapsTo F (PeriodTorusHigherHomology.CircleTopology.productU X)
      (PeriodTorusHigherHomology.CircleTopology.productU Y) := by
  intro z hz
  change (F z).1 ∈ PeriodTorusHigherHomology.CircleTopology.arcU
  rw [hF]
  exact hz

private theorem PeriodFamily.Homology.headMap_mapsToV {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    Set.MapsTo F (PeriodTorusHigherHomology.CircleTopology.productV X)
      (PeriodTorusHigherHomology.CircleTopology.productV Y) := by
  intro z hz
  change (F z).1 ∈ PeriodTorusHigherHomology.CircleTopology.arcV
  rw [hF]
  exact hz

private def PeriodFamily.Homology.headIntersectionMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    C(↥(PeriodTorusHigherHomology.CircleTopology.productU X ∩
          PeriodTorusHigherHomology.CircleTopology.productV X),
      ↥(PeriodTorusHigherHomology.CircleTopology.productU Y ∩
          PeriodTorusHigherHomology.CircleTopology.productV Y)) :=
  SingularMayerVietoris.intersectionRestriction F
    (PeriodTorusHigherHomology.CircleTopology.productU X)
    (PeriodTorusHigherHomology.CircleTopology.productV X)
    (PeriodTorusHigherHomology.CircleTopology.productU Y)
    (PeriodTorusHigherHomology.CircleTopology.productV Y) (headMap_mapsToU F hF)
    (headMap_mapsToV F hF)

private theorem PeriodFamily.Homology.headIntersectionMap_quarter {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    (headIntersectionMap F hF).comp
        (PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection X) =
      (PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection Y).comp
        (headMapFibre F PeriodTorusHigherHomology.CirclePaths.quarterPoint) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact hF (PeriodTorusHigherHomology.CirclePaths.quarterPoint, x)
  · rfl

private theorem
    PeriodFamily.Homology.headIntersectionMap_threeQuarter {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    (headIntersectionMap F hF).comp
        (PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection X) =
      (PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection Y).comp
        (headMapFibre F PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact hF (PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint, x)
  · rfl

private theorem PeriodFamily.Homology.intersectionHomology_sections {X : Type} [TopologicalSpace X]
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (PeriodTorusHigherHomology.CircleTopology.productU X ∩
            PeriodTorusHigherHomology.CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    a =
      SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection X) n
          (PeriodTorusHigherHomology.productIntersectionHomologyEquiv X n a).1 +
        SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection X) n
          (PeriodTorusHigherHomology.productIntersectionHomologyEquiv X n a).2 := by
  apply (PeriodTorusHigherHomology.productIntersectionHomologyEquiv X n).injective
  rw [map_add, PeriodTorusHigherHomology.quarterIntersectionHomology_coordinates,
    PeriodTorusHigherHomology.threeQuarterIntersectionHomology_coordinates]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]

private theorem
    PeriodFamily.Homology.headIntersectionHomology_quarter {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    PeriodTorusHigherHomology.productIntersectionHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (headIntersectionMap F hF) n
          (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection X) n a)) =
      (SingularMayerVietoris.singularHomologyMap
          (headMapFibre F PeriodTorusHigherHomology.CirclePaths.quarterPoint) n a,
        0) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    headIntersectionMap_quarter, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, PeriodTorusHigherHomology.quarterIntersectionHomology_coordinates]

private theorem PeriodFamily.Homology.headIntersectionHomology_threeQuarter {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    PeriodTorusHigherHomology.productIntersectionHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (headIntersectionMap F hF) n
          (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection X) n a)) =
      (0,
        SingularMayerVietoris.singularHomologyMap
          (headMapFibre F PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint) n a) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    headIntersectionMap_threeQuarter, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, PeriodTorusHigherHomology.threeQuarterIntersectionHomology_coordinates]

private theorem PeriodFamily.Homology.headIntersectionHomology_coordinates {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (PeriodTorusHigherHomology.CircleTopology.productU X ∩
            PeriodTorusHigherHomology.CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    PeriodTorusHigherHomology.productIntersectionHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (headIntersectionMap F hF) n a) =
      (SingularMayerVietoris.singularHomologyMap
          (headMapFibre F PeriodTorusHigherHomology.CirclePaths.quarterPoint) n
          (PeriodTorusHigherHomology.productIntersectionHomologyEquiv X n a).1,
        SingularMayerVietoris.singularHomologyMap
          (headMapFibre F PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint) n
          (PeriodTorusHigherHomology.productIntersectionHomologyEquiv X n a).2) := by
  conv_lhs => rw [intersectionHomology_sections n a]
  rw [map_add, map_add, headIntersectionHomology_quarter, headIntersectionHomology_threeQuarter]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

private theorem PeriodFamily.Homology.circleConnecting_headMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (headIntersectionMap F hF) n
        (PeriodTorusHigherHomology.circleMayerVietorisConnecting X n a) =
      PeriodTorusHigherHomology.circleMayerVietorisConnecting Y n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) :=
  SingularMayerVietoris.connectingHomomorphism_naturality_apply F
    (PeriodTorusHigherHomology.CircleTopology.productU X)
    (PeriodTorusHigherHomology.CircleTopology.productV X)
    (PeriodTorusHigherHomology.CircleTopology.productU Y)
    (PeriodTorusHigherHomology.CircleTopology.productV Y) (headMap_mapsToU F hF)
    (headMap_mapsToV F hF) (PeriodTorusHigherHomology.CircleTopology.productU_open X)
    (PeriodTorusHigherHomology.CircleTopology.productV_open X)
    (PeriodTorusHigherHomology.CircleTopology.product_cover X)
    (PeriodTorusHigherHomology.CircleTopology.productU_open Y)
    (PeriodTorusHigherHomology.CircleTopology.productV_open Y)
    (PeriodTorusHigherHomology.CircleTopology.product_cover Y) n a

private theorem PeriodFamily.Homology.circleBoundary_headMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y]
    (F :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
        (PeriodTorusHigherHomology.CircleTopology.Circle) × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    PeriodTorusHigherHomology.circleBoundary Y n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap
        (headMapFibre F PeriodTorusHigherHomology.CirclePaths.quarterPoint) n
        (PeriodTorusHigherHomology.circleBoundary X n a) := by
  change
    -(PeriodTorusHigherHomology.productIntersectionHomologyEquiv Y n
            (PeriodTorusHigherHomology.circleMayerVietorisConnecting Y n
              (SingularMayerVietoris.singularHomologyMap F (n + 1) a))).1 =
      SingularMayerVietoris.singularHomologyMap
        (headMapFibre F PeriodTorusHigherHomology.CirclePaths.quarterPoint) n
        (-(PeriodTorusHigherHomology.productIntersectionHomologyEquiv X n
              (PeriodTorusHigherHomology.circleMayerVietorisConnecting X n a)).1)
  rw [← circleConnecting_headMap F hF, headIntersectionHomology_coordinates, map_neg]

private def PeriodFamily.Homology.topDegreeTailMatrix (A : Matrix (Fin 4) (Fin 4) ℤ) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  A.submatrix Fin.succ Fin.succ

private def PeriodFamily.Homology.topDegreeCircleMap (A : Matrix (Fin 4) (Fin 4) ℤ) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3,
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3) :=
  (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3 : C(_, _)).comp
    ((PeriodTorusHigherHomology.torusMatrixMap A).comp
      ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm : C(_, _)))

@[simp]
private theorem PeriodFamily.Homology.topDegreeCircleMap_apply (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z :
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3) :
    topDegreeCircleMap A z =
      PeriodTorusHigherHomology.productTorusSuccHomeomorph 3
        (PeriodTorusHigherHomology.torusMatrixMap A
          ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm z)) :=
  rfl

private theorem PeriodFamily.Homology.topDegreeCircleMap_homeomorph (A : Matrix (Fin 4) (Fin 4) ℤ)
    (x : PeriodTorusHigherHomology.ProductTorus 4) :
    topDegreeCircleMap A (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3 x) =
      PeriodTorusHigherHomology.productTorusSuccHomeomorph 3
        (PeriodTorusHigherHomology.torusMatrixMap A x) := by
  rw [topDegreeCircleMap_apply, Homeomorph.symm_apply_apply]

private theorem
    PeriodFamily.Homology.topDegreeCircleMap_comp_homeomorph (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (topDegreeCircleMap A).comp
        (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3 : C(_, _)) =
      (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3 : C(_, _)).comp
        (PeriodTorusHigherHomology.torusMatrixMap A) := by
  apply ContinuousMap.ext
  intro x
  exact topDegreeCircleMap_homeomorph A x

private theorem PeriodFamily.Homology.topDegreeCircleMap_fst (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (z :
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3) :
    (topDegreeCircleMap A z).1 = z.1 := by
  change (∑ j : Fin 4, A 0 j • Fin.cons z.1 z.2 j) = z.1
  simp [hA]

private theorem PeriodFamily.Homology.topDegreeCircleMap_snd (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z :
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3)
    (i : Fin 3) :
    (topDegreeCircleMap A z).2 i =
      PeriodTorusHigherHomology.torusMatrixMap (topDegreeTailMatrix A) z.2 i + A i.succ 0 • z.1 :=
  by
  change
    (∑ j : Fin 4, A i.succ j • Fin.cons z.1 z.2 j) =
      (∑ j : Fin 3, A i.succ j.succ • z.2 j) + A i.succ 0 • z.1
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact add_comm _ _

private def PeriodFamily.Homology.topDegreeCircleSection
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    C(PeriodTorusHigherHomology.ProductTorus 3,
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3) :=
  ⟨fun x => (z, x), continuous_const.prodMk continuous_id⟩

private def PeriodFamily.Homology.topDegreeFibreMap (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3) :=
  ContinuousMap.snd.comp ((topDegreeCircleMap A).comp (topDegreeCircleSection z))

private theorem
    PeriodFamily.Homology.topDegreeFibreMap_apply_coordinate (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle))
    (x : PeriodTorusHigherHomology.ProductTorus 3) (i : Fin 3) :
    topDegreeFibreMap A z x i =
      PeriodTorusHigherHomology.torusMatrixMap (topDegreeTailMatrix A) x i + A i.succ 0 • z :=
  topDegreeCircleMap_snd A (z, x) i

private def PeriodFamily.Homology.topDegreeFibreTranslation (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    PeriodTorusHigherHomology.ProductTorus 3 := fun i => A i.succ 0 • z

private theorem
    PeriodFamily.Homology.topDegreeFibreMap_eq_translation (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    topDegreeFibreMap A z =
      (PeriodTorusHigherHomology.rightTranslation (topDegreeFibreTranslation A z)).comp
        (PeriodTorusHigherHomology.torusMatrixMap (topDegreeTailMatrix A)) := by
  apply ContinuousMap.ext
  intro x
  ext i
  exact topDegreeFibreMap_apply_coordinate A z x i

private theorem
    PeriodFamily.Homology.topDegreeFibreMap_singularHomologyMap (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (topDegreeFibreMap A z) n =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap (topDegreeTailMatrix A)) n := by
  rw [topDegreeFibreMap_eq_translation, PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.rightTranslation_singularHomologyMap, LinearMap.id_comp]

private theorem PeriodFamily.Homology.topDegree_det_eq_tail (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) : A.det = (topDegreeTailMatrix A).det := by
  rw [Matrix.det_succ_row_zero]
  simp [hA, topDegreeTailMatrix]

private theorem PeriodFamily.Homology.circleTopDegreeBoundary_injective :
    Function.Injective
      (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt (show 3 < 4 by decide)
  intro a b hab
  apply
    (PeriodTorusHigherHomology.circleProductHomologyEquiv
        (PeriodTorusHigherHomology.ProductTorus 3) 3).injective
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hab

private def PeriodFamily.Homology.circleTopDegreeEquiv :
    SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3)
        4 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 :=
  LinearEquiv.ofBijective
    (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3)
    ⟨circleTopDegreeBoundary_injective,
      PeriodTorusHigherHomology.circleBoundary_surjective
        (PeriodTorusHigherHomology.ProductTorus 3) 3⟩

@[simp]
private theorem PeriodFamily.Homology.circleTopDegreeEquiv_positiveCircleCross
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    circleTopDegreeEquiv
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3)
          3 a) =
      a :=
  PeriodTorusHigherHomology.circleBoundary_positiveCircleCross
    (PeriodTorusHigherHomology.ProductTorus 3) 3 a

private theorem PeriodFamily.Homology.circleTopDegreeEquiv_symm_apply
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    circleTopDegreeEquiv.symm a =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3) 3
        a := by
  apply circleTopDegreeEquiv.injective
  rw [LinearEquiv.apply_symm_apply, circleTopDegreeEquiv_positiveCircleCross]

private def PeriodFamily.Homology.circleTopDegreeCoordinates :
    SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3)
        4 ≃ₗ[ℤ]
      ℤ :=
  circleTopDegreeEquiv.trans Elliptic.HigherHomology.torusH3Coordinates

private def PeriodFamily.Homology.topDegreeTorusCoordinates :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3) 4).trans
    circleTopDegreeCoordinates

@[simp]
private theorem PeriodFamily.Homology.topDegreeTorusCoordinates_apply
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4) :
    topDegreeTorusCoordinates a =
      Elliptic.HigherHomology.torusH3Coordinates
        (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv
            (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3) 4 a)) :=
  rfl

private theorem PeriodFamily.Homology.topDegreeTorusCoordinates_topClass :
    topDegreeTorusCoordinates (PeriodTorusHigherHomology.productTorusTopClass 4) = 1 := by
  rw [topDegreeTorusCoordinates_apply,
    PeriodTorusHigherHomology.productTorusTopClass_succ_boundary]
  have h :
    PeriodTorusHigherHomology.productTorusTopClass 3 =
      Elliptic.HigherHomology.torusH3Coordinates.symm 1 :=
    PeriodTorusHigherHomology.productTorusTopClass_three.trans
      Elliptic.HigherHomology.torusH3Coordinates_symm_one.symm
  rw [h, LinearEquiv.apply_symm_apply]

private theorem PeriodFamily.Homology.circleTopDegreeBoundary_matrix (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3)
        4) :
    PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3
        (SingularMayerVietoris.singularHomologyMap (topDegreeCircleMap A) 4 a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap (topDegreeTailMatrix A)) 3
        (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3
          a) := by
  have h := circleBoundary_headMap (topDegreeCircleMap A) (topDegreeCircleMap_fst A hA) 3 a
  change
    PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3
        (SingularMayerVietoris.singularHomologyMap (topDegreeCircleMap A) 4 a) =
      SingularMayerVietoris.singularHomologyMap
        (topDegreeFibreMap A PeriodTorusHigherHomology.CirclePaths.quarterPoint) 3
        (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3
          a) at h
  rw [topDegreeFibreMap_singularHomologyMap] at h
  exact h

private theorem PeriodFamily.Homology.circleTopDegreeCoordinates_matrix (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3)
        4) :
    circleTopDegreeCoordinates
        (SingularMayerVietoris.singularHomologyMap (topDegreeCircleMap A) 4 a) =
      A.det * circleTopDegreeCoordinates a := by
  change
    Elliptic.HigherHomology.torusH3Coordinates
        (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3
          (SingularMayerVietoris.singularHomologyMap (topDegreeCircleMap A) 4 a)) =
      _
  rw [circleTopDegreeBoundary_matrix A hA,
    Elliptic.HigherHomology.torusH3Coordinates_matrix_natural, topDegree_det_eq_tail A hA]
  rfl

private theorem PeriodFamily.Homology.topDegreeTorusCoordinates_matrix (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4) :
    topDegreeTorusCoordinates
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 4
          a) =
      A.det * topDegreeTorusCoordinates a := by
  change
    circleTopDegreeCoordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3 : C(_, _)) 4
          (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A)
            4 a)) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    topDegreeCircleMap_comp_homeomorph, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]
  exact circleTopDegreeCoordinates_matrix A hA _

private theorem PeriodFamily.Homology.torusMatrixMap_homologyFour_apply (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 4 a =
      A.det • a := by
  apply topDegreeTorusCoordinates.injective
  rw [map_zsmul]
  simpa only [zsmul_eq_mul, Int.cast_id] using topDegreeTorusCoordinates_matrix A hA a

private theorem PeriodFamily.Homology.torusMatrixMap_homologyFour (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 4 =
      A.det •
        (LinearMap.id :
          SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4)
              4 →ₗ[ℤ]
            _) := by
  apply LinearMap.ext
  intro a
  exact torusMatrixMap_homologyFour_apply A hA a

private theorem PeriodFamily.Homology.torusMatrixMap_homologyFour_of_det_one (A : LatticeMatrix)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) (hdet : A.det = 1) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 4 =
      LinearMap.id := by rw [torusMatrixMap_homologyFour A hA, hdet, one_smul]

private theorem PeriodFamily.Homology.torusMatrixMap_A₁_homologyFour :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A₁) 4 =
      LinearMap.id := by
  apply torusMatrixMap_homologyFour_of_det_one A₁
  · intro j
    fin_cases j <;> decide
  · decide

private theorem PeriodFamily.Homology.torusMatrixMap_A₂_homologyFour :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A₂) 4 =
      LinearMap.id := by
  apply torusMatrixMap_homologyFour_of_det_one A₂
  · intro j
    fin_cases j <;> decide
  · decide

private theorem PeriodFamily.Homology.torusMatrixMap_M₀_homologyFour :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 4 =
      LinearMap.id := by
  apply torusMatrixMap_homologyFour_of_det_one M₀
  · intro j
    fin_cases j <;> decide
  · decide

private theorem PeriodFamily.Homology.dual_homology_one_mo1973_25539 :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap
          (SpecialPeriods.triangleDualRepresentation 1 : LatticeMatrix))
        4 =
      LinearMap.id := by
  rw [map_one, Matrix.SpecialLinearGroup.coe_one, PeriodTorusHigherHomology.torusMatrixMap_one,
    PeriodTorusHigherHomology.singularHomologyMap_id]

private theorem PeriodFamily.Homology.dual_homology_mul_mo1973_25540
    (g h : SpecialPeriods.TriangleGroup) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap
          (SpecialPeriods.triangleDualRepresentation (g * h) : LatticeMatrix))
        4 =
      (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.torusMatrixMap
              (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix))
            4).comp
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap
            (SpecialPeriods.triangleDualRepresentation h : LatticeMatrix))
          4) := by
  rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, PeriodTorusHigherHomology.torusMatrixMap_mul,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

private theorem PeriodFamily.Homology.triangleDualRepresentation_homologyFour
    (g : SpecialPeriods.TriangleGroup) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap
          (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix))
        4 =
      LinearMap.id := by
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · rw [SpecialPeriods.triangleDualRepresentation_generator₁_matrix]
      exact torusMatrixMap_A₁_homologyFour
    · have he : g = SpecialPeriods.triangleGenerator₂ := Set.mem_singleton_iff.mp hg
      subst g
      rw [SpecialPeriods.triangleDualRepresentation_generator₂_matrix]
      exact torusMatrixMap_A₂_homologyFour
  | one => exact dual_homology_one_mo1973_25539
  | mul g h _ _ ihg ihh => rw [dual_homology_mul_mo1973_25540, ihg, ihh, LinearMap.id_comp]
  | inv g _ ihg =>
    have h := dual_homology_mul_mo1973_25540 g⁻¹ g
    rw [inv_mul_cancel, dual_homology_one_mo1973_25539, ihg, LinearMap.comp_id] at h
    exact h.symm

private theorem PeriodFamily.HomologyDifference.triangleHomologyFour_identity
    (g : SpecialPeriods.TriangleGroup) :
    PeriodFamily.Homology.triangleHomologyEquiv g 4 =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ 4) := by
  apply LinearEquiv.ext
  intro a
  apply
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        PeriodTorusHigherHomology.flatTorusCircleHomeomorph 4).injective
  change
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        4
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 4 a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        4 a
  rw [PeriodFamily.FlatTorus.flatTorusCircleHomology_triangle_apply,
    PeriodFamily.Homology.triangleDualRepresentation_homologyFour, LinearMap.id_apply]

@[simp]
private theorem PeriodFamily.HomologyDifference.sourceDifference_four :
    PeriodFamily.Homology.sourceDifference 4 = 0 := by
  apply LinearMap.ext
  intro x
  change
    (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁ 4 x.1 - x.1) +
        (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₂ 4 x.2 -
          x.2) =
      0
  rw [triangleHomologyFour_identity, triangleHomologyFour_identity]
  simp

private theorem PeriodFamily.HomologyDifference.sourceDifferenceFour_coordinates
    (x :
      SingularMayerVietoris.SingularHomology RealTorus₄ 4 ×
        SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    PeriodTorusHigherHomology.realTorusH4Equiv (PeriodFamily.Homology.sourceDifference 4 x) =
      TrianglePeriodFamilyHomologyLattice.deltaFour
        (PeriodTorusHigherHomology.realTorusH4Equiv x.1,
          PeriodTorusHigherHomology.realTorusH4Equiv x.2) := by
  rw [sourceDifference_four, TrianglePeriodFamilyHomologyLattice.deltaFour_eq_zero]
  simp only [LinearMap.zero_apply, map_zero]

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelFourCoordinates :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 4) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaFour :=
  kernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 4)
    TrianglePeriodFamilyHomologyLattice.deltaFour
    (PeriodTorusHigherHomology.realTorusH4Equiv.toAddEquiv.prodCongr
        PeriodTorusHigherHomology.realTorusH4Equiv.toAddEquiv).toIntLinearEquiv
    PeriodTorusHigherHomology.realTorusH4Equiv sourceDifferenceFour_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.kernelFourEquiv :
    LinearMap.ker (PeriodFamily.Homology.sourceDifference 4) ≃ₗ[ℤ] (ℤ × ℤ) :=
  (kernelFourCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.kernelFourEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelFourCoordinates :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 4 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 4)) ≃ₗ[ℤ]
      (ℤ ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaFour) :=
  cokernelEquivOfCommuting (PeriodFamily.Homology.sourceDifference 4)
    TrianglePeriodFamilyHomologyLattice.deltaFour
    (PeriodTorusHigherHomology.realTorusH4Equiv.toAddEquiv.prodCongr
        PeriodTorusHigherHomology.realTorusH4Equiv.toAddEquiv).toIntLinearEquiv
    PeriodTorusHigherHomology.realTorusH4Equiv sourceDifferenceFour_coordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.HomologyDifference.cokernelFourEquiv :
    (SingularMayerVietoris.SingularHomology RealTorus₄ 4 ⧸
        LinearMap.range (PeriodFamily.Homology.sourceDifference 4)) ≃ₗ[ℤ]
      ℤ :=
  (cokernelFourCoordinates.toAddEquiv.trans
      TrianglePeriodFamilyHomologyLattice.cokernelFourEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH1ProductEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 1 ≃ₗ[ℤ] (ℤ × (ℤ × ℤ)) :=
  familyHomologyMarkedEquiv D 0 PeriodFamily.HomologyDifference.cokernelOneEquiv.toAddEquiv
    PeriodFamily.HomologyDifference.kernelZeroEquiv.toAddEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH2ProductEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 2 ≃ₗ[ℤ] (ℤ × (Fin 5 → ℤ)) :=
  familyHomologyMarkedEquiv D 1 PeriodFamily.HomologyDifference.cokernelTwoEquiv.toAddEquiv
    PeriodFamily.HomologyDifference.kernelOneEquiv.toAddEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH3ProductEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 3 ≃ₗ[ℤ] (ℤ × (Fin 7 → ℤ)) :=
  familyHomologyMarkedEquiv D 2 PeriodFamily.HomologyDifference.cokernelThreeEquiv.toAddEquiv
    PeriodFamily.HomologyDifference.kernelTwoEquiv.toAddEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH4ProductEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 4 ≃ₗ[ℤ] (ℤ × (Fin 5 → ℤ)) :=
  familyHomologyMarkedEquiv D 3 PeriodFamily.HomologyDifference.cokernelFourEquiv.toAddEquiv
    PeriodFamily.HomologyDifference.kernelThreeEquiv.toAddEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private theorem PeriodFamily.Homology.sourceKernelProjection_injective_of_torus_vanish
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ)
    (hn : Subsingleton (SingularMayerVietoris.SingularHomology RealTorus₄ (n + 1))) :
    Function.Injective (sourceKernelProjection D n) := by
  intro a b hab
  have hzero : sourceKernelProjection D n (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨q, hq⟩ := (sourceCoinvariantInclusion_kernelProjection_exact D n (a - b)).mp hzero
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : x = 0 := hn.elim _ _
  rw [hx, Submodule.Quotient.mk_zero, map_zero] at hq
  exact sub_eq_zero.mp hq.symm

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH5KernelEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 5 ≃ₗ[ℤ] LinearMap.ker (sourceDifference 4) :=
  LinearEquiv.ofBijective (sourceKernelProjection D 4)
    ⟨sourceKernelProjection_injective_of_torus_vanish D 4
        (PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt (by decide)),
      sourceKernelProjection_surjective D 4⟩

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH5ProductEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 5 ≃ₗ[ℤ] (ℤ × ℤ) :=
  ((familyH5KernelEquiv D).toAddEquiv.trans
      PeriodFamily.HomologyDifference.kernelFourEquiv.toAddEquiv).toIntLinearEquiv

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH1Equiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  let e : (ℤ × (ℤ × ℤ)) ≃+ (ℤ × (Fin 2 → ℤ)) :=
    (AddEquiv.refl ℤ).prodCongr (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv
  (((familyH1ProductEquiv D).toAddEquiv.trans e).toIntLinearEquiv).trans
    (TrianglePeriodFamilyHomologyFreeCoordinates.integerFreeCoordinateEquiv 2)

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH2Equiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (familyH2ProductEquiv D).trans
    (TrianglePeriodFamilyHomologyFreeCoordinates.integerFreeCoordinateEquiv 5)

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH3Equiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 3 ≃ₗ[ℤ] (Fin 8 → ℤ) :=
  (familyH3ProductEquiv D).trans
    (TrianglePeriodFamilyHomologyFreeCoordinates.integerFreeCoordinateEquiv 7)

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH4Equiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 4 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (familyH4ProductEquiv D).trans
    (TrianglePeriodFamilyHomologyFreeCoordinates.integerFreeCoordinateEquiv 5)

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
    TrianglePeriodFamilyHomologyAlgebra.kernelModule in
private def PeriodFamily.Homology.familyH5Equiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 5 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (familyH5ProductEquiv D).trans (LinearEquiv.finTwoArrow ℤ ℤ).symm

private theorem PeriodFamily.Homology.familyFibreInclusion_zero_surjective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (b : SlitBaseLift) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D b) 0) := by
  intro a
  have ha : a ∈ LinearMap.range (familyRightHomologyMap D 0) :=
    familyRightHomologyMap_zero_surjective D a
  rw [familyRightHomologyMap_range_eq_fibre D b 0] at ha
  exact ha

private theorem PeriodFamily.Homology.familyFibreInclusion_zero_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift)
        0) := by
  apply LinearMap.ker_eq_bot.mp
  rw [familyFibreInclusion_kernel, sourceDifference_zero, LinearMap.range_zero]

private def PeriodFamily.Homology.familyFibreHomologyZeroEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology RealTorus₄ 0 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.Space 0 :=
  LinearEquiv.ofBijective
    (SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 0)
    ⟨familyFibreInclusion_zero_injective D,
      familyFibreInclusion_zero_surjective D normalizedSlitBaseLift⟩

private def PeriodFamily.Homology.familyH0Equiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    SingularMayerVietoris.SingularHomology D.Space 0 ≃ₗ[ℤ] ℤ :=
  (familyFibreHomologyZeroEquiv D).symm.trans
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv RealTorus₄)

private theorem PeriodFamily.Homology.family_homology_subsingleton_of_lt
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) {n : ℕ} (hn : 5 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology D.Space n) := by
  cases n with
  | zero => omega
  | succ
    m =>
    let := PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt (n := m) (by omega)
    let := PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt (n := m + 1) (by omega)
    have hz (x : SingularMayerVietoris.SingularHomology D.Space (m + 1)) : x = 0 := by
      obtain ⟨q, hq⟩ :=
        (sourceCoinvariantInclusion_kernelProjection_exact D m x).mp (Subsingleton.elim _ _)
      have hq0 : q = 0 := Subsingleton.elim _ _
      simpa only [hq0, map_zero] using hq.symm
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private theorem PeriodFamily.Homology.family_homology_isZero_of_lt
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) {n : ℕ} (hn : 5 < n) :
    CategoryTheory.Limits.IsZero (SingularMayerVietoris.SingularHomology D.Space n) := by
  let := family_homology_subsingleton_of_lt D hn
  exact ModuleCat.isZero_of_subsingleton _

private def PeriodFamily.Homology.familyBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 8
  | 4 => 6
  | 5 => 2
  | _ + 6 => 0

private def PeriodFamily.Homology.familyHomologyEquiv
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    (n : ℕ) → SingularMayerVietoris.SingularHomology D.Space n ≃ₗ[ℤ] (Fin (familyBetti n) → ℤ)
  | 0 => (familyH0Equiv D).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => familyH1Equiv D
  | 2 => familyH2Equiv D
  | 3 => familyH3Equiv D
  | 4 => familyH4Equiv D
  | 5 => familyH5Equiv D
  | n + 6 =>
    by
    change SingularMayerVietoris.SingularHomology D.Space (n + 6) ≃ₗ[ℤ] (Fin 0 → ℤ)
    letI := family_homology_subsingleton_of_lt D (n := n + 6) (by omega)
    exact LinearEquiv.ofSubsingleton _ _

private theorem PeriodFamily.Homology.family_homology_free
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology D.Space n) :=
  Module.Free.of_equiv (familyHomologyEquiv D n).symm

private theorem PeriodFamily.Homology.family_homology_finite
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology D.Space n) :=
  Module.Finite.of_surjective (familyHomologyEquiv D n).symm.toLinearMap
    (familyHomologyEquiv D n).symm.surjective

private theorem PeriodFamily.Homology.family_homology_finrank
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology D.Space n) = familyBetti n := by
  rw [(familyHomologyEquiv D n).finrank_eq]
  simp

private abbrev PeriodFamily.Canonical.Model :=
  ℂ × ComplexPlane₂

private abbrev PeriodFamily.Canonical.Atlas.tangentCore (M : Type*) [TopologicalSpace M]
    [ChartedSpace PeriodFamily.Canonical.Model M]
    [IsManifold (modelWithCornersSelf ℂ PeriodFamily.Canonical.Model) ω M] :
    VectorBundleCore ℂ M PeriodFamily.Canonical.Model (atlas PeriodFamily.Canonical.Model M) :=
  tangentBundleCore (modelWithCornersSelf ℂ PeriodFamily.Canonical.Model) M


private theorem PeriodFamily.dualComplexMatrix_fixes_delta (g : SpecialPeriods.TriangleGroup) :
    dualComplexMatrix g *ᵥ ![0, 0, 0, 1] = (![0, 0, 0, 1] : Fin 4 → ℂ) := by
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem h hh =>
    rcases hh with rfl | rfl
    · rw [dualComplexMatrix_generator₁]
      ext i
      fin_cases i <;>
        norm_num [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_two,
          Matrix.cons_val_three]
    · rw [dualComplexMatrix_generator₂]
      ext i
      fin_cases i <;>
        norm_num [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_two,
          Matrix.cons_val_three]
  | one => rw [dualComplexMatrix_one, Matrix.one_mulVec]
  | mul g h _ _ ihg ihh => rw [dualComplexMatrix_mul, ← Matrix.mulVec_mulVec, ihh, ihg]
  | inv g _
    ih =>
    have he := congrArg (fun v : Fin 4 → ℂ => dualComplexMatrix g⁻¹ *ᵥ v) ih
    rw [Matrix.mulVec_mulVec, ← dualComplexMatrix_mul, inv_mul_cancel, dualComplexMatrix_one,
      Matrix.one_mulVec] at he
    exact he.symm

private theorem
    PeriodFamily.dualComplexMatrix_lastColumn (g : SpecialPeriods.TriangleGroup) (i : Fin 4) :
    dualComplexMatrix g i 3 = (![0, 0, 0, 1] : Fin 4 → ℂ) i := by
  have h := congrFun (dualComplexMatrix_fixes_delta g) i
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four] using h

private theorem PeriodFamily.Data.rightBlock_secondColumn {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) :
    (fun i => D.rightBlock g b i 1) = (![0, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;>
    simp [rightBlock, Matrix.mul_apply, Fin.sum_univ_four,
      PeriodFamily.dualComplexMatrix_lastColumn, PeriodPoint.matrix]

@[simp]
private theorem PeriodFamily.Data.rightBlock_zero_one {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) : D.rightBlock g b 0 1 = 0 :=
  congrFun (D.rightBlock_secondColumn g b) 0

@[simp]
private theorem PeriodFamily.Data.rightBlock_one_one {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) : D.rightBlock g b 1 1 = 1 :=
  congrFun (D.rightBlock_secondColumn g b) 1

private theorem PeriodFamily.Data.rightBlock_fixes_second {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) :
    D.rightBlock g b *ᵥ ![0, 1] = (![0, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private abbrev PeriodFamily.Canonical.specialRegularData :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.regularData SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

private abbrev PeriodFamily.Canonical.SpecialRegularFamily :=
  specialRegularData.Space

private theorem PeriodFamily.Canonical.specialRegularHomology_free (n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology SpecialRegularFamily n) :=
  PeriodFamily.Homology.family_homology_free specialRegularData n

private theorem PeriodFamily.Canonical.specialRegularHomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology SpecialRegularFamily n) :=
  PeriodFamily.Homology.family_homology_finite specialRegularData n

private theorem PeriodFamily.Canonical.specialRegularHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology SpecialRegularFamily n) =
      PeriodFamily.Homology.familyBetti n :=
  PeriodFamily.Homology.family_homology_finrank specialRegularData n

private theorem PeriodFamily.Canonical.specialRegularHomology_isZero_of_lt {n : ℕ} (hn : 5 < n) :
    CategoryTheory.Limits.IsZero
      (SingularMayerVietoris.SingularHomology SpecialRegularFamily n) :=
  PeriodFamily.Homology.family_homology_isZero_of_lt specialRegularData hn

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.zeroSectionPath {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) {b₀ b₁ : B} (p : Path b₀ b₁) :
    Path (D.fundamentalGroupBasepoint b₀) (D.fundamentalGroupBasepoint b₁) :=
  DiagonalQuotient.fibreBasepointPath (G := SpecialPeriods.TriangleGroup) (0 : RealTorus₄) p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.flatFibreFundamentalGroupHom_baseChange {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) {b₀ b₁ : B}
    (p : Path b₀ b₁) (v : FundamentalGroup RealTorus₄ 0) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (D.zeroSectionPath p)
        (D.flatFibreFundamentalGroupHom b₀ v) =
      D.flatFibreFundamentalGroupHom b₁ v :=
  DiagonalQuotient.fibreFundamentalGroupHom_baseChange (G := SpecialPeriods.TriangleGroup)
    (0 : RealTorus₄) p v

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.latticeFundamentalGroupHom_baseChange {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) {b₀ b₁ : B}
    (p : Path b₀ b₁) (v : Multiplicative Lattice) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (D.zeroSectionPath p)
        (D.latticeFundamentalGroupHom b₀ v) =
      D.latticeFundamentalGroupHom b₁ v :=
  D.flatFibreFundamentalGroupHom_baseChange p
    (PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm v)

private def PeriodDomain.fullPeriodCoordinatesEquiv : Lattice ≃ₗ[ℤ] FullPeriodMatrix.IntegerPeriods
    where
  toFun c := (![c 2, c 3], ![c 0, c 1])
  invFun c := ![c.2 0, c.2 1, c.1 0, c.1 1]
  left_inv c := by ext i; fin_cases i <;> rfl
  right_inv c := by ext i <;> fin_cases i <;> rfl
  map_add' c d := by ext i <;> fin_cases i <;> rfl
  map_smul' n c := by ext i <;> fin_cases i <;> rfl

private theorem PeriodDomain.fullPeriod_periodVector (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) (c : Lattice) :
    q.periodVector (fullPeriodCoordinatesEquiv c) = p.periodVector c := by
  ext i
  fin_cases i <;>
      simp [FullPeriodMatrix.periodVector, periodVector, fullPeriodCoordinatesEquiv, h,
        PeriodPoint.leftBlock, PeriodPoint.matrix, dotProduct, Fin.sum_univ_succ, Matrix.vecHead,
        Matrix.vecTail] <;>
    ring

private def PeriodFamily.Boundary.realCurveLift (c : C(ℝ, SpecialPeriods.TriangleRegularQuotient))
    (z : SpecialPeriods.TriangleRegularPoint)
    (hz : SpecialPeriods.triangleRegularProject z = c 0) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts c
      0 z hz).choose

@[simp]
private theorem PeriodFamily.Boundary.realCurveLift_zero
    (c : C(ℝ, SpecialPeriods.TriangleRegularQuotient)) (z : SpecialPeriods.TriangleRegularPoint)
    (hz : SpecialPeriods.triangleRegularProject z = c 0) : realCurveLift c z hz 0 = z :=
  (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts c
          0 z hz).choose_spec.1.1

@[simp]
private theorem PeriodFamily.Boundary.realCurveLift_projection
    (c : C(ℝ, SpecialPeriods.TriangleRegularQuotient)) (z : SpecialPeriods.TriangleRegularPoint)
    (hz : SpecialPeriods.triangleRegularProject z = c 0) (t : ℝ) :
    SpecialPeriods.triangleRegularProject (realCurveLift c z hz t) = c t :=
  congr_fun
    (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.existsUnique_continuousMap_lifts
            c 0 z hz).choose_spec.1.2
    t

private theorem PeriodFamily.Boundary.realCurveLift_unique
    (c : C(ℝ, SpecialPeriods.TriangleRegularQuotient)) (z : SpecialPeriods.TriangleRegularPoint)
    (hz : SpecialPeriods.triangleRegularProject z = c 0)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = c t) (hzero : L 0 = z) :
    L = realCurveLift c z hz := by
  apply ContinuousMap.ext
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq L.continuous
        (realCurveLift c z hz).continuous
        (by funext t; simp only [Function.comp_apply, hL, realCurveLift_projection]) 0
        (hzero.trans (realCurveLift_zero c z hz).symm))

private theorem PeriodFamily.Boundary.realCurveLift_translate_one
    (c : C(ℝ, SpecialPeriods.TriangleRegularQuotient)) (z : SpecialPeriods.TriangleRegularPoint)
    (hz : SpecialPeriods.triangleRegularProject z = c 0) (hperiod : ∀ t : ℝ, c (t + 1) = c t)
    (g : SpecialPeriods.TriangleGroup) (hend : realCurveLift c z hz 1 = g⁻¹ • z) (t : ℝ) :
    realCurveLift c z hz (t + 1) = g⁻¹ • realCurveLift c z hz t := by
  have hleft : Continuous (fun t : ℝ => realCurveLift c z hz (t + 1)) :=
    (realCurveLift c z hz).continuous.comp (continuous_id.add continuous_const)
  have hright : Continuous (fun t : ℝ => g⁻¹ • realCurveLift c z hz t) :=
    (ContinuousConstSMul.continuous_const_smul g⁻¹).comp (realCurveLift c z hz).continuous
  have he :
    SpecialPeriods.triangleRegularProject ∘ (fun t : ℝ => realCurveLift c z hz (t + 1)) =
      SpecialPeriods.triangleRegularProject ∘ (fun t : ℝ => g⁻¹ • realCurveLift c z hz t) := by
    funext t
    simp only [Function.comp_apply, realCurveLift_projection,
      SpecialPeriods.triangleRegularProject_covering.map_smul, hperiod]
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq hleft hright he
        0 (by simpa only [zero_add, realCurveLift_zero] using hend))
      t

private theorem PeriodFamily.Boundary.realCurve_integer_translate
    (L : ℝ → SpecialPeriods.TriangleRegularPoint) (g : SpecialPeriods.TriangleGroup)
    (hstep : ∀ t : ℝ, L (t + 1) = g⁻¹ • L t) (k : ℤ) (t : ℝ) : L (t + k) = (g ^ (-k)) • L t := by
  have hprev (s : ℝ) : L (s - 1) = g • L s := by
    have h := congrArg (fun y : SpecialPeriods.TriangleRegularPoint => g • y) (hstep (s - 1))
    simpa only [sub_add_cancel, smul_inv_smul] using h.symm
  have hall : ∀ k : ℤ, ∀ t : ℝ, L (t + k) = (g ^ (-k)) • L t := by
    intro k
    induction k using Int.induction_on with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [Int.cast_add, Int.cast_one, ← add_assoc, hstep, ih]
      rw [show -((k : ℤ) + 1) = -1 + -(k : ℤ) by omega, zpow_add, zpow_neg_one,
        SemigroupAction.mul_smul]
    | pred k ih =>
      intro t
      rw [Int.cast_sub, Int.cast_one, ← add_sub_assoc, hprev, ih]
      rw [show -(-(k : ℤ) - 1) = 1 + -(-(k : ℤ)) by omega, zpow_add, zpow_one,
        SemigroupAction.mul_smul]
  exact hall k t

private theorem PeriodFamily.Boundary.realCurveLift_translate
    (c : C(ℝ, SpecialPeriods.TriangleRegularQuotient)) (z : SpecialPeriods.TriangleRegularPoint)
    (hz : SpecialPeriods.triangleRegularProject z = c 0) (hperiod : ∀ t : ℝ, c (t + 1) = c t)
    (g : SpecialPeriods.TriangleGroup) (hend : realCurveLift c z hz 1 = g⁻¹ • z) (k : ℤ) (t : ℝ) :
    realCurveLift c z hz (t + k) = (g ^ (-k)) • realCurveLift c z hz t :=
  realCurve_integer_translate (realCurveLift c z hz) g
    (realCurveLift_translate_one c z hz hperiod g hend) k t

private def PeriodFamily.Boundary.realCurveLoop (c : C(ℝ, SpecialPeriods.TriangleRegularQuotient))
    (hperiod : ∀ t : ℝ, c (t + 1) = c t) : Path (c 0) (c 0)
    where
  toFun t := c t
  continuous_toFun := c.continuous.comp continuous_subtype_val
  source' := rfl
  target' := by
    change c (1 : ℝ) = c 0
    simpa only [zero_add] using hperiod 0

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def PeriodFamily.Boundary.Cusp.reciprocalCoordinate : ℂ → ℂ :=
  SpecialPeriods.MuTorsor.CuspCoordinates.t SpecialPeriods.Triangle.triangleSphereUniformization

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem PeriodFamily.Boundary.Cusp.reciprocalCoordinate_zero : reciprocalCoordinate 0 = 0 :=
  SpecialPeriods.MuTorsor.CuspCoordinates.t_zero
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.reciprocalCoordinate_analytic :
    AnalyticAt ℂ reciprocalCoordinate 0 :=
  SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.reciprocalCoordinate_derivative :
    deriv reciprocalCoordinate 0 ≠ 0 :=
  SpecialPeriods.TriangleSource.reciprocalCusp_deriv_ne_zero
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def PeriodFamily.Boundary.Cusp.reciprocalControl :
    SpecialPeriods.EllipticAttachingMeridians.LinearizationControl reciprocalCoordinate :=
  SpecialPeriods.EllipticAttachingMeridians.analyticLinearizationControl
    reciprocalCoordinate_analytic reciprocalCoordinate_derivative

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def PeriodFamily.Boundary.Cusp.controlledHeight :
    ThreefoldOverlapMappingTorus.Cusp.Height
      ThreefoldOverlapMappingTorus.Cusp.specialData.radius :=
  ⟨Max.max
        (ThreefoldOverlapMappingTorus.Cusp.heightThreshold
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
        (ThreefoldOverlapMappingTorus.Cusp.heightThreshold reciprocalControl.radius) +
      1,
    by
    change
      ThreefoldOverlapMappingTorus.Cusp.heightThreshold
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius <
        Max.max
            (ThreefoldOverlapMappingTorus.Cusp.heightThreshold
              ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
            (ThreefoldOverlapMappingTorus.Cusp.heightThreshold reciprocalControl.radius) +
          1
    exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def PeriodFamily.Boundary.Cusp.parameter
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    ℂ :=
  CuspUniformization.exponential
    (ThreefoldOverlapMappingTorus.Cusp.logPoint
      ThreefoldOverlapMappingTorus.Cusp.specialData.radius
      ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos 0 h)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.parameter_ne_zero
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    parameter h ≠ 0 :=
  CuspUniformization.exponential_ne_zero _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.parameter_controlled :
    ‖parameter controlledHeight‖ < reciprocalControl.radius := by
  apply (SpecialPeriods.CuspFamily.mem_logBase reciprocalControl.radius _).mp
  rw [ThreefoldOverlapMappingTorus.Cusp.mem_logBase_iff_height reciprocalControl.radius
      reciprocalControl.radius_pos,
    ThreefoldOverlapMappingTorus.Cusp.logPoint_im]
  change
    ThreefoldOverlapMappingTorus.Cusp.heightThreshold reciprocalControl.radius <
      Max.max
          (ThreefoldOverlapMappingTorus.Cusp.heightThreshold
            ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
          (ThreefoldOverlapMappingTorus.Cusp.heightThreshold reciprocalControl.radius) +
        1
  exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def PeriodFamily.Boundary.Cusp.baseLift
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  ⟨fun t =>
    SpecialPeriods.CuspFamily.logBaseToRegular
      ThreefoldOverlapMappingTorus.Cusp.specialData.radius
      ThreefoldOverlapMappingTorus.Cusp.specialRadius_cap
      (ThreefoldOverlapMappingTorus.Cusp.logPoint
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos t h),
    (SpecialPeriods.CuspFamily.logBaseToRegular_holomorphic
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius
          ThreefoldOverlapMappingTorus.Cusp.specialRadius_cap).continuous.comp
      ((ThreefoldOverlapMappingTorus.Cusp.logBaseHeightHomeomorph
            ThreefoldOverlapMappingTorus.Cusp.specialData.radius
            ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos).symm.continuous.comp
        (continuous_const.prodMk continuous_id))⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.baseLift_translate
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (k : ℤ) (t : ℝ) :
    baseLift h (t + k) = (SpecialPeriods.triangleCuspGenerator ^ (-k)) • baseLift h t := by
  have he :=
    SpecialPeriods.CuspFamily.logBaseToRegular_translate
      ThreefoldOverlapMappingTorus.Cusp.specialData.radius
      ThreefoldOverlapMappingTorus.Cusp.specialRadius_cap (-k)
      (ThreefoldOverlapMappingTorus.Cusp.logPoint
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos t h)
  rw [ThreefoldOverlapMappingTorus.Cusp.logPoint_translate] at he
  simpa only [baseLift, ContinuousMap.coe_mk, Int.cast_neg, sub_neg_eq_add] using he

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.baseLift_projection_periodic
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    Function.Periodic (fun t : ℝ => SpecialPeriods.triangleRegularProject (baseLift h t)) 1 := by
  intro t
  have he := congrArg SpecialPeriods.triangleRegularProject (baseLift_translate h 1 t)
  simpa only [Int.cast_one, SpecialPeriods.triangleRegularProject_covering.map_smul] using he

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.baseLift_mem_horodisc
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (t : ℝ) :
    (baseLift h t : UpperHalfPlane) ∈
      SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width :=
  SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc
    ThreefoldOverlapMappingTorus.Cusp.specialData.radius
    ThreefoldOverlapMappingTorus.Cusp.specialRadius_cap _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.baseLift_cuspQ
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (t : ℝ) :
    SpecialPeriods.Triangle.cuspQ (baseLift h t : UpperHalfPlane) =
      CuspUniformization.exponential
        (ThreefoldOverlapMappingTorus.Cusp.logPoint
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos t h) :=
  SpecialPeriods.CuspFamily.logBaseToRegular_cuspQ
    ThreefoldOverlapMappingTorus.Cusp.specialData.radius
    ThreefoldOverlapMappingTorus.Cusp.specialRadius_cap _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.boundaryToRegularFamily_mk (t : ℝ) (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none
        (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x)) =
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
        (baseLift ThreefoldOverlapMappingTorus.Cusp.specialHeight t, x) :=
  ThreefoldOverlapMappingTorus.Cusp.boundaryToRegularFamily_cusp_mk t x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.finiteProjection_eq_plane (z : UpperHalfPlane) :
    SpecialPeriods.BetaTorsor.finiteProjection
        SpecialPeriods.Triangle.triangleSphereUniformization z =
      SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph
        (SpecialPeriods.triangleOrbitProjection z) := by
  rw [SpecialPeriods.BetaTorsor.finiteProjection, SpecialPeriods.BetaTorsor.finiteOrbitCoordinate,
    SpecialPeriods.Triangle.triangleSphereUniformization_openInclusion,
    SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_coe]
  exact
    congrArg
      (fun e : SpecialPeriods.TriangleOrbitSpace ≃ₜ ℂ =>
        e (SpecialPeriods.triangleOrbitProjection z))
      SpecialPeriods.Triangle.trianglePlaneUniformization_toHomeomorph

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.regularCoordinate_eq_finiteProjection
    (z : SpecialPeriods.TriangleRegularPoint) :
    (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject z) :
        ℂ) =
      SpecialPeriods.BetaTorsor.finiteProjection
        SpecialPeriods.Triangle.triangleSphereUniformization z.val := by
  rw [SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph_project, finiteProjection_eq_plane]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.reciprocalCoordinate_baseLift
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (t : ℝ) :
    reciprocalCoordinate
        (CuspUniformization.exponential
          (ThreefoldOverlapMappingTorus.Cusp.logPoint
            ThreefoldOverlapMappingTorus.Cusp.specialData.radius
            ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos t h)) =
      ((SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
            (SpecialPeriods.triangleRegularProject (baseLift h t)) :
          ℂ))⁻¹ := by
  have hp :
    SpecialPeriods.BetaTorsor.finiteProjection
        SpecialPeriods.Triangle.triangleSphereUniformization (baseLift h t).val ≠
      0 := by
    rw [← regularCoordinate_eq_finiteProjection]
    exact
      (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
            (SpecialPeriods.triangleRegularProject (baseLift h t))).property.1
  have he :=
    SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection_of_mem
      SpecialPeriods.Triangle.triangleSphereUniformization
      SpecialPeriods.Triangle.triangleSphereUniformization_cusp (baseLift h t).val
      (baseLift_mem_horodisc h t) hp
  rw [baseLift_cuspQ] at he
  rw [regularCoordinate_eq_finiteProjection]
  exact he

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.clockwiseUnit_symm_exponential (t : unitInterval) :
    SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit (unitInterval.symm t) =
      CuspUniformization.exponential (((t : ℝ) : ℂ) - 1) := by
  unfold SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit CuspUniformization.exponential
  rw [unitInterval.coe_symm_eq]
  congr 1
  push_cast
  ring

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.parameter_positive
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (t : unitInterval) :
    CuspUniformization.exponential
        (ThreefoldOverlapMappingTorus.Cusp.logPoint
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos (t : ℝ) h) =
      parameter h *
        SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit (unitInterval.symm t) := by
  rw [clockwiseUnit_symm_exponential, parameter, ← CuspUniformization.exponential_add]
  apply (CuspUniformization.exponential_eq_iff _ _).mpr
  refine ⟨1, ?_⟩
  change
    ((t : ℝ) : ℂ) + (h : ℝ) * Complex.I =
      ((0 : ℝ) : ℂ) + (h : ℝ) * Complex.I + (((t : ℝ) : ℂ) - 1) + ((1 : ℤ) : ℂ)
  push_cast
  ring

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private def PeriodFamily.Boundary.Cusp.projectedCurve
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    C(ℝ, SpecialPeriods.TriangleRegularQuotient) :=
  ⟨fun t => SpecialPeriods.triangleRegularProject (baseLift h t),
    SpecialPeriods.triangleRegularProject_covering.continuous.comp (baseLift h).continuous⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private def PeriodFamily.Boundary.Cusp.nativeLoop
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    Path (projectedCurve h 0) (projectedCurve h 0) :=
  PeriodFamily.Boundary.realCurveLoop (projectedCurve h) (baseLift_projection_periodic h)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace in
private theorem PeriodFamily.Boundary.Cusp.nativeLoop_coordinate
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (t : unitInterval) :
    (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph (nativeLoop h t) : ℂ) =
      (reciprocalCoordinate
          (parameter h *
            SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit (unitInterval.symm t)))⁻¹ := by
  change
    (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject (baseLift h (t : ℝ))) :
        ℂ) =
      _
  rw [← parameter_positive, reciprocalCoordinate_baseLift, inv_inv]

private def PeriodFamily.Boundary.Cusp.planeInverse :
    SpecialPeriods.Triangle.TwicePuncturedPlane ≃ₜ SpecialPeriods.Triangle.TwicePuncturedPlane
    where
  toFun z := ⟨(z : ℂ)⁻¹, inv_ne_zero z.property.1, fun h => z.property.2 (inv_eq_one.mp h)⟩
  invFun z := ⟨(z : ℂ)⁻¹, inv_ne_zero z.property.1, fun h => z.property.2 (inv_eq_one.mp h)⟩
  left_inv z := Subtype.ext (inv_inv (z : ℂ))
  right_inv z := Subtype.ext (inv_inv (z : ℂ))
  continuous_toFun :=
    (continuous_subtype_val.inv₀
          (fun z : SpecialPeriods.Triangle.TwicePuncturedPlane => z.property.1)).subtype_mk
      _
  continuous_invFun :=
    (continuous_subtype_val.inv₀
          (fun z : SpecialPeriods.Triangle.TwicePuncturedPlane => z.property.1)).subtype_mk
      _

private def PeriodFamily.Boundary.Cusp.inverseMeridian :
    Path (planeInverse SpecialPeriods.Triangle.meridianBasepoint)
      (planeInverse SpecialPeriods.Triangle.meridianBasepoint) :=
  ((SpecialPeriods.EllipticAttachingMeridians.fixedClockwiseMeridian Bool.false).symm).map
    planeInverse.continuous

private theorem PeriodFamily.Boundary.Cusp.inverseMeridian_coe (t : unitInterval) :
    (inverseMeridian t : ℂ) = 2 * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t := by
  have hp :
    (SpecialPeriods.EllipticAttachingMeridians.fixedClockwiseMeridian Bool.false).symm =
      SpecialPeriods.Triangle.positiveMeridianZero := by
    simp only [SpecialPeriods.EllipticAttachingMeridians.fixedClockwiseMeridian,
      Bool.false_eq_true, ite_false, Path.symm_symm]
  change
    (((SpecialPeriods.EllipticAttachingMeridians.fixedClockwiseMeridian Bool.false).symm t :
          ℂ))⁻¹ =
      _
  rw [hp, SpecialPeriods.Triangle.positiveMeridianZero_apply, mul_inv_rev, ← Complex.exp_neg]
  norm_num only [inv_div, inv_one, one_mul]
  unfold SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit
  rw [show
      -((2 * Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)) =
        -(2 * Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)
      by ring]
  ring

private def PeriodFamily.Boundary.Cusp.inverseRegularMeridian :
    Path
      (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
        (planeInverse SpecialPeriods.Triangle.meridianBasepoint))
      (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
        (planeInverse SpecialPeriods.Triangle.meridianBasepoint)) :=
  inverseMeridian.map SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm.continuous

private theorem PeriodFamily.Boundary.Cusp.reciprocalCoordinate_center :
    reciprocalCoordinate 0 = SpecialPeriods.EllipticAttachingMeridians.center Bool.false :=
  reciprocalCoordinate_zero

private def PeriodFamily.Boundary.Cusp.nativeReciprocalSquare :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare (nativeLoop controlledHeight)
      inverseRegularMeridian := by
  let S :=
    reciprocalControl.analyticMeridianSquare Bool.false reciprocalCoordinate_center
      (parameter controlledHeight) (parameter_ne_zero controlledHeight) parameter_controlled
  let rev : C(unitInterval × unitInterval, unitInterval × unitInterval) :=
    ⟨fun z => (z.1, unitInterval.symm z.2),
      continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd)⟩
  refine
    { map :=
        (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm :
              C(SpecialPeriods.Triangle.TwicePuncturedPlane, _)).comp
          ((planeInverse :
                C(SpecialPeriods.Triangle.TwicePuncturedPlane,
                  SpecialPeriods.Triangle.TwicePuncturedPlane)).comp
            (S.map.comp rev))
      initial := ?_
      final := ?_
      closed := ?_ }
  · intro t
    change
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
          (planeInverse (S.map (0, unitInterval.symm t))) =
        nativeLoop controlledHeight t
    apply SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    change ((S.map (0, unitInterval.symm t) : ℂ))⁻¹ = _
    rw [S.initial]
    exact (nativeLoop_coordinate controlledHeight t).symm
  · intro t
    change
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
          (planeInverse (S.map (1, unitInterval.symm t))) =
        inverseRegularMeridian t
    rw [S.final]
    rfl
  · intro s
    change
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
          (planeInverse (S.map (s, unitInterval.symm 0))) =
        SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
          (planeInverse (S.map (s, unitInterval.symm 1)))
    simp only [unitInterval.symm_zero, unitInterval.symm_one]
    exact
      congrArg
        (fun z => SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (planeInverse z))
        (S.closed s).symm

private def PeriodFamily.Boundary.Cusp.outerDeformationCoefficient (s : unitInterval) : ℂ :=
  2 * Complex.exp ((-(Real.pi : ℂ) / 2 * Complex.I) * ((s : ℝ) : ℂ))

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerDeformationCoefficient_zero :
    outerDeformationCoefficient 0 = 2 := by simp [outerDeformationCoefficient]

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerDeformationCoefficient_one :
    outerDeformationCoefficient 1 = -2 * Complex.I := by
  simp [outerDeformationCoefficient, Complex.exp_neg_pi_div_two_mul_I]

private theorem PeriodFamily.Boundary.Cusp.outerDeformationCoefficient_norm (s : unitInterval) :
    ‖outerDeformationCoefficient s‖ = 2 := by simp [outerDeformationCoefficient, Complex.norm_exp]

private def PeriodFamily.Boundary.Cusp.outerDeformation (s t : unitInterval) : ℂ :=
  (((s : ℝ) / 2 : ℝ) : ℂ) +
    outerDeformationCoefficient s * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t

private theorem PeriodFamily.Boundary.Cusp.outerDeformation_continuous :
    Continuous (fun p : unitInterval × unitInterval => outerDeformation p.1 p.2) := by
  unfold outerDeformation outerDeformationCoefficient
    SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit
  fun_prop

private theorem PeriodFamily.Boundary.Cusp.outerDeformation_norm (s t : unitInterval) :
    ‖outerDeformation s t - (((s : ℝ) / 2 : ℝ) : ℂ)‖ = 2 := by
  simp only [outerDeformation, add_sub_cancel_left, norm_mul, outerDeformationCoefficient_norm,
    SpecialPeriods.EllipticAttachingMeridians.norm_clockwiseUnit, mul_one]

private theorem PeriodFamily.Boundary.Cusp.outerDeformation_mem (s t : unitInterval) :
    outerDeformation s t ∈ SpecialPeriods.Triangle.twicePuncturedPlaneDomain := by
  change outerDeformation s t ≠ 0 ∧ outerDeformation s t ≠ 1
  have hs0 : 0 ≤ (s : ℝ) / 2 := div_nonneg s.property.1 (by norm_num)
  have hs1 : 0 ≤ 1 - (s : ℝ) / 2 := by linarith [s.property.2]
  constructor
  · intro he
    have hn := outerDeformation_norm s t
    rw [he, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0] at hn
    linarith [s.property.2]
  · intro he
    have hn := outerDeformation_norm s t
    rw [he,
      show (1 : ℂ) - (((s : ℝ) / 2 : ℝ) : ℂ) = ((1 - (s : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs1] at hn
    linarith [s.property.1]

private theorem PeriodFamily.Boundary.Cusp.outerCircle_symm_coefficient (t : unitInterval) :
    ((SpecialPeriods.Triangle.outerPositiveCircle 2 (le_refl 2)).symm t : ℂ) =
      (1 / 2 : ℂ) +
        (-2 * Complex.I) * SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit t := by
  change (SpecialPeriods.Triangle.outerPositiveCircle 2 (le_refl 2) (unitInterval.symm t) : ℂ) = _
  rw [SpecialPeriods.Triangle.outerPositiveCircle_coe, unitInterval.coe_symm_eq]
  unfold circleMap SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit
  push_cast
  rw [show
      (-(Real.pi : ℂ) / 2 + 2 * Real.pi * (1 - ((t : ℝ) : ℂ))) * Complex.I =
        (-(Real.pi : ℂ) / 2 * Complex.I + (-(2 * Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ))) +
          2 * Real.pi * Complex.I
      by ring,
    Complex.exp_periodic, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
  ring

private def PeriodFamily.Boundary.Cusp.inverseOuterSquare :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare inverseMeridian
      ((SpecialPeriods.Triangle.outerPositiveCircle 2 (le_refl 2)).symm) := by
  refine
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare.ofContinuous
      (fun p => ⟨outerDeformation p.1 p.2, outerDeformation_mem p.1 p.2⟩)
      (outerDeformation_continuous.subtype_mk _) ?_ ?_ ?_
  · intro t
    apply Subtype.ext
    change outerDeformation 0 t = (inverseMeridian t : ℂ)
    rw [inverseMeridian_coe]
    simp [outerDeformation]
  · intro t
    apply Subtype.ext
    rw [outerCircle_symm_coefficient]
    simp [outerDeformation]
  · intro s
    apply Subtype.ext
    simp only [outerDeformation, SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_zero,
      SpecialPeriods.EllipticAttachingMeridians.clockwiseUnit_one]

private def PeriodFamily.Boundary.Cusp.nativeOuterSquare :
    SpecialPeriods.EllipticAttachingMeridians.LoopSquare (nativeLoop controlledHeight)
      (((SpecialPeriods.Triangle.outerPositiveCircle 2 (le_refl 2)).symm).map
        SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm.continuous) :=
  nativeReciprocalSquare.trans
    (inverseOuterSquare.postcompose SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm.continuous)

private abbrev PeriodFamily.BoundaryLoopSquares.LoopCircle :=
  AddCircle (1 : ℝ)

private abbrev PeriodFamily.BoundaryLoopSquares.LoopInterval :=
  Set.Icc (0 : ℝ) (0 + 1)

private abbrev PeriodFamily.BoundaryLoopSquares.LoopQuotient :=
  Quot (AddCircle.EndpointIdent (1 : ℝ) 0)

private def PeriodFamily.BoundaryLoopSquares.loopIntervalHomeomorph : unitInterval ≃ₜ LoopInterval
    where
  toFun t := ⟨t.val, by simpa only [LoopInterval, unitInterval, zero_add] using t.property⟩
  invFun t := ⟨t.val, by simpa only [LoopInterval, unitInterval, zero_add] using t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_subtype_val.subtype_mk
      (fun t => by simpa only [LoopInterval, unitInterval, zero_add] using t.property)
  continuous_invFun :=
    continuous_subtype_val.subtype_mk
      (fun t => by simpa only [LoopInterval, unitInterval, zero_add] using t.property)

private def PeriodFamily.BoundaryLoopSquares.loopQuotientMap (t : unitInterval) : LoopQuotient :=
  Quot.mk _ ⟨t.val, by simpa only [LoopInterval, unitInterval, zero_add] using t.property⟩

private theorem PeriodFamily.BoundaryLoopSquares.loopQuotientMap_isQuotientMap :
    Topology.IsQuotientMap loopQuotientMap :=
  isQuotientMap_quot_mk.comp loopIntervalHomeomorph.isQuotientMap

private theorem PeriodFamily.BoundaryLoopSquares.loopCircleQuotient_unit (t : unitInterval) :
    AddCircle.homeoIccQuot (1 : ℝ) 0 ((t : ℝ) : LoopCircle) = loopQuotientMap t := by
  apply (AddCircle.homeoIccQuot (1 : ℝ) 0).symm.injective
  rw [Homeomorph.symm_apply_apply]
  rfl

private theorem PeriodFamily.BoundaryLoopSquares.loopUnitCircle_surjective :
    Function.Surjective (fun t : unitInterval => ((t : ℝ) : LoopCircle)) := by
  intro z
  obtain ⟨t, ht⟩ := loopQuotientMap_isQuotientMap.surjective (AddCircle.homeoIccQuot (1 : ℝ) 0 z)
  refine ⟨t, (AddCircle.homeoIccQuot (1 : ℝ) 0).injective ?_⟩
  rw [loopCircleQuotient_unit, ht]

private theorem
    PeriodFamily.BoundaryLoopSquares.loopCircle_int (k : ℤ) : ((k : ℝ) : LoopCircle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨k, by simp [zsmul_eq_mul]⟩

private theorem PeriodFamily.BoundaryLoopSquares.loopCircle_add_int (t : ℝ) (k : ℤ) :
    ((t + (k : ℝ) : ℝ) : LoopCircle) = (t : LoopCircle) := by
  rw [AddCircle.coe_add, loopCircle_int, add_zero]

private theorem PeriodFamily.BoundaryLoopSquares.loopCircle_add_one (t : ℝ) :
    ((t + 1 : ℝ) : LoopCircle) = (t : LoopCircle) :=
  AddCircle.coe_add_period (1 : ℝ) t

private def PeriodFamily.BoundaryLoopSquares.loopOnQuotient {X : Type*} [TopologicalSpace X] {a : X}
    (p : Path a a) : C(LoopQuotient, X)
    where
  toFun :=
    Quot.lift
      (fun u : LoopInterval =>
        p ⟨u.val, by simpa only [LoopInterval, unitInterval, zero_add] using u.property⟩)
      (by
        intro u v h
        cases h
        calc
          _ = p 0 := congrArg p (Subtype.ext rfl)
          _ = p 1 := (p.source.trans p.target.symm)
          _ = _ := congrArg p (Subtype.ext (zero_add (1 : ℝ)).symm))
  continuous_toFun :=
    continuous_quot_lift _ (p.continuous.comp loopIntervalHomeomorph.symm.continuous)

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.loopOnQuotient_unit {X : Type*} [TopologicalSpace X]
    {a : X} (p : Path a a) (t : unitInterval) : loopOnQuotient p (loopQuotientMap t) = p t :=
  rfl

private def PeriodFamily.BoundaryLoopSquares.loopOnCircle {X : Type*} [TopologicalSpace X] {a : X}
    (p : Path a a) : C(LoopCircle, X) :=
  (loopOnQuotient p).comp (AddCircle.homeoIccQuot (1 : ℝ) 0 : C(LoopCircle, LoopQuotient))

@[simp]
private theorem PeriodFamily.BoundaryLoopSquares.loopOnCircle_unit {X : Type*} [TopologicalSpace X]
    {a : X} (p : Path a a) (t : unitInterval) : loopOnCircle p ((t : ℝ) : LoopCircle) = p t := by
  change loopOnQuotient p (AddCircle.homeoIccQuot (1 : ℝ) 0 ((t : ℝ) : LoopCircle)) = p t
  rw [loopCircleQuotient_unit, loopOnQuotient_unit]

private def PeriodFamily.BoundaryLoopSquares.loopPeriodic {X : Type*} [TopologicalSpace X] {a : X}
    (p : Path a a) : C(ℝ, X) :=
  (loopOnCircle p).comp ⟨fun t : ℝ => (t : LoopCircle), AddCircle.continuous_mk' (1 : ℝ)⟩

@[simp]
private theorem PeriodFamily.BoundaryLoopSquares.loopPeriodic_apply {X : Type*} [TopologicalSpace X]
    {a : X} (p : Path a a) (t : ℝ) : loopPeriodic p t = loopOnCircle p (t : LoopCircle) :=
  rfl

private theorem PeriodFamily.BoundaryLoopSquares.loopPeriodic_unit {X : Type*} [TopologicalSpace X]
    {a : X} (p : Path a a) (t : unitInterval) : loopPeriodic p (t : ℝ) = p t :=
  loopOnCircle_unit p t

private theorem
    PeriodFamily.BoundaryLoopSquares.loopPeriodic_add_one {X : Type*} [TopologicalSpace X]
    {a : X} (p : Path a a) (t : ℝ) : loopPeriodic p (t + 1) = loopPeriodic p t := by
  simp only [loopPeriodic_apply, loopCircle_add_one]

private theorem PeriodFamily.BoundaryLoopSquares.loopPeriodic_zero {X : Type*} [TopologicalSpace X]
    {a : X} (p : Path a a) : loopPeriodic p 0 = a :=
  (loopPeriodic_unit p 0).trans p.source

private theorem
    PeriodFamily.BoundaryLoopSquares.loopPeriodic_unique {X : Type*} [TopologicalSpace X]
    {a : X} {p : Path a a} (f : ℝ → X) (hf : Function.Periodic f 1)
    (hp : ∀ t : unitInterval, f (t : ℝ) = p t) : f = loopPeriodic p := by
  have h : hf.lift = (loopOnCircle p : LoopCircle → X) := by
    funext z
    obtain ⟨t, rfl⟩ := loopUnitCircle_surjective z
    rw [Function.Periodic.lift_coe, loopOnCircle_unit]
    exact hp t
  funext t
  exact congrFun h (t : LoopCircle)

private def
    PeriodFamily.BoundaryLoopSquares.loopSquareQuotient {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b} (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (z : unitInterval × LoopQuotient) : X :=
  Quot.lift
    (fun u : LoopInterval =>
      S.map (z.1, ⟨u.val, by simpa only [LoopInterval, unitInterval, zero_add] using u.property⟩))
    (by
      intro u v h
      cases h
      calc
        _ = S.map (z.1, 0) := congrArg (fun t => S.map (z.1, t)) (Subtype.ext rfl)
        _ = S.map (z.1, 1) := (S.closed z.1)
        _ = _ := congrArg (fun t => S.map (z.1, t)) (Subtype.ext (zero_add (1 : ℝ)).symm))
    z.2

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.loopSquareQuotient_unit {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (s t : unitInterval) :
    loopSquareQuotient S (s, loopQuotientMap t) = S.map (s, t) :=
  rfl

private theorem PeriodFamily.BoundaryLoopSquares.continuous_loopSquareQuotient {X : Type*}
    [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    Continuous (loopSquareQuotient S) := by
  apply loopQuotientMap_isQuotientMap.continuous_lift_prod_right
  change Continuous (fun z : unitInterval × unitInterval => S.map (z.1, z.2))
  exact S.map.continuous

private def
    PeriodFamily.BoundaryLoopSquares.quotientSquare {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b} (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    C(unitInterval × LoopQuotient, X) :=
  ⟨loopSquareQuotient S, continuous_loopSquareQuotient S⟩

private def PeriodFamily.BoundaryLoopSquares.circleSquare {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b} (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    C(unitInterval × LoopCircle, X) :=
  (quotientSquare S).comp
    ⟨fun z => (z.1, AddCircle.homeoIccQuot (1 : ℝ) 0 z.2),
      continuous_fst.prodMk ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp continuous_snd)⟩

@[simp]
private theorem PeriodFamily.BoundaryLoopSquares.circleSquare_unit {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (s t : unitInterval) :
    circleSquare S (s, ((t : ℝ) : LoopCircle)) = S.map (s, t) := by
  change loopSquareQuotient S (s, AddCircle.homeoIccQuot (1 : ℝ) 0 ((t : ℝ) : LoopCircle)) = _
  rw [loopCircleQuotient_unit, loopSquareQuotient_unit]

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.circleSquare_initial {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (z : LoopCircle) :
    circleSquare S (0, z) = loopOnCircle p z := by
  obtain ⟨t, rfl⟩ := loopUnitCircle_surjective z
  rw [circleSquare_unit, loopOnCircle_unit, S.initial]

@[simp]
private theorem PeriodFamily.BoundaryLoopSquares.circleSquare_final {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (z : LoopCircle) :
    circleSquare S (1, z) = loopOnCircle q z := by
  obtain ⟨t, rfl⟩ := loopUnitCircle_surjective z
  rw [circleSquare_unit, loopOnCircle_unit, S.final]

private def
    PeriodFamily.BoundaryLoopSquares.periodicSquare {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b} (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    C(unitInterval × ℝ, X) :=
  (circleSquare S).comp
    ⟨fun z => (z.1, (z.2 : LoopCircle)),
      continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)⟩

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.periodicSquare_unit {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (s t : unitInterval) :
    periodicSquare S (s, (t : ℝ)) = S.map (s, t) :=
  circleSquare_unit S s t

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.periodicSquare_initial {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (t : ℝ) :
    periodicSquare S (0, t) = loopPeriodic p t :=
  circleSquare_initial S (t : LoopCircle)

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.periodicSquare_final {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (t : ℝ) :
    periodicSquare S (1, t) = loopPeriodic q t :=
  circleSquare_final S (t : LoopCircle)

private theorem
    PeriodFamily.BoundaryLoopSquares.periodicSquare_add_int {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (s : unitInterval) (t : ℝ)
    (k : ℤ) : periodicSquare S (s, t + (k : ℝ)) = periodicSquare S (s, t) := by
  change circleSquare S (s, ((t + (k : ℝ) : ℝ) : LoopCircle)) = _
  rw [loopCircle_add_int]
  rfl

private def
    PeriodFamily.BoundaryLoopSquares.periodicHomotopy {X : Type*} [TopologicalSpace X] {a b : X}
    {p : Path a a} {q : Path b b} (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) :
    (loopPeriodic p).Homotopy (loopPeriodic q)
    where
  toFun := periodicSquare S
  continuous_toFun := (periodicSquare S).continuous
  map_zero_left := periodicSquare_initial S
  map_one_left := periodicSquare_final S

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.periodicHomotopy_unit {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (s t : unitInterval) :
    periodicHomotopy S (s, (t : ℝ)) = S.map (s, t) :=
  periodicSquare_unit S s t

private theorem
    PeriodFamily.BoundaryLoopSquares.periodicHomotopy_add_int {X : Type*} [TopologicalSpace X]
    {a b : X} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q) (s : unitInterval) (t : ℝ)
    (k : ℤ) : periodicHomotopy S (s, t + (k : ℝ)) = periodicHomotopy S (s, t) :=
  periodicSquare_add_int S s t k

private theorem PeriodFamily.Boundary.Cusp.projectedCurve_eq_periodic
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    (projectedCurve h : ℝ → SpecialPeriods.TriangleRegularQuotient) =
      PeriodFamily.BoundaryLoopSquares.loopPeriodic (nativeLoop h) :=
  PeriodFamily.BoundaryLoopSquares.loopPeriodic_unique (projectedCurve h)
    (baseLift_projection_periodic h) (fun _ => rfl)

private def PeriodFamily.Boundary.Cusp.nativePeriodicSquare :
    C(unitInterval × ℝ, SpecialPeriods.TriangleRegularQuotient) :=
  PeriodFamily.BoundaryLoopSquares.periodicSquare nativeOuterSquare

@[simp]
private theorem PeriodFamily.Boundary.Cusp.nativePeriodicSquare_zero (t : ℝ) :
    nativePeriodicSquare (0, t) =
      SpecialPeriods.triangleRegularProject (baseLift controlledHeight t) :=
  (PeriodFamily.BoundaryLoopSquares.periodicSquare_initial nativeOuterSquare t).trans
    (congrFun (projectedCurve_eq_periodic controlledHeight) t).symm

private theorem PeriodFamily.Boundary.Cusp.nativePeriodicSquare_translate (s : unitInterval) (k : ℤ)
    (t : ℝ) : nativePeriodicSquare (s, t + k) = nativePeriodicSquare (s, t) :=
  PeriodFamily.BoundaryLoopSquares.periodicSquare_add_int nativeOuterSquare s t k

private def PeriodFamily.Boundary.Cusp.nativeLiftedSquare :
    C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint) :=
  PeriodFamily.Boundary.baseHomotopyLift nativePeriodicSquare (baseLift controlledHeight)
    nativePeriodicSquare_zero

@[simp]
private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_zero (t : ℝ) :
    nativeLiftedSquare (0, t) = baseLift controlledHeight t :=
  PeriodFamily.Boundary.baseHomotopyLift_zero nativePeriodicSquare (baseLift controlledHeight)
    nativePeriodicSquare_zero t

private theorem
    PeriodFamily.Boundary.Cusp.nativeLiftedSquare_projection (s : unitInterval) (t : ℝ) :
    SpecialPeriods.triangleRegularProject (nativeLiftedSquare (s, t)) =
      nativePeriodicSquare (s, t) :=
  PeriodFamily.Boundary.baseHomotopyLift_projection nativePeriodicSquare
    (baseLift controlledHeight) nativePeriodicSquare_zero s t

private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_translate (s : unitInterval) (k : ℤ)
    (t : ℝ) :
    nativeLiftedSquare (s, t + k) =
      (SpecialPeriods.triangleCuspGenerator ^ (-k)) • nativeLiftedSquare (s, t) :=
  PeriodFamily.Boundary.baseHomotopyLift_translate nativePeriodicSquare
    (baseLift controlledHeight) nativePeriodicSquare_zero SpecialPeriods.triangleCuspGenerator
    nativePeriodicSquare_translate (baseLift_translate controlledHeight) s k t

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.quotient_same_base_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (z : SpecialPeriods.TriangleRegularPoint) :
    Function.Injective (fun x : RealTorus₄ => D.quotient (z, x)) :=
  DiagonalQuotient.fibreInclusion_injective (F := RealTorus₄)
    SpecialPeriods.triangleRegularProject_covering z

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.fibreMap_deck_of_actual {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space)) (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : SpecialPeriods.TriangleGroup)
    (hF : ∀ p : ℝ × X, F (MappingTorus.mk φ p) = D.quotient (L p.1, G p))
    (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t) (k : ℤ) (p : ℝ × X) :
    G (MappingTorus.deck φ k p) = (g ^ (-k)) • G p := by
  have hraw : D.quotient (L (p.1 + k), G (MappingTorus.deck φ k p)) = D.quotient (L p.1, G p) := by
    calc
      _ = F (MappingTorus.mk φ (MappingTorus.deck φ k p)) := (hF (MappingTorus.deck φ k p)).symm
      _ = F (MappingTorus.mk φ p) := (congrArg F (MappingTorus.mk_deck φ k p))
      _ = _ := hF p
  have hframe : D.quotient (L (p.1 + k), (g ^ (-k)) • G p) = D.quotient (L p.1, G p) := by
    rw [hL]
    exact D.quotient_smul (g ^ (-k)) (L p.1, G p)
  exact quotient_same_base_injective D (L (p.1 + k)) (hraw.trans hframe.symm)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.actualBoundary_homotopic_of_base {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space)) (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (G : C(ℝ × X, RealTorus₄)) (g : SpecialPeriods.TriangleGroup)
    (hF : ∀ p : ℝ × X, F (MappingTorus.mk φ p) = D.quotient (L p.1, G p))
    (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint)) (hzero : ∀ t, H (0, t) = L t)
    (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t)) :
    F.Homotopic
      (familyBoundaryMap D φ (baseHomotopySlice H 1) G g (hH 1)
        (fibreMap_deck_of_actual D φ F L G g hF hL)) := by
  have he :
    familyBoundaryMap D φ (baseHomotopySlice H 0) G g (hH 0)
        (fibreMap_deck_of_actual D φ F L G g hF hL) =
      F := by
    apply ContinuousMap.ext
    intro q
    obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective φ q
    change D.quotient (H (0, p.1), G p) = F (MappingTorus.mk φ p)
    exact (congrArg (fun z => D.quotient (z, G p)) (hzero p.1)).trans (hF p).symm
  exact
    ⟨(familyBoundaryHomotopy D φ H G g hH (fibreMap_deck_of_actual D φ F L G g hF hL)).cast he
        rfl⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.nativeFibreCylinder : C(ℝ × RealTorus₄, RealTorus₄) :=
  ⟨Prod.snd, continuous_snd⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.Cusp.nativeFibreCylinder_deck (k : ℤ) (p : ℝ × RealTorus₄) :
    nativeFibreCylinder (MappingTorus.deck ThreefoldOverlapMappingTorus.Cusp.monodromy k p) =
      (SpecialPeriods.triangleCuspGenerator ^ (-k)) • nativeFibreCylinder p :=
  PeriodFamily.Boundary.fibreMap_deck_of_actual
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
    ThreefoldOverlapMappingTorus.Cusp.monodromy
    (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none)
    (baseLift ThreefoldOverlapMappingTorus.Cusp.specialHeight) nativeFibreCylinder
    SpecialPeriods.triangleCuspGenerator (fun p => boundaryToRegularFamily_mk p.1 p.2)
    (baseLift_translate ThreefoldOverlapMappingTorus.Cusp.specialHeight) k p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.heightBoundaryMap
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    C(ThreefoldOverlapMappingTorus.Cusp.Boundary,
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.Space) :=
  PeriodFamily.Boundary.familyBoundaryMap ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
    ThreefoldOverlapMappingTorus.Cusp.monodromy (baseLift h) nativeFibreCylinder
    SpecialPeriods.triangleCuspGenerator (baseLift_translate h) nativeFibreCylinder_deck

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.Cusp.heightBoundaryMap_specialHeight :
    heightBoundaryMap ThreefoldOverlapMappingTorus.Cusp.specialHeight =
      ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy q
  exact (boundaryToRegularFamily_mk p.1 p.2).symm

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.heightSegment
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    C(unitInterval,
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :=
  ⟨fun s =>
    ⟨(1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ), by
      exact
        (convex_Ioi
              (ThreefoldOverlapMappingTorus.Cusp.heightThreshold
                ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
            Convex ℝ
              (Set.Ioi
                (ThreefoldOverlapMappingTorus.Cusp.heightThreshold
                  ThreefoldOverlapMappingTorus.Cusp.specialData.radius)))
          a.property b.property (sub_nonneg.mpr s.property.2) s.property.1
          (sub_add_cancel 1 (s : ℝ))⟩,
    (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
          (continuous_subtype_val.mul continuous_const)).subtype_mk
      _⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Boundary.Cusp.heightSegment_zero
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    heightSegment a b 0 = a := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) * (a : ℝ) + 0 * (b : ℝ) = (a : ℝ)
  simp

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Boundary.Cusp.heightSegment_one
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    heightSegment a b 1 = b := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) * (a : ℝ) + 1 * (b : ℝ) = (b : ℝ)
  simp

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.heightBaseHomotopy
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint) :=
  ⟨fun p => baseLift (heightSegment a b p.1) p.2,
    (SpecialPeriods.CuspFamily.logBaseToRegular_holomorphic
          ThreefoldOverlapMappingTorus.Cusp.specialData.radius
          ThreefoldOverlapMappingTorus.Cusp.specialRadius_cap).continuous.comp
      ((ThreefoldOverlapMappingTorus.Cusp.logBaseHeightHomeomorph
            ThreefoldOverlapMappingTorus.Cusp.specialData.radius
            ThreefoldOverlapMappingTorus.Cusp.specialData.radius_pos).symm.continuous.comp
        (((heightSegment a b).continuous.comp continuous_fst).prodMk continuous_snd))⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Boundary.Cusp.heightBaseHomotopy_apply
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (s : unitInterval) (t : ℝ) :
    heightBaseHomotopy a b (s, t) = baseLift (heightSegment a b s) t :=
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.Cusp.heightBaseHomotopy_zero
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (t : ℝ) : heightBaseHomotopy a b (0, t) = baseLift a t := by
  rw [heightBaseHomotopy_apply, heightSegment_zero]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.Cusp.heightBaseHomotopy_one
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (t : ℝ) : heightBaseHomotopy a b (1, t) = baseLift b t := by
  rw [heightBaseHomotopy_apply, heightSegment_one]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.Cusp.heightBaseHomotopy_translate
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius)
    (s : unitInterval) (k : ℤ) (t : ℝ) :
    heightBaseHomotopy a b (s, t + k) =
      (SpecialPeriods.triangleCuspGenerator ^ (-k)) • heightBaseHomotopy a b (s, t) :=
  baseLift_translate (heightSegment a b s) k t

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.heightBoundaryHomotopy
    (a b :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    (heightBoundaryMap a).Homotopy (heightBoundaryMap b) :=
  (PeriodFamily.Boundary.familyBoundaryHomotopy
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
        ThreefoldOverlapMappingTorus.Cusp.monodromy (heightBaseHomotopy a b) nativeFibreCylinder
        SpecialPeriods.triangleCuspGenerator (heightBaseHomotopy_translate a b)
        nativeFibreCylinder_deck).cast
    (by
      apply ContinuousMap.ext
      intro q
      obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy q
      change
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
            (heightBaseHomotopy a b (0, p.1), p.2) =
          ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient (baseLift a p.1, p.2)
      rw [heightBaseHomotopy_zero])
    (by
      apply ContinuousMap.ext
      intro q
      obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy q
      change
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
            (heightBaseHomotopy a b (1, p.1), p.2) =
          ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient (baseLift b p.1, p.2)
      rw [heightBaseHomotopy_one])

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.boundaryToRegularFamily_heightHomotopy
    (h :
      ThreefoldOverlapMappingTorus.Cusp.Height
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius) :
    (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none).Homotopy
      (heightBoundaryMap h) :=
  (heightBoundaryHomotopy ThreefoldOverlapMappingTorus.Cusp.specialHeight h).cast
    heightBoundaryMap_specialHeight rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.normalizedBoundaryMap :
    C(ThreefoldOverlapMappingTorus.Cusp.Boundary,
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.Space) :=
  PeriodFamily.Boundary.familyBoundaryMap ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
    ThreefoldOverlapMappingTorus.Cusp.monodromy
    (PeriodFamily.Boundary.baseHomotopySlice nativeLiftedSquare 1) nativeFibreCylinder
    SpecialPeriods.triangleCuspGenerator (nativeLiftedSquare_translate 1) nativeFibreCylinder_deck

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Boundary.Cusp.normalizedBoundaryMap_mk (t : ℝ) (x : RealTorus₄) :
    normalizedBoundaryMap (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x)) =
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
        (nativeLiftedSquare (1, t), x) :=
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.heightToNormalizedHomotopy :
    (heightBoundaryMap controlledHeight).Homotopy normalizedBoundaryMap :=
  (PeriodFamily.Boundary.familyBoundaryHomotopy
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
        ThreefoldOverlapMappingTorus.Cusp.monodromy nativeLiftedSquare nativeFibreCylinder
        SpecialPeriods.triangleCuspGenerator nativeLiftedSquare_translate
        nativeFibreCylinder_deck).cast
    (by
      apply ContinuousMap.ext
      intro q
      obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy q
      change
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
            (nativeLiftedSquare (0, p.1), p.2) =
          ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
            (baseLift controlledHeight p.1, p.2)
      rw [nativeLiftedSquare_zero])
    rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.Cusp.boundaryToNormalizedHomotopy :
    (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none).Homotopy
      normalizedBoundaryMap :=
  (boundaryToRegularFamily_heightHomotopy controlledHeight).trans heightToNormalizedHomotopy

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.Cusp.boundaryRegularHomologyMap_normalized (n : ℕ) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none n =
      SingularMayerVietoris.singularHomologyMap normalizedBoundaryMap n :=
  PeriodTorusHigherHomology.homotopy_homologyMap boundaryToNormalizedHomotopy n

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.Cusp.normalizedBoundaryMap_projection_mk (t : ℝ) (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection
        (normalizedBoundaryMap
          (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x))) =
      SpecialPeriods.triangleRegularProject (nativeLiftedSquare (1, t)) :=
  rfl

private theorem PeriodFamily.Boundary.Cusp.sin_two_pi_gt_half_of_le_quarter_mo1973_26635 (t : ℝ)
    (ht0 : 1 / 8 < t) (ht1 : t ≤ 1 / 4) : (1 / 2 : ℝ) < Real.sin (2 * Real.pi * t) := by
  have hlow := mul_lt_mul_of_pos_left ht0 Real.pi_pos
  have hupp := mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le
  calc
    (1 / 2 : ℝ) = Real.sin (Real.pi / 6) := Real.sin_pi_div_six.symm
    _ < Real.sin (2 * Real.pi * t) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · linarith
      · linarith [Real.pi_pos]

private theorem PeriodFamily.Boundary.Cusp.sin_two_pi_gt_half (t : ℝ) (ht0 : 1 / 8 < t)
    (ht1 : t < 3 / 8) : (1 / 2 : ℝ) < Real.sin (2 * Real.pi * t) := by
  by_cases ht : t ≤ 1 / 4
  · exact sin_two_pi_gt_half_of_le_quarter_mo1973_26635 t ht0 ht
  · have h :=
      sin_two_pi_gt_half_of_le_quarter_mo1973_26635 (1 / 2 - t) (by linarith) (by linarith)
    rwa [show 2 * Real.pi * (1 / 2 - t) = Real.pi - 2 * Real.pi * t by ring, Real.sin_pi_sub] at h

public
theorem PeriodFamily.Boundary.Cusp.sin_two_pi_lt_neg_half (t : ℝ) (ht0 : -(3 / 8) < t)
    (ht1 : t < -(1 / 8)) : Real.sin (2 * Real.pi * t) < -(1 / 2 : ℝ) := by
  have h := sin_two_pi_gt_half (-t) (by linarith) (by linarith)
  rw [mul_neg, Real.sin_neg] at h
  linarith

private def PeriodFamily.Boundary.Cusp.outerClockwiseCircle :
    Path (SpecialPeriods.Triangle.outerCircleBasepoint (2 : ℝ) (by norm_num))
      (SpecialPeriods.Triangle.outerCircleBasepoint (2 : ℝ) (by norm_num)) :=
  (SpecialPeriods.Triangle.outerPositiveCircle (2 : ℝ) (by norm_num)).symm

private def PeriodFamily.Boundary.Cusp.outerClockwiseCurve :
    C(ℝ, SpecialPeriods.Triangle.TwicePuncturedPlane) :=
  ⟨fun t =>
    ⟨SpecialPeriods.Triangle.outerCircleValue 2 (-t),
      SpecialPeriods.Triangle.outerCircleValue_avoids_punctures 2 (by norm_num) (-t)⟩,
    ((SpecialPeriods.Triangle.continuous_outerCircleValue 2).comp
          ContinuousNeg.continuous_neg).subtype_mk
      _⟩

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_coe (t : ℝ) :
    (outerClockwiseCurve t : ℂ) = SpecialPeriods.Triangle.outerCircleValue 2 (-t) :=
  rfl

private theorem PeriodFamily.Boundary.Cusp.outerValue_periodic_mo1973_26641 (R : ℝ) :
    Function.Periodic (SpecialPeriods.Triangle.outerCircleValue R) 1 := by
  intro t
  unfold SpecialPeriods.Triangle.outerCircleValue
  rw [show -Real.pi / 2 + 2 * Real.pi * (t + 1) = (-Real.pi / 2 + 2 * Real.pi * t) + 2 * Real.pi
      by ring]
  exact periodic_circleMap (1 / 2 : ℂ) R _

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_periodic :
    Function.Periodic outerClockwiseCurve 1 := by
  intro t
  apply Subtype.ext
  change
    SpecialPeriods.Triangle.outerCircleValue 2 (-(t + 1)) =
      SpecialPeriods.Triangle.outerCircleValue 2 (-t)
  rw [show -(t + 1) = -t - 1 by ring]
  exact (outerValue_periodic_mo1973_26641 2).sub_eq (-t)

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_add_one (t : ℝ) :
    outerClockwiseCurve (t + 1) = outerClockwiseCurve t :=
  outerClockwiseCurve_periodic t

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_unit (t : unitInterval) :
    outerClockwiseCurve (t : ℝ) = outerClockwiseCircle t := by
  apply Subtype.ext
  change
    SpecialPeriods.Triangle.outerCircleValue 2 (-(t : ℝ)) =
      SpecialPeriods.Triangle.outerCircleValue 2 ((unitInterval.symm t : unitInterval) : ℝ)
  rw [unitInterval.coe_symm_eq]
  exact (outerValue_periodic_mo1973_26641 2).sub_eq'.symm

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_quarter :
    (outerClockwiseCurve (1 / 4) : ℂ) = -(3 / 2 : ℂ) := by
  rw [outerClockwiseCurve_coe]
  have h :
    SpecialPeriods.Triangle.outerCircleValue 2 (-(1 / 4 : ℝ)) =
      SpecialPeriods.Triangle.outerCircleValue 2 (3 / 4) := by
    convert ((outerValue_periodic_mo1973_26641 2) (-(1 / 4 : ℝ))).symm using 1
    norm_num
  rw [h, SpecialPeriods.Triangle.outerCircleValue_threeQuarters]
  norm_num

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_threeQuarters :
    (outerClockwiseCurve (3 / 4) : ℂ) = (5 / 2 : ℂ) := by
  rw [outerClockwiseCurve_coe]
  have h :
    SpecialPeriods.Triangle.outerCircleValue 2 (-(3 / 4 : ℝ)) =
      SpecialPeriods.Triangle.outerCircleValue 2 (1 / 4) := by
    convert ((outerValue_periodic_mo1973_26641 2) (-(3 / 4 : ℝ))).symm using 1
    norm_num
  rw [h, SpecialPeriods.Triangle.outerCircleValue_quarter]
  norm_num

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_re (t : ℝ) :
    (outerClockwiseCurve t : ℂ).re = 1 / 2 - 2 * Real.sin (2 * Real.pi * t) := by
  have h :=
    congrArg Complex.re (circleMap_sub_center (1 / 2 : ℂ) 2 (-Real.pi / 2 + 2 * Real.pi * (-t)))
  rw [Complex.sub_re, circleMap_zero_re,
    show -Real.pi / 2 + 2 * Real.pi * (-t) = -(2 * Real.pi * t) - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two, Real.sin_neg] at h
  norm_num at h
  change (circleMap (1 / 2 : ℂ) 2 (-Real.pi / 2 + 2 * Real.pi * (-t))).re = _
  rw [show -Real.pi / 2 + 2 * Real.pi * (-t) = -(2 * Real.pi * t) - Real.pi / 2 by ring]
  linarith

private theorem
    PeriodFamily.Boundary.Cusp.outerClockwiseCircle_mem_upperSlitPlane (t : unitInterval)
    (ht0 : 1 / 4 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 3 / 4) :
    (outerClockwiseCircle t : ℂ) ∈ SpecialPeriods.Triangle.upperSlitPlane := by
  change
    (SpecialPeriods.Triangle.outerPositiveCircle 2 (by norm_num) (unitInterval.symm t) : ℂ) ∈
      SpecialPeriods.Triangle.upperSlitPlane
  apply SpecialPeriods.Triangle.outerPositiveCircle_mem_upperSlitPlane
  · rw [unitInterval.coe_symm_eq]
    linarith
  · rw [unitInterval.coe_symm_eq]
    linarith

private theorem
    PeriodFamily.Boundary.Cusp.outerClockwiseCircle_mem_lowerSlitPlane (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (t : ℝ)) :
    (outerClockwiseCircle t : ℂ) ∈ SpecialPeriods.Triangle.lowerSlitPlane := by
  change
    (SpecialPeriods.Triangle.outerPositiveCircle 2 (by norm_num) (unitInterval.symm t) : ℂ) ∈
      SpecialPeriods.Triangle.lowerSlitPlane
  apply SpecialPeriods.Triangle.outerPositiveCircle_mem_lowerSlitPlane
  rw [unitInterval.coe_symm_eq]
  rcases ht with ht | ht
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_mem_upperSlitPlane (t : ℝ)
    (ht0 : 1 / 8 < t) (ht1 : t < 7 / 8) :
    (outerClockwiseCurve t : ℂ) ∈ SpecialPeriods.Triangle.upperSlitPlane := by
  by_cases hleft : t < 1 / 4
  · have hs := sin_two_pi_gt_half t ht0 (by linarith)
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  by_cases hright : 3 / 4 < t
  · have hs := sin_two_pi_lt_neg_half (t - 1) (by linarith) (by linarith)
    rw [show 2 * Real.pi * (t - 1) = 2 * Real.pi * t - 2 * Real.pi by ring,
      Real.sin_sub_two_pi] at hs
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  · let u : unitInterval := ⟨t, by constructor <;> linarith⟩
    change (outerClockwiseCurve (u : ℝ) : ℂ) ∈ SpecialPeriods.Triangle.upperSlitPlane
    rw [outerClockwiseCurve_unit]
    exact outerClockwiseCircle_mem_upperSlitPlane u (le_of_not_gt hleft) (le_of_not_gt hright)

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseCurve_mem_lowerSlitPlane (t : ℝ)
    (ht0 : -(3 / 8) < t) (ht1 : t < 3 / 8) :
    (outerClockwiseCurve t : ℂ) ∈ SpecialPeriods.Triangle.lowerSlitPlane := by
  by_cases hleft : t < -(1 / 4)
  · have hs := sin_two_pi_lt_neg_half t ht0 (by linarith)
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  by_cases hright : 1 / 4 < t
  · have hs := sin_two_pi_gt_half t (by linarith) ht1
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  by_cases hneg : t < 0
  · let u : unitInterval := ⟨t + 1, by constructor <;> linarith⟩
    have hu : 3 / 4 ≤ (u : ℝ) := by
      change 3 / 4 ≤ t + 1
      linarith
    have h := outerClockwiseCircle_mem_lowerSlitPlane u (Or.inr hu)
    rw [← outerClockwiseCurve_unit] at h
    change (outerClockwiseCurve (t + 1) : ℂ) ∈ SpecialPeriods.Triangle.lowerSlitPlane at h
    rwa [outerClockwiseCurve_add_one] at h
  · let u : unitInterval := ⟨t, by constructor <;> linarith⟩
    change (outerClockwiseCurve (u : ℝ) : ℂ) ∈ SpecialPeriods.Triangle.lowerSlitPlane
    rw [outerClockwiseCurve_unit]
    exact outerClockwiseCircle_mem_lowerSlitPlane u (Or.inl (le_of_not_gt hright))

private def PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve :
    C(ℝ, SpecialPeriods.TriangleRegularQuotient) :=
  (SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm :
        C(SpecialPeriods.Triangle.TwicePuncturedPlane,
          SpecialPeriods.TriangleRegularQuotient)).comp
    outerClockwiseCurve

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_coordinate (t : ℝ) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph (outerClockwiseRegularCurve t) =
      outerClockwiseCurve t :=
  SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.apply_symm_apply _

private def PeriodFamily.Boundary.Cusp.outerClockwiseRegularBasepoint :
    SpecialPeriods.TriangleRegularQuotient :=
  SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm
    (SpecialPeriods.Triangle.outerCircleBasepoint 2 (by norm_num))

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularBasepoint_coordinate :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph outerClockwiseRegularBasepoint =
      SpecialPeriods.Triangle.outerCircleBasepoint 2 (by norm_num) :=
  SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.apply_symm_apply _

private def PeriodFamily.Boundary.Cusp.outerClockwiseRegularMeridian :
    Path outerClockwiseRegularBasepoint outerClockwiseRegularBasepoint :=
  outerClockwiseCircle.map SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm.continuous

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_unit (t : unitInterval) :
    outerClockwiseRegularCurve t = outerClockwiseRegularMeridian t := by
  change
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (outerClockwiseCurve t) =
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (outerClockwiseCircle t)
  rw [outerClockwiseCurve_unit]

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_zero :
    outerClockwiseRegularCurve 0 = outerClockwiseRegularBasepoint :=
  (outerClockwiseRegularCurve_unit 0).trans outerClockwiseRegularMeridian.source

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_one :
    outerClockwiseRegularCurve 1 = outerClockwiseRegularBasepoint :=
  (outerClockwiseRegularCurve_unit 1).trans outerClockwiseRegularMeridian.target

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_periodic :
    Function.Periodic outerClockwiseRegularCurve 1 := by
  intro t
  change
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (outerClockwiseCurve (t + 1)) =
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.symm (outerClockwiseCurve t)
  rw [outerClockwiseCurve_periodic t]

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularBasepoint_mem_lower :
    outerClockwiseRegularBasepoint ∈ PeriodFamily.Homology.lowerBase := by
  rw [PeriodFamily.Homology.mem_regularOpen, outerClockwiseRegularBasepoint_coordinate]
  change ((1 / 2 : ℂ) - (2 : ℂ) * Complex.I) ∈ SpecialPeriods.Triangle.lowerSlitPlane
  apply Or.inr
  norm_num

private def
    PeriodFamily.Boundary.Cusp.outerClockwiseLowerBasepoint : PeriodFamily.Homology.lowerBase :=
  ⟨outerClockwiseRegularBasepoint, outerClockwiseRegularBasepoint_mem_lower⟩

private def
    PeriodFamily.Boundary.Cusp.outerClockwiseBaseLift : SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift
    outerClockwiseLowerBasepoint

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseBaseLift_project :
    SpecialPeriods.triangleRegularProject outerClockwiseBaseLift =
      outerClockwiseRegularBasepoint :=
  PeriodFamily.Homology.lowerLift_project PeriodFamily.Homology.normalizedSlitBaseLift
    outerClockwiseLowerBasepoint

private def
    PeriodFamily.Boundary.Cusp.outerClockwiseLift : C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  PeriodFamily.Boundary.realCurveLift outerClockwiseRegularCurve outerClockwiseBaseLift
    (outerClockwiseBaseLift_project.trans outerClockwiseRegularCurve_zero.symm)

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_zero :
    outerClockwiseLift 0 = outerClockwiseBaseLift :=
  PeriodFamily.Boundary.realCurveLift_zero _ _ _

@[simp]
private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_projection (t : ℝ) :
    SpecialPeriods.triangleRegularProject (outerClockwiseLift t) = outerClockwiseRegularCurve t :=
  PeriodFamily.Boundary.realCurveLift_projection _ _ _ t

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_mem_upperBase (t : ℝ)
    (ht₀ : 1 / 8 < t) (ht₁ : t < 7 / 8) :
    outerClockwiseRegularCurve t ∈ PeriodFamily.Homology.upperBase := by
  rw [PeriodFamily.Homology.mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  exact outerClockwiseCurve_mem_upperSlitPlane t ht₀ ht₁

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_mem_lowerBase (t : ℝ)
    (ht₀ : -(3 / 8) < t) (ht₁ : t < 3 / 8) :
    outerClockwiseRegularCurve t ∈ PeriodFamily.Homology.lowerBase := by
  rw [PeriodFamily.Homology.mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  exact outerClockwiseCurve_mem_lowerSlitPlane t ht₀ ht₁

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_mem_lower_piece (t : ℝ)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (ht : t ≤ 1 / 4 ∨ 3 / 4 ≤ t) :
    outerClockwiseRegularCurve t ∈ PeriodFamily.Homology.lowerBase := by
  rw [PeriodFamily.Homology.mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve t : ℂ) ∈ SpecialPeriods.Triangle.lowerSlitPlane
  have he := outerClockwiseCurve_unit (⟨t, ht₀, ht₁⟩ : unitInterval)
  rw [he]
  exact outerClockwiseCircle_mem_lowerSlitPlane _ ht

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_mem_upper_piece (t : ℝ)
    (ht₀ : 1 / 4 ≤ t) (ht₁ : t ≤ 3 / 4) :
    outerClockwiseRegularCurve t ∈ PeriodFamily.Homology.upperBase := by
  rw [PeriodFamily.Homology.mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve t : ℂ) ∈ SpecialPeriods.Triangle.upperSlitPlane
  let u : unitInterval := ⟨t, by constructor <;> linarith⟩
  have he := outerClockwiseCurve_unit u
  rw [he]
  exact outerClockwiseCircle_mem_upperSlitPlane u ht₀ ht₁

private def
    PeriodFamily.Boundary.Cusp.outerClockwiseQuarterPoint : PeriodFamily.Homology.overlapBase 0 :=
  by
  refine ⟨outerClockwiseRegularCurve (1 / 4), ?_⟩
  rw [PeriodFamily.Homology.mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve (1 / 4) : ℂ) ∈ SpecialPeriods.Triangle.overlapStrip 0
  rw [outerClockwiseCurve_quarter]
  norm_num [SpecialPeriods.Triangle.overlapStrip]

private def PeriodFamily.Boundary.Cusp.outerClockwiseThreeQuarterPoint :
    PeriodFamily.Homology.overlapBase 2 := by
  refine ⟨outerClockwiseRegularCurve (3 / 4), ?_⟩
  rw [PeriodFamily.Homology.mem_regularOpen, outerClockwiseRegularCurve_coordinate]
  change (outerClockwiseCurve (3 / 4) : ℂ) ∈ SpecialPeriods.Triangle.overlapStrip 2
  rw [outerClockwiseCurve_threeQuarters]
  norm_num [SpecialPeriods.Triangle.overlapStrip]

private theorem PeriodFamily.Boundary.Cusp.outerLift_interval_unique_mo1973_26683 {a b : ℝ}
    (s : C(Set.Icc a b, SpecialPeriods.TriangleRegularPoint))
    (hs : ∀ t, SpecialPeriods.triangleRegularProject (s t) = outerClockwiseRegularCurve t)
    (t₀ : Set.Icc a b) (h₀ : outerClockwiseLift t₀ = s t₀) (t : Set.Icc a b) :
    outerClockwiseLift t = s t := by
  let : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  exact
    congrFun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
        (outerClockwiseLift.continuous.comp continuous_subtype_val) s.continuous
        (by
          funext u
          exact (outerClockwiseLift_projection u).trans (hs u).symm)
        t₀ h₀)
      t

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_lower_initial (t : ℝ) (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1 / 4) :
    outerClockwiseLift t =
      PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift
        ⟨outerClockwiseRegularCurve t,
          outerClockwiseRegularCurve_mem_lower_piece t ht₀ (by linarith) (Or.inl ht₁)⟩ := by
  let q : C(Set.Icc (0 : ℝ) (1 / 4), PeriodFamily.Homology.lowerBase) :=
    ⟨fun s =>
      ⟨outerClockwiseRegularCurve s,
        outerClockwiseRegularCurve_mem_lower_piece s s.property.1 (by linarith [s.property.2])
          (Or.inl s.property.2)⟩,
      (outerClockwiseRegularCurve.continuous.comp continuous_subtype_val).subtype_mk _⟩
  apply
    outerLift_interval_unique_mo1973_26683
      ((PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift).comp q)
      (fun s =>
        PeriodFamily.Homology.lowerLift_project PeriodFamily.Homology.normalizedSlitBaseLift
          (q s))
      (⟨0, by constructor <;> norm_num⟩ : Set.Icc (0 : ℝ) (1 / 4)) _
      (⟨t, ht₀, ht₁⟩ : Set.Icc (0 : ℝ) (1 / 4))
  rw [outerClockwiseLift_zero]
  change
    PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift
        outerClockwiseLowerBasepoint =
      PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift
        (q ⟨0, by constructor <;> norm_num⟩)
  apply congrArg (PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift)
  apply Subtype.ext
  exact outerClockwiseRegularCurve_zero.symm

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_quarter_frame :
    outerClockwiseLift (1 / 4) =
      SpecialPeriods.triangleGenerator₁ •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 0
          outerClockwiseQuarterPoint := by
  have h := PeriodFamily.Homology.normalizedOverlapTransition_apply 0 outerClockwiseQuarterPoint
  rw [PeriodFamily.Homology.normalizedOverlapTransition_left_of_nonpos
      PeriodFamily.Boundary.normalizationOrientation_nonpos] at h
  calc
    outerClockwiseLift (1 / 4) =
        PeriodFamily.Homology.lowerLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 0
          outerClockwiseQuarterPoint :=
      outerClockwiseLift_lower_initial _ (by norm_num) le_rfl
    _ =
        SpecialPeriods.triangleGenerator₁ •
          PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 0
            outerClockwiseQuarterPoint :=
      h.symm

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_upper_middle (t : ℝ) (ht₀ : 1 / 4 ≤ t)
    (ht₁ : t ≤ 3 / 4) :
    outerClockwiseLift t =
      SpecialPeriods.triangleGenerator₁ •
        PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift
          ⟨outerClockwiseRegularCurve t, outerClockwiseRegularCurve_mem_upper_piece t ht₀ ht₁⟩ := by
  let q : C(Set.Icc (1 / 4 : ℝ) (3 / 4), PeriodFamily.Homology.upperBase) :=
    ⟨fun s =>
      ⟨outerClockwiseRegularCurve s,
        outerClockwiseRegularCurve_mem_upper_piece s s.property.1 s.property.2⟩,
      (outerClockwiseRegularCurve.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let s : C(Set.Icc (1 / 4 : ℝ) (3 / 4), SpecialPeriods.TriangleRegularPoint) :=
    ⟨fun u =>
      SpecialPeriods.triangleGenerator₁ •
        PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift (q u),
      (SpecialPeriods.triangleRegularProject_covering.continuous_const_smul
            SpecialPeriods.triangleGenerator₁).comp
        ((PeriodFamily.Homology.upperLift
              PeriodFamily.Homology.normalizedSlitBaseLift).continuous.comp
          q.continuous)⟩
  apply
    outerLift_interval_unique_mo1973_26683 s _
      (⟨1 / 4, by constructor <;> norm_num⟩ : Set.Icc (1 / 4 : ℝ) (3 / 4)) _
      (⟨t, ht₀, ht₁⟩ : Set.Icc (1 / 4 : ℝ) (3 / 4))
  · intro u
    exact
      (SpecialPeriods.triangleRegularProject_covering.map_smul
            SpecialPeriods.triangleGenerator₁).trans
        (PeriodFamily.Homology.upperLift_project PeriodFamily.Homology.normalizedSlitBaseLift
          (q u))
  · exact outerClockwiseLift_quarter_frame

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_threeQuarters_frame :
    outerClockwiseLift (3 / 4) =
      SpecialPeriods.triangleGenerator₁ •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 2
          outerClockwiseThreeQuarterPoint :=
  outerClockwiseLift_upper_middle _ (by norm_num) le_rfl

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_threeQuarters_lower_mo1973_26688 :
    outerClockwiseLift (3 / 4) =
      (SpecialPeriods.triangleGenerator₁ * SpecialPeriods.triangleGenerator₂) •
        PeriodFamily.Homology.lowerLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 2
          outerClockwiseThreeQuarterPoint := by
  have h :=
    PeriodFamily.Homology.normalizedOverlapTransition_apply 2 outerClockwiseThreeQuarterPoint
  rw [PeriodFamily.Homology.normalizedOverlapTransition_right_of_nonpos
      PeriodFamily.Boundary.normalizationOrientation_nonpos] at h
  have he :=
    congrArg
      (fun z : SpecialPeriods.TriangleRegularPoint => SpecialPeriods.triangleGenerator₂ • z) h
  simp only [smul_inv_smul] at he
  rw [outerClockwiseLift_threeQuarters_frame, SemigroupAction.mul_smul, ← he]

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_lower_final (t : ℝ) (ht₀ : 3 / 4 ≤ t)
    (ht₁ : t ≤ 1) :
    outerClockwiseLift t =
      (SpecialPeriods.triangleGenerator₁ * SpecialPeriods.triangleGenerator₂) •
        PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift
          ⟨outerClockwiseRegularCurve t,
            outerClockwiseRegularCurve_mem_lower_piece t (by linarith) ht₁ (Or.inr ht₀)⟩ := by
  let q : C(Set.Icc (3 / 4 : ℝ) 1, PeriodFamily.Homology.lowerBase) :=
    ⟨fun s =>
      ⟨outerClockwiseRegularCurve s,
        outerClockwiseRegularCurve_mem_lower_piece s (by linarith [s.property.1]) s.property.2
          (Or.inr s.property.1)⟩,
      (outerClockwiseRegularCurve.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let s : C(Set.Icc (3 / 4 : ℝ) 1, SpecialPeriods.TriangleRegularPoint) :=
    ⟨fun u =>
      (SpecialPeriods.triangleGenerator₁ * SpecialPeriods.triangleGenerator₂) •
        PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift (q u),
      (SpecialPeriods.triangleRegularProject_covering.continuous_const_smul
            (SpecialPeriods.triangleGenerator₁ * SpecialPeriods.triangleGenerator₂)).comp
        ((PeriodFamily.Homology.lowerLift
              PeriodFamily.Homology.normalizedSlitBaseLift).continuous.comp
          q.continuous)⟩
  apply
    outerLift_interval_unique_mo1973_26683 s _
      (⟨3 / 4, by constructor <;> norm_num⟩ : Set.Icc (3 / 4 : ℝ) 1) _
      (⟨t, ht₀, ht₁⟩ : Set.Icc (3 / 4 : ℝ) 1)
  · intro u
    exact
      (SpecialPeriods.triangleRegularProject_covering.map_smul
            (SpecialPeriods.triangleGenerator₁ * SpecialPeriods.triangleGenerator₂)).trans
        (PeriodFamily.Homology.lowerLift_project PeriodFamily.Homology.normalizedSlitBaseLift
          (q u))
  · exact outerClockwiseLift_threeQuarters_lower_mo1973_26688

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseLift_one :
    outerClockwiseLift 1 = SpecialPeriods.triangleCuspGenerator⁻¹ • outerClockwiseBaseLift := by
  have h := outerClockwiseLift_lower_final 1 (by norm_num) le_rfl
  have hb :
    PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift
        ⟨outerClockwiseRegularCurve 1,
          outerClockwiseRegularCurve_mem_lower_piece 1 (by norm_num) le_rfl
            (Or.inr (by norm_num))⟩ =
      outerClockwiseBaseLift := by
    apply congrArg (PeriodFamily.Homology.lowerLift PeriodFamily.Homology.normalizedSlitBaseLift)
    apply Subtype.ext
    exact outerClockwiseRegularCurve_one
  rw [hb] at h
  simpa only [SpecialPeriods.triangleCuspGenerator, inv_inv] using h

private theorem PeriodFamily.Boundary.realSLPermutation_commute_cusp_lower_left (A : SL(2, ℝ))
    (h :
      Commute (SpecialPeriods.Triangle.realSLPermutation SpecialPeriods.Triangle.cuspSL)
        (SpecialPeriods.Triangle.realSLPermutation A)) :
    A 1 0 = 0 := by
  have he :
    SpecialPeriods.Triangle.realSLPermutation (SpecialPeriods.Triangle.cuspSL * A) =
      SpecialPeriods.Triangle.realSLPermutation (A * SpecialPeriods.Triangle.cuspSL) := by
    simpa only [map_mul] using h.eq
  rcases
    (SpecialPeriods.Triangle.realSLPermutation_eq_iff (SpecialPeriods.Triangle.cuspSL * A)
          (A * SpecialPeriods.Triangle.cuspSL)).mp
      he with
    hp | hm
  · have he₀ := congrArg (fun B : SL(2, ℝ) => B 0 0) hp
    simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialPeriods.Triangle.coe_cuspSL,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, mul_one, MulZeroClass.mul_zero,
      add_zero] at he₀
    have hz : SpecialPeriods.Triangle.width * A 1 0 = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left SpecialPeriods.Triangle.width_ne_zero
  · have he₁ := congrArg (fun B : SL(2, ℝ) => B 1 0) hm
    simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialPeriods.Triangle.coe_cuspSL,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      one_mul, MulZeroClass.zero_mul, mul_one, MulZeroClass.mul_zero, zero_add, add_zero] at he₁
    linarith

private theorem PeriodFamily.Boundary.triangleCuspGenerator_commute_mem_zpowers
    (g : SpecialPeriods.TriangleGroup) (h : Commute SpecialPeriods.triangleCuspGenerator g) :
    g ∈ Subgroup.zpowers SpecialPeriods.triangleCuspGenerator := by
  obtain ⟨A, hA⟩ := SpecialPeriods.Triangle.triangleGeometricRepresentation_matrixGroup_lift g
  apply (SpecialPeriods.Triangle.triangleGeometric_upperTriangular_lift_iff g A hA).mp
  apply realSLPermutation_commute_cusp_lower_left
  rw [hA, ← SpecialPeriods.triangleGeometricRepresentation_cusp]
  exact h.map SpecialPeriods.triangleGeometricRepresentation

private theorem PeriodFamily.Boundary.triangleCuspGenerator_commute_eq_zpow
    (g : SpecialPeriods.TriangleGroup) (h : Commute SpecialPeriods.triangleCuspGenerator g) :
    ∃ k : ℤ, g = SpecialPeriods.triangleCuspGenerator ^ k := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (triangleCuspGenerator_commute_mem_zpowers g h)
  exact ⟨k, hk.symm⟩

private theorem
    PeriodFamily.Boundary.triangleHomologyEquiv_zpow_fixed (g : SpecialPeriods.TriangleGroup)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n)
    (ha : PeriodFamily.Homology.triangleHomologyEquiv g n a = a) (k : ℤ) :
    PeriodFamily.Homology.triangleHomologyEquiv (g ^ k) n a = a := by
  cases k with
  | ofNat k =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
      triangleHomologyEquiv_pow_fixed g n a ha k
  | negSucc k =>
    rw [zpow_negSucc, PeriodFamily.Homology.triangleHomologyEquiv_inv]
    apply (PeriodFamily.Homology.triangleHomologyEquiv (g ^ (k + 1)) n).injective
    rw [LinearEquiv.apply_symm_apply, triangleHomologyEquiv_pow_fixed g n a ha]

private theorem
    PeriodFamily.Boundary.cuspCentralizer_homology_fixed (g : SpecialPeriods.TriangleGroup)
    (h : Commute SpecialPeriods.triangleCuspGenerator g) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n)
    (ha :
      PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleCuspGenerator n a = a) :
    PeriodFamily.Homology.triangleHomologyEquiv g n a = a := by
  obtain ⟨k, hk⟩ := triangleCuspGenerator_commute_eq_zpow g h
  rw [hk]
  exact triangleHomologyEquiv_zpow_fixed SpecialPeriods.triangleCuspGenerator n a ha k

private theorem PeriodFamily.Boundary.cuspCentralizer_inv_homology_fixed
    (g : SpecialPeriods.TriangleGroup) (h : Commute SpecialPeriods.triangleCuspGenerator g)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n)
    (ha :
      PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleCuspGenerator n a = a) :
    PeriodFamily.Homology.triangleHomologyEquiv g⁻¹ n a = a :=
  cuspCentralizer_homology_fixed g⁻¹ h.inv_right n a ha

private theorem PeriodFamily.Boundary.Cusp.outerClockwiseRegularCurve_eq_periodic :
    (outerClockwiseRegularCurve : ℝ → SpecialPeriods.TriangleRegularQuotient) =
      PeriodFamily.BoundaryLoopSquares.loopPeriodic outerClockwiseRegularMeridian :=
  PeriodFamily.BoundaryLoopSquares.loopPeriodic_unique outerClockwiseRegularCurve
    outerClockwiseRegularCurve_periodic outerClockwiseRegularCurve_unit

@[simp]
private theorem PeriodFamily.Boundary.Cusp.nativePeriodicSquare_one (t : ℝ) :
    nativePeriodicSquare (1, t) = outerClockwiseRegularCurve t :=
  (PeriodFamily.BoundaryLoopSquares.periodicSquare_final nativeOuterSquare t).trans
    (congrFun outerClockwiseRegularCurve_eq_periodic t).symm

@[simp]
private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_final_projection (t : ℝ) :
    SpecialPeriods.triangleRegularProject (nativeLiftedSquare (1, t)) =
      outerClockwiseRegularCurve t :=
  (nativeLiftedSquare_projection 1 t).trans (nativePeriodicSquare_one t)

private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_exists_tailFrame :
    ∃ d : SpecialPeriods.TriangleGroup, nativeLiftedSquare (1, 0) = d • outerClockwiseBaseLift := by
  have he :
    SpecialPeriods.triangleRegularProject (nativeLiftedSquare (1, 0)) =
      SpecialPeriods.triangleRegularProject outerClockwiseBaseLift :=
    (nativeLiftedSquare_final_projection 0).trans
      (outerClockwiseRegularCurve_zero.trans outerClockwiseBaseLift_project.symm)
  obtain ⟨d, hd⟩ := SpecialPeriods.triangleRegularProject_covering.apply_eq_iff_mem_orbit.mp he
  exact ⟨d, hd.symm⟩

private def PeriodFamily.Boundary.Cusp.tailFrame : SpecialPeriods.TriangleGroup :=
  nativeLiftedSquare_exists_tailFrame.choose

private theorem PeriodFamily.Boundary.Cusp.tailFrame_apply :
    nativeLiftedSquare (1, 0) = tailFrame • outerClockwiseBaseLift :=
  nativeLiftedSquare_exists_tailFrame.choose_spec

private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_final (t : ℝ) :
    nativeLiftedSquare (1, t) = tailFrame • outerClockwiseLift t := by
  have hleft : Continuous (fun u : ℝ => nativeLiftedSquare (1, u)) :=
    nativeLiftedSquare.continuous.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun u : ℝ => tailFrame • outerClockwiseLift u) :=
    (SpecialPeriods.triangleRegularProject_covering.continuous_const_smul tailFrame).comp
      outerClockwiseLift.continuous
  have he :
    SpecialPeriods.triangleRegularProject ∘ (fun u : ℝ => nativeLiftedSquare (1, u)) =
      SpecialPeriods.triangleRegularProject ∘ (fun u : ℝ => tailFrame • outerClockwiseLift u) := by
    funext u
    simp only [Function.comp_apply, nativeLiftedSquare_final_projection,
      SpecialPeriods.triangleRegularProject_covering.map_smul, outerClockwiseLift_projection]
  exact
    congrFun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq hleft hright he
        0 (by simpa only [outerClockwiseLift_zero] using tailFrame_apply))
      t

private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_final_endpoint :
    nativeLiftedSquare (1, 1) =
      SpecialPeriods.triangleCuspGenerator⁻¹ • nativeLiftedSquare (1, 0) := by
  simpa only [Int.cast_one, zero_add, zpow_neg_one] using nativeLiftedSquare_translate 1 1 0

private theorem PeriodFamily.Boundary.Cusp.tailFrame_inverse_cusp_commute :
    Commute SpecialPeriods.triangleCuspGenerator⁻¹ tailFrame := by
  let := SpecialPeriods.triangleRegularProject_covering.isCancelSMul
  change
    SpecialPeriods.triangleCuspGenerator⁻¹ * tailFrame =
      tailFrame * SpecialPeriods.triangleCuspGenerator⁻¹
  apply IsCancelSMul.right_cancel _ _ outerClockwiseBaseLift
  calc
    (SpecialPeriods.triangleCuspGenerator⁻¹ * tailFrame) • outerClockwiseBaseLift =
        SpecialPeriods.triangleCuspGenerator⁻¹ • nativeLiftedSquare (1, 0) := by
      rw [SemigroupAction.mul_smul, tailFrame_apply]
    _ = nativeLiftedSquare (1, 1) := nativeLiftedSquare_final_endpoint.symm
    _ = tailFrame • outerClockwiseLift 1 := (nativeLiftedSquare_final 1)
    _ = (tailFrame * SpecialPeriods.triangleCuspGenerator⁻¹) • outerClockwiseBaseLift := by
      rw [outerClockwiseLift_one, SemigroupAction.mul_smul]

private theorem PeriodFamily.Boundary.Cusp.tailFrame_commute :
    Commute SpecialPeriods.triangleCuspGenerator tailFrame := by
  simpa only [inv_inv] using tailFrame_inverse_cusp_commute.inv_left

private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_quarter_frame :
    nativeLiftedSquare (1, 1 / 4) =
      (tailFrame * SpecialPeriods.triangleGenerator₁) •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 0
          outerClockwiseQuarterPoint := by
  rw [nativeLiftedSquare_final, outerClockwiseLift_quarter_frame, SemigroupAction.mul_smul]

private theorem PeriodFamily.Boundary.Cusp.nativeLiftedSquare_threeQuarters_frame :
    nativeLiftedSquare (1, 3 / 4) =
      (tailFrame * SpecialPeriods.triangleGenerator₁) •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 2
          outerClockwiseThreeQuarterPoint := by
  rw [nativeLiftedSquare_final, outerClockwiseLift_threeQuarters_frame, SemigroupAction.mul_smul]

private def PeriodFamily.Boundary.RefinedWang.U {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    Set (MappingTorus.Torus φ) :=
  MappingTorus.mk φ '' (Set.Ioo (1 / 8 : ℝ) (7 / 8) ×ˢ (Set.univ : Set X))

private def PeriodFamily.Boundary.RefinedWang.V {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    Set (MappingTorus.Torus φ) :=
  MappingTorus.mk φ '' (Set.Ioo (-(3 / 8 : ℝ)) (3 / 8) ×ˢ (Set.univ : Set X))

private theorem
    PeriodFamily.Boundary.RefinedWang.mem_U_iff {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    {q : MappingTorus.Torus φ} :
    q ∈ U φ ↔ ∃ (t : ℝ) (x : X), 1 / 8 < t ∧ t < 7 / 8 ∧ MappingTorus.mk φ (t, x) = q := by
  constructor
  · rintro ⟨⟨t, x⟩, ⟨ht, _⟩, hq⟩
    exact ⟨t, x, ht.1, ht.2, hq⟩
  · rintro ⟨t, x, ht, ht', hq⟩
    exact ⟨(t, x), ⟨⟨ht, ht'⟩, Set.mem_univ x⟩, hq⟩

private theorem
    PeriodFamily.Boundary.RefinedWang.mem_V_iff {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    {q : MappingTorus.Torus φ} :
    q ∈ V φ ↔ ∃ (t : ℝ) (x : X), -(3 / 8) < t ∧ t < 3 / 8 ∧ MappingTorus.mk φ (t, x) = q := by
  constructor
  · rintro ⟨⟨t, x⟩, ⟨ht, _⟩, hq⟩
    exact ⟨t, x, ht.1, ht.2, hq⟩
  · rintro ⟨t, x, ht, ht', hq⟩
    exact ⟨(t, x), ⟨⟨ht, ht'⟩, Set.mem_univ x⟩, hq⟩

private theorem
    PeriodFamily.Boundary.RefinedWang.U_open {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    IsOpen (U φ) :=
  MappingTorus.mk_open φ _ (isOpen_Ioo.prod isOpen_univ)

private theorem
    PeriodFamily.Boundary.RefinedWang.V_open {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    IsOpen (V φ) :=
  MappingTorus.mk_open φ _ (isOpen_Ioo.prod isOpen_univ)

private theorem
    PeriodFamily.Boundary.RefinedWang.U_subset {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    U φ ⊆ MappingTorus.HomologyCover.U φ := by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ := (mem_U_iff φ).mp hq
  exact MappingTorus.base_mk_ne_of_mem_Ioo φ 0 ⟨t, by constructor <;> linarith⟩ x

private theorem
    PeriodFamily.Boundary.RefinedWang.V_subset {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    V φ ⊆ MappingTorus.HomologyCover.V φ := by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ := (mem_V_iff φ).mp hq
  exact MappingTorus.base_mk_ne_of_mem_Ioo φ (-(1 / 2 : ℝ)) ⟨t, by constructor <;> linarith⟩ x

private theorem
    PeriodFamily.Boundary.RefinedWang.cover {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    U φ ∪ V φ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : q ∈ MappingTorus.HomologyCover.U φ ∪ MappingTorus.HomologyCover.V φ := by
    rw [MappingTorus.HomologyCover.cover]
    exact Set.mem_univ q
  rcases hq with hq | hq
  · let p := MappingTorus.HomologyCover.chartU φ ⟨q, hq⟩
    let t : ℝ := p.1
    have ht : 0 < t ∧ t < 1 := p.1.property
    have hp : MappingTorus.mk φ (t, p.2) = q :=
      MappingTorus.HomologyCover.chartU_representation φ ⟨q, hq⟩
    by_cases hu : 1 / 8 < t ∧ t < 7 / 8
    · exact Or.inl ((mem_U_iff φ).mpr ⟨t, p.2, hu.1, hu.2, hp⟩)
    · apply Or.inr
      apply (mem_V_iff φ).mpr
      by_cases hs : t < 3 / 8
      · exact ⟨t, p.2, by linarith, hs, hp⟩
      · have hl : 7 / 8 ≤ t := by
          by_contra hl
          apply hu
          constructor <;> linarith
        exact ⟨t - 1, φ p.2, by linarith, by linarith, (MappingTorus.mk_sub_one φ t p.2).trans hp⟩
  · let p := MappingTorus.HomologyCover.chartV φ ⟨q, hq⟩
    let t : ℝ := p.1
    have ht : -(1 / 2) < t ∧ t < 1 / 2 := p.1.property
    have hp : MappingTorus.mk φ (t, p.2) = q :=
      MappingTorus.HomologyCover.chartV_representation φ ⟨q, hq⟩
    by_cases hv : -(3 / 8) < t ∧ t < 3 / 8
    · exact Or.inr ((mem_V_iff φ).mpr ⟨t, p.2, hv.1, hv.2, hp⟩)
    · apply Or.inl
      apply (mem_U_iff φ).mpr
      by_cases hs : 1 / 8 < t
      · exact ⟨t, p.2, hs, by linarith, hp⟩
      · have hl : t ≤ -(3 / 8) := by
          by_contra hl
          apply hv
          constructor <;> linarith
        refine ⟨t + 1, φ.symm p.2, by linarith, by linarith, ?_⟩
        exact
          (MappingTorus.mk_add_one φ t (φ.symm p.2)).trans
            (by simpa only [Homeomorph.apply_symm_apply] using hp)

private def PeriodFamily.Boundary.RefinedWang.intersectionInclusion {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) :
    C(↥(U φ ∩ V φ), ↥(MappingTorus.HomologyCover.U φ ∩ MappingTorus.HomologyCover.V φ)) :=
  ContinuousMap.inclusion (Set.inter_subset_inter (U_subset φ) (V_subset φ))

private abbrev PeriodFamily.Boundary.RefinedWang.LowerInterval :=
  Set.Ioo (1 / 8 : ℝ) (3 / 8)

private abbrev PeriodFamily.Boundary.RefinedWang.UpperInterval :=
  Set.Ioo (5 / 8 : ℝ) (7 / 8)

private def PeriodFamily.Boundary.RefinedWang.lowerParam_mo1973_26734 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : LowerInterval × X) : ↥(U φ ∩ V φ) :=
  ⟨MappingTorus.mk φ ((p.1 : ℝ), p.2),
    (mem_U_iff φ).mpr ⟨p.1, p.2, p.1.property.1, by linarith [p.1.property.2], rfl⟩,
    (mem_V_iff φ).mpr ⟨p.1, p.2, by linarith [p.1.property.1], p.1.property.2, rfl⟩⟩

private def PeriodFamily.Boundary.RefinedWang.upperParam_mo1973_26735 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : UpperInterval × X) : ↥(U φ ∩ V φ) :=
  ⟨MappingTorus.mk φ ((p.1 : ℝ), p.2),
    (mem_U_iff φ).mpr ⟨p.1, p.2, by linarith [p.1.property.1], p.1.property.2, rfl⟩,
    (mem_V_iff φ).mpr
      ⟨(p.1 : ℝ) - 1, φ p.2, by linarith [p.1.property.1], by linarith [p.1.property.2],
        MappingTorus.mk_sub_one φ (p.1 : ℝ) p.2⟩⟩

private theorem PeriodFamily.Boundary.RefinedWang.lowerParam_continuous_mo1973_26736 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) : Continuous (lowerParam_mo1973_26734 φ) :=
  ((MappingTorus.mk_continuous φ).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk
    _

private theorem PeriodFamily.Boundary.RefinedWang.upperParam_continuous_mo1973_26737 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) : Continuous (upperParam_mo1973_26735 φ) :=
  ((MappingTorus.mk_continuous φ).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk
    _

private theorem PeriodFamily.Boundary.RefinedWang.lowerParam_open_mo1973_26738 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) : IsOpenMap (lowerParam_mo1973_26734 φ) :=
  ((MappingTorus.mk_open φ).comp
        (isOpen_Ioo.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk
    _

private theorem PeriodFamily.Boundary.RefinedWang.upperParam_open_mo1973_26739 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) : IsOpenMap (upperParam_mo1973_26735 φ) :=
  ((MappingTorus.mk_open φ).comp
        (isOpen_Ioo.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk
    _

private theorem PeriodFamily.Boundary.RefinedWang.lowerParam_inclusion_mo1973_26740 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : LowerInterval × X) :
    intersectionInclusion φ (lowerParam_mo1973_26734 φ p) =
      (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inl
          (⟨(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) := by
  apply Subtype.ext
  rw [MappingTorus.HomologyCover.intersectionHomeomorph_symm_inl_coe]
  rfl

private theorem PeriodFamily.Boundary.RefinedWang.upperParam_inclusion_mo1973_26741 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : UpperInterval × X) :
    intersectionInclusion φ (upperParam_mo1973_26735 φ p) =
      (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inr
          (⟨(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) := by
  apply Subtype.ext
  rw [MappingTorus.HomologyCover.intersectionHomeomorph_symm_inr_coe]
  rfl

private theorem PeriodFamily.Boundary.RefinedWang.lowerParam_oldChart_mo1973_26742 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : LowerInterval × X) :
    MappingTorus.HomologyCover.intersectionHomeomorph φ
        (intersectionInclusion φ (lowerParam_mo1973_26734 φ p)) =
      Sum.inl (⟨(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2) := by
  rw [lowerParam_inclusion_mo1973_26740, Homeomorph.apply_symm_apply]

private theorem PeriodFamily.Boundary.RefinedWang.upperParam_oldChart_mo1973_26743 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : UpperInterval × X) :
    MappingTorus.HomologyCover.intersectionHomeomorph φ
        (intersectionInclusion φ (upperParam_mo1973_26735 φ p)) =
      Sum.inr (⟨(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2) := by
  rw [upperParam_inclusion_mo1973_26741, Homeomorph.apply_symm_apply]

private def PeriodFamily.Boundary.RefinedWang.intersectionParam_mo1973_26744 {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) :
    ((LowerInterval × X) ⊕ (UpperInterval × X)) → ↥(U φ ∩ V φ) :=
  Sum.elim (lowerParam_mo1973_26734 φ) (upperParam_mo1973_26735 φ)

private theorem PeriodFamily.Boundary.RefinedWang.intersectionParam_injective_mo1973_26745
    {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    Function.Injective (intersectionParam_mo1973_26744 φ) := by
  intro p q hpq
  have he :=
    congrArg
      (fun q => MappingTorus.HomologyCover.intersectionHomeomorph φ (intersectionInclusion φ q))
      hpq
  cases p with
  | inl p =>
    cases q with
    | inl
      q =>
      simp only [intersectionParam_mo1973_26744, Sum.elim_inl, lowerParam_oldChart_mo1973_26742,
        Sum.inl.injEq, Prod.mk.injEq] at he
      have ht : (p.1 : ℝ) = (q.1 : ℝ) :=
        congrArg (fun z : Set.Ioo (0 : ℝ) (1 / 2) => (z : ℝ)) he.1
      exact congrArg Sum.inl (Prod.ext (Subtype.ext ht) he.2)
    | inr q =>
      simp only [intersectionParam_mo1973_26744, Sum.elim_inl, Sum.elim_inr,
        lowerParam_oldChart_mo1973_26742, upperParam_oldChart_mo1973_26743, Sum.inl_ne_inr] at he
  | inr p =>
    cases q with
    | inl q =>
      simp only [intersectionParam_mo1973_26744, Sum.elim_inl, Sum.elim_inr,
        lowerParam_oldChart_mo1973_26742, upperParam_oldChart_mo1973_26743, Sum.inr_ne_inl] at he
    | inr
      q =>
      simp only [intersectionParam_mo1973_26744, Sum.elim_inr, upperParam_oldChart_mo1973_26743,
        Sum.inr.injEq, Prod.mk.injEq] at he
      have ht : (p.1 : ℝ) = (q.1 : ℝ) := congrArg (fun z : Set.Ioo (1 / 2 : ℝ) 1 => (z : ℝ)) he.1
      exact congrArg Sum.inr (Prod.ext (Subtype.ext ht) he.2)

private theorem PeriodFamily.Boundary.RefinedWang.intersectionParam_surjective_mo1973_26746
    {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    Function.Surjective (intersectionParam_mo1973_26744 φ) := by
  intro q
  obtain ⟨t, x, ht, ht', hu⟩ := (mem_U_iff φ).mp q.property.1
  obtain ⟨s, y, hs, hs', hv⟩ := (mem_V_iff φ).mp q.property.2
  obtain ⟨n, hn, _⟩ := (MappingTorus.mk_eq_mk_iff φ (t, x) (s, y)).mp (hu.trans hv.symm)
  dsimp only at hn
  have hnloR : (-2 : ℝ) < (n : ℝ) := by linarith
  have hnhiR : (n : ℝ) < 1 := by linarith
  have hnlo : (-2 : ℤ) < n := by exact_mod_cast hnloR
  have hnhi : n < 1 := by exact_mod_cast hnhiR
  have hn0 : n = 0 ∨ n = -1 := by omega
  rcases hn0 with rfl | rfl
  · simp only [Int.cast_zero, add_zero] at hn
    refine ⟨Sum.inl (⟨t, ht, by linarith⟩, x), ?_⟩
    exact Subtype.ext hu
  · simp only [Int.cast_neg, Int.cast_one] at hn
    refine ⟨Sum.inr (⟨t, by linarith, ht'⟩, x), ?_⟩
    exact Subtype.ext hu

private def PeriodFamily.Boundary.RefinedWang.intersectionHomeomorph {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) : ↥(U φ ∩ V φ) ≃ₜ ((LowerInterval × X) ⊕ (UpperInterval × X)) :=
  ((Equiv.ofBijective (intersectionParam_mo1973_26744 φ)
          ⟨intersectionParam_injective_mo1973_26745 φ,
            intersectionParam_surjective_mo1973_26746 φ⟩).toHomeomorphOfContinuousOpen
      ((lowerParam_continuous_mo1973_26736 φ).sumElim (upperParam_continuous_mo1973_26737 φ))
      ((lowerParam_open_mo1973_26738 φ).sumElim (upperParam_open_mo1973_26739 φ))).symm

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomeomorph_symm_inl_coe {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : LowerInterval × X) :
    ((intersectionHomeomorph φ).symm (Sum.inl p) : MappingTorus.Torus φ) =
      MappingTorus.mk φ ((p.1 : ℝ), p.2) :=
  rfl

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomeomorph_symm_inr_coe {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : UpperInterval × X) :
    ((intersectionHomeomorph φ).symm (Sum.inr p) : MappingTorus.Torus φ) =
      MappingTorus.mk φ ((p.1 : ℝ), p.2) :=
  rfl

private theorem
    PeriodFamily.Boundary.RefinedWang.intersectionHomeomorph_symm_inl_inclusion {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : LowerInterval × X) :
    intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inl p)) =
      (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inl
          (⟨(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) :=
  lowerParam_inclusion_mo1973_26740 φ p

private theorem
    PeriodFamily.Boundary.RefinedWang.intersectionHomeomorph_symm_inr_inclusion {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : UpperInterval × X) :
    intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inr p)) =
      (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inr
          (⟨(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) :=
  upperParam_inclusion_mo1973_26741 φ p

private def
    PeriodFamily.Boundary.RefinedWang.intersectionHomotopyEquiv {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) : ↥(U φ ∩ V φ) ≃ₕ X ⊕ X := by
  letI : ContractibleSpace LowerInterval :=
    PeriodTorusHigherHomology.CircleTopology.intervalContractible (1 / 8 : ℝ) (3 / 8)
      (by norm_num)
  letI : ContractibleSpace UpperInterval :=
    PeriodTorusHigherHomology.CircleTopology.intervalContractible (5 / 8 : ℝ) (7 / 8)
      (by norm_num)
  exact
    (intersectionHomeomorph φ).toHomotopyEquiv.trans
      (PeriodTorusHigherHomology.CircleTopology.sumHomotopyEquiv
        (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv LowerInterval X)
        (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv UpperInterval X))

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomotopyEquiv_inl {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : LowerInterval × X) :
    intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inl p)) = Sum.inl p.2 := by
  change
    Sum.map (fun p : LowerInterval × X => p.2) (fun p : UpperInterval × X => p.2)
        (intersectionHomeomorph φ ((intersectionHomeomorph φ).symm (Sum.inl p))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomotopyEquiv_inr {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (p : UpperInterval × X) :
    intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inr p)) = Sum.inr p.2 := by
  change
    Sum.map (fun p : LowerInterval × X => p.2) (fun p : UpperInterval × X => p.2)
        (intersectionHomeomorph φ ((intersectionHomeomorph φ).symm (Sum.inr p))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomotopyEquiv_inclusion {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv φ).toFun.comp
        (intersectionInclusion φ) =
      (intersectionHomotopyEquiv φ).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph φ).symm.surjective q
  cases p with
  | inl
    p =>
    change
      MappingTorus.HomologyCover.intersectionHomotopyEquiv φ
          (intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inl p))) =
        intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inl p))
    rw [intersectionHomeomorph_symm_inl_inclusion,
      MappingTorus.HomologyCover.intersectionHomotopyEquiv_inl, intersectionHomotopyEquiv_inl]
  | inr
    p =>
    change
      MappingTorus.HomologyCover.intersectionHomotopyEquiv φ
          (intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inr p))) =
        intersectionHomotopyEquiv φ ((intersectionHomeomorph φ).symm (Sum.inr p))
    rw [intersectionHomeomorph_symm_inr_inclusion,
      MappingTorus.HomologyCover.intersectionHomotopyEquiv_inr, intersectionHomotopyEquiv_inr]

private def PeriodFamily.Boundary.RefinedWang.lowerComponentTime : LowerInterval :=
  ⟨1 / 4, by constructor <;> norm_num⟩

private def PeriodFamily.Boundary.RefinedWang.upperComponentTime : UpperInterval :=
  ⟨3 / 4, by constructor <;> norm_num⟩

private def PeriodFamily.Boundary.RefinedWang.lowerComponentFibre {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) : C(X, ↥(U φ ∩ V φ))
    where
  toFun x := (intersectionHomeomorph φ).symm (Sum.inl (lowerComponentTime, x))
  continuous_toFun :=
    (intersectionHomeomorph φ).symm.continuous.comp
      (continuous_inl.comp (continuous_const.prodMk continuous_id))

private def PeriodFamily.Boundary.RefinedWang.upperComponentFibre {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) : C(X, ↥(U φ ∩ V φ))
    where
  toFun x := (intersectionHomeomorph φ).symm (Sum.inr (upperComponentTime, x))
  continuous_toFun :=
    (intersectionHomeomorph φ).symm.continuous.comp
      (continuous_inr.comp (continuous_const.prodMk continuous_id))

@[simp]
private theorem
    PeriodFamily.Boundary.RefinedWang.lowerComponentFibre_coe {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (x : X) : (lowerComponentFibre φ x).val = MappingTorus.mk φ (1 / 4, x) :=
  intersectionHomeomorph_symm_inl_coe φ (lowerComponentTime, x)

@[simp]
private theorem
    PeriodFamily.Boundary.RefinedWang.upperComponentFibre_coe {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (x : X) : (upperComponentFibre φ x).val = MappingTorus.mk φ (3 / 4, x) :=
  intersectionHomeomorph_symm_inr_coe φ (upperComponentTime, x)

private theorem PeriodFamily.Boundary.RefinedWang.lowerComponentFibre_retraction {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) :
    (intersectionHomotopyEquiv φ).toFun.comp (lowerComponentFibre φ) =
      PeriodTorusHigherHomology.sumInlMap X X := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inl φ (lowerComponentTime, x)

private theorem PeriodFamily.Boundary.RefinedWang.upperComponentFibre_retraction {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) :
    (intersectionHomotopyEquiv φ).toFun.comp (upperComponentFibre φ) =
      PeriodTorusHigherHomology.sumInrMap X X := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inr φ (upperComponentTime, x)

private def
    PeriodFamily.Boundary.RefinedWang.intersectionHomologyEquiv {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (intersectionHomotopyEquiv φ) n).trans
    (PeriodTorusHigherHomology.sumHomologyEquiv X X n)

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomologyEquiv_apply {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n) :
    intersectionHomologyEquiv φ n a =
      PeriodTorusHigherHomology.sumHomologyEquiv X X n
        (SingularMayerVietoris.singularHomologyMap (intersectionHomotopyEquiv φ).toFun n a) :=
  rfl

private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomologyEquiv_inclusion {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n) :
    MappingTorusHomology.intersectionHomologyEquiv φ n
        (SingularMayerVietoris.singularHomologyMap (intersectionInclusion φ) n a) =
      intersectionHomologyEquiv φ n a := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, intersectionHomologyEquiv_apply]
  have h :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f n)
      (intersectionHomotopyEquiv_inclusion φ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact congrArg (PeriodTorusHigherHomology.sumHomologyEquiv X X n) (LinearMap.congr_fun h a)

private theorem PeriodFamily.Boundary.RefinedWang.intersectionInclusion_eq_intersectionRestriction
    {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    intersectionInclusion φ =
      SingularMayerVietoris.intersectionRestriction (ContinuousMap.id (MappingTorus.Torus φ))
        (U φ) (V φ) (MappingTorus.HomologyCover.U φ) (MappingTorus.HomologyCover.V φ) (U_subset φ)
        (V_subset φ) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

private abbrev
    PeriodFamily.Boundary.RefinedWang.mayerVietorisConnecting {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (U φ ∩ V φ : Set (MappingTorus.Torus φ)) n :=
  SingularMayerVietoris.connectingHomomorphism (U φ) (V φ) (U_open φ) (V_open φ) (cover φ) n

private theorem PeriodFamily.Boundary.RefinedWang.mayerVietorisConnecting_refinement {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (intersectionInclusion φ) n
        (mayerVietorisConnecting φ n a) =
      MappingTorusHomology.mayerVietorisConnecting φ n a := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply
      (ContinuousMap.id (MappingTorus.Torus φ)) (U φ) (V φ) (MappingTorus.HomologyCover.U φ)
      (MappingTorus.HomologyCover.V φ) (U_subset φ) (V_subset φ) (U_open φ) (V_open φ) (cover φ)
      (MappingTorus.HomologyCover.U_open φ) (MappingTorus.HomologyCover.V_open φ)
      (MappingTorus.HomologyCover.cover φ) n a
  rw [← intersectionInclusion_eq_intersectionRestriction,
    PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h
  exact h

private def PeriodFamily.Boundary.RefinedWang.boundaryCoordinates {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (intersectionHomologyEquiv φ n).toLinearMap.comp (mayerVietorisConnecting φ n)

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.boundaryCoordinates_apply {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    boundaryCoordinates φ n a = intersectionHomologyEquiv φ n (mayerVietorisConnecting φ n a) :=
  rfl

private theorem PeriodFamily.Boundary.RefinedWang.boundaryCoordinates_refinement {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    boundaryCoordinates φ n a = MappingTorusHomology.boundaryCoordinates φ n a := by
  rw [boundaryCoordinates_apply, ← intersectionHomologyEquiv_inclusion,
    mayerVietorisConnecting_refinement]
  rfl

private theorem PeriodFamily.Boundary.RefinedWang.boundaryCoordinates_eq_antidiagonal {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    boundaryCoordinates φ n a =
      (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) :=
  (boundaryCoordinates_refinement φ n a).trans
    (MappingTorusHomology.boundaryCoordinates_eq_antidiagonal φ n a)

private theorem
    PeriodFamily.Boundary.RefinedWang.mappingTorusConnecting_eq_marked_boundary {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    mayerVietorisConnecting φ n a =
      (intersectionHomologyEquiv φ n).symm
        (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  apply (intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply]
  exact boundaryCoordinates_eq_antidiagonal φ n a

private theorem PeriodFamily.Boundary.RefinedWang.lowerComponentFibre_homology {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionHomologyEquiv φ n
        (SingularMayerVietoris.singularHomologyMap (lowerComponentFibre φ) n a) =
      (a, 0) := by
  rw [intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, lowerComponentFibre_retraction,
    PeriodTorusHigherHomology.sumHomologyEquiv_inl]

private theorem PeriodFamily.Boundary.RefinedWang.upperComponentFibre_homology {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionHomologyEquiv φ n
        (SingularMayerVietoris.singularHomologyMap (upperComponentFibre φ) n a) =
      (0, a) := by
  rw [intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, upperComponentFibre_retraction,
    PeriodTorusHigherHomology.sumHomologyEquiv_inr]

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomologyEquiv_symm_lower {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    (intersectionHomologyEquiv φ n).symm (a, 0) =
      SingularMayerVietoris.singularHomologyMap (lowerComponentFibre φ) n a := by
  apply (intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, lowerComponentFibre_homology]

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionHomologyEquiv_symm_upper {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    (intersectionHomologyEquiv φ n).symm (0, a) =
      SingularMayerVietoris.singularHomologyMap (upperComponentFibre φ) n a := by
  apply (intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, upperComponentFibre_homology]

private def PeriodFamily.Boundary.RefinedWang.intersectionMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D)) :
    C((U φ ∩ V φ : Set (MappingTorus.Torus φ)), PeriodFamily.Homology.familyIntersection D) :=
  SingularMayerVietoris.intersectionRestriction F (U φ) (V φ)
    (PeriodFamily.Homology.upperFamily D) (PeriodFamily.Homology.lowerFamily D) hU hV

private theorem PeriodFamily.Boundary.RefinedWang.markedConnecting_naturality {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    PeriodFamily.Homology.familyMarkedConnecting D b n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n
          (mayerVietorisConnecting φ n a)) := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply F (U φ) (V φ)
      (PeriodFamily.Homology.upperFamily D) (PeriodFamily.Homology.lowerFamily D) hU hV (U_open φ)
      (V_open φ) (cover φ) (PeriodFamily.Homology.upperFamily D).isOpen
      (PeriodFamily.Homology.lowerFamily D).isOpen
      (PeriodFamily.Homology.upperFamily_union_lowerFamily D) n a
  exact (congrArg (PeriodFamily.Homology.intersectionHomologyEquiv D b n) h).symm

private def PeriodFamily.Boundary.RefinedWang.intersectionComparison {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology X n ×
        SingularMayerVietoris.SingularHomology X n) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n)) :=
  (PeriodFamily.Homology.intersectionHomologyEquiv D b n).toLinearMap.comp
    ((SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n).comp
      (intersectionHomologyEquiv φ n).symm.toLinearMap)

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.intersectionComparison_apply {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n a =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n
          ((intersectionHomologyEquiv φ n).symm a)) :=
  rfl

private theorem PeriodFamily.Boundary.RefinedWang.markedConnecting_wangBoundary {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    PeriodFamily.Homology.familyMarkedConnecting D b n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      intersectionComparison D φ F hU hV b n
        (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  refine (markedConnecting_naturality D φ F hU hV b n a).trans ?_
  exact
    congrArg
      (fun z =>
        PeriodFamily.Homology.intersectionHomologyEquiv D b n
          (SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n z))
      (mappingTorusConnecting_eq_marked_boundary φ n a)

private theorem PeriodFamily.Boundary.RefinedWang.intersectionComparison_antidiagonal {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (-a, a) =
      -intersectionComparison D φ F hU hV b n (a, 0) +
        intersectionComparison D φ F hU hV b n (0, a) := by
  have h : (-a, a) = -(a, (0 : SingularMayerVietoris.SingularHomology X n)) + (0, a) := by
    ext <;> simp
  rw [h, map_add, map_neg]

private def PeriodFamily.Boundary.RefinedWang.lowerColumnMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D)) :
    C(X, PeriodFamily.Homology.familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (lowerComponentFibre φ)

private def PeriodFamily.Boundary.RefinedWang.upperColumnMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D)) :
    C(X, PeriodFamily.Homology.familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (upperComponentFibre φ)

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.lowerColumnMap_coe {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D)) (x : X) :
    (lowerColumnMap D φ F hU hV x).val = F (MappingTorus.mk φ (1 / 4, x)) := by
  change F (lowerComponentFibre φ x).val = _
  rw [lowerComponentFibre_coe]

@[simp]
private theorem PeriodFamily.Boundary.RefinedWang.upperColumnMap_coe {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D)) (x : X) :
    (upperColumnMap D φ F hU hV x).val = F (MappingTorus.mk φ (3 / 4, x)) := by
  change F (upperComponentFibre φ x).val = _
  rw [upperComponentFibre_coe]

private theorem PeriodFamily.Boundary.RefinedWang.intersectionComparison_lowerColumn {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (a, 0) =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (lowerColumnMap D φ F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_lower]
  exact
    congrArg (PeriodFamily.Homology.intersectionHomologyEquiv D b n)
      (LinearMap.congr_fun
          (PeriodTorusHigherHomology.singularHomologyMap_comp (lowerComponentFibre φ)
            (intersectionMap D φ F hU hV) n)
          a).symm

private theorem PeriodFamily.Boundary.RefinedWang.intersectionComparison_upperColumn {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (0, a) =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (upperColumnMap D φ F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_upper]
  exact
    congrArg (PeriodFamily.Homology.intersectionHomologyEquiv D b n)
      (LinearMap.congr_fun
          (PeriodTorusHigherHomology.singularHomologyMap_comp (upperComponentFibre φ)
            (intersectionMap D φ F hU hV) n)
          a).symm

private theorem PeriodFamily.Boundary.RefinedWang.markedConnecting_quarterColumns {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    PeriodFamily.Homology.familyMarkedConnecting D b n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      -PeriodFamily.Homology.intersectionHomologyEquiv D b n
            (SingularMayerVietoris.singularHomologyMap (lowerColumnMap D φ F hU hV) n
              (MappingTorusHomology.wangBoundary φ n a)) +
        PeriodFamily.Homology.intersectionHomologyEquiv D b n
          (SingularMayerVietoris.singularHomologyMap (upperColumnMap D φ F hU hV) n
            (MappingTorusHomology.wangBoundary φ n a)) := by
  rw [markedConnecting_wangBoundary D φ F hU hV b n a, intersectionComparison_antidiagonal,
    intersectionComparison_lowerColumn, intersectionComparison_upperColumn]

private theorem PeriodFamily.Boundary.RefinedWang.sourceKernelProjection_quarterColumns {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (φ : X ≃ₜ X) (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (V φ) (PeriodFamily.Homology.lowerFamily D)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection D n
          (SingularMayerVietoris.singularHomologyMap F (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      PeriodFamily.Homology.normalizedSourceDomainEquiv n
        (-PeriodFamily.Homology.intersectionHomologyEquiv D
                PeriodFamily.Homology.normalizedSlitBaseLift n
                (SingularMayerVietoris.singularHomologyMap (lowerColumnMap D φ F hU hV) n
                  (MappingTorusHomology.wangBoundary φ n a)) +
            PeriodFamily.Homology.intersectionHomologyEquiv D
              PeriodFamily.Homology.normalizedSlitBaseLift n
              (SingularMayerVietoris.singularHomologyMap (upperColumnMap D φ F hU hV) n
                (MappingTorusHomology.wangBoundary φ n a))).2 := by
  exact
    congrArg
      (fun z :
          SingularMayerVietoris.SingularHomology RealTorus₄ n ×
            (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
              SingularMayerVietoris.SingularHomology RealTorus₄ n) =>
        PeriodFamily.Homology.normalizedSourceDomainEquiv n z.2)
      (markedConnecting_quarterColumns D φ F hU hV PeriodFamily.Homology.normalizedSlitBaseLift n
        a)

private theorem PeriodFamily.Boundary.Cusp.normalizedBoundaryMap_outer_projection (t : ℝ)
    (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection
        (normalizedBoundaryMap
          (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x))) =
      outerClockwiseRegularCurve t := by
  rw [normalizedBoundaryMap_projection_mk, nativeLiftedSquare_final_projection]

private theorem PeriodFamily.Boundary.Cusp.normalizedBoundaryMap_upper :
    Set.MapsTo normalizedBoundaryMap
      (PeriodFamily.Boundary.RefinedWang.U ThreefoldOverlapMappingTorus.Cusp.monodromy)
      (PeriodFamily.Homology.upperFamily ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData) :=
  by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ :=
    (PeriodFamily.Boundary.RefinedWang.mem_U_iff ThreefoldOverlapMappingTorus.Cusp.monodromy).mp
      hq
  change
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection
        (normalizedBoundaryMap
          (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x))) ∈
      PeriodFamily.Homology.upperBase
  rw [normalizedBoundaryMap_outer_projection]
  exact outerClockwiseRegularCurve_mem_upperBase t ht ht'

private theorem PeriodFamily.Boundary.Cusp.normalizedBoundaryMap_lower :
    Set.MapsTo normalizedBoundaryMap
      (PeriodFamily.Boundary.RefinedWang.V ThreefoldOverlapMappingTorus.Cusp.monodromy)
      (PeriodFamily.Homology.lowerFamily ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData) :=
  by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ :=
    (PeriodFamily.Boundary.RefinedWang.mem_V_iff ThreefoldOverlapMappingTorus.Cusp.monodromy).mp
      hq
  change
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection
        (normalizedBoundaryMap
          (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x))) ∈
      PeriodFamily.Homology.lowerBase
  rw [normalizedBoundaryMap_outer_projection]
  exact outerClockwiseRegularCurve_mem_lowerBase t ht ht'

private def PeriodFamily.Boundary.Cusp.lowerColumn :
    C(RealTorus₄,
      PeriodFamily.Homology.familyIntersection
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData) :=
  PeriodFamily.Boundary.RefinedWang.lowerColumnMap
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
    ThreefoldOverlapMappingTorus.Cusp.monodromy normalizedBoundaryMap normalizedBoundaryMap_upper
    normalizedBoundaryMap_lower

private def PeriodFamily.Boundary.Cusp.upperColumn :
    C(RealTorus₄,
      PeriodFamily.Homology.familyIntersection
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData) :=
  PeriodFamily.Boundary.RefinedWang.upperColumnMap
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
    ThreefoldOverlapMappingTorus.Cusp.monodromy normalizedBoundaryMap normalizedBoundaryMap_upper
    normalizedBoundaryMap_lower

private theorem PeriodFamily.Boundary.Cusp.lowerColumn_coe (x : RealTorus₄) :
    (lowerColumn x).val =
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
        (nativeLiftedSquare (1, 1 / 4), x) := by
  rw [lowerColumn, PeriodFamily.Boundary.RefinedWang.lowerColumnMap_coe, normalizedBoundaryMap_mk]

private theorem PeriodFamily.Boundary.Cusp.upperColumn_coe (x : RealTorus₄) :
    (upperColumn x).val =
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.quotient
        (nativeLiftedSquare (1, 3 / 4), x) := by
  rw [upperColumn, PeriodFamily.Boundary.RefinedWang.upperColumnMap_coe, normalizedBoundaryMap_mk]

private theorem PeriodFamily.Boundary.Cusp.lowerColumn_mem (x : RealTorus₄) :
    lowerColumn x ∈
      PeriodFamily.Homology.intersectionPiece
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData 1 := by
  change
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection (lowerColumn x).val ∈
      PeriodFamily.Homology.overlapBase (PeriodFamily.Homology.intersectionIndex 1)
  rw [lowerColumn_coe, ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection_quotient]
  change
    SpecialPeriods.triangleRegularProject (nativeLiftedSquare (1, 1 / 4)) ∈
      PeriodFamily.Homology.overlapBase 0
  rw [nativeLiftedSquare_final_projection]
  exact outerClockwiseQuarterPoint.property

private theorem PeriodFamily.Boundary.Cusp.upperColumn_mem (x : RealTorus₄) :
    upperColumn x ∈
      PeriodFamily.Homology.intersectionPiece
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData 2 := by
  change
    ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection (upperColumn x).val ∈
      PeriodFamily.Homology.overlapBase (PeriodFamily.Homology.intersectionIndex 2)
  rw [upperColumn_coe, ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.projection_quotient]
  change
    SpecialPeriods.triangleRegularProject (nativeLiftedSquare (1, 3 / 4)) ∈
      PeriodFamily.Homology.overlapBase 2
  rw [nativeLiftedSquare_final_projection]
  exact outerClockwiseThreeQuarterPoint.property

private theorem PeriodFamily.Boundary.Cusp.monodromyHomology_triangle (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.Cusp.monodromy : C(RealTorus₄, RealTorus₄)) n =
      (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleCuspGenerator
          n).toLinearMap := by
  have hm :
    ThreefoldOverlapMappingTorus.Cusp.monodromy =
      SpecialPeriods.triangleTorusHomeomorph SpecialPeriods.triangleCuspGenerator := by
    simpa only [zpow_one] using (SpecialPeriods.triangleTorusHomeomorph_cusp_zpow (1 : ℤ)).symm
  rw [hm]
  rfl

private theorem PeriodFamily.Boundary.Cusp.wangBoundary_generator_fixed (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleCuspGenerator n
        (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a) =
      MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a := by
  have hb :
    MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a ∈
      LinearMap.ker
        (MappingTorusHomology.wangDifference ThreefoldOverlapMappingTorus.Cusp.monodromy n) := by
    rw [← MappingTorusHomology.wangBoundary_range]
    exact ⟨a, rfl⟩
  have he := LinearMap.mem_ker.mp hb
  change
    MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a -
        SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.Cusp.monodromy : C(RealTorus₄, RealTorus₄)) n
          (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a) =
      0 at he
  rw [monodromyHomology_triangle] at he
  exact (sub_eq_zero.mp he).symm

private theorem PeriodFamily.Boundary.Cusp.wangBoundary_inverse_word (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    (PeriodFamily.Homology.generatorHomologyEquiv Bool.true n).symm
        (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a)) =
      MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a := by
  have he := wangBoundary_generator_fixed n a
  rw [SpecialPeriods.triangleCuspGenerator, mul_inv_rev,
    PeriodFamily.Boundary.triangleHomologyEquiv_mul_apply,
    PeriodFamily.Homology.triangleHomologyEquiv_inv] at he
  exact he

private theorem PeriodFamily.Boundary.Cusp.commutingFrame_inv_wangBoundary
    (g : SpecialPeriods.TriangleGroup) (hg : Commute SpecialPeriods.triangleCuspGenerator g)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv g⁻¹ n
        (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a) =
      MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a :=
  PeriodFamily.Boundary.cuspCentralizer_inv_homology_fixed g hg n _
    (wangBoundary_generator_fixed n a)

private theorem PeriodFamily.Boundary.Cusp.commutingColumnFrame_inv_wangBoundary
    (g : SpecialPeriods.TriangleGroup) (hg : Commute SpecialPeriods.triangleCuspGenerator g)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv (g * SpecialPeriods.triangleGenerator₁)⁻¹ n
        (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a) =
      PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
        (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a) := by
  rw [mul_inv_rev, PeriodFamily.Boundary.triangleHomologyEquiv_mul_apply,
    commutingFrame_inv_wangBoundary g hg]

private def PeriodFamily.Boundary.intersectionMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D)) :
    C((MappingTorus.HomologyCover.U φ ∩ MappingTorus.HomologyCover.V φ :
        Set (MappingTorus.Torus φ)),
      PeriodFamily.Homology.familyIntersection D) :=
  SingularMayerVietoris.intersectionRestriction F (MappingTorus.HomologyCover.U φ)
    (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.upperFamily D)
    (PeriodFamily.Homology.lowerFamily D) hU hV

private theorem PeriodFamily.Boundary.markedConnecting_naturality {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    PeriodFamily.Homology.familyMarkedConnecting D b n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n
          (MappingTorusHomology.mayerVietorisConnecting φ n a)) := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply F
      (MappingTorus.HomologyCover.U φ) (MappingTorus.HomologyCover.V φ)
      (PeriodFamily.Homology.upperFamily D) (PeriodFamily.Homology.lowerFamily D) hU hV
      (MappingTorus.HomologyCover.U_open φ) (MappingTorus.HomologyCover.V_open φ)
      (MappingTorus.HomologyCover.cover φ) (PeriodFamily.Homology.upperFamily D).isOpen
      (PeriodFamily.Homology.lowerFamily D).isOpen
      (PeriodFamily.Homology.upperFamily_union_lowerFamily D) n a
  exact (congrArg (PeriodFamily.Homology.intersectionHomologyEquiv D b n) h).symm

private def PeriodFamily.Boundary.intersectionComparison {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology X n ×
        SingularMayerVietoris.SingularHomology X n) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n)) :=
  (PeriodFamily.Homology.intersectionHomologyEquiv D b n).toLinearMap.comp
    ((SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n).comp
      (MappingTorusHomology.intersectionHomologyEquiv φ n).symm.toLinearMap)

@[simp]
private theorem PeriodFamily.Boundary.intersectionComparison_apply {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n a =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n
          ((MappingTorusHomology.intersectionHomologyEquiv φ n).symm a)) :=
  rfl

private theorem PeriodFamily.Boundary.mappingTorusConnecting_eq_marked_boundary {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    MappingTorusHomology.mayerVietorisConnecting φ n a =
      (MappingTorusHomology.intersectionHomologyEquiv φ n).symm
        (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  apply (MappingTorusHomology.intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply]
  exact MappingTorusHomology.boundaryCoordinates_eq_antidiagonal φ n a

private theorem PeriodFamily.Boundary.markedConnecting_wangBoundary {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    PeriodFamily.Homology.familyMarkedConnecting D b n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      intersectionComparison D φ F hU hV b n
        (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  refine (markedConnecting_naturality D φ F hU hV b n a).trans ?_
  exact
    congrArg
      (fun z =>
        PeriodFamily.Homology.intersectionHomologyEquiv D b n
          (SingularMayerVietoris.singularHomologyMap (intersectionMap D φ F hU hV) n z))
      (mappingTorusConnecting_eq_marked_boundary φ n a)

private theorem
    PeriodFamily.Boundary.sourceKernelProjection_wangBoundary {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection D n
          (SingularMayerVietoris.singularHomologyMap F (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      PeriodFamily.Homology.normalizedSourceDomainEquiv n
        (intersectionComparison D φ F hU hV PeriodFamily.Homology.normalizedSlitBaseLift n
            (-MappingTorusHomology.wangBoundary φ n a,
              MappingTorusHomology.wangBoundary φ n a)).2 := by
  exact
    congrArg
      (fun z :
          SingularMayerVietoris.SingularHomology RealTorus₄ n ×
            (SingularMayerVietoris.SingularHomology RealTorus₄ n ×
              SingularMayerVietoris.SingularHomology RealTorus₄ n) =>
        PeriodFamily.Homology.normalizedSourceDomainEquiv n z.2)
      (markedConnecting_wangBoundary D φ F hU hV PeriodFamily.Homology.normalizedSlitBaseLift n a)

private theorem
    PeriodFamily.Boundary.intersectionComparison_antidiagonal {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (-a, a) =
      -intersectionComparison D φ F hU hV b n (a, 0) +
        intersectionComparison D φ F hU hV b n (0, a) := by
  have h : (-a, a) = -(a, (0 : SingularMayerVietoris.SingularHomology X n)) + (0, a) := by
    ext <;> simp
  rw [h, map_add, map_neg]

private def PeriodFamily.Boundary.lowerComponentTime : Set.Ioo (0 : ℝ) (1 / 2) :=
  ⟨1 / 4, by constructor <;> norm_num⟩

private def PeriodFamily.Boundary.upperComponentTime : Set.Ioo (1 / 2 : ℝ) 1 :=
  ⟨3 / 4, by constructor <;> norm_num⟩

private def PeriodFamily.Boundary.lowerComponentFibre {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    C(X,
      (MappingTorus.HomologyCover.U φ ∩ MappingTorus.HomologyCover.V φ :
        Set (MappingTorus.Torus φ)))
    where
  toFun
    x :=
    (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm (Sum.inl (lowerComponentTime, x))
  continuous_toFun :=
    (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm.continuous.comp
      (continuous_inl.comp (continuous_const.prodMk continuous_id))

private def PeriodFamily.Boundary.upperComponentFibre {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X) :
    C(X,
      (MappingTorus.HomologyCover.U φ ∩ MappingTorus.HomologyCover.V φ :
        Set (MappingTorus.Torus φ)))
    where
  toFun
    x :=
    (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm (Sum.inr (upperComponentTime, x))
  continuous_toFun :=
    (MappingTorus.HomologyCover.intersectionHomeomorph φ).symm.continuous.comp
      (continuous_inr.comp (continuous_const.prodMk continuous_id))

@[simp]
private theorem
    PeriodFamily.Boundary.lowerComponentFibre_coe {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    (x : X) : (lowerComponentFibre φ x).val = MappingTorus.mk φ (1 / 4, x) :=
  MappingTorus.HomologyCover.intersectionHomeomorph_symm_inl_coe φ (lowerComponentTime, x)

@[simp]
private theorem
    PeriodFamily.Boundary.upperComponentFibre_coe {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    (x : X) : (upperComponentFibre φ x).val = MappingTorus.mk φ (3 / 4, x) :=
  MappingTorus.HomologyCover.intersectionHomeomorph_symm_inr_coe φ (upperComponentTime, x)

private theorem PeriodFamily.Boundary.lowerComponentFibre_retraction {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv φ).toFun.comp (lowerComponentFibre φ) =
      PeriodTorusHigherHomology.sumInlMap X X := by
  apply ContinuousMap.ext
  intro x
  exact MappingTorus.HomologyCover.intersectionHomotopyEquiv_inl φ (lowerComponentTime, x)

private theorem PeriodFamily.Boundary.upperComponentFibre_retraction {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) :
    (MappingTorus.HomologyCover.intersectionHomotopyEquiv φ).toFun.comp (upperComponentFibre φ) =
      PeriodTorusHigherHomology.sumInrMap X X := by
  apply ContinuousMap.ext
  intro x
  exact MappingTorus.HomologyCover.intersectionHomotopyEquiv_inr φ (upperComponentTime, x)

private theorem PeriodFamily.Boundary.lowerComponentFibre_homology {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv φ n
        (SingularMayerVietoris.singularHomologyMap (lowerComponentFibre φ) n a) =
      (a, 0) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, lowerComponentFibre_retraction,
    PeriodTorusHigherHomology.sumHomologyEquiv_inl]

private theorem PeriodFamily.Boundary.upperComponentFibre_homology {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv φ n
        (SingularMayerVietoris.singularHomologyMap (upperComponentFibre φ) n a) =
      (0, a) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, upperComponentFibre_retraction,
    PeriodTorusHigherHomology.sumHomologyEquiv_inr]

@[simp]
private theorem
    PeriodFamily.Boundary.intersectionHomologyEquiv_symm_lower {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    (MappingTorusHomology.intersectionHomologyEquiv φ n).symm (a, 0) =
      SingularMayerVietoris.singularHomologyMap (lowerComponentFibre φ) n a := by
  apply (MappingTorusHomology.intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, lowerComponentFibre_homology]

@[simp]
private theorem
    PeriodFamily.Boundary.intersectionHomologyEquiv_symm_upper {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    (MappingTorusHomology.intersectionHomologyEquiv φ n).symm (0, a) =
      SingularMayerVietoris.singularHomologyMap (upperComponentFibre φ) n a := by
  apply (MappingTorusHomology.intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, upperComponentFibre_homology]

private def PeriodFamily.Boundary.lowerColumnMap {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D)) :
    C(X, PeriodFamily.Homology.familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (lowerComponentFibre φ)

private def PeriodFamily.Boundary.upperColumnMap {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D)) :
    C(X, PeriodFamily.Homology.familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (upperComponentFibre φ)

@[simp]
private theorem
    PeriodFamily.Boundary.lowerColumnMap_coe {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (x : X) : (lowerColumnMap φ D F hU hV x).val = F (MappingTorus.mk φ (1 / 4, x)) := by
  change F (lowerComponentFibre φ x).val = _
  rw [lowerComponentFibre_coe]

@[simp]
private theorem
    PeriodFamily.Boundary.upperColumnMap_coe {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (x : X) : (upperColumnMap φ D F hU hV x).val = F (MappingTorus.mk φ (3 / 4, x)) := by
  change F (upperComponentFibre φ x).val = _
  rw [upperComponentFibre_coe]

private theorem
    PeriodFamily.Boundary.intersectionComparison_lowerColumn {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (a, 0) =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (lowerColumnMap φ D F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_lower]
  exact
    congrArg (PeriodFamily.Homology.intersectionHomologyEquiv D b n)
      (LinearMap.congr_fun
          (PeriodTorusHigherHomology.singularHomologyMap_comp (lowerComponentFibre φ)
            (intersectionMap D φ F hU hV) n)
          a).symm

private theorem
    PeriodFamily.Boundary.intersectionComparison_upperColumn {X : Type} [TopologicalSpace X]
    (φ : X ≃ₜ X) (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (F : C(MappingTorus.Torus φ, D.Space))
    (hU : Set.MapsTo F (MappingTorus.HomologyCover.U φ) (PeriodFamily.Homology.upperFamily D))
    (hV : Set.MapsTo F (MappingTorus.HomologyCover.V φ) (PeriodFamily.Homology.lowerFamily D))
    (b : PeriodFamily.Homology.SlitBaseLift) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (0, a) =
      PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap (upperColumnMap φ D F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_upper]
  exact
    congrArg (PeriodFamily.Homology.intersectionHomologyEquiv D b n)
      (LinearMap.congr_fun
          (PeriodTorusHigherHomology.singularHomologyMap_comp (upperComponentFibre φ)
            (intersectionMap D φ F hU hV) n)
          a).symm

private def PeriodFamily.Boundary.componentCoordinates {H : Type*} [Zero H] (i : Fin 3) (a : H) :
    H × (H × H) :=
  ![(a, (0, 0)), (0, (a, 0)), (0, (0, a))] i

@[simp]
private theorem PeriodFamily.Boundary.componentCoordinates_one {H : Type*} [Zero H] (a : H) :
    componentCoordinates 1 a = (0, (a, 0)) :=
  rfl

@[simp]
private theorem PeriodFamily.Boundary.componentCoordinates_two {H : Type*} [Zero H] (a : H) :
    componentCoordinates 2 a = (0, (0, a)) :=
  rfl

private def PeriodFamily.Boundary.pieceFibreProjection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift) (i : Fin 3) :
    C(PeriodFamily.Homology.intersectionPiece D i, RealTorus₄) :=
  (PeriodFamily.Homology.overlapHomotopyEquiv D b
        (PeriodFamily.Homology.intersectionIndex i)).toFun.comp
    (PeriodFamily.Homology.intersectionPieceHomeomorph D i : C(_, _))

private theorem PeriodFamily.Boundary.pieceFibreProjection_homology
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift) (i : Fin 3) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (pieceFibreProjection D b i) n =
      (PeriodFamily.Homology.intersectionPieceHomologyEquiv D b i n).toLinearMap := by
  rw [pieceFibreProjection, PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private def PeriodFamily.Boundary.componentLift {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i) :
    C(X, PeriodFamily.Homology.intersectionPiece D i) :=
  ⟨fun x => ⟨C x, hC x⟩, C.continuous.subtype_mk _⟩

private theorem PeriodFamily.Boundary.componentLift_factor {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i) :
    (PeriodFamily.Homology.openPartitionInclusion (PeriodFamily.Homology.intersectionPiece D)
            i).comp
        (componentLift D C i hC) =
      C := by
  apply ContinuousMap.ext
  intro x
  rfl

private def PeriodFamily.Boundary.componentFibreMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i) : C(X, RealTorus₄) :=
  (pieceFibreProjection D b i).comp (componentLift D C i hC)

@[simp]
private theorem PeriodFamily.Boundary.componentFibreMap_apply {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i) (x : X) :
    componentFibreMap D b C i hC x =
      (PeriodFamily.Homology.overlapChart D b (PeriodFamily.Homology.intersectionIndex i)
          ⟨(C x).val, hC x⟩).2 :=
  rfl

private theorem PeriodFamily.Boundary.componentFibreMap_homology {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (componentFibreMap D b C i hC) n a =
      PeriodFamily.Homology.intersectionPieceHomologyEquiv D b i n
        (SingularMayerVietoris.singularHomologyMap (componentLift D C i hC) n a) := by
  rw [componentFibreMap, PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    pieceFibreProjection_homology]
  rfl

private theorem
    PeriodFamily.Boundary.intersectionHomology_componentMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap C n a) =
      componentCoordinates i
        (SingularMayerVietoris.singularHomologyMap (componentFibreMap D b C i hC) n a) := by
  have hfactor :
    SingularMayerVietoris.singularHomologyMap C n a =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.openPartitionInclusion (PeriodFamily.Homology.intersectionPiece D)
          i)
        n (SingularMayerVietoris.singularHomologyMap (componentLift D C i hC) n a) := by
    rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
      componentLift_factor]
  rw [hfactor, componentFibreMap_homology]
  fin_cases i
  · exact PeriodFamily.Homology.intersectionHomologyEquiv_inclusion_middle D b n _
  · exact PeriodFamily.Homology.intersectionHomologyEquiv_inclusion_left D b n _
  · exact PeriodFamily.Homology.intersectionHomologyEquiv_inclusion_right D b n _

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.componentFibreMap_eq_deck_comp {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i)
    (q : PeriodFamily.Homology.overlapBase (PeriodFamily.Homology.intersectionIndex i))
    (z : SpecialPeriods.TriangleRegularPoint) (g : SpecialPeriods.TriangleGroup)
    (hz :
      z =
        g •
          PeriodFamily.Homology.upperLiftOnOverlap b (PeriodFamily.Homology.intersectionIndex i)
            q)
    (F : C(X, RealTorus₄)) (hF : ∀ x, (C x).val = D.quotient (z, F x)) :
    componentFibreMap D b C i hC =
      (SpecialPeriods.triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)).comp F := by
  apply ContinuousMap.ext
  intro x
  rw [componentFibreMap_apply]
  have he :
    (⟨(C x).val, hC x⟩ :
        PeriodFamily.Homology.overlapFamily D (PeriodFamily.Homology.intersectionIndex i)) =
      (PeriodFamily.Homology.overlapChart D b (PeriodFamily.Homology.intersectionIndex i)).symm
        (q, g⁻¹ • F x) := by
    apply Subtype.ext
    rw [PeriodFamily.Homology.overlapChart_symm_coe, hF, hz]
    have h :=
      D.quotient_smul g
        (PeriodFamily.Homology.upperLiftOnOverlap b (PeriodFamily.Homology.intersectionIndex i) q,
          g⁻¹ • F x)
    change
      D.quotient
          (g •
              PeriodFamily.Homology.upperLiftOnOverlap b
                (PeriodFamily.Homology.intersectionIndex i) q,
            g • (g⁻¹ • F x)) =
        D.quotient
          (PeriodFamily.Homology.upperLiftOnOverlap b (PeriodFamily.Homology.intersectionIndex i)
              q,
            g⁻¹ • F x) at h
    simpa only [smul_inv_smul] using h
  rw [he, Homeomorph.apply_symm_apply]
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.componentFibreMap_homology_deck_comp {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i)
    (q : PeriodFamily.Homology.overlapBase (PeriodFamily.Homology.intersectionIndex i))
    (z : SpecialPeriods.TriangleRegularPoint) (g : SpecialPeriods.TriangleGroup)
    (hz :
      z =
        g •
          PeriodFamily.Homology.upperLiftOnOverlap b (PeriodFamily.Homology.intersectionIndex i)
            q)
    (F : C(X, RealTorus₄)) (hF : ∀ x, (C x).val = D.quotient (z, F x)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (componentFibreMap D b C i hC) n =
      (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)) n).comp
        (SingularMayerVietoris.singularHomologyMap F n) := by
  rw [componentFibreMap_eq_deck_comp D b C i hC q z g hz F hF,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.componentFibreMap_homology_affine {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i)
    (q : PeriodFamily.Homology.overlapBase (PeriodFamily.Homology.intersectionIndex i))
    (z : SpecialPeriods.TriangleRegularPoint) (g : SpecialPeriods.TriangleGroup)
    (hz :
      z =
        g •
          PeriodFamily.Homology.upperLiftOnOverlap b (PeriodFamily.Homology.intersectionIndex i)
            q)
    (F : C(X, RealTorus₄)) (v : RealTorus₄) (hF : ∀ x, (C x).val = D.quotient (z, F x + v))
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (componentFibreMap D b C i hC) n =
      (SingularMayerVietoris.singularHomologyMap
            (SpecialPeriods.triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)) n).comp
        (SingularMayerVietoris.singularHomologyMap F n) := by
  rw [componentFibreMap_homology_deck_comp D b C i hC q z g hz
      ((PeriodTorusHigherHomology.rightTranslation v).comp F) hF,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.rightTranslation_singularHomologyMap, LinearMap.id_comp]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.intersectionHomology_component_affine {X : Type}
    [TopologicalSpace X] (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (b : PeriodFamily.Homology.SlitBaseLift)
    (C : C(X, PeriodFamily.Homology.familyIntersection D)) (i : Fin 3)
    (hC : ∀ x, C x ∈ PeriodFamily.Homology.intersectionPiece D i)
    (q : PeriodFamily.Homology.overlapBase (PeriodFamily.Homology.intersectionIndex i))
    (z : SpecialPeriods.TriangleRegularPoint) (g : SpecialPeriods.TriangleGroup)
    (hz :
      z =
        g •
          PeriodFamily.Homology.upperLiftOnOverlap b (PeriodFamily.Homology.intersectionIndex i)
            q)
    (F : C(X, RealTorus₄)) (v : RealTorus₄) (hF : ∀ x, (C x).val = D.quotient (z, F x + v))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    PeriodFamily.Homology.intersectionHomologyEquiv D b n
        (SingularMayerVietoris.singularHomologyMap C n a) =
      componentCoordinates i
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph g⁻¹ : C(RealTorus₄, RealTorus₄)) n
          (SingularMayerVietoris.singularHomologyMap F n a)) := by
  rw [intersectionHomology_componentMap D b C i hC n a,
    componentFibreMap_homology_affine D b C i hC q z g hz F v hF n, LinearMap.comp_apply]

private theorem PeriodFamily.Boundary.Cusp.lowerColumn_homology (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap lowerColumn n a) =
      PeriodFamily.Boundary.componentCoordinates 1
        (PeriodFamily.Homology.triangleHomologyEquiv
          (tailFrame * SpecialPeriods.triangleGenerator₁)⁻¹ n a) := by
  rw [PeriodFamily.Boundary.intersectionHomology_componentMap
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
      PeriodFamily.Homology.normalizedSlitBaseLift lowerColumn 1 lowerColumn_mem n a]
  have h :=
    PeriodFamily.Boundary.componentFibreMap_homology_deck_comp
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
      PeriodFamily.Homology.normalizedSlitBaseLift lowerColumn 1 lowerColumn_mem
      outerClockwiseQuarterPoint (nativeLiftedSquare (1, 1 / 4))
      (tailFrame * SpecialPeriods.triangleGenerator₁) nativeLiftedSquare_quarter_frame
      (ContinuousMap.id RealTorus₄) lowerColumn_coe n
  rw [h, PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.comp_apply,
    LinearMap.id_apply]
  rfl

private theorem PeriodFamily.Boundary.Cusp.upperColumn_homology (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap upperColumn n a) =
      PeriodFamily.Boundary.componentCoordinates 2
        (PeriodFamily.Homology.triangleHomologyEquiv
          (tailFrame * SpecialPeriods.triangleGenerator₁)⁻¹ n a) := by
  rw [PeriodFamily.Boundary.intersectionHomology_componentMap
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
      PeriodFamily.Homology.normalizedSlitBaseLift upperColumn 2 upperColumn_mem n a]
  have h :=
    PeriodFamily.Boundary.componentFibreMap_homology_deck_comp
      ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
      PeriodFamily.Homology.normalizedSlitBaseLift upperColumn 2 upperColumn_mem
      outerClockwiseThreeQuarterPoint (nativeLiftedSquare (1, 3 / 4))
      (tailFrame * SpecialPeriods.triangleGenerator₁) nativeLiftedSquare_threeQuarters_frame
      (ContinuousMap.id RealTorus₄) upperColumn_coe n
  rw [h, PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.comp_apply,
    LinearMap.id_apply]
  rfl

private theorem PeriodFamily.Boundary.Cusp.lowerColumn_wangBoundary (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap lowerColumn n
          (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a)) =
      PeriodFamily.Boundary.componentCoordinates 1
        (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a)) := by
  rw [lowerColumn_homology, commutingColumnFrame_inv_wangBoundary tailFrame tailFrame_commute]

private theorem PeriodFamily.Boundary.Cusp.upperColumn_wangBoundary (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap upperColumn n
          (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a)) =
      PeriodFamily.Boundary.componentCoordinates 2
        (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a)) := by
  rw [upperColumn_homology, commutingColumnFrame_inv_wangBoundary tailFrame tailFrame_commute]

private def PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy (j : Elliptic.Kind) :
    (loopPeriodic (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j)).Homotopy
      (loopPeriodic
        (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))) :=
  periodicHomotopy (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j)

@[simp]
private theorem
    PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_unit (j : Elliptic.Kind)
    (s t : unitInterval) :
    chosenAttachingPeriodicHomotopy j (s, (t : ℝ)) =
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j).map (s, t) :=
  periodicHomotopy_unit (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j) s t

private theorem PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_initial
    (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicHomotopy j (0, t) =
      loopPeriodic (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j) t :=
  periodicSquare_initial (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j) t

private theorem
    PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_final (j : Elliptic.Kind)
    (t : ℝ) :
    chosenAttachingPeriodicHomotopy j (1, t) =
      loopPeriodic
        (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))
        t :=
  periodicSquare_final (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j) t

private theorem PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_add_int
    (j : Elliptic.Kind) (s : unitInterval) (t : ℝ) (k : ℤ) :
    chosenAttachingPeriodicHomotopy j (s, t + (k : ℝ)) =
      chosenAttachingPeriodicHomotopy j (s, t) :=
  periodicHomotopy_add_int (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j) s t
    k

private theorem PeriodFamily.Boundary.chosenAttachingPeriodicBasepoint (j : Elliptic.Kind) :
    SpecialPeriods.triangleRegularProject (chosenNativeLift j 0) =
      PeriodFamily.BoundaryLoopSquares.loopPeriodic
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j) 0 := by
  rw [PeriodFamily.BoundaryLoopSquares.loopPeriodic_zero]
  exact
    (chosenNativeLift_projection j 0).trans
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j).source

private def PeriodFamily.Boundary.chosenAttachingPeriodicLift (j : Elliptic.Kind) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  realCurveLift
    (PeriodFamily.BoundaryLoopSquares.loopPeriodic
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j))
    (chosenNativeLift j 0) (chosenAttachingPeriodicBasepoint j)

@[simp]
private theorem PeriodFamily.Boundary.chosenAttachingPeriodicLift_zero (j : Elliptic.Kind) :
    chosenAttachingPeriodicLift j 0 = chosenNativeLift j 0 :=
  realCurveLift_zero _ _ _

@[simp]
private theorem
    PeriodFamily.Boundary.chosenAttachingPeriodicLift_projection (j : Elliptic.Kind) (t : ℝ) :
    SpecialPeriods.triangleRegularProject (chosenAttachingPeriodicLift j t) =
      PeriodFamily.BoundaryLoopSquares.loopPeriodic
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j) t :=
  realCurveLift_projection _ _ _ t

@[simp]
private theorem PeriodFamily.Boundary.chosenAttachingPeriodicLift_unit (j : Elliptic.Kind)
    (t : unitInterval) : chosenAttachingPeriodicLift j (t : ℝ) = chosenNativeLift j t := by
  have he :
    SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => chosenAttachingPeriodicLift j (u : ℝ)) =
      SpecialPeriods.triangleRegularProject ∘ chosenNativeLift j := by
    funext u
    simp only [Function.comp_apply, chosenAttachingPeriodicLift_projection,
      PeriodFamily.BoundaryLoopSquares.loopPeriodic_unit, chosenNativeLift_projection]
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
        ((chosenAttachingPeriodicLift j).continuous.comp continuous_subtype_val)
        (chosenNativeLift j).continuous he 0 (chosenAttachingPeriodicLift_zero j))
      t

private theorem
    PeriodFamily.Boundary.chosenAttachingPeriodicLift_translate (j : Elliptic.Kind) (k : ℤ)
    (t : ℝ) :
    chosenAttachingPeriodicLift j (t + k) =
      ((SpecialPeriods.Triangle.ellipticGenerator j)⁻¹ ^ (-k)) •
        chosenAttachingPeriodicLift j t := by
  apply
    realCurveLift_translate
      (PeriodFamily.BoundaryLoopSquares.loopPeriodic
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j))
      (chosenNativeLift j 0) (chosenAttachingPeriodicBasepoint j)
      (PeriodFamily.BoundaryLoopSquares.loopPeriodic_add_one
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j))
      (SpecialPeriods.Triangle.ellipticGenerator j)⁻¹ _ k t
  change
    chosenAttachingPeriodicLift j 1 =
      ((SpecialPeriods.Triangle.ellipticGenerator j)⁻¹)⁻¹ • chosenNativeLift j 0
  rw [inv_inv]
  exact (chosenAttachingPeriodicLift_unit j 1).trans (chosenNativeLift_one j)

private theorem
    PeriodFamily.Boundary.chosenAttachingPeriodicHomotopy_initialLift (j : Elliptic.Kind)
    (t : ℝ) :
    PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy j (0, t) =
      SpecialPeriods.triangleRegularProject (chosenAttachingPeriodicLift j t) :=
  (PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_initial j t).trans
    (chosenAttachingPeriodicLift_projection j t).symm

private def PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift (j : Elliptic.Kind) :
    C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint) :=
  baseHomotopyLift
    (PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy j).toContinuousMap
    (chosenAttachingPeriodicLift j) (chosenAttachingPeriodicHomotopy_initialLift j)

@[simp]
private theorem
    PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_zero (j : Elliptic.Kind) (t : ℝ) :
    chosenAttachingPeriodicSquareLift j (0, t) = chosenAttachingPeriodicLift j t :=
  baseHomotopyLift_zero _ _ _ t

@[simp]
private theorem
    PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_projection (j : Elliptic.Kind)
    (s : unitInterval) (t : ℝ) :
    SpecialPeriods.triangleRegularProject (chosenAttachingPeriodicSquareLift j (s, t)) =
      PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy j (s, t) :=
  baseHomotopyLift_projection _ _ _ s t

@[simp]
private theorem PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_unit (j : Elliptic.Kind)
    (s t : unitInterval) :
    chosenAttachingPeriodicSquareLift j (s, (t : ℝ)) = chosenNativeSquareLift j (s, t) := by
  have hleft :
    Continuous (fun u : unitInterval => chosenAttachingPeriodicSquareLift j (u, (t : ℝ))) :=
    (chosenAttachingPeriodicSquareLift j).continuous.comp (continuous_id.prodMk continuous_const)
  have hright : Continuous (fun u : unitInterval => chosenNativeSquareLift j (u, t)) :=
    (chosenNativeSquareLift j).continuous.comp (continuous_id.prodMk continuous_const)
  have he :
    SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => chosenAttachingPeriodicSquareLift j (u, (t : ℝ))) =
      SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => chosenNativeSquareLift j (u, t)) := by
    funext u
    exact
      (chosenAttachingPeriodicSquareLift_projection j u t).trans
        ((PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_unit j u t).trans
          (loopSquareLift_projection
              (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j)
              (chosenNativeLift j) (chosenNativeLift_projection j) u t).symm)
  have hzero :
    chosenAttachingPeriodicSquareLift j (0, (t : ℝ)) = chosenNativeSquareLift j (0, t) :=
    (chosenAttachingPeriodicSquareLift_zero j t).trans
      ((chosenAttachingPeriodicLift_unit j t).trans
        (loopSquareLift_zero (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingSquare j)
            (chosenNativeLift j) (chosenNativeLift_projection j) t).symm)
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq hleft hright he
        0 hzero)
      s

end Mathoverflow1973

end
