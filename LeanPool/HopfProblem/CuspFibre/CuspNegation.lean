/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core9
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.CuspFibre.CuspBoundaryTopVanishing
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology3
import all LeanPool.HopfProblem.PeriodFamily.Core9

/-!
# Hopf problem: cusp fibre · cusp negation

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

private def CuspNegation.fibreNeg : C(RealTorus₄, RealTorus₄) :=
  ⟨Neg.neg, ContinuousNeg.continuous_neg⟩

public
theorem CuspNegation.monodromy_map_neg (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.Cusp.monodromy (-x) =
      -ThreefoldOverlapMappingTorus.Cusp.monodromy x := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  change
    SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 (-standardLattice.mkQ v) =
      -SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 (standardLattice.mkQ v)
  rw [← map_neg, SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ, map_neg, map_neg,
    SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ]

private theorem CuspNegation.fibreNeg_monodromy (x : RealTorus₄) :
    fibreNeg (ThreefoldOverlapMappingTorus.Cusp.monodromy x) =
      ThreefoldOverlapMappingTorus.Cusp.monodromy (fibreNeg x) :=
  (monodromy_map_neg x).symm

private def CuspNegation.boundaryNeg :
    C(ThreefoldOverlapMappingTorus.Cusp.Boundary, ThreefoldOverlapMappingTorus.Cusp.Boundary) :=
  CuspBoundaryGammaZero.mappingTorusMap ThreefoldOverlapMappingTorus.Cusp.monodromy
    ThreefoldOverlapMappingTorus.Cusp.monodromy fibreNeg fibreNeg_monodromy

@[simp]
private theorem CuspNegation.boundaryNeg_mk (t : ℝ) (x : RealTorus₄) :
    boundaryNeg (MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x)) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, -x) :=
  rfl

private theorem CuspNegation.quotientNegation_boundaryCylinder (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (t : ℝ) (x : RealTorus₄) :
    quotientNegation D.correction D.radius
        (ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder D h (t, x)).val =
      (ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder D h (t, -x)).val := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  have hneg : -standardLattice.mkQ v = standardLattice.mkQ (-v) := (map_neg _ _).symm
  rw [hneg, ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_realCoordinates,
    ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_realCoordinates,
    quotientNegation_puncturedCuspCover]
  apply
    congrArg
      (fun p : CuspUniformization.LogCover D.radius =>
        (CuspUniformization.puncturedCuspCover D.correction D.radius p).val)
  apply Subtype.ext
  change
    ((ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h : ℂ),
        -D.periods.periodEquiv
            (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h) v) =
      ((ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h : ℂ),
        D.periods.periodEquiv
          (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h) (-v))
  rw [map_neg]

private theorem CuspNegation.quotientNegation_boundaryInclusion (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (x : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    quotientNegation D.correction D.radius
        (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion D h x).val =
      (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion D h (boundaryNeg x)).val := by
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy x
  rw [boundaryNeg_mk]
  exact quotientNegation_boundaryCylinder D h t y

private def CuspNegation.specialCapHomeomorph :
    SpecialPeriods.Threefold.SpecialCuspPiece ≃ₜ SpecialPeriods.Threefold.SpecialCuspPiece :=
  quotientHomeomorph SpecialPeriods.specialCuspData.correction
    (SpecialPeriods.Threefold.specialBaseCover.radius Option.none)

private def CuspNegation.specialCapMap :
    C(SpecialPeriods.Threefold.SpecialCuspPiece, SpecialPeriods.Threefold.SpecialCuspPiece) :=
  ⟨specialCapHomeomorph, specialCapHomeomorph.continuous⟩

private theorem CuspNegation.specialCapMap_specialBoundaryToPiece
    (x : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    specialCapMap (ThreefoldOverlapMappingTorus.Cusp.specialBoundaryToPiece x) =
      ThreefoldOverlapMappingTorus.Cusp.specialBoundaryToPiece (boundaryNeg x) := by
  change
    quotientNegation ThreefoldOverlapMappingTorus.Cusp.specialData.correction
        ThreefoldOverlapMappingTorus.Cusp.specialData.radius
        (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion
            ThreefoldOverlapMappingTorus.Cusp.specialData
            ThreefoldOverlapMappingTorus.Cusp.specialHeight x).val =
      (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion
          ThreefoldOverlapMappingTorus.Cusp.specialData
          ThreefoldOverlapMappingTorus.Cusp.specialHeight (boundaryNeg x)).val
  exact
    quotientNegation_boundaryInclusion ThreefoldOverlapMappingTorus.Cusp.specialData
      ThreefoldOverlapMappingTorus.Cusp.specialHeight x

private theorem CuspNegation.boundaryToFilling_neg :
    (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none).comp boundaryNeg =
      specialCapMap.comp (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none) := by
  rw [ThreefoldOverlapMappingTorus.boundaryToFilling_cusp]
  apply ContinuousMap.ext
  intro x
  exact (specialCapMap_specialBoundaryToPiece x).symm

private theorem PeriodFamily.Boundary.ThirdRelation.referenceClasses_cusp_regular_negation :
    SingularMayerVietoris.singularHomologyMap
        (familyNegation
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂))
        3
        (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
          (ThreefoldHomology.ThirdDegree.referenceClasses Option.none).val) =
      ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 3
        (ThreefoldHomology.ThirdDegree.referenceClasses Option.none).val :=
  cuspNegation_capKernel_regular_fixed CuspNegation.boundaryNeg CuspNegation.boundaryNeg_mk
    CuspNegation.specialCapMap CuspNegation.boundaryToFilling_neg
    (ThreefoldHomology.ThirdDegree.referenceClasses Option.none)

private theorem PeriodFamily.Boundary.ThirdRelation.referenceClasses_regular :
    ThreefoldHomology.CapElimination.nativeCapKernelRegularMap 3
        ThreefoldHomology.ThirdDegree.referenceClasses =
      ThreefoldHomology.ThirdDegree.thirdFibreCyclicMap 1 :=
  referenceClasses_regular_of_cusp_negation referenceClasses_cusp_regular_negation

end Mathoverflow1973

end
