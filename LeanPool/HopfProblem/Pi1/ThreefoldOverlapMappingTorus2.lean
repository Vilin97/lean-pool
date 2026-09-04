/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.CuspUniformization4
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Uniformization.CuspUniformization4

/-!
# Hopf problem: pi 1 · threefold overlap mapping torus 2

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

private def ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral (j : Elliptic.Kind) :
    C(SpecialBoundary j, BoundaryCentralSurface j) :=
  ((SpecialPeriods.EllipticFilling.specialLocalData j).fillingSurfaceRetraction j.twist
        (Elliptic.mainTwist_admissible j)).comp
    (specialBoundaryToFullFilling j)

private theorem ThreefoldOverlapMappingTorus.Elliptic.centralInclusion_surfaceRetraction
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (y : D.Space v hv) :
    D.centralFibreInclusion v hv (D.fillingSurfaceRetraction v hv y) = D.fillingRadial v hv 1 y :=
  congrArg (fun f : C(D.Space v hv, D.Space v hv) => f y)
    (D.surfaceIntoFilling_comp_retraction v hv)

private theorem ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_realCoordinates
    (j : Elliptic.Kind) (t : ℝ) (x : Elliptic.RealCoordinates) :
    specialBoundaryToCentral j
        (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, standardLattice.mkQ x)) =
      Elliptic.surfaceProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)
        (Elliptic.flatProjection
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val x) := by
  let y :
    (SpecialPeriods.EllipticFilling.specialLocalData j).Space j.twist
      (Elliptic.mainTwist_admissible j) :=
    specialBoundaryToFullFilling j
      (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, standardLattice.mkQ x))
  have hy :
    y =
      (SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
        (Elliptic.mainTwist_admissible j)
        (ThreefoldOverlapMappingTorus.root j.order
            (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
            (specialRootRadius j) ((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle),
          standardLattice.mkQ x) :=
    specialBoundaryInclusion_mk j t (standardLattice.mkQ x)
  apply
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralFibreInclusion_injective j.twist
      (Elliptic.mainTwist_admissible j)
  change
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralFibreInclusion j.twist
        (Elliptic.mainTwist_admissible j)
        ((SpecialPeriods.EllipticFilling.specialLocalData j).fillingSurfaceRetraction j.twist
          (Elliptic.mainTwist_admissible j) y) =
      _
  rw [centralInclusion_surfaceRetraction, hy, Elliptic.Equivariant.Data.fillingRadial_quotient,
    Elliptic.discRadial_one, Elliptic.Equivariant.Data.centralFibreInclusion_surfaceProjection,
    Elliptic.Equivariant.Data.centralInclusion_flatProjection]
  rfl

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk (j : Elliptic.Kind)
    (t : ℝ) (x : RealTorus₄) :
    specialBoundaryToCentral j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      Elliptic.surfaceProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)
        (Elliptic.flatTorusPeriodHomeomorph
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val x) := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [Elliptic.flatTorusPeriodHomeomorph_mkQ]
  exact specialBoundaryToCentral_realCoordinates j t u

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_angle (j : Elliptic.Kind)
    (t s : ℝ) (x : RealTorus₄) :
    specialBoundaryToCentral j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      specialBoundaryToCentral j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (s, x)) := by
  rw [specialBoundaryToCentral_mk, specialBoundaryToCentral_mk]

public
theorem FundamentalGroupVanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (hV : Function.Surjective D.overlapHomV) : Function.Surjective D.inclusionHomU := by
  intro γ
  obtain ⟨q, rfl⟩ := D.pushoutEquiv.surjective γ
  induction q using Monoid.PushoutI.induction_on with
  | of i g =>
    cases i with
    | false => exact ⟨g, (D.pushoutEquiv_of Bool.false g).symm⟩
    | true =>
      obtain ⟨a, rfl⟩ := hV g
      exact
        ⟨D.overlapHomU a,
          (DFunLike.congr_fun D.inclusionHom_compatible a).trans
            (D.pushoutEquiv_of Bool.true (D.overlapHomV a)).symm⟩
  | base a =>
    refine ⟨D.overlapHomU a, ?_⟩
    exact
      (D.pushoutEquiv_of Bool.false (D.overlapHomU a)).symm.trans
        (congrArg D.pushoutEquiv (Monoid.PushoutI.of_apply_eq_base D.overlapHom Bool.false a))
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩

end Mathoverflow1973

end
