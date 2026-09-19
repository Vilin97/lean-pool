/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core5
public import LeanPool.HopfProblem.Foundations.PeriodTorusTypeOneOne
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology8
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology2
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus2
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.Elliptic.Core6
import all LeanPool.HopfProblem.Threefold.SpecialPeriods10
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology9
import all LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.Pi1.TwistGroup
import all LeanPool.HopfProblem.Pi1.MappingTorusHomology
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.Elliptic.Core7
import all LeanPool.HopfProblem.Foundations.PeriodTorusTypeOneOne

/-!
# Hopf problem: period family · core 6

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
private theorem PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_tail (j : Elliptic.Kind)
    (s : unitInterval) :
    chosenAttachingPeriodicSquareLift j (s, 0) = chosenNativeSquareLift j (s, 0) :=
  chosenAttachingPeriodicSquareLift_unit j s 0

private theorem PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_frame (j : Elliptic.Kind) :
    chosenAttachingPeriodicSquareLift j (1, 0) =
      nativeTailFrame j • PeriodFamily.Meridians.normalizedRegularMeridianBasepoint :=
  (chosenAttachingPeriodicSquareLift_tail j 1).trans (nativeTailFrame_apply j)

private theorem
    PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_translate (j : Elliptic.Kind)
    (s : unitInterval) (k : ℤ) (t : ℝ) :
    chosenAttachingPeriodicSquareLift j (s, t + k) =
      ((SpecialPeriods.Triangle.ellipticGenerator j)⁻¹ ^ (-k)) •
        chosenAttachingPeriodicSquareLift j (s, t) :=
  baseHomotopyLift_translate
    (PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy j).toContinuousMap
    (chosenAttachingPeriodicLift j) (chosenAttachingPeriodicHomotopy_initialLift j)
    (SpecialPeriods.Triangle.ellipticGenerator j)⁻¹
    (fun u k v =>
      PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_add_int j u v k)
    (chosenAttachingPeriodicLift_translate j) s k t

private theorem PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_add_int (j : Elliptic.Kind)
    (s : unitInterval) (t : ℝ) (k : ℤ) :
    chosenAttachingPeriodicSquareLift j (s, t + (k : ℝ)) =
      (SpecialPeriods.Triangle.ellipticGenerator j ^ k) •
        chosenAttachingPeriodicSquareLift j (s, t) := by
  simpa only [inv_zpow, zpow_neg, inv_inv] using
    chosenAttachingPeriodicSquareLift_translate j s k t

private def PeriodFamily.Boundary.clockwisePeriodicLift (b : Bool) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  realCurveLift
    (PeriodFamily.BoundaryLoopSquares.loopPeriodic
      (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b))
    PeriodFamily.Meridians.normalizedRegularMeridianBasepoint
    (PeriodFamily.BoundaryLoopSquares.loopPeriodic_zero
        (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b)).symm

@[simp]
private theorem PeriodFamily.Boundary.clockwisePeriodicLift_projection (b : Bool) (t : ℝ) :
    SpecialPeriods.triangleRegularProject (clockwisePeriodicLift b t) =
      PeriodFamily.BoundaryLoopSquares.loopPeriodic
        (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b) t :=
  realCurveLift_projection _ _ _ t

@[simp]
private theorem PeriodFamily.Boundary.clockwisePeriodicLift_zero (b : Bool) :
    clockwisePeriodicLift b 0 = PeriodFamily.Meridians.normalizedRegularMeridianBasepoint :=
  realCurveLift_zero _ _ _

@[simp]
private theorem PeriodFamily.Boundary.clockwisePeriodicLift_unit (b : Bool) (t : unitInterval) :
    clockwisePeriodicLift b (t : ℝ) = clockwiseFinalLift b t := by
  have he :
    SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => clockwisePeriodicLift b (u : ℝ)) =
      SpecialPeriods.triangleRegularProject ∘ clockwiseFinalLift b := by
    funext u
    simp only [Function.comp_apply, clockwisePeriodicLift_projection,
      PeriodFamily.BoundaryLoopSquares.loopPeriodic_unit, clockwiseFinalLift_projection]
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
        ((clockwisePeriodicLift b).continuous.comp continuous_subtype_val)
        (clockwiseFinalLift b).continuous he 0
        ((clockwisePeriodicLift_zero b).trans (clockwiseFinalLift_zero b).symm))
      t

private theorem PeriodFamily.Boundary.clockwisePeriodicLift_one (b : Bool) :
    clockwisePeriodicLift b 1 = clockwiseLiftEndpoint b • clockwisePeriodicLift b 0 := by
  rw [clockwisePeriodicLift_zero]
  have h := clockwiseFinalLift_one b
  rw [clockwiseFinalLift_zero] at h
  exact (clockwisePeriodicLift_unit b 1).trans h

private theorem PeriodFamily.Boundary.clockwisePeriodicLift_translate (b : Bool) (k : ℤ) (t : ℝ) :
    clockwisePeriodicLift b (t + k) =
      ((clockwiseLiftEndpoint b)⁻¹ ^ (-k)) • clockwisePeriodicLift b t := by
  apply
    realCurveLift_translate
      (PeriodFamily.BoundaryLoopSquares.loopPeriodic
        (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b))
      PeriodFamily.Meridians.normalizedRegularMeridianBasepoint
      (PeriodFamily.BoundaryLoopSquares.loopPeriodic_zero
          (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b)).symm
      (PeriodFamily.BoundaryLoopSquares.loopPeriodic_add_one
        (SpecialPeriods.EllipticAttachingMeridians.clockwiseRegularMeridian b))
      (clockwiseLiftEndpoint b)⁻¹ _ k t
  change
    clockwisePeriodicLift b 1 =
      ((clockwiseLiftEndpoint b)⁻¹)⁻¹ • PeriodFamily.Meridians.normalizedRegularMeridianBasepoint
  rw [inv_inv, ← clockwisePeriodicLift_zero b]
  exact clockwisePeriodicLift_one b

private theorem PeriodFamily.Boundary.clockwisePeriodicLift_add_int (b : Bool) (t : ℝ) (k : ℤ) :
    clockwisePeriodicLift b (t + (k : ℝ)) =
      (clockwiseLiftEndpoint b ^ k) • clockwisePeriodicLift b t := by
  simpa only [inv_zpow, zpow_neg, inv_inv] using clockwisePeriodicLift_translate b k t

private theorem PeriodFamily.Boundary.chosenAttachingPeriodicSquareLift_final (j : Elliptic.Kind)
    (t : ℝ) :
    chosenAttachingPeriodicSquareLift j (1, t) =
      nativeTailFrame j •
        clockwisePeriodicLift (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)
          t := by
  have hleft : Continuous (fun u : ℝ => chosenAttachingPeriodicSquareLift j (1, u)) :=
    (chosenAttachingPeriodicSquareLift j).continuous.comp (continuous_const.prodMk continuous_id)
  have hright :
    Continuous
      (fun u : ℝ =>
        nativeTailFrame j •
          clockwisePeriodicLift
            (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) u) :=
    (ContinuousConstSMul.continuous_const_smul (nativeTailFrame j)).comp
      (clockwisePeriodicLift
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).continuous
  have he :
    SpecialPeriods.triangleRegularProject ∘
        (fun u : ℝ => chosenAttachingPeriodicSquareLift j (1, u)) =
      SpecialPeriods.triangleRegularProject ∘
        (fun u : ℝ =>
          nativeTailFrame j •
            clockwisePeriodicLift
              (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) u) := by
    funext u
    simp only [Function.comp_apply, chosenAttachingPeriodicSquareLift_projection,
      PeriodFamily.BoundaryLoopSquares.chosenAttachingPeriodicHomotopy_final,
      SpecialPeriods.triangleRegularProject_covering.map_smul, clockwisePeriodicLift_projection]
  have hzero :
    chosenAttachingPeriodicSquareLift j (1, 0) =
      nativeTailFrame j •
        clockwisePeriodicLift (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)
          0 := by
    rw [clockwisePeriodicLift_zero]
    exact chosenAttachingPeriodicSquareLift_frame j
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq hleft hright he
        0 hzero)
      t

private def PeriodFamily.Boundary.nativeClockwiseParameter (j : Elliptic.Kind) (t : ℝ) : ℂ :=
  SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j - (t : ℂ) / (j.order : ℂ)

@[simp]
private theorem PeriodFamily.Boundary.nativeClockwiseParameter_im (j : Elliptic.Kind) (t : ℝ) :
    (nativeClockwiseParameter j t).im =
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j).im := by
  simp [nativeClockwiseParameter, Complex.div_im]

private def
    PeriodFamily.Boundary.nativeClockwiseRoot (j : Elliptic.Kind) : C(ℝ, SpecialPeriods.Disc)
    where
  toFun
    t :=
    ⟨CuspUniformization.exponential (nativeClockwiseParameter j t),
      by
      change Dist.dist (CuspUniformization.exponential (nativeClockwiseParameter j t)) 0 < 1
      rw [dist_zero_right]
      apply SpecialPeriods.TauCusp.exponential_norm_lt_one_of_upperHalfPlane
      simpa only [nativeClockwiseParameter_im] using
        SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_im_pos j⟩
  continuous_toFun :=
    (CuspUniformization.exponential_holomorphic.continuous.comp
          (continuous_const.sub (Complex.continuous_ofReal.div_const (j.order : ℂ)))).subtype_mk
      _

@[simp]
private theorem PeriodFamily.Boundary.nativeClockwiseRoot_coe (j : Elliptic.Kind) (t : ℝ) :
    (nativeClockwiseRoot j t : ℂ) =
      CuspUniformization.exponential (nativeClockwiseParameter j t) :=
  rfl

private theorem PeriodFamily.Boundary.nativeClockwiseRoot_ne_zero (j : Elliptic.Kind) (t : ℝ) :
    (nativeClockwiseRoot j t : ℂ) ≠ 0 :=
  CuspUniformization.exponential_ne_zero _

private theorem
    PeriodFamily.Boundary.nativeClockwiseRoot_unit (j : Elliptic.Kind) (t : unitInterval) :
    nativeClockwiseRoot j (t : ℝ) =
      Elliptic.LogGauge.logMeridianRoot j
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j)
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_im_pos j) t := by
  apply Subtype.ext
  rfl

private theorem PeriodFamily.Boundary.nativeClockwiseRoot_add_one (j : Elliptic.Kind) (t : ℝ) :
    nativeClockwiseRoot j (t + 1) = Elliptic.familyRotation j (nativeClockwiseRoot j t) := by
  apply Subtype.ext
  rw [Elliptic.LogGauge.familyRotation_val_exponential, nativeClockwiseRoot_coe,
    nativeClockwiseRoot_coe]
  have he :
    nativeClockwiseParameter j (t + 1) = nativeClockwiseParameter j t + -(1 / (j.order : ℂ)) := by
    simp only [nativeClockwiseParameter]
    push_cast
    ring
  rw [he, CuspUniformization.exponential_add]
  exact mul_comm _ _

private def PeriodFamily.Boundary.nativeClockwiseBase (j : Elliptic.Kind) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  ⟨fun t =>
    SpecialPeriods.EllipticFilling.localBase j
      ⟨nativeClockwiseRoot j t, nativeClockwiseRoot_ne_zero j t⟩,
    (SpecialPeriods.EllipticFilling.localBase_continuous j).comp
      ((nativeClockwiseRoot j).continuous.subtype_mk _)⟩

private theorem
    PeriodFamily.Boundary.nativeClockwiseBase_unit (j : Elliptic.Kind) (t : unitInterval) :
    nativeClockwiseBase j (t : ℝ) = chosenNativeLift j t := by
  change
    SpecialPeriods.EllipticFilling.localBase j ⟨nativeClockwiseRoot j (t : ℝ), _⟩ =
      SpecialPeriods.EllipticFilling.localBase j
        (Elliptic.LogGauge.logMeridianRootStar (j := j)
          (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j)
          (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_im_pos j) t)
  apply congrArg (SpecialPeriods.EllipticFilling.localBase j)
  apply Subtype.ext
  exact nativeClockwiseRoot_unit j t

private theorem PeriodFamily.Boundary.nativeClockwiseBase_endpoint (j : Elliptic.Kind) (t : ℝ) :
    nativeClockwiseBase j (t + 1) =
      SpecialPeriods.Triangle.ellipticGenerator j • nativeClockwiseBase j t := by
  let z₀ : Elliptic.LogGauge.BaseStar :=
    ⟨nativeClockwiseRoot j t, nativeClockwiseRoot_ne_zero j t⟩
  let z₁ : Elliptic.LogGauge.BaseStar :=
    ⟨nativeClockwiseRoot j (t + 1), nativeClockwiseRoot_ne_zero j (t + 1)⟩
  have hz : SpecialPeriods.EllipticFilling.puncturedRotation j z₀ = z₁ :=
    Subtype.ext (nativeClockwiseRoot_add_one j t).symm
  have h := SpecialPeriods.EllipticFilling.localBase_rotation j z₀
  rw [hz] at h
  exact h

private theorem PeriodFamily.Boundary.nativeClockwiseBase_projection_periodic (j : Elliptic.Kind) :
    Function.Periodic
      (fun t : ℝ => SpecialPeriods.triangleRegularProject (nativeClockwiseBase j t)) 1 := by
  intro t
  change
    SpecialPeriods.triangleRegularProject (nativeClockwiseBase j (t + 1)) =
      SpecialPeriods.triangleRegularProject (nativeClockwiseBase j t)
  rw [nativeClockwiseBase_endpoint, SpecialPeriods.triangleRegularProject_covering.map_smul]

private theorem
    PeriodFamily.Boundary.nativeClockwiseBase_projection_eq (j : Elliptic.Kind) (t : ℝ) :
    SpecialPeriods.triangleRegularProject (nativeClockwiseBase j t) =
      PeriodFamily.BoundaryLoopSquares.loopPeriodic
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j) t := by
  apply
    congrFun
      (PeriodFamily.BoundaryLoopSquares.loopPeriodic_unique
        (fun t : ℝ => SpecialPeriods.triangleRegularProject (nativeClockwiseBase j t))
        (nativeClockwiseBase_projection_periodic j) _)
      t
  intro u
  rw [nativeClockwiseBase_unit, chosenNativeLift_projection]

private theorem PeriodFamily.Boundary.nativeClockwiseBase_eq_periodicLift (j : Elliptic.Kind) :
    nativeClockwiseBase j = chosenAttachingPeriodicLift j :=
  realCurveLift_unique
    (PeriodFamily.BoundaryLoopSquares.loopPeriodic
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingBaseLoop j))
    (chosenNativeLift j 0) (chosenAttachingPeriodicBasepoint j) (nativeClockwiseBase j)
    (nativeClockwiseBase_projection_eq j) (nativeClockwiseBase_unit j 0)

private def PeriodFamily.Boundary.nativePositiveBase (j : Elliptic.Kind) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  (nativeClockwiseBase j).comp ⟨Neg.neg, ContinuousNeg.continuous_neg⟩

@[simp]
private theorem PeriodFamily.Boundary.nativePositiveBase_apply (j : Elliptic.Kind) (t : ℝ) :
    nativePositiveBase j t = nativeClockwiseBase j (-t) :=
  rfl

private theorem
    PeriodFamily.Boundary.nativePositiveBase_eq_periodicLift (j : Elliptic.Kind) (t : ℝ) :
    nativePositiveBase j t = chosenAttachingPeriodicLift j (-t) := by
  rw [nativePositiveBase_apply, nativeClockwiseBase_eq_periodicLift]

private def PeriodFamily.Boundary.nativePositiveSquareLift (j : Elliptic.Kind) :
    C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint) :=
  (chosenAttachingPeriodicSquareLift j).comp
    ⟨fun p => (p.1, -p.2),
      continuous_fst.prodMk (ContinuousNeg.continuous_neg.comp continuous_snd)⟩

@[simp]
private theorem PeriodFamily.Boundary.nativePositiveSquareLift_apply (j : Elliptic.Kind)
    (s : unitInterval) (t : ℝ) :
    nativePositiveSquareLift j (s, t) = chosenAttachingPeriodicSquareLift j (s, -t) :=
  rfl

private theorem PeriodFamily.Boundary.nativePositiveSquareLift_zero (j : Elliptic.Kind) (t : ℝ) :
    nativePositiveSquareLift j (0, t) = nativePositiveBase j t := by
  rw [nativePositiveSquareLift_apply, chosenAttachingPeriodicSquareLift_zero,
    nativePositiveBase_eq_periodicLift]

private theorem PeriodFamily.Boundary.nativePositiveSquareLift_translate (j : Elliptic.Kind)
    (s : unitInterval) (k : ℤ) (t : ℝ) :
    nativePositiveSquareLift j (s, t + k) =
      (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • nativePositiveSquareLift j (s, t) := by
  rw [nativePositiveSquareLift_apply, nativePositiveSquareLift_apply]
  have ht : -(t + (k : ℝ)) = -t + ((-k : ℤ) : ℝ) := by push_cast; ring
  rw [ht]
  exact chosenAttachingPeriodicSquareLift_add_int j s (-t) (-k)

private theorem PeriodFamily.Boundary.nativePositiveSquareLift_final (j : Elliptic.Kind) (t : ℝ) :
    nativePositiveSquareLift j (1, t) =
      nativeTailFrame j •
        clockwisePeriodicLift (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)
          (-t) :=
  chosenAttachingPeriodicSquareLift_final j (-t)

private theorem PeriodFamily.Boundary.exponential_eq_norm_mul_real (s : ℂ) :
    CuspUniformization.exponential s =
      (‖CuspUniformization.exponential s‖ : ℂ) * CuspUniformization.exponential (s.re : ℂ) := by
  simp only [CuspUniformization.exponential]
  rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private def PeriodFamily.Boundary.nativeBoundaryRootRadius (j : Elliptic.Kind) :
    ThreefoldOverlapMappingTorus.Radius j.order
      (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :=
  ⟨‖CuspUniformization.exponential
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j)‖,
    norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _),
    SpecialPeriods.TauCusp.exponential_norm_lt_one_of_upperHalfPlane
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_im_pos j),
    SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter_filling_bound j⟩

private def PeriodFamily.Boundary.nativeBoundaryRootPhase (j : Elliptic.Kind) : ℝ :=
  (j.order : ℝ) * (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j).re

private theorem PeriodFamily.Boundary.nativeBoundaryRoot_coe (j : Elliptic.Kind) (t : ℝ) :
    (ThreefoldOverlapMappingTorus.root j.order
          (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
          (nativeBoundaryRootRadius j)
          (((t + nativeBoundaryRootPhase j) / j.order : ℝ) :
            (ThreefoldOverlapMappingTorus.Circle)) :
        ℂ) =
      CuspUniformization.exponential
        (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j +
          (t : ℂ) / (j.order : ℂ)) := by
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have ht :
    (t + nativeBoundaryRootPhase j) / (j.order : ℝ) =
      (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j).re +
        t / (j.order : ℝ) := by
    dsimp [nativeBoundaryRootPhase]
    field_simp
    ring
  change
    ‖CuspUniformization.exponential
            (SpecialPeriods.Threefold.EllipticGeometry.chosenAttachingParameter j)‖ •
        (ThreefoldOverlapMappingTorus.phase
            (((t + nativeBoundaryRootPhase j) / j.order : ℝ) :
              (ThreefoldOverlapMappingTorus.Circle)) :
          ℂ) =
      _
  rw [ThreefoldOverlapMappingTorus.phase_real, Complex.real_smul, ht]
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [CuspUniformization.exponential_add, ← mul_assoc, ← exponential_eq_norm_mul_real, ←
    CuspUniformization.exponential_add]

private theorem PeriodFamily.Boundary.nativeBoundaryRoot_eq (j : Elliptic.Kind) (t : ℝ) :
    ThreefoldOverlapMappingTorus.root j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
        (nativeBoundaryRootRadius j)
        (((t + nativeBoundaryRootPhase j) / j.order : ℝ) :
          (ThreefoldOverlapMappingTorus.Circle)) =
      nativeClockwiseRoot j (-t) := by
  apply Subtype.ext
  rw [nativeBoundaryRoot_coe, nativeClockwiseRoot_coe]
  simp only [nativeClockwiseParameter, Complex.ofReal_neg, neg_div, sub_neg_eq_add]

private def PeriodFamily.Boundary.nativeShiftedBase (j : Elliptic.Kind) (τ : ℝ) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  (nativePositiveBase j).comp ⟨fun t => t + τ, continuous_id.add continuous_const⟩

private def PeriodFamily.Boundary.nativeShiftedSquareLift (j : Elliptic.Kind) (τ : ℝ) :
    C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint) :=
  (nativePositiveSquareLift j).comp
    ⟨fun p => (p.1, p.2 + τ), continuous_fst.prodMk (continuous_snd.add continuous_const)⟩

@[simp]
private theorem PeriodFamily.Boundary.nativeShiftedSquareLift_zero (j : Elliptic.Kind) (τ t : ℝ) :
    nativeShiftedSquareLift j τ (0, t) = nativeShiftedBase j τ t :=
  nativePositiveSquareLift_zero j (t + τ)

private theorem PeriodFamily.Boundary.nativeShiftedSquareLift_translate (j : Elliptic.Kind) (τ : ℝ)
    (s : unitInterval) (k : ℤ) (t : ℝ) :
    nativeShiftedSquareLift j τ (s, t + k) =
      (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • nativeShiftedSquareLift j τ (s, t) :=
  by
  change
    nativePositiveSquareLift j (s, (t + k) + τ) =
      (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • nativePositiveSquareLift j (s, t + τ)
  rw [show (t + (k : ℝ)) + τ = (t + τ) + (k : ℝ) by ring]
  exact nativePositiveSquareLift_translate j s k (t + τ)

private theorem
    PeriodFamily.Boundary.nativeShiftedBase_translate (j : Elliptic.Kind) (τ : ℝ) (k : ℤ)
    (t : ℝ) :
    nativeShiftedBase j τ (t + k) =
      (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • nativeShiftedBase j τ t := by
  simpa only [nativeShiftedSquareLift_zero] using nativeShiftedSquareLift_translate j τ 0 k t

private def PeriodFamily.Boundary.nativeGaugeFamilyStar (j : Elliptic.Kind) (τ : ℝ) :
    C(ℝ × RealTorus₄,
      Elliptic.LogGauge.FamilyStar (SpecialPeriods.EllipticFilling.specialLocalData j).periods)
    where
  toFun
    p := ⟨(nativeClockwiseRoot j (-(p.1 + τ)), p.2), nativeClockwiseRoot_ne_zero j (-(p.1 + τ))⟩
  continuous_toFun :=
    (((nativeClockwiseRoot j).continuous.comp (continuous_fst.add continuous_const).neg).prodMk
          continuous_snd).subtype_mk
      _

private def PeriodFamily.Boundary.nativeGaugeCylinder (j : Elliptic.Kind) (τ : ℝ) :
    C(ℝ × RealTorus₄, RealTorus₄) :=
  ⟨fun p =>
    (Elliptic.LogGauge.gaugeMap (SpecialPeriods.EllipticFilling.specialLocalData j).periods
          j.twist (nativeGaugeFamilyStar j τ p)).val.2,
    (continuous_snd.comp continuous_subtype_val).comp
      ((Elliptic.LogGauge.gaugeMap_continuous
            (SpecialPeriods.EllipticFilling.specialLocalData j).periods j.twist).comp
        (nativeGaugeFamilyStar j τ).continuous)⟩

@[simp]
private theorem PeriodFamily.Boundary.nativeGaugeCylinder_apply (j : Elliptic.Kind) (τ t : ℝ)
    (x : RealTorus₄) :
    nativeGaugeCylinder j τ (t, x) =
      x +
        Elliptic.LogGauge.sectionCoordinate
          (SpecialPeriods.EllipticFilling.specialLocalData j).periods j.twist
          (nativeClockwiseRoot j (-(t + τ))) :=
  rfl

private theorem PeriodFamily.Boundary.nativeShiftedSquareLift_final (j : Elliptic.Kind) (τ t : ℝ) :
    nativeShiftedSquareLift j τ (1, t) =
      nativeTailFrame j •
        clockwisePeriodicLift (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)
          (-(t + τ)) :=
  nativePositiveSquareLift_final j (t + τ)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private def PeriodFamily.Boundary.nativeBoundaryInclusion (j : Elliptic.Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j,
      ThreefoldOverlapMappingTorus.PuncturedPiece (Option.some j)) :=
  ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusionAt j (nativeBoundaryRootRadius j)
    (nativeBoundaryRootPhase j + τ)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private def PeriodFamily.Boundary.nativeRegularBoundaryMap (j : Elliptic.Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j,
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space) :=
  ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToRegularFamilyAt j
    (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem PeriodFamily.Boundary.nativeBoundaryInclusion_mk (j : Elliptic.Kind) (τ t : ℝ)
    (x : RealTorus₄) :
    ((nativeBoundaryInclusion j τ
              (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x))).val :
          SpecialPeriods.Threefold.SpecialEllipticPiece j).val =
      (SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
        (Elliptic.mainTwist_admissible j) (nativeClockwiseRoot j (-(t + τ)), x) := by
  have h :=
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusionAt_mk j
      (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ) t x
  have hr :
    ThreefoldOverlapMappingTorus.root j.order
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
        (nativeBoundaryRootRadius j)
        (((t + (nativeBoundaryRootPhase j + τ)) / j.order : ℝ) :
          ThreefoldOverlapMappingTorus.Circle) =
      nativeClockwiseRoot j (-(t + τ)) := by
    rw [show t + (nativeBoundaryRootPhase j + τ) = (t + τ) + nativeBoundaryRootPhase j by ring]
    exact nativeBoundaryRoot_eq j (t + τ)
  exact
    h.trans
      (congrArg
        ((SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
          (Elliptic.mainTwist_admissible j))
        (Prod.ext hr rfl))

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem PeriodFamily.Boundary.nativeRegularBoundaryMap_gauge (j : Elliptic.Kind) (τ t : ℝ)
    (x : RealTorus₄) :
    nativeRegularBoundaryMap j τ (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      SpecialPeriods.EllipticFilling.regularMap SpecialPeriods.specialPeriodMap j
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        (Elliptic.LogGauge.gaugeMap (SpecialPeriods.EllipticFilling.specialLocalData j).periods
          j.twist (nativeGaugeFamilyStar j τ (t, x))) := by
  let y :=
    nativeBoundaryInclusion j τ (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x))
  change ThreefoldOverlapMappingTorus.puncturedPieceToRegular (Option.some j) y = _
  rw [ThreefoldOverlapMappingTorus.Elliptic.puncturedPieceToRegular_elliptic]
  have hx :
    (SpecialPeriods.EllipticFilling.specialFullFillingProjection j
          (y.val : SpecialPeriods.Threefold.SpecialEllipticPiece j).val :
        ℂ) ≠
      0 :=
    (ThreefoldOverlapMappingTorus.Elliptic.specialPiece_regular_iff j y.val).mp y.property
  have hstar :
    (⟨(y.val : SpecialPeriods.Threefold.SpecialEllipticPiece j).val, hx⟩ :
        SpecialPeriods.EllipticFilling.MainFillingStar SpecialPeriods.specialPeriodMap j
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂) =
      Elliptic.LogGauge.fillingStarProject (SpecialPeriods.EllipticFilling.specialLocalData j)
        j.twist (Elliptic.mainTwist_admissible j) (nativeGaugeFamilyStar j τ (t, x)) := by
    apply Subtype.ext
    exact nativeBoundaryInclusion_mk j τ t x
  change
    SpecialPeriods.EllipticFilling.smallOverlap SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        SpecialPeriods.Threefold.specialBaseCover j y.val =
      _
  rw [SpecialPeriods.EllipticFilling.smallOverlap_apply_mainStar SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
      SpecialPeriods.Threefold.specialBaseCover j y.val hx,
    hstar]
  change
    (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph SpecialPeriods.specialPeriodMap
          j SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          (Elliptic.LogGauge.fillingToTautologicalBiholomorph
            (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
            (Elliptic.mainTwist_admissible j)
            (Elliptic.LogGauge.fillingStarProject
              (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
              (Elliptic.mainTwist_admissible j) (nativeGaugeFamilyStar j τ (t, x))))).val =
      _
  rw [Elliptic.LogGauge.fillingToTautologicalBiholomorph_project]
  exact
    congrArg Subtype.val
      (SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_project
        SpecialPeriods.specialPeriodMap j SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂
        (Elliptic.LogGauge.gaugeMap (SpecialPeriods.EllipticFilling.specialLocalData j).periods
          j.twist (nativeGaugeFamilyStar j τ (t, x))))

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem PeriodFamily.Boundary.nativeRegularBoundaryMap_mk (j : Elliptic.Kind) (τ t : ℝ)
    (x : RealTorus₄) :
    nativeRegularBoundaryMap j τ (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (nativeShiftedBase j τ t, nativeGaugeCylinder j τ (t, x)) := by
  rw [nativeRegularBoundaryMap_gauge]
  rfl

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem PeriodFamily.Boundary.boundaryRegularHomologyMap_native (j : Elliptic.Kind) (τ : ℝ)
    (n : ℕ) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) n =
      SingularMayerVietoris.singularHomologyMap (nativeRegularBoundaryMap j τ) n :=
  ThreefoldOverlapMappingTorus.Elliptic.boundaryRegularHomologyMap_at j
    (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ) n

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem PeriodFamily.Boundary.nativeGaugeCylinder_deck (j : Elliptic.Kind) (τ : ℝ) (k : ℤ)
    (p : ℝ × RealTorus₄) :
    nativeGaugeCylinder j τ (MappingTorus.deck (Elliptic.flatTorusAffine j j.twist) k p) =
      SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k))
        (nativeGaugeCylinder j τ p) := by
  exact
    fibreMap_deck_of_actual
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      (Elliptic.flatTorusAffine j j.twist) (nativeRegularBoundaryMap j τ) (nativeShiftedBase j τ)
      (nativeGaugeCylinder j τ) (SpecialPeriods.Triangle.ellipticGenerator j)
      (fun p => nativeRegularBoundaryMap_mk j τ p.1 p.2) (nativeShiftedBase_translate j τ) k p

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private def PeriodFamily.Boundary.normalizedEllipticBoundaryMap (j : Elliptic.Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j,
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space) :=
  familyBoundaryMap
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
    (Elliptic.flatTorusAffine j j.twist) (baseHomotopySlice (nativeShiftedSquareLift j τ) 1)
    (nativeGaugeCylinder j τ) (SpecialPeriods.Triangle.ellipticGenerator j)
    (nativeShiftedSquareLift_translate j τ 1) (nativeGaugeCylinder_deck j τ)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem
    PeriodFamily.Boundary.nativeRegularBoundaryMap_homotopic_normalized (j : Elliptic.Kind)
    (τ : ℝ) : (nativeRegularBoundaryMap j τ).Homotopic (normalizedEllipticBoundaryMap j τ) :=
  actualBoundary_homotopic_of_base
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
    (Elliptic.flatTorusAffine j j.twist) (nativeRegularBoundaryMap j τ) (nativeShiftedBase j τ)
    (nativeGaugeCylinder j τ) (SpecialPeriods.Triangle.ellipticGenerator j)
    (fun p => nativeRegularBoundaryMap_mk j τ p.1 p.2) (nativeShiftedBase_translate j τ)
    (nativeShiftedSquareLift j τ) (nativeShiftedSquareLift_zero j τ)
    (nativeShiftedSquareLift_translate j τ)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem
    PeriodFamily.Boundary.boundaryRegularHomologyMap_normalized (j : Elliptic.Kind) (τ : ℝ)
    (n : ℕ) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) n =
      SingularMayerVietoris.singularHomologyMap (normalizedEllipticBoundaryMap j τ) n :=
  (boundaryRegularHomologyMap_native j τ n).trans
    (PeriodTorusHigherHomology.homotopic_homologyMap
      (nativeRegularBoundaryMap_homotopic_normalized j τ) n)

attribute [local instance] SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace
    SpecialPeriods.EllipticFilling.specialFullFillingChartedSpace in
private theorem PeriodFamily.Boundary.normalizedEllipticBoundaryMap_mk (j : Elliptic.Kind) (τ t : ℝ)
    (x : RealTorus₄) :
    normalizedEllipticBoundaryMap j τ
        (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (nativeShiftedSquareLift j τ (1, t), nativeGaugeCylinder j τ (t, x)) :=
  rfl

private theorem PeriodFamily.Boundary.clockwiseEndpoint_eq_generator_mo1973_26994 (b : Bool) :
    clockwiseLiftEndpoint b = PeriodFamily.Meridians.compatibleMeridianGenerator b := by
  simp only [clockwiseLiftEndpoint, normalizationReversesMeridians_false, Bool.false_eq_true,
    ite_false]

private theorem PeriodFamily.Boundary.clockwiseFinalLift_eq_reverse_mo1973_26995 (b : Bool)
    (t : unitInterval) :
    clockwiseFinalLift b t =
      PeriodFamily.Meridians.compatibleMeridianGenerator b •
        PeriodFamily.Meridians.compatibleMeridianLift b (unitInterval.symm t) := by
  rw [clockwiseFinalLift, normalizationReversesMeridians_false]
  rfl

private def PeriodFamily.Boundary.canonicalPositiveLift (b : Bool) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  (clockwisePeriodicLift b).comp ⟨fun t : ℝ => -t, ContinuousNeg.continuous_neg⟩

@[simp]
private theorem PeriodFamily.Boundary.canonicalPositiveLift_apply (b : Bool) (t : ℝ) :
    canonicalPositiveLift b t = clockwisePeriodicLift b (-t) :=
  rfl

private theorem PeriodFamily.Boundary.canonicalPositiveLift_unit (b : Bool) (t : unitInterval) :
    canonicalPositiveLift b (t : ℝ) = PeriodFamily.Meridians.compatibleMeridianLift b t := by
  calc
    _ = clockwisePeriodicLift b ((unitInterval.symm t : ℝ) + (-1 : ℝ)) := by
      rw [canonicalPositiveLift_apply, unitInterval.coe_symm_eq]
      congr 1
      ring
    _ =
        (clockwiseLiftEndpoint b ^ (-1 : ℤ)) •
          clockwisePeriodicLift b (unitInterval.symm t : ℝ) := by
      simpa only [Int.cast_neg, Int.cast_one] using
        clockwisePeriodicLift_add_int b (unitInterval.symm t : ℝ) (-1)
    _ =
        (PeriodFamily.Meridians.compatibleMeridianGenerator b)⁻¹ •
          (PeriodFamily.Meridians.compatibleMeridianGenerator b •
            PeriodFamily.Meridians.compatibleMeridianLift b t) := by
      rw [clockwiseEndpoint_eq_generator_mo1973_26994, zpow_neg_one, clockwisePeriodicLift_unit,
        clockwiseFinalLift_eq_reverse_mo1973_26995, unitInterval.symm_symm]
    _ = _ := inv_smul_smul _ _

private theorem PeriodFamily.Boundary.canonicalPositiveLift_one (b : Bool) :
    canonicalPositiveLift b 1 =
      (PeriodFamily.Meridians.compatibleMeridianGenerator b)⁻¹ •
        PeriodFamily.Meridians.normalizedRegularMeridianBasepoint :=
  (canonicalPositiveLift_unit b 1).trans (PeriodFamily.Meridians.compatibleMeridianLift b).target

private theorem PeriodFamily.Boundary.canonicalPositiveLift_translate (b : Bool) (k : ℤ) (t : ℝ) :
    canonicalPositiveLift b (t + k) =
      (PeriodFamily.Meridians.compatibleMeridianGenerator b ^ (-k)) • canonicalPositiveLift b t :=
  by
  simpa only [canonicalPositiveLift_apply, neg_add, Int.cast_neg,
    clockwiseEndpoint_eq_generator_mo1973_26994] using clockwisePeriodicLift_add_int b (-t) (-k)

private theorem PeriodFamily.Boundary.canonicalPositiveLift_projection (b : Bool) (t : ℝ) :
    SpecialPeriods.triangleRegularProject (canonicalPositiveLift b t) =
      PeriodFamily.BoundaryLoopSquares.loopPeriodic
        (PeriodFamily.Meridians.compatibleRegularMeridian b) t := by
  have hp :
    Function.Periodic
      (fun u : ℝ => SpecialPeriods.triangleRegularProject (canonicalPositiveLift b u)) 1 := by
    intro u
    have h :=
      congrArg SpecialPeriods.triangleRegularProject (canonicalPositiveLift_translate b 1 u)
    simpa only [Int.cast_one, SpecialPeriods.triangleRegularProject_covering.map_smul] using h
  have hu (u : unitInterval) :
    SpecialPeriods.triangleRegularProject (canonicalPositiveLift b (u : ℝ)) =
      PeriodFamily.Meridians.compatibleRegularMeridian b u := by
    rw [canonicalPositiveLift_unit]
    exact compatibleLift_projection b u
  exact
    congrFun
      (PeriodFamily.BoundaryLoopSquares.loopPeriodic_unique (p :=
        PeriodFamily.Meridians.compatibleRegularMeridian b)
        (fun u : ℝ => SpecialPeriods.triangleRegularProject (canonicalPositiveLift b u)) hp hu)
      t

private def PeriodFamily.Boundary.canonicalPositivePhaseLift (b : Bool) (phase : ℝ) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  (canonicalPositiveLift b).comp ⟨fun t => t + phase, continuous_id.add continuous_const⟩

private theorem PeriodFamily.Boundary.canonicalUpperLeft :
    PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 0
        PeriodFamily.Homology.meridianLeftOverlapPoint =
      SpecialPeriods.triangleGenerator₁⁻¹ •
        PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint := by
  have hn : ¬0 < RiemannMapping.normalizationOrientation :=
    not_lt.mpr normalizationOrientation_nonpos
  change
    PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift
        ⟨SpecialPeriods.triangleRegularProject
            PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint,
          _⟩ =
      _
  have hp (t : unitInterval) :
    SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.reflectedZeroHalfPath t) ∈
      PeriodFamily.Homology.upperBase := by
    rw [PeriodFamily.Homology.mem_regularOpen,
      PeriodFamily.Meridians.reflectedZeroHalfPath_coordinate,
      PeriodFamily.Meridians.oppositeZeroPath, ite_eq_right hn]
    exact SpecialPeriods.Triangle.upperZeroPath_mem_upperSlitPlane t
  apply
    PeriodFamily.Homology.upperLift_endpoint PeriodFamily.Homology.normalizedSlitBaseLift _
      PeriodFamily.Meridians.reflectedZeroHalfPath hp
  exact (SpecialPeriods.triangleRegularProject_covering.map_smul _).symm

private theorem PeriodFamily.Boundary.canonicalUpperRight :
    PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 2
        PeriodFamily.Homology.meridianRightOverlapPoint =
      SpecialPeriods.triangleGenerator₂ •
        PeriodFamily.Meridians.normalizedRegularMeridianRightPoint := by
  have hn : ¬0 < RiemannMapping.normalizationOrientation :=
    not_lt.mpr normalizationOrientation_nonpos
  change
    PeriodFamily.Homology.upperLift PeriodFamily.Homology.normalizedSlitBaseLift
        ⟨SpecialPeriods.triangleRegularProject
            PeriodFamily.Meridians.normalizedRegularMeridianRightPoint,
          _⟩ =
      _
  have hp (t : unitInterval) :
    SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.reflectedOneHalfPath t) ∈
      PeriodFamily.Homology.upperBase := by
    rw [PeriodFamily.Homology.mem_regularOpen,
      PeriodFamily.Meridians.reflectedOneHalfPath_coordinate,
      PeriodFamily.Meridians.oppositeOnePath, ite_eq_right hn]
    exact SpecialPeriods.Triangle.upperOnePath_mem_upperSlitPlane t
  apply
    PeriodFamily.Homology.upperLift_endpoint PeriodFamily.Homology.normalizedSlitBaseLift _
      PeriodFamily.Meridians.reflectedOneHalfPath hp
  exact (SpecialPeriods.triangleRegularProject_covering.map_smul _).symm

private def PeriodFamily.Boundary.canonicalHalfTime : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

private theorem PeriodFamily.Boundary.path_trans_canonicalHalfTime_mo1973_27012 {X : Type*}
    [TopologicalSpace X] {a b c : X} (p : Path a b) (q : Path b c) :
    (p.trans q) canonicalHalfTime = b := by
  rw [Path.trans_apply, dite_eq_left (show (canonicalHalfTime : ℝ) ≤ 1 / 2 from le_rfl)]
  calc
    _ = p 1 := congrArg p (Subtype.ext (by norm_num [canonicalHalfTime]))
    _ = b := p.target

private theorem PeriodFamily.Boundary.compatibleMeridianLift_false_half :
    PeriodFamily.Meridians.compatibleMeridianLift Bool.false canonicalHalfTime =
      SpecialPeriods.triangleGenerator₁⁻¹ •
        PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint :=
  path_trans_canonicalHalfTime_mo1973_27012 PeriodFamily.Meridians.reflectedZeroHalfPath
    (PeriodFamily.Meridians.liftedZeroHalfPath.symm.map
      (ContinuousConstSMul.continuous_const_smul SpecialPeriods.triangleGenerator₁⁻¹))

private theorem PeriodFamily.Boundary.compatibleMeridianLift_true_half :
    PeriodFamily.Meridians.compatibleMeridianLift Bool.true canonicalHalfTime =
      PeriodFamily.Meridians.normalizedRegularMeridianRightPoint :=
  path_trans_canonicalHalfTime_mo1973_27012 PeriodFamily.Meridians.liftedOneHalfPath
    ((PeriodFamily.Meridians.reflectedOneHalfPath.symm.map
          (ContinuousConstSMul.continuous_const_smul SpecialPeriods.triangleGenerator₂⁻¹)).cast
      (inv_smul_smul SpecialPeriods.triangleGenerator₂
          PeriodFamily.Meridians.normalizedRegularMeridianRightPoint).symm
      rfl)

private abbrev PeriodFamily.BoundaryRadius.SmallRadius :=
  Set.Ioc (0 : ℝ) (1 / 2)

private def PeriodFamily.BoundaryRadius.outerRadius : SmallRadius :=
  ⟨1 / 2, by norm_num⟩

private abbrev PeriodFamily.BoundaryRadius.RadiusStrip :=
  SmallRadius × ℝ

private theorem PeriodFamily.BoundaryRadius.small_circle_ne_one_mo1973_27030 (r : SmallRadius)
    (θ : ℝ) : circleMap 0 (r : ℝ) θ ≠ 1 := by
  intro h
  have hn := norm_circleMap_zero (r : ℝ) θ
  rw [h, NormOneClass.norm_one, abs_of_pos r.property.1] at hn
  have hr := r.property.2
  linarith

private theorem PeriodFamily.BoundaryRadius.radialCoordinate_mem_mo1973_27031 (b : Bool)
    (x : RadiusStrip) :
    (if b then 1 - circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2)
      else circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2)) ∈
      SpecialPeriods.Triangle.twicePuncturedPlaneDomain := by
  have h₀ := circleMap_ne_center (ne_of_gt x.1.property.1) (c := (0 : ℂ)) (θ := 2 * Real.pi * x.2)
  have h₁ := small_circle_ne_one_mo1973_27030 x.1 (2 * Real.pi * x.2)
  cases b
  · exact ⟨h₀, h₁⟩
  · constructor
    · exact sub_ne_zero.mpr h₁.symm
    · intro h
      exact h₀ (sub_eq_self.mp h)

private def PeriodFamily.BoundaryRadius.radialCoordinate (b : Bool) :
    C(RadiusStrip, SpecialPeriods.Triangle.TwicePuncturedPlane) :=
  ⟨fun x =>
    ⟨if b then 1 - circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2)
      else circleMap 0 (x.1 : ℝ) (2 * Real.pi * x.2),
      radialCoordinate_mem_mo1973_27031 b x⟩,
    by
    apply Continuous.subtype_mk
    cases b <;> dsimp [circleMap] <;> fun_prop⟩

private def PeriodFamily.BoundaryCircleSlits.shiftedTrigPoint (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) : ℂ :=
  ⟨(if b then 1 else 0) + (r : ℝ) * Real.sin (2 * Real.pi * t),
    -(r : ℝ) * Real.cos (2 * Real.pi * t)⟩

private theorem PeriodFamily.BoundaryCircleSlits.shiftedTrigPoint_re_ne_mo1973_27039 (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) (hs : Real.sin (2 * Real.pi * t) ≠ 0) :
    (shiftedTrigPoint b r t).re ≠ 0 ∧ (shiftedTrigPoint b r t).re ≠ 1 := by
  have hp : (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 0 := mul_ne_zero (ne_of_gt r.property.1) hs
  have hle : (r : ℝ) * Real.sin (2 * Real.pi * t) ≤ (r : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.sin_le_one (2 * Real.pi * t)) r.property.1.le
  have hge : -(r : ℝ) ≤ (r : ℝ) * Real.sin (2 * Real.pi * t) := by
    simpa only [mul_neg, mul_one] using
      mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (2 * Real.pi * t)) r.property.1.le
  have hr := r.property.2
  cases b with
  |
    false =>
    change
      0 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 0 ∧ 0 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 1
    constructor
    · simpa only [zero_add] using hp
    · linarith
  |
    true =>
    change
      1 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 0 ∧ 1 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 1
    constructor
    · linarith
    · intro h
      apply hp
      linarith

private theorem PeriodFamily.BoundaryCircleSlits.sin_two_pi_pos_mo1973_27040 {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1 / 2) : 0 < Real.sin (2 * Real.pi * t) := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi ht0)
  calc
    2 * Real.pi * t < 2 * Real.pi * (1 / 2) := mul_lt_mul_of_pos_left ht1 hpi
    _ = Real.pi := by ring

private theorem PeriodFamily.BoundaryCircleSlits.sin_two_pi_neg_mo1973_27041 {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 0) : Real.sin (2 * Real.pi * t) < 0 := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  apply Real.sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_pos_of_neg hpi ht1)
  calc
    -Real.pi = 2 * Real.pi * (-(1 / 2 : ℝ)) := by ring
    _ < 2 * Real.pi * t := mul_lt_mul_of_pos_left ht0 hpi

private theorem PeriodFamily.BoundaryCircleSlits.shiftedTrigPoint_upper (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    shiftedTrigPoint b r t ∈ SpecialPeriods.Triangle.upperSlitPlane := by
  rcases lt_trichotomy t (1 / 2) with h | h | h
  · exact
      Or.inr
        (shiftedTrigPoint_re_ne_mo1973_27039 b r t (ne_of_gt (sin_two_pi_pos_mo1973_27040 ht0 h)))
  · apply Or.inl
    change 0 < -(r : ℝ) * Real.cos (2 * Real.pi * t)
    rw [h, show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi]
    simpa only [mul_neg, mul_one, neg_neg] using r.property.1
  · have hs := sin_two_pi_neg_mo1973_27041 (t := t - 1) (by linarith) (by linarith)
    rw [show 2 * Real.pi * (t - 1) = 2 * Real.pi * t - 2 * Real.pi by ring,
      Real.sin_sub_two_pi] at hs
    exact Or.inr (shiftedTrigPoint_re_ne_mo1973_27039 b r t (ne_of_lt hs))

private theorem PeriodFamily.BoundaryCircleSlits.shiftedTrigPoint_lower (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) {t : ℝ} (ht0 : -(1 / 2 : ℝ) < t)
    (ht1 : t < 1 / 2) : shiftedTrigPoint b r t ∈ SpecialPeriods.Triangle.lowerSlitPlane := by
  rcases lt_trichotomy t 0 with h | h | h
  · exact
      Or.inr
        (shiftedTrigPoint_re_ne_mo1973_27039 b r t (ne_of_lt (sin_two_pi_neg_mo1973_27041 ht0 h)))
  · apply Or.inl
    change -(r : ℝ) * Real.cos (2 * Real.pi * t) < 0
    rw [h, MulZeroClass.mul_zero, Real.cos_zero, mul_one]
    exact neg_neg_of_pos r.property.1
  · exact
      Or.inr
        (shiftedTrigPoint_re_ne_mo1973_27039 b r t (ne_of_gt (sin_two_pi_pos_mo1973_27040 h ht1)))

private def PeriodFamily.BoundaryCircleSlits.circlePhase : Bool → ℝ
  | false => 3 / 4
  | true => 1 / 4

private def PeriodFamily.BoundaryCircleSlits.shiftedCircle (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) :
    C(ℝ, SpecialPeriods.Triangle.TwicePuncturedPlane) :=
  (PeriodFamily.BoundaryRadius.radialCoordinate b).comp
    ⟨fun t => (r, t + circlePhase b),
      continuous_const.prodMk (continuous_id.add continuous_const)⟩

@[simp]
private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_radialCoordinate (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) :
    shiftedCircle b r t = PeriodFamily.BoundaryRadius.radialCoordinate b (r, t + circlePhase b) :=
  rfl

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_coe (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ) =
      if b then 1 - circleMap 0 (r : ℝ) (2 * Real.pi * (t + circlePhase b))
      else circleMap 0 (r : ℝ) (2 * Real.pi * (t + circlePhase b)) :=
  rfl

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_re (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ).re = (if b then 1 else 0) + (r : ℝ) * Real.sin (2 * Real.pi * t) := by
  cases b
  · change
      (circleMap 0 (r : ℝ) (2 * Real.pi * (t + 3 / 4))).re =
        0 + (r : ℝ) * Real.sin (2 * Real.pi * t)
    rw [circleMap_zero_re,
      show 2 * Real.pi * (t + 3 / 4) = (2 * Real.pi * t + Real.pi) + Real.pi / 2 by ring,
      Real.cos_add_pi_div_two, Real.sin_add_pi, neg_neg, zero_add]
  · change
      (1 - circleMap 0 (r : ℝ) (2 * Real.pi * (t + 1 / 4))).re =
        1 + (r : ℝ) * Real.sin (2 * Real.pi * t)
    rw [Complex.sub_re, Complex.one_re, circleMap_zero_re,
      show 2 * Real.pi * (t + 1 / 4) = 2 * Real.pi * t + Real.pi / 2 by ring,
      Real.cos_add_pi_div_two]
    ring

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_im (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ).im = -(r : ℝ) * Real.cos (2 * Real.pi * t) := by
  cases b
  · change
      (circleMap 0 (r : ℝ) (2 * Real.pi * (t + 3 / 4))).im = -(r : ℝ) * Real.cos (2 * Real.pi * t)
    rw [circleMap_zero_im,
      show 2 * Real.pi * (t + 3 / 4) = (2 * Real.pi * t + Real.pi) + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two, Real.cos_add_pi]
    ring
  · change
      (1 - circleMap 0 (r : ℝ) (2 * Real.pi * (t + 1 / 4))).im =
        -(r : ℝ) * Real.cos (2 * Real.pi * t)
    rw [Complex.sub_im, Complex.one_im, circleMap_zero_im,
      show 2 * Real.pi * (t + 1 / 4) = 2 * Real.pi * t + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two]
    ring

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_eq_trig (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ) = shiftedTrigPoint b r t :=
  Complex.ext (shiftedCircle_re b r t) (shiftedCircle_im b r t)

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_upper (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (shiftedCircle b r t : ℂ) ∈ SpecialPeriods.Triangle.upperSlitPlane := by
  rw [shiftedCircle_eq_trig]
  exact shiftedTrigPoint_upper b r ht0 ht1

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_lower (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) {t : ℝ} (ht0 : -(1 / 2 : ℝ) < t)
    (ht1 : t < 1 / 2) : (shiftedCircle b r t : ℂ) ∈ SpecialPeriods.Triangle.lowerSlitPlane := by
  rw [shiftedCircle_eq_trig]
  exact shiftedTrigPoint_lower b r ht0 ht1

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_mem_upperSlit (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    shiftedCircle b r t ∈ SpecialPeriods.Triangle.upperSlit :=
  shiftedCircle_upper b r ht0 ht1

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_mem_lowerSlit (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) {t : ℝ} (ht0 : -(1 / 2 : ℝ) < t)
    (ht1 : t < 1 / 2) : shiftedCircle b r t ∈ SpecialPeriods.Triangle.lowerSlit :=
  shiftedCircle_lower b r ht0 ht1

private theorem PeriodFamily.BoundaryCircleSlits.smallCircle_period_mo1973_27057 (r t : ℝ) :
    circleMap 0 r (2 * Real.pi * (t + 1)) = circleMap 0 r (2 * Real.pi * t) := by
  rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring]
  exact periodic_circleMap (0 : ℂ) r (2 * Real.pi * t)

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_periodic (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) : Function.Periodic (shiftedCircle b r) 1 := by
  intro t
  apply Subtype.ext
  rw [shiftedCircle_coe, shiftedCircle_coe,
    show t + 1 + circlePhase b = (t + circlePhase b) + 1 by ring, smallCircle_period_mo1973_27057]

private theorem PeriodFamily.BoundaryCircleSlits.shiftedCircle_add_one (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) (t : ℝ) :
    shiftedCircle b r (t + 1) = shiftedCircle b r t :=
  shiftedCircle_periodic b r t

private theorem PeriodFamily.BoundaryCircleSlits.radialCoordinate_outer_positiveMeridian (b : Bool)
    (t : unitInterval) :
    PeriodFamily.BoundaryRadius.radialCoordinate b
        (PeriodFamily.BoundaryRadius.outerRadius, (t : ℝ)) =
      if b then SpecialPeriods.Triangle.positiveMeridianOne t
      else SpecialPeriods.Triangle.positiveMeridianZero t := by
  cases b
  · apply Subtype.ext
    change
      circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) =
        (SpecialPeriods.Triangle.positiveMeridianZero t : ℂ)
    exact (SpecialPeriods.Triangle.positiveMeridianZero_eq_circleMap t).symm
  · apply Subtype.ext
    change
      1 - circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) =
        (SpecialPeriods.Triangle.positiveMeridianOne t : ℂ)
    rw [← SpecialPeriods.Triangle.positiveMeridianZero_eq_circleMap,
      SpecialPeriods.Triangle.positiveMeridianZero_apply,
      SpecialPeriods.Triangle.positiveMeridianOne_apply]

private def PeriodFamily.Boundary.canonicalQuarterOverlapIndex (b : Bool) : Fin 3 :=
  if b then 2 else 1

private def PeriodFamily.Boundary.canonicalThreeQuarterOverlapIndex (b : Bool) : Fin 3 :=
  if b then 1 else 0

private def PeriodFamily.Boundary.canonicalQuarterOverlapPoint :
    (b : Bool) → PeriodFamily.Homology.overlapBase (canonicalQuarterOverlapIndex b)
  | false => PeriodFamily.Homology.middleOverlapPoint
  | true => PeriodFamily.Homology.meridianRightOverlapPoint

private def PeriodFamily.Boundary.canonicalThreeQuarterOverlapPoint :
    (b : Bool) → PeriodFamily.Homology.overlapBase (canonicalThreeQuarterOverlapIndex b)
  | false => PeriodFamily.Homology.meridianLeftOverlapPoint
  | true => PeriodFamily.Homology.middleOverlapPoint

private theorem PeriodFamily.Boundary.canonicalPositiveLift_false_half :
    canonicalPositiveLift Bool.false (1 / 2) =
      SpecialPeriods.triangleGenerator₁⁻¹ •
        PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint :=
  (canonicalPositiveLift_unit Bool.false canonicalHalfTime).trans
    compatibleMeridianLift_false_half

private theorem PeriodFamily.Boundary.canonicalPositiveLift_true_half :
    canonicalPositiveLift Bool.true (1 / 2) =
      PeriodFamily.Meridians.normalizedRegularMeridianRightPoint :=
  (canonicalPositiveLift_unit Bool.true canonicalHalfTime).trans compatibleMeridianLift_true_half

private def PeriodFamily.Boundary.canonicalPhasedLift (b : Bool) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  canonicalPositivePhaseLift b (PeriodFamily.BoundaryCircleSlits.circlePhase b)

private theorem PeriodFamily.Boundary.canonicalPhasedLift_quarter_frame (b : Bool) :
    canonicalPhasedLift b (1 / 4) =
      (PeriodFamily.Meridians.compatibleMeridianGenerator b)⁻¹ •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift
          (canonicalQuarterOverlapIndex b) (canonicalQuarterOverlapPoint b) := by
  cases b
  · change
      canonicalPositiveLift Bool.false ((1 / 4 : ℝ) + 3 / 4) =
        SpecialPeriods.triangleGenerator₁⁻¹ •
          PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 1
            PeriodFamily.Homology.middleOverlapPoint
    rw [show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num]
    simp only [canonicalPositiveLift_one, PeriodFamily.Meridians.compatibleMeridianGenerator,
      PeriodFamily.Homology.upperLift_middleOverlapPoint,
      PeriodFamily.Homology.normalizedSlitBaseLift_val]
  · change
      canonicalPositiveLift Bool.true ((1 / 4 : ℝ) + 1 / 4) =
        SpecialPeriods.triangleGenerator₂⁻¹ •
          PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 2
            PeriodFamily.Homology.meridianRightOverlapPoint
    rw [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num, canonicalPositiveLift_true_half,
      canonicalUpperRight, inv_smul_smul]

private theorem PeriodFamily.Boundary.canonicalPhasedLift_threeQuarter_frame (b : Bool) :
    canonicalPhasedLift b (3 / 4) =
      (PeriodFamily.Meridians.compatibleMeridianGenerator b)⁻¹ •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift
          (canonicalThreeQuarterOverlapIndex b) (canonicalThreeQuarterOverlapPoint b) := by
  cases b
  · change
      canonicalPositiveLift Bool.false ((3 / 4 : ℝ) + 3 / 4) =
        SpecialPeriods.triangleGenerator₁⁻¹ •
          PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 0
            PeriodFamily.Homology.meridianLeftOverlapPoint
    rw [show (3 / 4 : ℝ) + 3 / 4 = (1 / 2 : ℝ) + 1 by norm_num, canonicalUpperLeft]
    simpa only [Int.cast_one, zpow_neg_one, PeriodFamily.Meridians.compatibleMeridianGenerator,
      canonicalPositiveLift_false_half] using canonicalPositiveLift_translate Bool.false 1 (1 / 2)
  · change
      canonicalPositiveLift Bool.true ((3 / 4 : ℝ) + 1 / 4) =
        SpecialPeriods.triangleGenerator₂⁻¹ •
          PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift 1
            PeriodFamily.Homology.middleOverlapPoint
    rw [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num]
    simp only [canonicalPositiveLift_one, PeriodFamily.Meridians.compatibleMeridianGenerator,
      PeriodFamily.Homology.upperLift_middleOverlapPoint,
      PeriodFamily.Homology.normalizedSlitBaseLift_val]

private theorem PeriodFamily.Boundary.canonicalPhasedLift_quarter_project (b : Bool) :
    SpecialPeriods.triangleRegularProject (canonicalPhasedLift b (1 / 4)) =
      (canonicalQuarterOverlapPoint b).val := by
  rw [canonicalPhasedLift_quarter_frame, SpecialPeriods.triangleRegularProject_covering.map_smul,
    PeriodFamily.Homology.upperLiftOnOverlap_project]

private theorem PeriodFamily.Boundary.canonicalPhasedLift_threeQuarter_project (b : Bool) :
    SpecialPeriods.triangleRegularProject (canonicalPhasedLift b (3 / 4)) =
      (canonicalThreeQuarterOverlapPoint b).val := by
  rw [canonicalPhasedLift_threeQuarter_frame,
    SpecialPeriods.triangleRegularProject_covering.map_smul,
    PeriodFamily.Homology.upperLiftOnOverlap_project]

private def PeriodFamily.Boundary.ellipticBoundaryPhase (j : Elliptic.Kind) : ℝ :=
  PeriodFamily.BoundaryCircleSlits.circlePhase
    (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)

private theorem PeriodFamily.Boundary.ellipticBoundary_generator (j : Elliptic.Kind) :
    PeriodFamily.Meridians.compatibleMeridianGenerator
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) =
      SpecialPeriods.Triangle.ellipticGenerator j := by cases j <;> rfl

private def PeriodFamily.Boundary.ellipticBoundaryFrame (j : Elliptic.Kind) :
    SpecialPeriods.TriangleGroup :=
  nativeTailFrame j * (SpecialPeriods.Triangle.ellipticGenerator j)⁻¹

private theorem
    PeriodFamily.Boundary.nativeShiftedSquareLift_canonical (j : Elliptic.Kind) (t : ℝ) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, t) =
      nativeTailFrame j •
        canonicalPhasedLift (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)
          t :=
  nativeShiftedSquareLift_final j (ellipticBoundaryPhase j) t

private theorem PeriodFamily.Boundary.nativeShiftedSquareLift_quarter_frame (j : Elliptic.Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4) =
      ellipticBoundaryFrame j •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift
          (canonicalQuarterOverlapIndex
            (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))
          (canonicalQuarterOverlapPoint
            (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)) := by
  rw [nativeShiftedSquareLift_canonical, canonicalPhasedLift_quarter_frame,
    ellipticBoundary_generator, ellipticBoundaryFrame, SemigroupAction.mul_smul]

private theorem
    PeriodFamily.Boundary.nativeShiftedSquareLift_threeQuarter_frame (j : Elliptic.Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4) =
      ellipticBoundaryFrame j •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift
          (canonicalThreeQuarterOverlapIndex
            (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j))
          (canonicalThreeQuarterOverlapPoint
            (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)) := by
  rw [nativeShiftedSquareLift_canonical, canonicalPhasedLift_threeQuarter_frame,
    ellipticBoundary_generator, ellipticBoundaryFrame, SemigroupAction.mul_smul]

private theorem PeriodFamily.Boundary.nativeShiftedSquareLift_quarter_project (j : Elliptic.Kind) :
    SpecialPeriods.triangleRegularProject
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4)) =
      (canonicalQuarterOverlapPoint
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).val := by
  rw [nativeShiftedSquareLift_canonical, SpecialPeriods.triangleRegularProject_covering.map_smul,
    canonicalPhasedLift_quarter_project]

private theorem
    PeriodFamily.Boundary.nativeShiftedSquareLift_threeQuarter_project (j : Elliptic.Kind) :
    SpecialPeriods.triangleRegularProject
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4)) =
      (canonicalThreeQuarterOverlapPoint
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).val := by
  rw [nativeShiftedSquareLift_canonical, SpecialPeriods.triangleRegularProject_covering.map_smul,
    canonicalPhasedLift_threeQuarter_project]

private theorem PeriodFamily.Boundary.ellipticBoundaryFrame_inv_wangBoundary (j : Elliptic.Kind)
    (v : Lattice) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus (Elliptic.flatTorusAffine j v))
        (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv (ellipticBoundaryFrame j)⁻¹ n
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a := by
  rw [ellipticBoundaryFrame, mul_inv_rev, inv_inv, triangleHomologyEquiv_mul_apply,
    nativeTailFrame_inv_wangBoundary, ellipticWangBoundary_generator_fixed]

private theorem PeriodFamily.Boundary.canonicalRadialCoordinate_periodic (b : Bool)
    (r : PeriodFamily.BoundaryRadius.SmallRadius) :
    Function.Periodic (fun t : ℝ => PeriodFamily.BoundaryRadius.radialCoordinate b (r, t)) 1 := by
  intro t
  have h :=
    PeriodFamily.BoundaryCircleSlits.shiftedCircle_add_one b r
      (t - PeriodFamily.BoundaryCircleSlits.circlePhase b)
  simpa only [PeriodFamily.BoundaryCircleSlits.shiftedCircle_radialCoordinate,
    show
        t - PeriodFamily.BoundaryCircleSlits.circlePhase b + 1 +
            PeriodFamily.BoundaryCircleSlits.circlePhase b =
          t + 1
        by ring,
    sub_add_cancel] using h

private theorem PeriodFamily.Boundary.canonicalRadialOuter_unit (b : Bool) (t : unitInterval) :
    PeriodFamily.BoundaryRadius.radialCoordinate b
        (PeriodFamily.BoundaryRadius.outerRadius, (t : ℝ)) =
      PeriodFamily.Meridians.compatiblePlanarMeridian b t := by
  rw [PeriodFamily.BoundaryCircleSlits.radialCoordinate_outer_positiveMeridian,
    PeriodFamily.Meridians.compatiblePlanarMeridian_eq,
    ite_eq_right (not_lt.mpr normalizationOrientation_nonpos)]
  cases b <;> rfl

private theorem PeriodFamily.Boundary.canonicalPositiveLift_coordinate (b : Bool) (t : ℝ) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (canonicalPositiveLift b t)) =
      PeriodFamily.BoundaryRadius.radialCoordinate b
        (PeriodFamily.BoundaryRadius.outerRadius, t) := by
  have hp :
    Function.Periodic
      (fun u : ℝ =>
        SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject (canonicalPositiveLift b u)))
      1 := by
    intro u
    simp only [canonicalPositiveLift_projection,
      PeriodFamily.BoundaryLoopSquares.loopPeriodic_add_one]
  have hu (u : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (canonicalPositiveLift b (u : ℝ))) =
      PeriodFamily.Meridians.compatiblePlanarMeridian b u := by
    rw [canonicalPositiveLift_projection, PeriodFamily.BoundaryLoopSquares.loopPeriodic_unit,
      PeriodFamily.Meridians.compatibleRegularMeridian_coordinate]
  have hpositive :=
    PeriodFamily.BoundaryLoopSquares.loopPeriodic_unique (p :=
      PeriodFamily.Meridians.compatiblePlanarMeridian b)
      (fun u : ℝ =>
        SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject (canonicalPositiveLift b u)))
      hp hu
  have hradial :=
    PeriodFamily.BoundaryLoopSquares.loopPeriodic_unique (p :=
      PeriodFamily.Meridians.compatiblePlanarMeridian b)
      (fun u : ℝ =>
        PeriodFamily.BoundaryRadius.radialCoordinate b
          (PeriodFamily.BoundaryRadius.outerRadius, u))
      (canonicalRadialCoordinate_periodic b PeriodFamily.BoundaryRadius.outerRadius)
      (canonicalRadialOuter_unit b)
  exact (congrFun hpositive t).trans (congrFun hradial t).symm

private theorem PeriodFamily.Boundary.canonicalPhasedLift_coordinate (b : Bool) (t : ℝ) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (canonicalPhasedLift b t)) =
      PeriodFamily.BoundaryCircleSlits.shiftedCircle b PeriodFamily.BoundaryRadius.outerRadius
        t := by
  change
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject
          (canonicalPositiveLift b (t + PeriodFamily.BoundaryCircleSlits.circlePhase b))) =
      PeriodFamily.BoundaryRadius.radialCoordinate b
        (PeriodFamily.BoundaryRadius.outerRadius,
          t + PeriodFamily.BoundaryCircleSlits.circlePhase b)
  exact canonicalPositiveLift_coordinate b (t + PeriodFamily.BoundaryCircleSlits.circlePhase b)

private theorem
    PeriodFamily.Boundary.canonicalPhasedLift_mem_upperSlit (b : Bool) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (canonicalPhasedLift b t)) ∈
      SpecialPeriods.Triangle.upperSlit := by
  rw [canonicalPhasedLift_coordinate]
  exact
    PeriodFamily.BoundaryCircleSlits.shiftedCircle_mem_upperSlit b
      PeriodFamily.BoundaryRadius.outerRadius ht0 ht1

private theorem PeriodFamily.Boundary.canonicalPhasedLift_mem_lowerSlit (b : Bool) {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 1 / 2) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (canonicalPhasedLift b t)) ∈
      SpecialPeriods.Triangle.lowerSlit := by
  rw [canonicalPhasedLift_coordinate]
  exact
    PeriodFamily.BoundaryCircleSlits.shiftedCircle_mem_lowerSlit b
      PeriodFamily.BoundaryRadius.outerRadius ht0 ht1

private theorem
    PeriodFamily.Boundary.canonicalPhasedLift_mem_upperBase (b : Bool) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    SpecialPeriods.triangleRegularProject (canonicalPhasedLift b t) ∈
      PeriodFamily.Homology.upperBase := by
  rw [PeriodFamily.Homology.mem_regularOpen]
  exact canonicalPhasedLift_mem_upperSlit b ht0 ht1

private theorem PeriodFamily.Boundary.canonicalPhasedLift_mem_lowerBase (b : Bool) {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 1 / 2) :
    SpecialPeriods.triangleRegularProject (canonicalPhasedLift b t) ∈
      PeriodFamily.Homology.lowerBase := by
  rw [PeriodFamily.Homology.mem_regularOpen]
  exact canonicalPhasedLift_mem_lowerSlit b ht0 ht1

private def PeriodFamily.Boundary.ellipticSlitBoundaryMap (j : Elliptic.Kind) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j,
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space) :=
  normalizedEllipticBoundaryMap j (ellipticBoundaryPhase j)

private theorem
    PeriodFamily.Boundary.ellipticSlitBoundaryMap_projection_mk (j : Elliptic.Kind) (t : ℝ)
    (x : RealTorus₄) :
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).projection
        (ellipticSlitBoundaryMap j
          (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x))) =
      SpecialPeriods.triangleRegularProject
        (canonicalPhasedLift (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)
          t) := by
  rw [ellipticSlitBoundaryMap, normalizedEllipticBoundaryMap_mk,
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).projection_quotient]
  change
    SpecialPeriods.triangleRegularProject
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, t)) =
      _
  rw [nativeShiftedSquareLift_canonical, SpecialPeriods.triangleRegularProject_covering.map_smul]

private theorem PeriodFamily.Boundary.ellipticSlitBoundaryMap_upper (j : Elliptic.Kind) :
    Set.MapsTo (ellipticSlitBoundaryMap j)
      (MappingTorus.HomologyCover.U (Elliptic.flatTorusAffine j j.twist))
      (PeriodFamily.Homology.upperFamily
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)) := by
  intro q hq
  let p := MappingTorus.HomologyCover.chartU (Elliptic.flatTorusAffine j j.twist) ⟨q, hq⟩
  have hp : MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) ((p.1 : ℝ), p.2) = q :=
    MappingTorus.HomologyCover.chartU_representation (Elliptic.flatTorusAffine j j.twist) ⟨q, hq⟩
  rw [← hp]
  change
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).projection
        (ellipticSlitBoundaryMap j
          (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) ((p.1 : ℝ), p.2))) ∈
      PeriodFamily.Homology.upperBase
  rw [ellipticSlitBoundaryMap_projection_mk]
  exact
    canonicalPhasedLift_mem_upperBase
      (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) p.1.property.1
      p.1.property.2

private theorem PeriodFamily.Boundary.ellipticSlitBoundaryMap_lower (j : Elliptic.Kind) :
    Set.MapsTo (ellipticSlitBoundaryMap j)
      (MappingTorus.HomologyCover.V (Elliptic.flatTorusAffine j j.twist))
      (PeriodFamily.Homology.lowerFamily
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)) := by
  intro q hq
  let p := MappingTorus.HomologyCover.chartV (Elliptic.flatTorusAffine j j.twist) ⟨q, hq⟩
  have hp : MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) ((p.1 : ℝ), p.2) = q :=
    MappingTorus.HomologyCover.chartV_representation (Elliptic.flatTorusAffine j j.twist) ⟨q, hq⟩
  rw [← hp]
  change
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).projection
        (ellipticSlitBoundaryMap j
          (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) ((p.1 : ℝ), p.2))) ∈
      PeriodFamily.Homology.lowerBase
  rw [ellipticSlitBoundaryMap_projection_mk]
  exact
    canonicalPhasedLift_mem_lowerBase
      (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) p.1.property.1
      p.1.property.2

private theorem PeriodFamily.Boundary.boundaryRegularHomologyMap_slit (j : Elliptic.Kind) (n : ℕ) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) n =
      SingularMayerVietoris.singularHomologyMap (ellipticSlitBoundaryMap j) n :=
  boundaryRegularHomologyMap_normalized j (ellipticBoundaryPhase j) n

private def PeriodFamily.Boundary.ellipticLowerColumn (j : Elliptic.Kind) :
    C(RealTorus₄,
      PeriodFamily.Homology.familyIntersection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)) :=
  lowerColumnMap (Elliptic.flatTorusAffine j j.twist)
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
    (ellipticSlitBoundaryMap j) (ellipticSlitBoundaryMap_upper j)
    (ellipticSlitBoundaryMap_lower j)

private def PeriodFamily.Boundary.ellipticUpperColumn (j : Elliptic.Kind) :
    C(RealTorus₄,
      PeriodFamily.Homology.familyIntersection
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)) :=
  upperColumnMap (Elliptic.flatTorusAffine j j.twist)
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
    (ellipticSlitBoundaryMap j) (ellipticSlitBoundaryMap_upper j)
    (ellipticSlitBoundaryMap_lower j)

private theorem PeriodFamily.Boundary.ellipticLowerColumn_coe (j : Elliptic.Kind) (x : RealTorus₄) :
    (ellipticLowerColumn j x).val =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4),
          nativeGaugeCylinder j (ellipticBoundaryPhase j) (1 / 4, x)) := by
  rw [ellipticLowerColumn, lowerColumnMap_coe]
  exact normalizedEllipticBoundaryMap_mk j (ellipticBoundaryPhase j) (1 / 4) x

private theorem PeriodFamily.Boundary.ellipticUpperColumn_coe (j : Elliptic.Kind) (x : RealTorus₄) :
    (ellipticUpperColumn j x).val =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4),
          nativeGaugeCylinder j (ellipticBoundaryPhase j) (3 / 4, x)) := by
  rw [ellipticUpperColumn, upperColumnMap_coe]
  exact normalizedEllipticBoundaryMap_mk j (ellipticBoundaryPhase j) (3 / 4) x

private def PeriodFamily.Boundary.ellipticLowerColumnIndex (j : Elliptic.Kind) : Fin 3 :=
  if SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j then 2 else 0

private def PeriodFamily.Boundary.ellipticUpperColumnIndex (j : Elliptic.Kind) : Fin 3 :=
  if SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j then 0 else 1

private theorem PeriodFamily.Boundary.ellipticLowerColumnIndex_overlap (j : Elliptic.Kind) :
    PeriodFamily.Homology.intersectionIndex (ellipticLowerColumnIndex j) =
      canonicalQuarterOverlapIndex
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) := by
  cases j <;> decide

private theorem PeriodFamily.Boundary.ellipticUpperColumnIndex_overlap (j : Elliptic.Kind) :
    PeriodFamily.Homology.intersectionIndex (ellipticUpperColumnIndex j) =
      canonicalThreeQuarterOverlapIndex
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j) := by
  cases j <;> decide

private def PeriodFamily.Boundary.ellipticLowerColumnPoint (j : Elliptic.Kind) :
    PeriodFamily.Homology.overlapBase
      (PeriodFamily.Homology.intersectionIndex (ellipticLowerColumnIndex j)) :=
  ⟨(canonicalQuarterOverlapPoint
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).val,
    by
    rw [ellipticLowerColumnIndex_overlap]
    exact
      (canonicalQuarterOverlapPoint
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).property⟩

private def PeriodFamily.Boundary.ellipticUpperColumnPoint (j : Elliptic.Kind) :
    PeriodFamily.Homology.overlapBase
      (PeriodFamily.Homology.intersectionIndex (ellipticUpperColumnIndex j)) :=
  ⟨(canonicalThreeQuarterOverlapPoint
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).val,
    by
    rw [ellipticUpperColumnIndex_overlap]
    exact
      (canonicalThreeQuarterOverlapPoint
          (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).property⟩

private theorem PeriodFamily.Boundary.ellipticLowerColumn_mem (j : Elliptic.Kind) (x : RealTorus₄) :
    ellipticLowerColumn j x ∈
      PeriodFamily.Homology.intersectionPiece
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (ellipticLowerColumnIndex j) := by
  change
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).projection
        (ellipticLowerColumn j x).val ∈
      PeriodFamily.Homology.overlapBase
        (PeriodFamily.Homology.intersectionIndex (ellipticLowerColumnIndex j))
  rw [ellipticLowerColumn_coe,
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).projection_quotient]
  change
    SpecialPeriods.triangleRegularProject
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4)) ∈
      _
  rw [nativeShiftedSquareLift_quarter_project, ellipticLowerColumnIndex_overlap]
  exact
    (canonicalQuarterOverlapPoint
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).property

private theorem PeriodFamily.Boundary.ellipticUpperColumn_mem (j : Elliptic.Kind) (x : RealTorus₄) :
    ellipticUpperColumn j x ∈
      PeriodFamily.Homology.intersectionPiece
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (ellipticUpperColumnIndex j) := by
  change
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).projection
        (ellipticUpperColumn j x).val ∈
      PeriodFamily.Homology.overlapBase
        (PeriodFamily.Homology.intersectionIndex (ellipticUpperColumnIndex j))
  rw [ellipticUpperColumn_coe,
    ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁
        SpecialPeriods.specialPeriodMap_generator₂)).projection_quotient]
  change
    SpecialPeriods.triangleRegularProject
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4)) ∈
      _
  rw [nativeShiftedSquareLift_threeQuarter_project, ellipticUpperColumnIndex_overlap]
  exact
    (canonicalThreeQuarterOverlapPoint
        (SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j)).property

private theorem PeriodFamily.Boundary.ellipticLowerColumn_frame (j : Elliptic.Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4) =
      ellipticBoundaryFrame j •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift
          (PeriodFamily.Homology.intersectionIndex (ellipticLowerColumnIndex j))
          (ellipticLowerColumnPoint j) := by
  cases j <;> exact nativeShiftedSquareLift_quarter_frame _

private theorem PeriodFamily.Boundary.ellipticUpperColumn_frame (j : Elliptic.Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4) =
      ellipticBoundaryFrame j •
        PeriodFamily.Homology.upperLiftOnOverlap PeriodFamily.Homology.normalizedSlitBaseLift
          (PeriodFamily.Homology.intersectionIndex (ellipticUpperColumnIndex j))
          (ellipticUpperColumnPoint j) := by
  cases j <;> exact nativeShiftedSquareLift_threeQuarter_frame _

private theorem
    PeriodFamily.Boundary.nativeGaugeCylinder_fibre_translation (j : Elliptic.Kind) (τ t : ℝ)
    (x : RealTorus₄) : nativeGaugeCylinder j τ (t, x) = x + nativeGaugeCylinder j τ (t, 0) := by
  simp only [nativeGaugeCylinder_apply, zero_add]

private theorem PeriodFamily.Boundary.ellipticLowerColumn_homology (j : Elliptic.Kind) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap (ellipticLowerColumn j) n a) =
      componentCoordinates (ellipticLowerColumnIndex j)
        (PeriodFamily.Homology.triangleHomologyEquiv (ellipticBoundaryFrame j)⁻¹ n a) := by
  have h :=
    intersectionHomology_component_affine
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      PeriodFamily.Homology.normalizedSlitBaseLift (ellipticLowerColumn j)
      (ellipticLowerColumnIndex j) (ellipticLowerColumn_mem j) (ellipticLowerColumnPoint j)
      (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4)) (ellipticBoundaryFrame j)
      (ellipticLowerColumn_frame j) (ContinuousMap.id RealTorus₄)
      (nativeGaugeCylinder j (ellipticBoundaryPhase j) (1 / 4, 0))
      (fun x => by
        rw [ellipticLowerColumn_coe, nativeGaugeCylinder_fibre_translation]
        rfl)
      n a
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h
  exact h

private theorem PeriodFamily.Boundary.ellipticUpperColumn_homology (j : Elliptic.Kind) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap (ellipticUpperColumn j) n a) =
      componentCoordinates (ellipticUpperColumnIndex j)
        (PeriodFamily.Homology.triangleHomologyEquiv (ellipticBoundaryFrame j)⁻¹ n a) := by
  have h :=
    intersectionHomology_component_affine
      (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
      PeriodFamily.Homology.normalizedSlitBaseLift (ellipticUpperColumn j)
      (ellipticUpperColumnIndex j) (ellipticUpperColumn_mem j) (ellipticUpperColumnPoint j)
      (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4)) (ellipticBoundaryFrame j)
      (ellipticUpperColumn_frame j) (ContinuousMap.id RealTorus₄)
      (nativeGaugeCylinder j (ellipticBoundaryPhase j) (3 / 4, 0))
      (fun x => by
        rw [ellipticUpperColumn_coe, nativeGaugeCylinder_fibre_translation]
        rfl)
      n a
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h
  exact h

private theorem PeriodFamily.Boundary.ellipticLowerColumn_wangBoundary (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus (Elliptic.flatTorusAffine j j.twist)) (n + 1)) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap (ellipticLowerColumn j) n
          (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a)) =
      componentCoordinates (ellipticLowerColumnIndex j)
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a) := by
  rw [ellipticLowerColumn_homology, ellipticBoundaryFrame_inv_wangBoundary]

private theorem PeriodFamily.Boundary.ellipticUpperColumn_wangBoundary (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus (Elliptic.flatTorusAffine j j.twist)) (n + 1)) :
    PeriodFamily.Homology.intersectionHomologyEquiv
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        PeriodFamily.Homology.normalizedSlitBaseLift n
        (SingularMayerVietoris.singularHomologyMap (ellipticUpperColumn j) n
          (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a)) =
      componentCoordinates (ellipticUpperColumnIndex j)
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a) := by
  rw [ellipticUpperColumn_homology, ellipticBoundaryFrame_inv_wangBoundary]

private theorem PeriodFamily.Boundary.normalizedSourceDomainEquiv_nonpos (n : ℕ)
    (x :
      SingularMayerVietoris.SingularHomology RealTorus₄ n ×
        SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    PeriodFamily.Homology.normalizedSourceDomainEquiv n x =
      (x.1, -(PeriodFamily.Homology.generatorHomologyEquiv Bool.true n).symm x.2) := by
  rw [PeriodFamily.Homology.normalizedSourceDomainEquiv,
    ite_eq_right (not_lt.mpr normalizationOrientation_nonpos),
    TrianglePeriodFamilyHomologyAlgebra.inverseSecondCoordinate_apply]

private theorem PeriodFamily.Boundary.ellipticWangBoundary_generator_inv_fixed (j : Elliptic.Kind)
    (v : Lattice) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus (Elliptic.flatTorusAffine j v))
        (n + 1)) :
    PeriodFamily.Homology.triangleHomologyEquiv (SpecialPeriods.Triangle.ellipticGenerator j)⁻¹ n
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j v) n a := by
  rw [PeriodFamily.Homology.triangleHomologyEquiv_inv]
  apply
    (PeriodFamily.Homology.triangleHomologyEquiv (SpecialPeriods.Triangle.ellipticGenerator j)
        n).injective
  rw [LinearEquiv.apply_symm_apply, ellipticWangBoundary_generator_fixed]

private theorem PeriodFamily.Boundary.ellipticBoundary_sourceKernelProjection_components
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus (Elliptic.flatTorusAffine j j.twist)) (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      PeriodFamily.Homology.normalizedSourceDomainEquiv n
        (-componentCoordinates (ellipticLowerColumnIndex j)
                (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a) +
            componentCoordinates (ellipticUpperColumnIndex j)
              (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a)).2 := by
  refine
    (congrArg
          (fun z :
              SingularMayerVietoris.SingularHomology
                ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                    SpecialPeriods.specialPeriodMap_generator₁
                    SpecialPeriods.specialPeriodMap_generator₂)).Space
                (n + 1) =>
            (PeriodFamily.Homology.sourceKernelProjection
                (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                  SpecialPeriods.specialPeriodMap_generator₁
                  SpecialPeriods.specialPeriodMap_generator₂)
                n z :
              SingularMayerVietoris.SingularHomology RealTorus₄ n ×
                SingularMayerVietoris.SingularHomology RealTorus₄ n))
          (LinearMap.congr_fun (boundaryRegularHomologyMap_slit j (n + 1)) a)).trans
      ?_
  refine
    (sourceKernelProjection_wangBoundary
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          (Elliptic.flatTorusAffine j j.twist) (ellipticSlitBoundaryMap j)
          (ellipticSlitBoundaryMap_upper j) (ellipticSlitBoundaryMap_lower j) n a).trans
      ?_
  rw [intersectionComparison_antidiagonal, intersectionComparison_lowerColumn,
    intersectionComparison_upperColumn]
  change
    PeriodFamily.Homology.normalizedSourceDomainEquiv n
        (-PeriodFamily.Homology.intersectionHomologyEquiv
                (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                  SpecialPeriods.specialPeriodMap_generator₁
                  SpecialPeriods.specialPeriodMap_generator₂)
                PeriodFamily.Homology.normalizedSlitBaseLift n
                (SingularMayerVietoris.singularHomologyMap (ellipticLowerColumn j) n
                  (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a)) +
            PeriodFamily.Homology.intersectionHomologyEquiv
              (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
                SpecialPeriods.specialPeriodMap_generator₁
                SpecialPeriods.specialPeriodMap_generator₂)
              PeriodFamily.Homology.normalizedSlitBaseLift n
              (SingularMayerVietoris.singularHomologyMap (ellipticUpperColumn j) n
                (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a))).2 =
      _
  rw [ellipticLowerColumn_wangBoundary, ellipticUpperColumn_wangBoundary]

private theorem
    PeriodFamily.Boundary.ellipticBoundary_sourceKernelProjection (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus (Elliptic.flatTorusAffine j j.twist)) (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      if SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex j then
        (0, MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a)
      else (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a, 0) := by
  rw [ellipticBoundary_sourceKernelProjection_components, normalizedSourceDomainEquiv_nonpos]
  cases j with
  | three =>
    simp [componentCoordinates, ellipticLowerColumnIndex, ellipticUpperColumnIndex,
      SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex]
  |
    four =>
    have hw := ellipticWangBoundary_generator_inv_fixed .four Elliptic.Kind.four.twist n a
    rw [PeriodFamily.Homology.triangleHomologyEquiv_inv] at hw
    change
      (PeriodFamily.Homology.generatorHomologyEquiv Bool.true n).symm
          (MappingTorusHomology.wangBoundary
            (Elliptic.flatTorusAffine .four Elliptic.Kind.four.twist) n a) =
        MappingTorusHomology.wangBoundary
          (Elliptic.flatTorusAffine .four Elliptic.Kind.four.twist) n a at hw
    simpa [componentCoordinates, ellipticLowerColumnIndex, ellipticUpperColumnIndex,
      SpecialPeriods.Threefold.EllipticGeometry.attachingMeridianIndex] using hw

private theorem PeriodFamily.Boundary.ellipticThreeBoundary_sourceKernelProjection (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus (Elliptic.flatTorusAffine .three Elliptic.Kind.three.twist))
        (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
            (Option.some Elliptic.Kind.three) (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      (MappingTorusHomology.wangBoundary
          (Elliptic.flatTorusAffine .three Elliptic.Kind.three.twist) n a,
        0) :=
  ellipticBoundary_sourceKernelProjection .three n a

private theorem PeriodFamily.Boundary.ellipticFourBoundary_sourceKernelProjection (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus (Elliptic.flatTorusAffine .four Elliptic.Kind.four.twist)) (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          n
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
            (Option.some Elliptic.Kind.four) (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      (0,
        MappingTorusHomology.wangBoundary
          (Elliptic.flatTorusAffine .four Elliptic.Kind.four.twist) n a) :=
  ellipticBoundary_sourceKernelProjection .four n a

private theorem PeriodFamily.Boundary.Cusp.boundary_sourceKernelProjection_components (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection
          ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData n
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      PeriodFamily.Homology.normalizedSourceDomainEquiv n
        (-PeriodFamily.Boundary.componentCoordinates 1
                (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
                  (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
                    a)) +
            PeriodFamily.Boundary.componentCoordinates 2
              (PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
                (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
                  a))).2 := by
  refine
    (congrArg
          (fun z :
              SingularMayerVietoris.SingularHomology
                ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData.Space (n + 1) =>
            (PeriodFamily.Homology.sourceKernelProjection
                ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData n z :
              SingularMayerVietoris.SingularHomology RealTorus₄ n ×
                SingularMayerVietoris.SingularHomology RealTorus₄ n))
          (LinearMap.congr_fun (boundaryRegularHomologyMap_normalized (n + 1)) a)).trans
      ?_
  refine
    (PeriodFamily.Boundary.RefinedWang.sourceKernelProjection_quarterColumns
          ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
          ThreefoldOverlapMappingTorus.Cusp.monodromy normalizedBoundaryMap
          normalizedBoundaryMap_upper normalizedBoundaryMap_lower n a).trans
      ?_
  change
    PeriodFamily.Homology.normalizedSourceDomainEquiv n
        (-PeriodFamily.Homology.intersectionHomologyEquiv
                ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
                PeriodFamily.Homology.normalizedSlitBaseLift n
                (SingularMayerVietoris.singularHomologyMap lowerColumn n
                  (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
                    a)) +
            PeriodFamily.Homology.intersectionHomologyEquiv
              ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
              PeriodFamily.Homology.normalizedSlitBaseLift n
              (SingularMayerVietoris.singularHomologyMap upperColumn n
                (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
                  a))).2 =
      _
  rw [lowerColumn_wangBoundary, upperColumn_wangBoundary]

private theorem PeriodFamily.Boundary.Cusp.boundary_sourceKernelProjection (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) (n + 1)) :
    (PeriodFamily.Homology.sourceKernelProjection
          ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData n
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none (n + 1) a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ n ×
          SingularMayerVietoris.SingularHomology RealTorus₄ n) =
      (-PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
            (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a),
        -MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a) := by
  rw [boundary_sourceKernelProjection_components,
    PeriodFamily.Boundary.normalizedSourceDomainEquiv_nonpos]
  simpa only [PeriodFamily.Boundary.componentCoordinates_one,
    PeriodFamily.Boundary.componentCoordinates_two, Prod.neg_mk, Prod.mk_add_mk, neg_zero,
    zero_add, add_zero] using
    congrArg
      (fun b : SingularMayerVietoris.SingularHomology RealTorus₄ n =>
        (-PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ n
              (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n a),
          -b))
      (wangBoundary_inverse_word n a)

private theorem PeriodFamily.Boundary.Cusp.boundary_four_sourceKernelProjection
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Torus ThreefoldOverlapMappingTorus.Cusp.monodromy) 4) :
    (PeriodFamily.Homology.sourceKernelProjection
          ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData 3
          (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 4 a) :
        SingularMayerVietoris.SingularHomology RealTorus₄ 3 ×
          SingularMayerVietoris.SingularHomology RealTorus₄ 3) =
      (-PeriodFamily.Homology.triangleHomologyEquiv SpecialPeriods.triangleGenerator₁⁻¹ 3
            (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3 a),
        -MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3 a) :=
  boundary_sourceKernelProjection 3 a

private def PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4Equiv (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) 4 ≃ₗ[ℤ]
      (ℤ × (Fin 2 → ℤ)) :=
  ((boundaryCapHomologyEquiv j 3).toAddEquiv.trans
      ((Elliptic.HigherHomology.surfaceH4Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData
                j).centralPeriod).toAddEquiv.prodCongr
        (Elliptic.HigherHomology.surfaceH3Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData
                j).centralPeriod).toAddEquiv)).toIntLinearEquiv

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4Equiv_apply (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) 4) :
    boundaryCapH4Equiv j a =
      (Elliptic.HigherHomology.surfaceH4Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
          (boundaryCapHomologyEquiv j 3 a).1,
        Elliptic.HigherHomology.surfaceH3Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
          (boundaryCapHomologyEquiv j 3 a).2) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_H4_first
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) 4) :
    Elliptic.HigherHomology.surfaceH4Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4
          (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4 a)) =
      (boundaryCapH4Equiv j a).1 := by
  rw [boundaryFillingHomologyMap_first]
  rfl

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4Equiv_section (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 4) :
    boundaryCapH4Equiv j (SingularMayerVietoris.singularHomologyMap (capSection j) 4 a) =
      (Elliptic.HigherHomology.surfaceH4Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a,
        0) := by
  rw [boundaryCapH4Equiv_apply, boundaryCapHomologyEquiv_section]
  simp only [map_zero]

private def
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4CoordinatesMap (j : Elliptic.Kind) :
    (ℤ × (Fin 2 → ℤ)) →ₗ[ℤ] ℤ :=
  (Elliptic.HigherHomology.surfaceH4Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).toLinearMap.comp
    ((ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4).toLinearMap.comp
      ((ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4).comp
        (boundaryCapH4Equiv j).symm.toLinearMap))

private def PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4KernelEquiv (j : Elliptic.Kind) :
    LinearMap.ker
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4) ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (boundaryCapKernelEquiv j 3).trans
    (Elliptic.HigherHomology.surfaceH3Equiv j
      (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4KernelEquiv_symm_val
    (j : Elliptic.Kind) (a : Fin 2 → ℤ) :
    ((boundaryCapH4KernelEquiv j).symm a).val =
      boundaryPositiveCircleCross j 3
        ((Elliptic.HigherHomology.surfaceH3Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
          a) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflection_mk_shifted {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (t : ℝ)
    (x : X) : F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (1 - t, g.symm (G t x)) := by
  rw [hF]
  calc
    MappingTorus.mk g (-t, G t x) = MappingTorus.mk g (-t + 1, g.symm (G t x)) := by
      rw [MappingTorus.mk_add_one, Homeomorph.apply_symm_apply]
    _ = MappingTorus.mk g (1 - t, g.symm (G t x)) :=
      congrArg (fun s : ℝ => MappingTorus.mk g (s, g.symm (G t x))) (by ring)

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflection_mapsTo_U {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) :
    Set.MapsTo F (MappingTorus.HomologyCover.U f) (MappingTorus.HomologyCover.U g) := by
  intro q hq
  let p := MappingTorus.HomologyCover.chartU f ⟨q, hq⟩
  let t : Set.Ioo (0 : ℝ) 1 :=
    ⟨1 - (p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  have he :
    F q =
      ((MappingTorus.HomologyCover.chartU g).symm (t, g.symm (G p.1 p.2)) :
        MappingTorus.Torus g) := by
    rw [MappingTorus.HomologyCover.chartU_symm_coe]
    exact
      (congrArg F (MappingTorus.HomologyCover.chartU_representation f ⟨q, hq⟩)).symm.trans
        (reflection_mk_shifted f g F G hF p.1 p.2)
  rw [he]
  exact ((MappingTorus.HomologyCover.chartU g).symm (t, g.symm (G p.1 p.2))).property

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflection_mapsTo_V {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) :
    Set.MapsTo F (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.V g) := by
  intro q hq
  let p := MappingTorus.HomologyCover.chartV f ⟨q, hq⟩
  let t : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨-(p.1 : ℝ), by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  have he :
    F q = ((MappingTorus.HomologyCover.chartV g).symm (t, G p.1 p.2) : MappingTorus.Torus g) := by
    rw [MappingTorus.HomologyCover.chartV_symm_coe]
    exact
      (congrArg F (MappingTorus.HomologyCover.chartV_representation f ⟨q, hq⟩)).symm.trans
        (hF p.1 p.2)
  rw [he]
  exact ((MappingTorus.HomologyCover.chartV g).symm (t, G p.1 p.2)).property

private def PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) :
    C((MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
        Set (MappingTorus.Torus f)),
      (MappingTorus.HomologyCover.U g ∩ MappingTorus.HomologyCover.V g :
        Set (MappingTorus.Torus g))) :=
  SingularMayerVietoris.intersectionRestriction F (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U g)
    (MappingTorus.HomologyCover.V g) (reflection_mapsTo_U f g F G hF)
    (reflection_mapsTo_V f g F G hF)

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionMap_lower {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) :
    (reflectionIntersectionMap f g F G hF).comp (PeriodFamily.Boundary.lowerComponentFibre f) =
      (PeriodFamily.Boundary.upperComponentFibre g).comp ((g.symm : C(Y, Y)).comp (G (1 / 4))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    F (PeriodFamily.Boundary.lowerComponentFibre f x).val =
      (PeriodFamily.Boundary.upperComponentFibre g (g.symm (G (1 / 4) x))).val
  rw [PeriodFamily.Boundary.lowerComponentFibre_coe,
    PeriodFamily.Boundary.upperComponentFibre_coe]
  convert reflection_mk_shifted f g F G hF (1 / 4) x using 1; norm_num

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionMap_upper {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) :
    (reflectionIntersectionMap f g F G hF).comp (PeriodFamily.Boundary.upperComponentFibre f) =
      (PeriodFamily.Boundary.lowerComponentFibre g).comp ((g.symm : C(Y, Y)).comp (G (3 / 4))) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    F (PeriodFamily.Boundary.upperComponentFibre f x).val =
      (PeriodFamily.Boundary.lowerComponentFibre g (g.symm (G (3 / 4) x))).val
  rw [PeriodFamily.Boundary.upperComponentFibre_coe,
    PeriodFamily.Boundary.lowerComponentFibre_coe]
  convert reflection_mk_shifted f g F G hF (3 / 4) x using 1; norm_num

private def PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionComparison {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x))
    (n : ℕ) :
    (SingularMayerVietoris.SingularHomology X n ×
        SingularMayerVietoris.SingularHomology X n) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology Y n × SingularMayerVietoris.SingularHomology Y n) :=
  (MappingTorusHomology.intersectionHomologyEquiv g n).toLinearMap.comp
    ((SingularMayerVietoris.singularHomologyMap (reflectionIntersectionMap f g F G hF) n).comp
      (MappingTorusHomology.intersectionHomologyEquiv f n).symm.toLinearMap)

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionComparison_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n a =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (SingularMayerVietoris.singularHomologyMap (reflectionIntersectionMap f g F G hF) n
          ((MappingTorusHomology.intersectionHomologyEquiv f n).symm a)) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionComparison_lower
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n (a, 0) =
      (0, SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (1 / 4))) n a) := by
  rw [reflectionIntersectionComparison_apply,
    PeriodFamily.Boundary.intersectionHomologyEquiv_symm_lower, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, reflectionIntersectionMap_lower,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    PeriodFamily.Boundary.upperComponentFibre_homology]

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionComparison_upper
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n (0, a) =
      (SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n a, 0) := by
  rw [reflectionIntersectionComparison_apply,
    PeriodFamily.Boundary.intersectionHomologyEquiv_symm_upper, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, reflectionIntersectionMap_upper,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    PeriodFamily.Boundary.lowerComponentFibre_homology]

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflectionIntersectionComparison_pair
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a b : SingularMayerVietoris.SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n (a, b) =
      (SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n b,
        SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (1 / 4))) n a) := by
  have hab : (a, b) = (a, (0 : SingularMayerVietoris.SingularHomology X n)) + (0, b) := by
    ext <;> simp
  rw [hab, map_add, reflectionIntersectionComparison_lower,
    reflectionIntersectionComparison_upper]
  simp

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflection_boundaryCoordinates_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (SingularMayerVietoris.singularHomologyMap (reflectionIntersectionMap f g F G hF) n
          (MappingTorusHomology.mayerVietorisConnecting f n a)) := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply F
      (MappingTorus.HomologyCover.U f) (MappingTorus.HomologyCover.V f)
      (MappingTorus.HomologyCover.U g) (MappingTorus.HomologyCover.V g)
      (reflection_mapsTo_U f g F G hF) (reflection_mapsTo_V f g F G hF)
      (MappingTorus.HomologyCover.U_open f) (MappingTorus.HomologyCover.V_open f)
      (MappingTorus.HomologyCover.cover f) (MappingTorus.HomologyCover.U_open g)
      (MappingTorus.HomologyCover.V_open g) (MappingTorus.HomologyCover.cover g) n a
  exact (congrArg (MappingTorusHomology.intersectionHomologyEquiv g n) h).symm

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflection_boundaryCoordinates_comparison
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      reflectionIntersectionComparison f g F G hF n
        (-MappingTorusHomology.wangBoundary f n a, MappingTorusHomology.wangBoundary f n a) := by
  rw [reflection_boundaryCoordinates_naturality f g F G hF,
    PeriodFamily.Boundary.mappingTorusConnecting_eq_marked_boundary f n a]
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.reflection_boundaryCoordinates_quarters
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n
          (MappingTorusHomology.wangBoundary f n a),
        -SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (1 / 4))) n
            (MappingTorusHomology.wangBoundary f n a)) := by
  rw [reflection_boundaryCoordinates_comparison f g F G hF, reflectionIntersectionComparison_pair,
    map_neg]

private theorem PeriodFamily.Boundary.EllipticCapProduct.wangBoundary_timeReflection {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.wangBoundary g n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n
          (MappingTorusHomology.wangBoundary f n a) := by
  change
    -(MappingTorusHomology.boundaryCoordinates g n
            (SingularMayerVietoris.singularHomologyMap F (n + 1) a)).1 =
      _
  rw [reflection_boundaryCoordinates_quarters f g F G hF]

private theorem PeriodFamily.Boundary.EllipticCapProduct.wangBoundary_timeReflection_of_quarter
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (F : C(MappingTorus.Torus f, MappingTorus.Torus g)) (G : ℝ → C(X, Y))
    (hF : ∀ (t : ℝ) (x : X), F (MappingTorus.mk f (t, x)) = MappingTorus.mk g (-t, G t x))
    (h : C(X, Y)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1))
    (hquarter :
      SingularMayerVietoris.singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n
          (MappingTorusHomology.wangBoundary f n a) =
        SingularMayerVietoris.singularHomologyMap h n (MappingTorusHomology.wangBoundary f n a)) :
    MappingTorusHomology.wangBoundary g n
        (SingularMayerVietoris.singularHomologyMap F (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap h n (MappingTorusHomology.wangBoundary f n a) := by
  rw [wangBoundary_timeReflection f g F G hF, hquarter]

private def PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre (j : Elliptic.Kind) (s : ℝ) :
    C(PeriodTorusHigherHomology.ProductTorus 3, RealTorus₄)
    where
  toFun
    y :=
    (Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm
      (((s / j.order : ℝ) : MappingTorus.Circle), y)
  continuous_toFun :=
    (Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm.continuous.comp
      (continuous_const.prodMk continuous_id)

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_apply (j : Elliptic.Kind) (s : ℝ)
    (y : PeriodTorusHigherHomology.ProductTorus 3) :
    capSectionFibre j s y =
      (Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm
        (((s / j.order : ℝ) : MappingTorus.Circle), y) :=
  rfl

private def PeriodFamily.Boundary.EllipticCapProduct.capSectionFibreHomotopy (j : Elliptic.Kind)
    (s t : ℝ) : (capSectionFibre j s).Homotopy (capSectionFibre j t)
    where
  toFun
    p :=
    (Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm
      (((((1 - (p.1 : ℝ)) * s + (p.1 : ℝ) * t) / j.order : ℝ) : MappingTorus.Circle), p.2)
  continuous_toFun :=
    (Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm.continuous.comp
      (((AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)).prodMk continuous_snd)
  map_zero_left y := by simp [capSectionFibre]
  map_one_left y := by simp [capSectionFibre]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_homology (j : Elliptic.Kind)
    (s t : ℝ) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (capSectionFibre j s) n =
      SingularMayerVietoris.singularHomologyMap (capSectionFibre j t) n :=
  PeriodTorusHigherHomology.homotopy_homologyMap (capSectionFibreHomotopy j s t) n

private theorem PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_coordinateProjection
    (j : Elliptic.Kind) (k : Elliptic.HigherHomology.FibreCoordinates) :
    capSectionFibre j 0 (PeriodTorusHigherHomology.coordinateProjection 3 k) =
      standardLattice.mkQ (Fin.cons 0 k) := by
  rw [capSectionFibre_apply, zero_div]
  rw [Elliptic.HigherHomology.splitFlatTorusHomeomorph_symm_coordinateProjection]
  simp only [Elliptic.HigherHomology.splitRealCoordinates_symm_apply, zero_smul, zero_add]

private def PeriodFamily.Boundary.EllipticCapProduct.capSectionFromModel (j : Elliptic.Kind) :
    C(Elliptic.HigherHomology.mappingTorusModel j,
      ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j) :=
  (capSection j).comp
    ((Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm :
      C(_, _))

private theorem PeriodFamily.Boundary.EllipticCapProduct.capSectionFromModel_mk (j : Elliptic.Kind)
    (s : ℝ) (y : PeriodTorusHigherHomology.ProductTorus 3) :
    capSectionFromModel j
        (MappingTorus.mk (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm (s, y)) =
      MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (-s, capSectionFibre j s y) := by
  apply (boundaryProductHomeomorph j).injective
  change
    boundaryProductHomeomorph j
        ((boundaryProductHomeomorph j).symm
          ((Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
              (MappingTorus.mk (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm (s, y)),
            0)) =
      _
  rw [Homeomorph.apply_symm_apply, boundaryProductHomeomorph_mk,
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk,
    Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_symm_mk]
  apply Prod.ext
  · apply
      congrArg
        (Elliptic.surfaceProjection j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
          (Elliptic.mainTwist_admissible j))
    rw [← splitPeriodTorusHomeomorph_symm_splitFlat j]
    simp only [capSectionFibre_apply, Homeomorph.apply_symm_apply]
  · simp only [capSectionFibre_apply, Homeomorph.apply_symm_apply]
    change
      (0 : MappingTorus.Circle) =
        ((s / j.order : ℝ) : MappingTorus.Circle) + ((-s / j.order : ℝ) : MappingTorus.Circle)
    rw [← AddCircle.coe_add, ← add_div, add_neg_cancel, zero_div, AddCircle.coe_zero]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.affine_symm_capSectionFibre (j : Elliptic.Kind)
    (s : ℝ) (y : PeriodTorusHigherHomology.ProductTorus 3) :
    (Elliptic.flatTorusAffine j j.twist).symm (capSectionFibre j s y) =
      capSectionFibre j (s - 1) ((Elliptic.HigherHomology.fibreTorusHomeomorph j).symm y) := by
  apply (Elliptic.flatTorusAffine j j.twist).injective
  rw [Homeomorph.apply_symm_apply]
  simp only [capSectionFibre_apply,
    Elliptic.HigherHomology.flatTorusAffine_splitFlatTorusHomeomorph_symm,
    Homeomorph.apply_symm_apply]
  apply congrArg (Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm
  apply Prod.ext
  · change
      ((s / j.order : ℝ) : MappingTorus.Circle) =
        (((s - 1) / j.order : ℝ) : MappingTorus.Circle) +
          ((1 / j.order : ℝ) : MappingTorus.Circle)
    rw [← AddCircle.coe_add]
    congr 1
    ring
  · rfl

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.surfaceWangBoundary_fixed (j : Elliptic.Kind)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (Elliptic.HigherHomology.mappingTorusModel j)
        (n + 1)) :
    SingularMayerVietoris.singularHomologyMap
        ((Elliptic.HigherHomology.fibreTorusHomeomorph j).symm : C(_, _)) n
        (MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm n
          a) =
      MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm n
        a := by
  have h :
    MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm n a ∈
      LinearMap.range
        (MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm
          n) :=
    ⟨a, rfl⟩
  rw [MappingTorusHomology.wangBoundary_range] at h
  change
    MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm n a -
        SingularMayerVietoris.singularHomologyMap
          ((Elliptic.HigherHomology.fibreTorusHomeomorph j).symm : C(_, _)) n
          (MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm
            n a) =
      0 at h
  exact (sub_eq_zero.mp h).symm

private theorem PeriodFamily.Boundary.EllipticCapProduct.affine_symm_capSectionFibre_wang
    (j : Elliptic.Kind) (s : ℝ) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (Elliptic.HigherHomology.mappingTorusModel j)
        (n + 1)) :
    SingularMayerVietoris.singularHomologyMap
        (((Elliptic.flatTorusAffine j j.twist).symm : C(RealTorus₄, RealTorus₄)).comp
          (capSectionFibre j s))
        n
        (MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm n
          a) =
      SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) n
        (MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm n
          a) := by
  have hmap :
    ((Elliptic.flatTorusAffine j j.twist).symm : C(RealTorus₄, RealTorus₄)).comp
        (capSectionFibre j s) =
      (capSectionFibre j (s - 1)).comp
        ((Elliptic.HigherHomology.fibreTorusHomeomorph j).symm :
          C(PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 3)) := by
    ext y
    exact affine_symm_capSectionFibre j s y
  rw [hmap, PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    surfaceWangBoundary_fixed, capSectionFibre_homology j (s - 1) 0]

private def
    PeriodFamily.Boundary.EllipticCapProduct.sectionFibreMatrix : Matrix (Fin 4) (Fin 3) ℤ :=
  PeriodTorusHigherHomology.omitHeadMatrix (1 : Elliptic.HigherHomology.FibreMatrix)

private theorem PeriodFamily.Boundary.EllipticCapProduct.sectionFibreMatrix_basis (i : Fin 3) :
    sectionFibreMatrix *ᵥ Pi.single i 1 = Pi.single i.succ 1 := by fin_cases i <;> decide

private theorem PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_flatCoordinates
    (j : Elliptic.Kind) :
    (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)).comp
        (capSectionFibre j 0) =
      PeriodTorusHigherHomology.torusMatrixMap sectionFibreMatrix := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨k, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 3 y
  change
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph
        (capSectionFibre j 0 (PeriodTorusHigherHomology.coordinateProjection 3 k)) =
      _
  rw [capSectionFibre_zero_coordinateProjection,
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ]
  rw [sectionFibreMatrix, PeriodTorusHigherHomology.torusMatrixMap_omitHeadMatrix,
    PeriodTorusHigherHomology.torusMatrixMap_one]
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · change ((0 : ℝ) : MappingTorus.Circle) = 0
    simp only [AddCircle.coe_zero]
  · rfl

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.sectionFibreMatrix_loopHomology (i : Fin 3) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap sectionFibreMatrix) 1
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single i 1))) =
      FirstHurewicz.loopHomologyClass
        (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single i.succ 1)) := by
  rw [SingularMayerVietoris.singularHomologyMap_one,
    PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology, sectionFibreMatrix_basis]

private theorem PeriodFamily.Boundary.EllipticCapProduct.sectionFibreMatrix_topClass :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap sectionFibreMatrix) 3
        (Elliptic.HigherHomology.torusH3Coordinates.symm 1) =
      PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv.symm
        (PeriodTorusHigherHomologyExterior.cubeBasis 3) := by
  rw [Elliptic.HigherHomology.torusH3Coordinates_symm_one,
    PeriodTorusHigherHomologyPontryagin.tripleProduct_natural _
      (PeriodTorusHigherHomology.torusMatrixMap_add sectionFibreMatrix),
    sectionFibreMatrix_loopHomology, sectionFibreMatrix_loopHomology,
    sectionFibreMatrix_loopHomology, PeriodTorusHigherHomologyExterior.cubeBasis_apply,
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_symm_ιMulti]
  have hi : LocalSystemMatrices.tripleIndices 3 = Fin.succ := by decide
  rw [hi]
  simp only [Function.comp_apply, PeriodTorusHigherHomologyExterior.latticeBasis,
    Pi.basisFun_apply]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_h3_one (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) 3
          (Elliptic.HigherHomology.torusH3Coordinates.symm 1)) =
      Pi.single (3 : Fin 4) 1 := by
  change
    PeriodTorusHigherHomologyExterior.cubeCoordinates
        (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
              C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
            3
            (SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) 3
              (Elliptic.HigherHomology.torusH3Coordinates.symm 1)))) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    capSectionFibre_zero_flatCoordinates, sectionFibreMatrix_topClass,
    LinearEquiv.apply_symm_apply]
  change
    PeriodTorusHigherHomologyExterior.cubeBasis.equivFun
        (PeriodTorusHigherHomologyExterior.cubeBasis 3) =
      _
  ext i
  simp [Pi.single_apply, eq_comm]

private theorem PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_h3 (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) 3 a) =
      Pi.single (3 : Fin 4) (Elliptic.HigherHomology.torusH3Coordinates a) := by
  have ha :
    a =
      Elliptic.HigherHomology.torusH3Coordinates a •
        Elliptic.HigherHomology.torusH3Coordinates.symm 1 := by
    apply Elliptic.HigherHomology.torusH3Coordinates.injective
    simp
  calc
    _ =
        PeriodFamily.FlatTorus.singularH3Coordinates
          (SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) 3
            (Elliptic.HigherHomology.torusH3Coordinates a •
              Elliptic.HigherHomology.torusH3Coordinates.symm 1)) :=
      congrArg
        (fun b =>
          PeriodFamily.FlatTorus.singularH3Coordinates
            (SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) 3 b))
        ha
    _ = Elliptic.HigherHomology.torusH3Coordinates a • Pi.single (3 : Fin 4) 1 := by
      rw [map_zsmul, map_zsmul, capSectionFibre_zero_h3_one]
    _ = _ := by
      ext i
      by_cases hi : i = 3
      · subst i
        simp
      · simp [hi]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFromModel_wang (j : Elliptic.Kind)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (Elliptic.HigherHomology.mappingTorusModel j)
        (n + 1)) :
    MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n
        (SingularMayerVietoris.singularHomologyMap (capSectionFromModel j) (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) n
          (MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm
            n a) :=
  wangBoundary_timeReflection_of_quarter (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm
    (Elliptic.flatTorusAffine j j.twist) (capSectionFromModel j) (capSectionFibre j)
    (capSectionFromModel_mk j) (capSectionFibre j 0) n a
    (affine_symm_capSectionFibre_wang j (3 / 4) n a)

private theorem PeriodFamily.Boundary.EllipticCapProduct.capSection_wang (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) (n + 1)) :
    MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n
        (SingularMayerVietoris.singularHomologyMap (capSection j) (n + 1) a) =
      -SingularMayerVietoris.singularHomologyMap (capSectionFibre j 0) n
          (MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm
            n
            (PeriodTorusHigherHomology.homeomorphHomologyEquiv
              (Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)
              (n + 1) a)) := by
  have hcomp :
    (capSectionFromModel j).comp
        (Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod :
          C(_, _)) =
      capSection j := by
    ext x
    change
      capSection j
          ((Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
            (Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod x)) =
        _
    rw [Homeomorph.symm_apply_apply]
  rw [← hcomp, PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    capSectionFromModel_wang]
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.capSection_wang_h4_coordinates
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) 4) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 3
          (SingularMayerVietoris.singularHomologyMap (capSection j) 4 a)) =
      -Pi.single (3 : Fin 4)
          (Elliptic.HigherHomology.surfaceH4Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a) := by
  rw [capSection_wang, map_neg, capSectionFibre_zero_h3]
  congr 2

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.capSection_wang_h4_unit (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 3
          (SingularMayerVietoris.singularHomologyMap (capSection j) 4
            ((Elliptic.HigherHomology.surfaceH4Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
              1))) =
      -Pi.single (3 : Fin 4) 1 := by
  rw [capSection_wang_h4_coordinates, LinearEquiv.apply_symm_apply]

private def PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology
      (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j) 4 :=
  SingularMayerVietoris.singularHomologyMap (capSection j) 4
    ((Elliptic.HigherHomology.surfaceH4Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
      1)

private theorem PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_coordinates
    (j : Elliptic.Kind) : boundaryCapH4Equiv j (unitCapSectionClass j) = (1, 0) := by
  rw [unitCapSectionClass, boundaryCapH4Equiv_section, LinearEquiv.apply_symm_apply]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_filling (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH4Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 4
          (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4
            (unitCapSectionClass j))) =
      1 := by rw [boundaryFillingHomologyMap_H4_first, unitCapSectionClass_coordinates]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.unitCapSectionClass_wang (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 3
          (unitCapSectionClass j)) =
      -Pi.single (3 : Fin 4) 1 :=
  capSection_wang_h4_unit j

private def PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover (j : Elliptic.Kind) :
    C(RealTorus₄, (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) :=
  (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j).comp
    (MappingTorus.HomologyCover.fibreInclusion (Elliptic.flatTorusAffine j j.twist))

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_apply (j : Elliptic.Kind)
    (x : RealTorus₄) :
    surfaceCover j x =
      Elliptic.surfaceProjection j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)
        (Elliptic.flatTorusPeriodHomeomorph
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val x) :=
  ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk j 0 x

private def PeriodFamily.Boundary.EllipticCapKernelWang.twistCircleCharacter (j : Elliptic.Kind) :
    C(RealTorus₄, MappingTorus.Circle)
    where
  toFun x := (Elliptic.HigherHomology.splitFlatTorusHomeomorph j x).1
  continuous_toFun :=
    continuous_fst.comp (Elliptic.HigherHomology.splitFlatTorusHomeomorph j).continuous

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.twistCircleCharacter_apply (j : Elliptic.Kind)
    (x : RealTorus₄) :
    twistCircleCharacter j x = (Elliptic.HigherHomology.splitFlatTorusHomeomorph j x).1 :=
  rfl

private def PeriodFamily.Boundary.EllipticCapKernelWang.nativeShear (j : Elliptic.Kind) :
    C(MappingTorus.Circle × RealTorus₄, MappingTorus.Circle × RealTorus₄)
    where
  toFun p := (p.1 - twistCircleCharacter j p.2, p.2)
  continuous_toFun :=
    (continuous_fst.sub ((twistCircleCharacter j).continuous.comp continuous_snd)).prodMk
      continuous_snd

private def PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover (j : Elliptic.Kind) :
    C(MappingTorus.Circle × RealTorus₄,
      (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) :=
  MappingTorusHomology.Covering.productCover j.order (Elliptic.flatTorusAffine j j.twist).symm
    (ThreefoldOverlapMappingTorus.Elliptic.affine_symm_pow_order j j.twist j.matrix_fixes_twist)

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover_real_apply
    (j : Elliptic.Kind) (t : ℝ) (x : RealTorus₄) :
    nativeProductCover j ((t : MappingTorus.Circle), x) =
      MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t * j.order, x) :=
  MappingTorusHomology.Covering.productCover_real_apply j.order
    (Elliptic.flatTorusAffine j j.twist).symm
    (ThreefoldOverlapMappingTorus.Elliptic.affine_symm_pow_order j j.twist j.matrix_fixes_twist) t
    x

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.boundaryCircleFirstHomeomorph_mk
    (j : Elliptic.Kind) (t : ℝ) (x : RealTorus₄) :
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph j
        (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      (twistCircleCharacter j x + ((t / j.order : ℝ) : MappingTorus.Circle), surfaceCover j x) := by
  change
    Prod.swap
        (PeriodFamily.Boundary.EllipticCapProduct.boundaryProductHomeomorph j
          (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x))) =
      _
  rw [PeriodFamily.Boundary.EllipticCapProduct.boundaryProductHomeomorph_mk]
  apply Prod.ext
  · rfl
  · exact ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_angle j t 0 x

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover_shear_apply
    (j : Elliptic.Kind) (c : MappingTorus.Circle) (x : RealTorus₄) :
    nativeProductCover j (nativeShear j (c, x)) =
      (PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph j).symm
        (c, surfaceCover j x) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (c - twistCircleCharacter j x)
  apply (PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph j).injective
  rw [Homeomorph.apply_symm_apply]
  change
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph j
        (nativeProductCover j (c - twistCircleCharacter j x, x)) =
      _
  rw [← ht, nativeProductCover_real_apply, boundaryCircleFirstHomeomorph_mk]
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  rw [mul_div_cancel_right₀ _ hm, ht]
  exact Prod.ext (add_sub_cancel _ _) rfl

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.nativeProductCover_comp_shear
    (j : Elliptic.Kind) :
    (nativeProductCover j).comp (nativeShear j) =
      ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph j).symm :
            C(_, _)).comp
        (PeriodTorusHigherHomology.circleProductMap (surfaceCover j)) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  exact nativeProductCover_shear_apply j c x

private def PeriodFamily.Boundary.EllipticCapKernelWang.crossWang (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n).comp
    (PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross j n)

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.crossWang_apply (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n) :
    crossWang j n a =
      MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n
        (PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross j n a) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.crossWang_surfaceCover_of_shear
    (j : Elliptic.Kind) (n : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n)
    (ha :
      SingularMayerVietoris.singularHomologyMap (nativeShear j) (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a) =
        PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a) :
    crossWang j n (SingularMayerVietoris.singularHomologyMap (surfaceCover j) n a) =
      MappingTorusHomology.Covering.homologyNorm j.order (Elliptic.flatTorusAffine j j.twist).symm
        n a := by
  rw [crossWang_apply, PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross_apply,
    ← PeriodTorusHigherHomology.positiveCircleCross_naturality]
  have hmap :=
    congrArg
      (fun f :
          C(MappingTorus.Circle × RealTorus₄,
            (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) =>
        SingularMayerVietoris.singularHomologyMap f (n + 1))
      (nativeProductCover_comp_shear j)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at hmap
  have hc :=
    LinearMap.congr_fun hmap (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a)
  simp only [LinearMap.comp_apply, ha] at hc
  rw [← hc]
  exact
    MappingTorusHomology.Covering.wangBoundary_productCover_positiveCircleCross j.order
      (Elliptic.flatTorusAffine j j.twist).symm
      (ThreefoldOverlapMappingTorus.Elliptic.affine_symm_pow_order j j.twist j.matrix_fixes_twist)
      n a

private def
    PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n :=
  MappingTorusHomology.Covering.homologyNorm j.order (Elliptic.flatTorusAffine j j.twist).symm n

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.originalAffine_pow_order (j : Elliptic.Kind) :
    Elliptic.flatTorusAffine j j.twist ^ j.order = 1 :=
  ThreefoldOverlapMappingTorus.Elliptic.affine_pow_order j j.twist j.matrix_fixes_twist

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_eq_positive
    (j : Elliptic.Kind) (n : ℕ) :
    originalAffineNorm j n =
      MappingTorusHomology.Covering.homologyNorm j.order (Elliptic.flatTorusAffine j j.twist) n :=
  MappingTorusHomology.Covering.homologyNorm_symm j.order (Elliptic.flatTorusAffine j j.twist) n
    (originalAffine_pow_order j)

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_sum_powers
    (j : Elliptic.Kind) (n : ℕ) :
    originalAffineNorm j n =
      ∑ k ∈ Finset.range j.order,
        (MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) n) ^ k := by
  rw [originalAffineNorm_eq_positive, MappingTorusHomology.Covering.homologyNorm_eq_sum_powers]

private def PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixOne (j : Elliptic.Kind) :
    LatticeMatrix :=
  ∑ k ∈ Finset.range j.order, j.matrix ^ k

private def PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixTwo (j : Elliptic.Kind) :
    Matrix (Fin 6) (Fin 6) ℤ :=
  ∑ k ∈ Finset.range j.order, (LocalSystemMatrices.exteriorSquare j.matrix) ^ k

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffine_h1_coordinates
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 1 a) =
      j.matrix *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a := by
  rw [MappingTorusHomology.monodromyHomologyMap,
    PeriodFamily.Boundary.flatTorusAffine_homology_triangle]
  change
    PeriodFamily.FlatTorus.singularH1Equiv
        (FirstHurewicz.inducedHomology
          (SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) :
            C(RealTorus₄, RealTorus₄))
          a) =
      _
  rw [PeriodFamily.FlatTorus.singularH1Equiv_inducedHomology_triangle,
    SpecialPeriods.EllipticFilling.ellipticGenerator_dual_matrix]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffine_h2_coordinates
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 2 a) =
      LocalSystemMatrices.exteriorSquare j.matrix *ᵥ
        PeriodFamily.FlatTorus.singularH2Coordinates a := by
  rw [MappingTorusHomology.monodromyHomologyMap,
    PeriodFamily.Boundary.flatTorusAffine_homology_triangle]
  change
    PeriodFamily.FlatTorus.singularH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) :
            C(RealTorus₄, RealTorus₄))
          2 a) =
      _
  rw [PeriodFamily.FlatTorus.singularH2Coordinates_inducedHomology_triangle,
    SpecialPeriods.EllipticFilling.ellipticGenerator_dual_matrix]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.marked_endomorphism_pow_mo1973_27421
    {M : Type*} [AddCommGroup M] [Module ℤ M] {r : ℕ} (e : M ≃ₗ[ℤ] (Fin r → ℤ))
    (f : Module.End ℤ M) (A : Matrix (Fin r) (Fin r) ℤ) (hf : ∀ a, e (f a) = A *ᵥ e a) (k : ℕ)
    (a : M) : e ((f ^ k) a) = A ^ k *ᵥ e a := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
  | succ k ih => rw [pow_succ', Module.End.mul_apply, hf, ih, Matrix.mulVec_mulVec, ← pow_succ']

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffine_pow_h1_coordinates
    (j : Elliptic.Kind) (k : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv
        ((MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 1 ^ k)
          a) =
      j.matrix ^ k *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a :=
  marked_endomorphism_pow_mo1973_27421 PeriodFamily.FlatTorus.singularH1Equiv
    (MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 1) j.matrix
    (originalAffine_h1_coordinates j) k a

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffine_pow_h2_coordinates
    (j : Elliptic.Kind) (k : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        ((MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 2 ^ k)
          a) =
      (LocalSystemMatrices.exteriorSquare j.matrix) ^ k *ᵥ
        PeriodFamily.FlatTorus.singularH2Coordinates a :=
  marked_endomorphism_pow_mo1973_27421 PeriodFamily.FlatTorus.singularH2Coordinates
    (MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 2)
    (LocalSystemMatrices.exteriorSquare j.matrix) (originalAffine_h2_coordinates j) k a

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_h1_coordinates
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    PeriodFamily.FlatTorus.singularH1Equiv (originalAffineNorm j 1 a) =
      originalNormMatrixOne j *ᵥ PeriodFamily.FlatTorus.singularH1Equiv a := by
  rw [originalAffineNorm_sum_powers, LinearMap.sum_apply, map_sum]
  simp only [originalAffine_pow_h1_coordinates]
  exact (Matrix.sum_mulVec _ _ _).symm

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_h2_coordinates
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    PeriodFamily.FlatTorus.singularH2Coordinates (originalAffineNorm j 2 a) =
      originalNormMatrixTwo j *ᵥ PeriodFamily.FlatTorus.singularH2Coordinates a := by
  rw [originalAffineNorm_sum_powers, LinearMap.sum_apply, map_sum]
  simp only [originalAffine_pow_h2_coordinates]
  exact (Matrix.sum_mulVec _ _ _).symm

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixOne_three :
    originalNormMatrixOne .three = !![3, 0, 0, 0; 6, 0, 0, 0; -12, 0, 0, 0; 0, 2, 1, 3] := by
  decide

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixOne_four :
    originalNormMatrixOne .four = !![4, 0, 0, 0; 12, 0, 0, 0; -12, 0, 0, 0; 0, 2, 2, 4] := by
  decide

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixTwo_three :
    originalNormMatrixTwo .three =
      !![0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0;
        2, 1, 3, 0, 0, 0;
        -12, -6, 0, 3, 0, 0;
        8, 4, 6, -1, 0, 0;
        -16, -8, -12, 2, 0, 0] := by
  change (∑ k ∈ Finset.range 3, PeriodTorusHigherHomologyExterior.squareA₁ ^ k) = _
  rw [PeriodTorusHigherHomologyExterior.squareA₁_eq]
  decide

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixTwo_four :
    originalNormMatrixTwo .four =
      !![0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0;
        2, 2, 4, 0, 0, 0;
        -12, -12, 0, 4, 0, 0;
        12, 12, 12, -2, 0, 0;
        -12, -12, -12, 2, 0, 0] := by
  change (∑ k ∈ Finset.range 4, PeriodTorusHigherHomologyExterior.squareA₂ ^ k) = _
  rw [PeriodTorusHigherHomologyExterior.squareA₂_eq]
  decide

private def PeriodFamily.CapKernelShear.shear
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 4,
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 4) :=
  ⟨fun p => (p.1 - χ p.2, p.2),
    (continuous_fst.sub (χ.continuous.comp continuous_snd)).prodMk continuous_snd⟩

private def PeriodFamily.CapKernelShear.torusShear
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    C(PeriodTorusHigherHomology.ProductTorus 5, PeriodTorusHigherHomology.ProductTorus 5)
    where
  toFun z := Fin.cons (z 0 - χ (fun i => z i.succ)) (fun i => z i.succ)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact
        (continuous_apply 0).sub
          (χ.continuous.comp (continuous_pi fun j => continuous_apply j.succ))
    · exact continuous_apply j.succ

@[simp]
private theorem PeriodFamily.CapKernelShear.torusShear_apply
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (z : PeriodTorusHigherHomology.ProductTorus 5) :
    torusShear χ z = Fin.cons (z 0 - χ (fun i => z i.succ)) (fun i => z i.succ) :=
  rfl

private theorem PeriodFamily.CapKernelShear.torusShear_comp_unsplit
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    (torusShear χ).comp
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 4,
            PeriodTorusHigherHomology.ProductTorus 5)) =
      ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
                PeriodTorusHigherHomology.ProductTorus 4,
              PeriodTorusHigherHomology.ProductTorus 5)).comp
        (shear χ) :=
  rfl

private theorem PeriodFamily.CapKernelShear.character_zero
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) : χ 0 = 0 := by
  have h : χ 0 + χ 0 = χ 0 + 0 := by simpa only [zero_add, add_zero] using (hχ 0 0).symm
  exact add_left_cancel h

private theorem PeriodFamily.CapKernelShear.torusShear_add
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (z w : PeriodTorusHigherHomology.ProductTorus 5) :
    torusShear χ (z + w) = torusShear χ z + torusShear χ w := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change
      z 0 + w 0 - χ ((fun j => z j.succ) + (fun j => w j.succ)) =
        (z 0 - χ (fun j => z j.succ)) + (w 0 - χ (fun j => w j.succ))
    rw [hχ]
    abel
  · rfl

private theorem PeriodFamily.CapKernelShear.torusShear_comp_head
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) :
    (torusShear χ).comp (PeriodTorusHigherHomology.torusHeadCircleMap 4) =
      PeriodTorusHigherHomology.torusHeadCircleMap 4 := by
  apply ContinuousMap.ext
  intro z
  change
    torusShear χ (PeriodTorusHigherHomology.torusHeadCircleMap 4 z) =
      PeriodTorusHigherHomology.torusHeadCircleMap 4 z
  rw [PeriodTorusHigherHomology.torusHeadCircleMap_apply, torusShear_apply]
  change
    Fin.cons (α := fun _ : Fin 5 => (PeriodTorusHigherHomology.CircleTopology.Circle)) (z - χ 0)
        0 =
      Fin.cons z 0
  rw [character_zero χ hχ, sub_zero]

private theorem PeriodFamily.CapKernelShear.torusShear_comp_tail
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    (torusShear χ).comp (PeriodTorusHigherHomology.torusTailMap 4) =
      PeriodTorusHigherHomology.torusTailMap 4 -
        (PeriodTorusHigherHomology.torusHeadCircleMap 4).comp χ := by
  apply ContinuousMap.ext
  intro x
  change
    torusShear χ (PeriodTorusHigherHomology.torusTailMap 4 x) =
      PeriodTorusHigherHomology.torusTailMap 4 x -
        PeriodTorusHigherHomology.torusHeadCircleMap 4 (χ x)
  simp only [PeriodTorusHigherHomology.torusTailMap_apply, torusShear_apply,
    PeriodTorusHigherHomology.torusHeadCircleMap_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem PeriodFamily.CapKernelShear.loopHomologyClass_add_zero_mo1973_27446 {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (p q : Path (0 : G) 0) :
    FirstHurewicz.loopHomologyClass (p.add q) =
      FirstHurewicz.loopHomologyClass p + FirstHurewicz.loopHomologyClass q := by
  have hp : (p.prod (Path.refl (0 : G))).map continuous_add = p.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply, Path.cast_coe,
      add_zero]
  have hq : ((Path.refl (0 : G)).prod q).map continuous_add = q.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply, Path.cast_coe,
      zero_add]
  have h :
    ((p.prod (Path.refl (0 : G))).trans ((Path.refl (0 : G)).prod q)).Homotopic (p.prod q) := by
    rw [Path.trans_prod_eq_prod_trans]
    exact ⟨Path.Homotopic.prodHomotopy (Path.Homotopy.transRefl p) (Path.Homotopy.reflTrans q)⟩
  have he :=
    FirstHurewicz.loopHomologyClass_homotopic
      (h.map (⟨fun x : G × G => x.1 + x.2, continuous_add⟩ : C(G × G, G)))
  rw [Path.map_trans, FirstHurewicz.loopHomologyClass_trans, hp, hq] at he
  exact he.symm

private theorem PeriodFamily.CapKernelShear.inducedH1_add_of_zero_mo1973_27447 {X G : Type}
    [TopologicalSpace X] [PathConnectedSpace X] [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (f g : C(X, G)) (b : X) (hf : f b = 0) (hg : g b = 0) :
    FirstHurewicz.inducedHomology (f + g) =
      FirstHurewicz.inducedHomology f + FirstHurewicz.inducedHomology g := by
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := FirstHurewicz.loopHomologyClass_surjective b a
  let pf : Path (0 : G) 0 := (p.map f.continuous).cast hf.symm hf.symm
  let pg : Path (0 : G) 0 := (p.map g.continuous).cast hg.symm hg.symm
  have h :
    p.map (f + g).continuous =
      (pf.add pg).cast (by simp only [ContinuousMap.add_apply, hf, hg])
        (by simp only [ContinuousMap.add_apply, hf, hg]) := by
    ext t
    rfl
  simp only [LinearMap.add_apply, FirstHurewicz.inducedHomology_loopHomologyClass]
  rw [h]
  exact loopHomologyClass_add_zero_mo1973_27446 pf pg

private theorem PeriodFamily.CapKernelShear.inducedH1_sub_of_zero_mo1973_27448 {X G : Type}
    [TopologicalSpace X] [PathConnectedSpace X] [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (f g : C(X, G)) (b : X) (hf : f b = 0) (hg : g b = 0) :
    FirstHurewicz.inducedHomology (f - g) =
      FirstHurewicz.inducedHomology f - FirstHurewicz.inducedHomology g := by
  have h :=
    inducedH1_add_of_zero_mo1973_27447 (f - g) g b
      (by simp only [ContinuousMap.sub_apply, hf, hg, sub_self]) hg
  rw [sub_add_cancel] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

private def PeriodFamily.CapKernelShear.headClass :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 5) 1 :=
  FirstHurewicz.loopHomologyClass
    (PeriodTorusHigherHomology.coordinatePeriodLoop 5 (Pi.single 0 1))

private theorem PeriodFamily.CapKernelShear.headClass_eq_image :
    headClass =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusHeadCircleMap 4) 1
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) :=
  (PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology 4).symm

private theorem PeriodFamily.CapKernelShear.headHomology_eq_degree_smul
    (a :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.CircleTopology.Circle)
        1) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusHeadCircleMap 4) 1
        a =
      PeriodTorusHigherHomology.circleHomologyOneEquiv a • headClass := by
  have ha :
    a =
      PeriodTorusHigherHomology.circleHomologyOneEquiv a •
        FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
    simpa only [LinearEquiv.symm_apply_apply] using
      PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int
        (PeriodTorusHigherHomology.circleHomologyOneEquiv a)
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusHeadCircleMap 4)
          1
          (PeriodTorusHigherHomology.circleHomologyOneEquiv a •
            FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) :=
      congrArg
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusHeadCircleMap 4) 1)
        ha
    _ = PeriodTorusHigherHomology.circleHomologyOneEquiv a • headClass := by
      rw [map_zsmul, PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology]
      rfl

private theorem PeriodFamily.CapKernelShear.torusShear_headHomology
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.CircleTopology.Circle)
        1) :
    SingularMayerVietoris.singularHomologyMap (torusShear χ) 1
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusHeadCircleMap 4) 1 a) =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusHeadCircleMap 4) 1
        a := by
  change
    ((SingularMayerVietoris.singularHomologyMap (torusShear χ) 1).comp
          (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.torusHeadCircleMap 4) 1))
        a =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, torusShear_comp_head χ hχ]

private theorem PeriodFamily.CapKernelShear.torusShear_headClass
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) :
    SingularMayerVietoris.singularHomologyMap (torusShear χ) 1 headClass = headClass := by
  simpa only [headClass_eq_image] using
    torusShear_headHomology χ hχ
      (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop)

private theorem PeriodFamily.CapKernelShear.torusShear_tailHomology
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1) :
    SingularMayerVietoris.singularHomologyMap (torusShear χ) 1
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1
          b) =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1 b -
        PeriodTorusHigherHomology.circleHomologyOneEquiv
            (SingularMayerVietoris.singularHomologyMap χ 1 b) •
          headClass := by
  have hzero :
    ((PeriodTorusHigherHomology.torusHeadCircleMap 4).comp χ)
        (0 : PeriodTorusHigherHomology.ProductTorus 4) =
      0 := by
    change PeriodTorusHigherHomology.torusHeadCircleMap 4 (χ 0) = 0
    rw [character_zero χ hχ]
    exact PeriodTorusHigherHomology.coordinateCircleMap_zero (Pi.single (0 : Fin 5) 1)
  have hsub :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusTailMap 4 -
          (PeriodTorusHigherHomology.torusHeadCircleMap 4).comp χ)
        1 =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1 -
        SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.torusHeadCircleMap 4).comp χ) 1 := by
    simpa only [SingularMayerVietoris.singularHomologyMap_one] using
      inducedH1_sub_of_zero_mo1973_27448 (PeriodTorusHigherHomology.torusTailMap 4)
        ((PeriodTorusHigherHomology.torusHeadCircleMap 4).comp χ)
        (0 : PeriodTorusHigherHomology.ProductTorus 4)
        (PeriodTorusHigherHomology.torusTailMap_zero 4) hzero
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusTailMap 4 -
            (PeriodTorusHigherHomology.torusHeadCircleMap 4).comp χ)
          1 b := by
      rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
        torusShear_comp_tail]
    _ =
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1 b -
          SingularMayerVietoris.singularHomologyMap
            ((PeriodTorusHigherHomology.torusHeadCircleMap 4).comp χ) 1 b := by
      rw [hsub, LinearMap.sub_apply]
    _ =
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1 b -
          PeriodTorusHigherHomology.circleHomologyOneEquiv
              (SingularMayerVietoris.singularHomologyMap χ 1 b) •
            headClass := by
      rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
        headHomology_eq_degree_smul]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.product11_sub_head (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) (k : ℤ) :
    PeriodTorusHigherHomologyPontryagin.product11 G a (b - k • a) =
      PeriodTorusHigherHomologyPontryagin.product11 G a b := by
  rw [map_sub, map_zsmul, PeriodTorusHigherHomologyPontryagin.product11_self, zsmul_zero,
    sub_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.tripleProduct_sub_head (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b c : SingularMayerVietoris.SingularHomology G 1) (k l : ℤ) :
    PeriodTorusHigherHomologyPontryagin.tripleProduct G a (b - k • a) (c - l • a) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct G a b c := by
  calc
    PeriodTorusHigherHomologyPontryagin.tripleProduct G a (b - k • a) (c - l • a) =
        PeriodTorusHigherHomologyPontryagin.tripleProduct G a b (c - l • a) -
          k • PeriodTorusHigherHomologyPontryagin.tripleProduct G a a (c - l • a) := by
      rw [(PeriodTorusHigherHomologyPontryagin.tripleProduct G a).map_sub, LinearMap.sub_apply]
      exact
        congrArg
          (fun t => PeriodTorusHigherHomologyPontryagin.tripleProduct G a b (c - l • a) - t)
          (congrArg
            (fun f :
                SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
                  SingularMayerVietoris.SingularHomology G 3 =>
              f (c - l • a))
            (map_zsmul (PeriodTorusHigherHomologyPontryagin.tripleProduct G a) k a))
    _ = PeriodTorusHigherHomologyPontryagin.tripleProduct G a b (c - l • a) := by
      rw [PeriodTorusHigherHomologyPontryagin.tripleProduct_self01, zsmul_zero, sub_zero]
    _ = PeriodTorusHigherHomologyPontryagin.tripleProduct G a b c := by
      rw [map_sub, map_zsmul, PeriodTorusHigherHomologyPontryagin.tripleProduct_self02,
        zsmul_zero, sub_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.product11_fixed_of_head (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] (f : C(G, G))
    (hf : ∀ x y, f (x + y) = f x + f y) (a b : SingularMayerVietoris.SingularHomology G 1) (k : ℤ)
    (ha : SingularMayerVietoris.singularHomologyMap f 1 a = a)
    (hb : SingularMayerVietoris.singularHomologyMap f 1 b = b - k • a) :
    SingularMayerVietoris.singularHomologyMap f 2
        (PeriodTorusHigherHomologyPontryagin.product11 G a b) =
      PeriodTorusHigherHomologyPontryagin.product11 G a b := by
  rw [PeriodTorusHigherHomologyPontryagin.product_natural f hf 1, ha, hb, product11_sub_head]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodFamily.CapKernelShear.tripleProduct_fixed_of_head (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] (f : C(G, G))
    (hf : ∀ x y, f (x + y) = f x + f y) (a b c : SingularMayerVietoris.SingularHomology G 1)
    (k l : ℤ) (ha : SingularMayerVietoris.singularHomologyMap f 1 a = a)
    (hb : SingularMayerVietoris.singularHomologyMap f 1 b = b - k • a)
    (hc : SingularMayerVietoris.singularHomologyMap f 1 c = c - l • a) :
    SingularMayerVietoris.singularHomologyMap f 3
        (PeriodTorusHigherHomologyPontryagin.tripleProduct G a b c) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct G a b c := by
  rw [PeriodTorusHigherHomologyPontryagin.tripleProduct_natural f hf, ha, hb, hc,
    tripleProduct_sub_head]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.shear_unsplit_homology
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 4)
        n) :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 4,
            PeriodTorusHigherHomology.ProductTorus 5))
        n (SingularMayerVietoris.singularHomologyMap (shear χ) n a) =
      SingularMayerVietoris.singularHomologyMap (torusShear χ) n
        (SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
                PeriodTorusHigherHomology.ProductTorus 4,
              PeriodTorusHigherHomology.ProductTorus 5))
          n a) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    torusShear_comp_unsplit, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.unsplit_positiveCircleCross (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 4,
            PeriodTorusHigherHomology.ProductTorus 5))
        (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          n b) =
      PeriodTorusHigherHomologyPontryagin.product (PeriodTorusHigherHomology.ProductTorus 5) n
        headClass
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) n
          b) := by
  rw [PeriodTorusHigherHomology.torusSplit_positiveCircleCross,
    PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.shear_positiveCircleCross_of_product
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n)
    (h :
      SingularMayerVietoris.singularHomologyMap (torusShear χ) (n + 1)
          (PeriodTorusHigherHomologyPontryagin.product (PeriodTorusHigherHomology.ProductTorus 5)
            n headClass
            (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4)
              n b)) =
        PeriodTorusHigherHomologyPontryagin.product (PeriodTorusHigherHomology.ProductTorus 5) n
          headClass
          (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) n
            b)) :
    SingularMayerVietoris.singularHomologyMap (shear χ) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          n b) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) n
        b := by
  apply
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm (n + 1)).injective
  change
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 4,
            PeriodTorusHigherHomology.ProductTorus 5))
        (n + 1)
        (SingularMayerVietoris.singularHomologyMap (shear χ) (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross
            (PeriodTorusHigherHomology.ProductTorus 4) n b)) =
      SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 4).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 4,
            PeriodTorusHigherHomology.ProductTorus 5))
        (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          n b)
  rw [shear_unsplit_homology, unsplit_positiveCircleCross]
  exact h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.shear_positiveCircleCross_one
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1) :
    SingularMayerVietoris.singularHomologyMap (shear χ) 2
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          1 b) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) 1
        b := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 5 2
  apply shear_positiveCircleCross_of_product χ 1 b
  exact
    product11_fixed_of_head (PeriodTorusHigherHomology.ProductTorus 5) (torusShear χ)
      (torusShear_add χ hχ) headClass
      (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1 b)
      (PeriodTorusHigherHomology.circleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap χ 1 b))
      (torusShear_headClass χ hχ) (torusShear_tailHomology χ hχ b)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.shear_positiveCircleCross_two_product11
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b c : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1) :
    SingularMayerVietoris.singularHomologyMap (shear χ) 3
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          2
          (PeriodTorusHigherHomologyPontryagin.product11
            (PeriodTorusHigherHomology.ProductTorus 4) b c)) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) 2
        (PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 4)
          b c) := by
  let := PeriodTorusHigherHomology.productTorus_homology_torsionFree 5 2
  apply
    shear_positiveCircleCross_of_product χ 2
      (PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 4) b
        c)
  rw [PeriodTorusHigherHomologyPontryagin.product_natural
      (PeriodTorusHigherHomology.torusTailMap 4) (PeriodTorusHigherHomology.torusTailMap_add 4) 1]
  exact
    tripleProduct_fixed_of_head (PeriodTorusHigherHomology.ProductTorus 5) (torusShear χ)
      (torusShear_add χ hχ) headClass
      (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1 b)
      (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 4) 1 c)
      (PeriodTorusHigherHomology.circleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap χ 1 b))
      (PeriodTorusHigherHomology.circleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap χ 1 c))
      (torusShear_headClass χ hχ) (torusShear_tailHomology χ hχ b)
      (torusShear_tailHomology χ hχ c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.shear_positiveCircleCross_two
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2) :
    SingularMayerVietoris.singularHomologyMap (shear χ) 3
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          2 b) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) 2
        b := by
  have h :
    ((SingularMayerVietoris.singularHomologyMap (shear χ) 3).comp
            (PeriodTorusHigherHomology.positiveCircleCross
              (PeriodTorusHigherHomology.ProductTorus 4) 2)).comp
        PeriodTorusHigherHomology.coordinateTorusWedgeTwo =
      (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
            2).comp
        PeriodTorusHigherHomology.coordinateTorusWedgeTwo := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change
      SingularMayerVietoris.singularHomologyMap (shear χ) 3
          (PeriodTorusHigherHomology.positiveCircleCross
            (PeriodTorusHigherHomology.ProductTorus 4) 2
            (PeriodTorusHigherHomology.coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v))) =
        PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) 2
          (PeriodTorusHigherHomology.coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v))
    rw [PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti]
    exact shear_positiveCircleCross_two_product11 χ hχ _ _
  obtain ⟨v, rfl⟩ := PeriodTorusHigherHomology.coordinateTorusWedgeTwo_surjective b
  exact LinearMap.congr_fun h v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodFamily.CapKernelShear.shear_positiveCircleCross
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap (shear χ) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          n b) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) n
        b := by
  rcases hn with rfl | rfl
  · exact shear_positiveCircleCross_one χ hχ b
  · exact shear_positiveCircleCross_two χ hχ b

private def PeriodFamily.CapKernelShear.realShear
    (χ : C(RealTorus₄, (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄,
      (PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄)
    where
  toFun z := (z.1 - χ z.2, z.2)
  continuous_toFun :=
    (continuous_fst.sub (χ.continuous.comp continuous_snd)).prodMk continuous_snd

private def PeriodFamily.CapKernelShear.coordinateCharacter
    (χ : C(RealTorus₄, (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    C(PeriodTorusHigherHomology.ProductTorus 4,
      (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  χ.comp
    (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm :
      C(PeriodTorusHigherHomology.ProductTorus 4, RealTorus₄))

private theorem PeriodFamily.CapKernelShear.coordinateCharacter_add
    (χ : C(RealTorus₄, (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (x y : PeriodTorusHigherHomology.ProductTorus 4) :
    coordinateCharacter χ (x + y) = coordinateCharacter χ x + coordinateCharacter χ y := by
  have h :
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm (x + y) =
      PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm x +
        PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm y := by
    apply PeriodTorusHigherHomology.flatTorusCircleHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, PeriodTorusHigherHomology.flatTorusCircleHomeomorph_add,
      Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  change
    χ (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm (x + y)) =
      χ (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm x) +
        χ (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm y)
  rw [h, hχ]

private def PeriodFamily.CapKernelShear.realCircleCoordinates :
    ((PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄) ≃ₜ
      ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 4) :=
  (Homeomorph.refl (PeriodTorusHigherHomology.CircleTopology.Circle)).prodCongr
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph

private theorem PeriodFamily.CapKernelShear.realShear_coordinates
    (χ : C(RealTorus₄, (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    (PeriodTorusHigherHomology.circleProductMap
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
              C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))).comp
        (realShear χ) =
      (shear (coordinateCharacter χ)).comp
        (PeriodTorusHigherHomology.circleProductMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))) := by
  apply ContinuousMap.ext
  rintro ⟨z, x⟩
  change
    (z - χ x, PeriodTorusHigherHomology.flatTorusCircleHomeomorph x) =
      (z -
          χ
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm
              (PeriodTorusHigherHomology.flatTorusCircleHomeomorph x)),
        PeriodTorusHigherHomology.flatTorusCircleHomeomorph x)
  rw [Homeomorph.symm_apply_apply]

private theorem PeriodFamily.CapKernelShear.realShear_coordinate_homology
    (χ : C(RealTorus₄, (PeriodTorusHigherHomology.CircleTopology.Circle))) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × RealTorus₄) n) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)))
        n (SingularMayerVietoris.singularHomologyMap (realShear χ) n a) =
      SingularMayerVietoris.singularHomologyMap (shear (coordinateCharacter χ)) n
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.circleProductMap
            (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
              C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)))
          n a) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    realShear_coordinates, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]

private theorem PeriodFamily.CapKernelShear.realShear_positiveCircleCross
    (χ : C(RealTorus₄, (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (b : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap (realShear χ) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n b) =
      PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n b := by
  apply
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv realCircleCoordinates (n + 1)).injective
  change
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)))
        (n + 1)
        (SingularMayerVietoris.singularHomologyMap (realShear χ) (n + 1)
          (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n b)) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)))
        (n + 1) (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n b)
  simp only [realShear_coordinate_homology,
    PeriodTorusHigherHomology.positiveCircleCross_naturality]
  exact
    shear_positiveCircleCross (coordinateCharacter χ) (coordinateCharacter_add χ hχ) n hn
      (SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        n b)

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.twistCircleCharacter_add (j : Elliptic.Kind)
    (x y : RealTorus₄) :
    twistCircleCharacter j (x + y) = twistCircleCharacter j x + twistCircleCharacter j y := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective y
  rw [← map_add, twistCircleCharacter_apply, twistCircleCharacter_apply,
    twistCircleCharacter_apply, Elliptic.HigherHomology.splitFlatTorusHomeomorph_mkQ,
    Elliptic.HigherHomology.splitFlatTorusHomeomorph_mkQ,
    Elliptic.HigherHomology.splitFlatTorusHomeomorph_mkQ]
  simp only [map_add, Prod.fst_add, AddCircle.coe_add]

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.nativeShear_eq_realShear (j : Elliptic.Kind) :
    nativeShear j = PeriodFamily.CapKernelShear.realShear (twistCircleCharacter j) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.nativeShear_positiveCircleCross
    (j : Elliptic.Kind) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    SingularMayerVietoris.singularHomologyMap (nativeShear j) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a) =
      PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ n a := by
  rw [nativeShear_eq_realShear]
  exact
    PeriodFamily.CapKernelShear.realShear_positiveCircleCross (twistCircleCharacter j)
      (twistCircleCharacter_add j) n hn a

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.crossWang_surfaceCover (j : Elliptic.Kind)
    (n : ℕ) (hn : n = 1 ∨ n = 2) (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    crossWang j n (SingularMayerVietoris.singularHomologyMap (surfaceCover j) n a) =
      originalAffineNorm j n a :=
  crossWang_surfaceCover_of_shear j n a (nativeShear_positiveCircleCross j n hn a)

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.crossWang_surfaceCover_one (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    crossWang j 1 (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 a) =
      originalAffineNorm j 1 a :=
  crossWang_surfaceCover j 1 (Or.inl rfl) a

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.crossWang_surfaceCover_two (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    crossWang j 2 (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 a) =
      originalAffineNorm j 2 a :=
  crossWang_surfaceCover j 2 (Or.inr rfl) a

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_eq_periodCover
    (j : Elliptic.Kind) :
    surfaceCover j =
      (Elliptic.HigherHomology.periodCover j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
            (Elliptic.mainTwist_admissible j)).comp
        (Elliptic.flatTorusPeriodHomeomorph
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val :
          C(_, _)) := by
  apply ContinuousMap.ext
  exact surfaceCover_apply j

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_split (j : Elliptic.Kind) :
    (Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod :
            C(_, _)).comp
        ((surfaceCover j).comp
          ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm : C(_, _))) =
      MappingTorusHomology.Covering.productCover j.order
        (Elliptic.HigherHomology.fibreTorusHomeomorph j)
        (Elliptic.HigherHomology.fibreTorusHomeomorph_pow_order j) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective c
  change
    Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (surfaceCover j
          ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm
            ((t : MappingTorus.Circle), x))) =
      _
  rw [surfaceCover_apply]
  change
    Elliptic.HigherHomology.surfaceMappingTorusHomeomorph j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (Elliptic.surfaceProjection j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
          (Elliptic.mainTwist_admissible j)
          ((Elliptic.HigherHomology.splitPeriodTorusHomeomorph j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod.val).symm
            ((t : MappingTorus.Circle), x))) =
      _
  rw [Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_splitPeriodTorus,
    MappingTorusHomology.Covering.productCover_real_apply]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_split_homology
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.Circle × PeriodTorusHigherHomology.ProductTorus 3) n) :
    Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod n
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) n
          (SingularMayerVietoris.singularHomologyMap
            ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm : C(_, _)) n a)) =
      MappingTorusHomology.Covering.productCoverHomology j.order
        (Elliptic.HigherHomology.fibreTorusHomeomorph j)
        (Elliptic.HigherHomology.fibreTorusHomeomorph_pow_order j) n a := by
  have h :=
    congrArg
      (fun f :
          C(MappingTorus.Circle × PeriodTorusHigherHomology.ProductTorus 3,
            Elliptic.HigherHomology.mappingTorusModel j) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (surfaceCover_split j)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_split_section (j : Elliptic.Kind)
    (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n) :
    Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod n
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) n
          (SingularMayerVietoris.singularHomologyMap
            ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm : C(_, _)) n
            (PeriodTorusHigherHomology.circleSectionHomology
              (PeriodTorusHigherHomology.ProductTorus 3) n a))) =
      MappingTorusHomology.fibreHomologyMap (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm
        n a := by
  rw [surfaceCover_split_homology,
    MappingTorusHomology.Covering.productCoverHomology_circleSection_apply]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_split_cross_wang
    (j : Elliptic.Kind) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n) :
    MappingTorusHomology.wangBoundary (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm n
        (Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod (n + 1)
          (SingularMayerVietoris.singularHomologyMap (surfaceCover j) (n + 1)
            (SingularMayerVietoris.singularHomologyMap
              ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm : C(_, _)) (n + 1)
              (PeriodTorusHigherHomology.positiveCircleCross
                (PeriodTorusHigherHomology.ProductTorus 3) n a)))) =
      Elliptic.HigherHomology.fibreHomologyNorm j n a := by
  rw [surfaceCover_split_homology,
    MappingTorusHomology.Covering.wangBoundary_productCover_positiveCircleCross]
  exact LinearMap.congr_fun (Elliptic.HigherHomology.fibreHomologyNorm_eq_homologyNorm j n).symm a

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreInputOne :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1 :=
  Elliptic.HigherHomology.torusH1Equiv.symm ![0, 1, 0]

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreInputTwo :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 :=
  Elliptic.HigherHomology.torusH2Coordinates.symm ![1, 0, 0]

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassOne (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology RealTorus₄ 1 :=
  SingularMayerVietoris.singularHomologyMap
    ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3,
        RealTorus₄))
    1
    (PeriodTorusHigherHomology.circleSectionHomology (PeriodTorusHigherHomology.ProductTorus 3) 1
      splitFibreInputOne)

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassOne (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology RealTorus₄ 1 :=
  SingularMayerVietoris.singularHomologyMap
    ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3,
        RealTorus₄))
    1
    (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3) 0
      (PeriodTorusHigherHomology.pointClass (0 : PeriodTorusHigherHomology.ProductTorus 3)))

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology RealTorus₄ 2 :=
  SingularMayerVietoris.singularHomologyMap
    ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3,
        RealTorus₄))
    2
    (PeriodTorusHigherHomology.circleSectionHomology (PeriodTorusHigherHomology.ProductTorus 3) 2
      splitFibreInputTwo)

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology RealTorus₄ 2 :=
  SingularMayerVietoris.singularHomologyMap
    ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3,
        RealTorus₄))
    2
    (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3) 1
      splitFibreInputOne)

private def PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearOne (j : Elliptic.Kind) : ℤ :=
  Elliptic.HigherHomology.surfaceH1Equiv j
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
    (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) 0

private def PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearTwo (j : Elliptic.Kind) : ℤ :=
  Elliptic.HigherHomology.surfaceH2Equiv j
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
    (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) 0

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitFibreClassOne
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH1Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitFibreClassOne j)) =
      ![1, 0] := by
  change
    Elliptic.HigherHomology.mappingTorusH1Equiv j
        (Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod 1
          (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitFibreClassOne j))) =
      _
  rw [splitFibreClassOne, surfaceCover_split_section,
    Elliptic.HigherHomology.mappingTorusH1Equiv_fibre, splitFibreInputOne,
    LinearEquiv.apply_symm_apply, Elliptic.HigherHomology.fibreCoinvariantCoordinate_section]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassOne_second
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH1Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) 1 =
      j.order := by
  change
    Elliptic.HigherHomology.mappingTorusH1Equiv j
        (Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod 1
          (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)))
        1 =
      _
  rw [Elliptic.HigherHomology.mappingTorusH1Equiv_boundary, splitCircleClassOne,
    surfaceCover_split_cross_wang, Elliptic.HigherHomology.fibreHomologyNorm_zero,
    Elliptic.HigherHomology.torusH0Coordinates_pointClass, mul_one]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassOne
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH1Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) =
      ![sourceShearOne j, (j.order : ℤ)] := by
  ext i
  fin_cases i
  · rfl
  · exact surfaceCover_splitCircleClassOne_second j

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitFibreClassTwo
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitFibreClassTwo j)) =
      ![1, 0] := by
  change
    Elliptic.HigherHomology.mappingTorusH2Equiv j
        (Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod 2
          (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitFibreClassTwo j))) =
      _
  rw [splitFibreClassTwo, surfaceCover_split_section,
    Elliptic.HigherHomology.mappingTorusH2Equiv_fibre, splitFibreInputTwo,
    LinearEquiv.apply_symm_apply]
  rfl

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassTwo_second
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) 1 =
      Elliptic.HigherHomology.fibreNormIndex j := by
  change
    Elliptic.HigherHomology.mappingTorusH2Equiv j
        (Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod 2
          (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)))
        1 =
      _
  rw [Elliptic.HigherHomology.mappingTorusH2Equiv_boundary, splitCircleClassTwo,
    surfaceCover_split_cross_wang]
  change Elliptic.HigherHomology.fibreHomologyNormOneCoordinate j splitFibreInputOne = _
  rw [Elliptic.HigherHomology.fibreHomologyNormOneCoordinate_apply, splitFibreInputOne,
    LinearEquiv.apply_symm_apply, Elliptic.HigherHomology.fibreCoinvariantCoordinate_section,
    mul_one]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassTwo
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) =
      ![sourceShearTwo j, (Elliptic.HigherHomology.fibreNormIndex j : ℤ)] := by
  ext i
  fin_cases i
  · rfl
  · exact surfaceCover_splitCircleClassTwo_second j

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.cover_columns_smul {A : Type*}
    [AddCommGroup A] [Module ℤ A] (e : A ≃ₗ[ℤ] (Fin 2 → ℤ)) (u v a : A) (c d : ℤ)
    (hu : e u = ![1, 0]) (hv : e v = ![c, d]) : d • a = (d * e a 0 - c * e a 1) • u + e a 1 • v :=
  by
  apply e.injective
  rw [map_add, map_zsmul, map_zsmul, map_zsmul, hu, hv]
  ext i
  fin_cases i
  · change d * e a 0 = (d * e a 0 - c * e a 1) * 1 + e a 1 * c
    ring
  · change d * e a 1 = (d * e a 0 - c * e a 1) * 0 + e a 1 * d
    ring

public
theorem PeriodFamily.Boundary.EllipticCapKernelWang.map_cover_columns {A B : Type*}
    [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B] (e : A ≃ₗ[ℤ] (Fin 2 → ℤ))
    (L : A →ₗ[ℤ] B) (u v a : A) (c d : ℤ) (hu : e u = ![1, 0]) (hv : e v = ![c, d]) :
    d • L a = (d * e a 0 - c * e a 1) • L u + e a 1 • L v := by
  simpa only [map_add, map_zsmul] using congrArg L (cover_columns_smul e u v a c d hu hv)

private def PeriodFamily.Boundary.EllipticCapKernelWang.h1Coordinates (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 1 →ₗ[ℤ]
      Lattice :=
  PeriodFamily.FlatTorus.singularH1Equiv.toLinearMap.comp (crossWang j 1)

private def PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 2 →ₗ[ℤ]
      (Fin 6 → ℤ) :=
  PeriodFamily.FlatTorus.singularH2Coordinates.toLinearMap.comp (crossWang j 2)

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h1Coordinates_apply (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 1) :
    h1Coordinates j a = PeriodFamily.FlatTorus.singularH1Equiv (crossWang j 1 a) :=
  rfl

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_apply (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 2) :
    h2Coordinates j a = PeriodFamily.FlatTorus.singularH2Coordinates (crossWang j 2 a) :=
  rfl

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.h1Coordinates_surfaceCover (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) :
    h1Coordinates j (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 a) =
      PeriodFamily.FlatTorus.singularH1Equiv (originalAffineNorm j 1 a) := by
  rw [h1Coordinates_apply, crossWang_surfaceCover_one]

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_surfaceCover (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 2) :
    h2Coordinates j (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 a) =
      PeriodFamily.FlatTorus.singularH2Coordinates (originalAffineNorm j 2 a) := by
  rw [h2Coordinates_apply, crossWang_surfaceCover_two]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h1Coordinates_cover_columns
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 1) :
    (j.order : ℤ) • h1Coordinates j a =
      ((j.order : ℤ) *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            sourceShearOne j *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) •
          PeriodFamily.FlatTorus.singularH1Equiv (originalAffineNorm j 1 (splitFibreClassOne j)) +
        Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
          PeriodFamily.FlatTorus.singularH1Equiv
            (originalAffineNorm j 1 (splitCircleClassOne j)) := by
  have h :=
    map_cover_columns
      (Elliptic.HigherHomology.surfaceH1Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)
      (h1Coordinates j)
      (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitFibreClassOne j))
      (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) a
      (sourceShearOne j) (j.order : ℤ) (surfaceCover_splitFibreClassOne j)
      (surfaceCover_splitCircleClassOne j)
  simpa only [h1Coordinates_surfaceCover] using h

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_cover_columns
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 2) :
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ) • h2Coordinates j a =
      ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            sourceShearTwo j *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) •
          PeriodFamily.FlatTorus.singularH2Coordinates
            (originalAffineNorm j 2 (splitFibreClassTwo j)) +
        Elliptic.HigherHomology.surfaceH2Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
          PeriodFamily.FlatTorus.singularH2Coordinates
            (originalAffineNorm j 2 (splitCircleClassTwo j)) := by
  have h :=
    map_cover_columns
      (Elliptic.HigherHomology.surfaceH2Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)
      (h2Coordinates j)
      (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitFibreClassTwo j))
      (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) a
      (sourceShearTwo j) (Elliptic.HigherHomology.fibreNormIndex j : ℤ)
      (surfaceCover_splitFibreClassTwo j) (surfaceCover_splitCircleClassTwo j)
  simpa only [h2Coordinates_surfaceCover] using h

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFlat_inverse_circle_comp
    (j : Elliptic.Kind) :
    (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)).comp
        ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 3,
            RealTorus₄)) =
      (PeriodTorusHigherHomology.torusMatrixMap (Elliptic.HigherHomology.twistBasisMatrix j)).comp
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 4)) := by
  apply ContinuousMap.ext
  intro x
  change
    PeriodTorusHigherHomology.flatTorusCircleHomeomorph
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph.symm
          (PeriodTorusHigherHomology.torusMatrixMap (Elliptic.HigherHomology.twistBasisMatrix j)
            ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm x))) =
      _
  exact PeriodTorusHigherHomology.flatTorusCircleHomeomorph.apply_symm_apply _

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFlat_inverse_circle_homology
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3)
        n) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        n
        (SingularMayerVietoris.singularHomologyMap
          ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
                PeriodTorusHigherHomology.ProductTorus 3,
              RealTorus₄))
          n a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap (Elliptic.HigherHomology.twistBasisMatrix j)) n
        (SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
                PeriodTorusHigherHomology.ProductTorus 3,
              PeriodTorusHigherHomology.ProductTorus 4))
          n a) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    splitFlat_inverse_circle_comp, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitOne_unsplit_fibre
    (v : Elliptic.HigherHomology.FibreLattice) :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 4))
        1
        (PeriodTorusHigherHomology.circleSectionHomology
          (PeriodTorusHigherHomology.ProductTorus 3) 1
          (Elliptic.HigherHomology.torusH1Equiv.symm v)) =
      FirstHurewicz.loopHomologyClass
        (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Fin.cons 0 v)) := by
  rw [Elliptic.HigherHomology.torusH1Equiv_symm_apply_loop,
    PeriodTorusHigherHomology.circleSectionHomology, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology 3 v

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitOne_unsplit_circle :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
          C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
              PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 4))
        1
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3)
          0
          (PeriodTorusHigherHomology.pointClass (0 : PeriodTorusHigherHomology.ProductTorus 3))) =
      FirstHurewicz.loopHomologyClass
        (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 0 1)) := by
  rw [PeriodTorusHigherHomology.positiveCircleCross,
    PeriodTorusHigherHomology.crossProductHomology_pointClass_right]
  have hmap :
    ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
                PeriodTorusHigherHomology.ProductTorus 3,
              PeriodTorusHigherHomology.ProductTorus 4)).comp
        (PeriodTorusHigherHomology.crossInsertRight
          (0 : PeriodTorusHigherHomology.ProductTorus 3)) =
      PeriodTorusHigherHomology.torusHeadCircleMap 3 := by
    apply ContinuousMap.ext
    intro z
    rw [PeriodTorusHigherHomology.torusHeadCircleMap_apply]
    rfl
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, hmap]
  exact PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology 3

private theorem
  PeriodFamily.Boundary.EllipticCapKernelWang.splitOne_originalCoordinates_mo1973_27797
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 1) (v : Lattice)
    (h :
      SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
          1 a =
        FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 4 v)) :
    PeriodFamily.FlatTorus.singularH1Equiv a = v := by
  apply PeriodFamily.FlatTorus.singularH1Equiv.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        PeriodTorusHigherHomology.flatTorusCircleHomeomorph 1).injective
  exact h.trans (PeriodFamily.FlatTorus.inducedHomology_singularH1Equiv_symm_circle v).symm

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassOne_coordinates
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH1Equiv (splitFibreClassOne j) = ![0, 0, 1, 0] := by
  apply splitOne_originalCoordinates_mo1973_27797
  rw [splitFibreClassOne, splitFlat_inverse_circle_homology, splitFibreInputOne,
    splitOne_unsplit_fibre, SingularMayerVietoris.singularHomologyMap_one,
    PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology]
  have h : Elliptic.HigherHomology.twistBasisMatrix j *ᵥ Fin.cons 0 ![0, 1, 0] = ![0, 0, 1, 0] := by
    cases j <;> decide
  rw [h]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassOne_coordinates
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH1Equiv (splitCircleClassOne j) = j.twist := by
  apply splitOne_originalCoordinates_mo1973_27797
  rw [splitCircleClassOne, splitFlat_inverse_circle_homology, splitOne_unsplit_circle,
    SingularMayerVietoris.singularHomologyMap_one,
    PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology]
  have h : Elliptic.HigherHomology.twistBasisMatrix j *ᵥ Pi.single 0 1 = j.twist := by
    cases j <;> decide
  rw [h]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreInputTwo_product :
    splitFibreInputTwo =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 1 1))) := by
  have hv : (![1, 0, 0] : Fin 3 → ℤ) = Pi.single 0 1 := by decide
  rw [splitFibreInputTwo, hv, Elliptic.HigherHomology.torusH2Coordinates_symm_basis]
  rfl

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitTwo_fibre_unsplit :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
          C(PeriodTorusHigherHomology.CircleTopology.Circle ×
              PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 4))
        2
        (PeriodTorusHigherHomology.circleSectionHomology
          (PeriodTorusHigherHomology.ProductTorus 3) 2 splitFibreInputTwo) =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 4)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 1 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 2 1))) := by
  rw [PeriodTorusHigherHomology.circleSectionHomology, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 3) 2
        splitFibreInputTwo =
      _
  rw [splitFibreInputTwo_product]
  change
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 3) 2
        (PeriodTorusHigherHomologyPontryagin.product (PeriodTorusHigherHomology.ProductTorus 3) 1
          _ _) =
      PeriodTorusHigherHomologyPontryagin.product (PeriodTorusHigherHomology.ProductTorus 4) 1 _ _
  rw [PeriodTorusHigherHomologyPontryagin.product_natural
      (PeriodTorusHigherHomology.torusTailMap 3) (PeriodTorusHigherHomology.torusTailMap_add 3) 1,
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology,
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology]
  have hu : (Fin.cons 0 (Pi.single (0 : Fin 3) 1) : Lattice) = Pi.single 1 1 := by decide
  have hw : (Fin.cons 0 (Pi.single (1 : Fin 3) 1) : Lattice) = Pi.single 2 1 := by decide
  rw [hu, hw]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitTwo_circle_unsplit :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
          C(PeriodTorusHigherHomology.CircleTopology.Circle ×
              PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 4))
        2
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3)
          1 splitFibreInputOne) =
      PeriodTorusHigherHomologyPontryagin.product11 (PeriodTorusHigherHomology.ProductTorus 4)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 2 1))) := by
  rw [PeriodTorusHigherHomology.torusSplit_positiveCircleCross,
    PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology, splitFibreInputOne,
    Elliptic.HigherHomology.torusH1Equiv_symm_apply_loop,
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology]
  have hw : (Fin.cons 0 ![0, 1, 0] : Lattice) = Pi.single 2 1 := by decide
  rw [hw]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitTwo_fibre_unsplit_coordinates :
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
            C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                PeriodTorusHigherHomology.ProductTorus 3,
              PeriodTorusHigherHomology.ProductTorus 4))
          2
          (PeriodTorusHigherHomology.circleSectionHomology
            (PeriodTorusHigherHomology.ProductTorus 3) 2 splitFibreInputTwo)) =
      Pi.single 3 1 := by
  rw [splitTwo_fibre_unsplit]
  exact PeriodTorusCohomologyCup.coordinateTorusH2Coordinates_basis_pair 3

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitTwo_circle_unsplit_coordinates :
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
            C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                PeriodTorusHigherHomology.ProductTorus 3,
              PeriodTorusHigherHomology.ProductTorus 4))
          2
          (PeriodTorusHigherHomology.positiveCircleCross
            (PeriodTorusHigherHomology.ProductTorus 3) 1 splitFibreInputOne)) =
      Pi.single 1 1 := by
  rw [splitTwo_circle_unsplit]
  exact PeriodTorusCohomologyCup.coordinateTorusH2Coordinates_basis_pair 1

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFlat_inverse_h2_coordinates
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (PeriodTorusHigherHomology.CircleTopology.Circle ×
          PeriodTorusHigherHomology.ProductTorus 3)
        2) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (SingularMayerVietoris.singularHomologyMap
          ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
            C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                PeriodTorusHigherHomology.ProductTorus 3,
              RealTorus₄))
          2 a) =
      LocalSystemMatrices.exteriorSquare (Elliptic.HigherHomology.twistBasisMatrix j) *ᵥ
        PeriodTorusHigherHomology.coordinateTorusH2Coordinates
          (SingularMayerVietoris.singularHomologyMap
            ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
              C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                  PeriodTorusHigherHomology.ProductTorus 3,
                PeriodTorusHigherHomology.ProductTorus 4))
            2 a) := by
  rw [PeriodFamily.FlatTorus.singularH2Coordinates_apply,
    PeriodFamily.FlatTorus.singularH2Equiv_apply, splitFlat_inverse_circle_homology]
  exact
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates_matrix
      (Elliptic.HigherHomology.twistBasisMatrix j) _

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassTwo_coordinates
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH2Coordinates (splitFibreClassTwo j) = ![0, 0, 0, 1, 0, 0] := by
  rw [splitFibreClassTwo, splitFlat_inverse_h2_coordinates, splitTwo_fibre_unsplit_coordinates]
  cases j <;> decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassTwo_coordinates
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH2Coordinates (splitCircleClassTwo j) =
      ![0, j.twist 0, 0, j.twist 1, 0, 0] := by
  rw [splitCircleClassTwo, splitFlat_inverse_h2_coordinates, splitTwo_circle_unsplit_coordinates]
  cases j <;> decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_splitFibreClassOne
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH1Equiv (originalAffineNorm j 1 (splitFibreClassOne j)) =
      (Elliptic.HigherHomology.fibreNormIndex j : ℤ) • (![0, 0, 0, 1] : Lattice) := by
  rw [originalAffineNorm_h1_coordinates, splitFibreClassOne_coordinates]
  cases j
  · rw [originalNormMatrixOne_three]
    decide
  · rw [originalNormMatrixOne_four]
    decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_splitCircleClassOne
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH1Equiv (originalAffineNorm j 1 (splitCircleClassOne j)) =
      (j.order : ℤ) • j.twist := by
  rw [originalAffineNorm_h1_coordinates, splitCircleClassOne_coordinates]
  cases j
  · rw [originalNormMatrixOne_three]
    decide
  · rw [originalNormMatrixOne_four]
    decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_splitFibreClassTwo
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH2Coordinates (originalAffineNorm j 2 (splitFibreClassTwo j)) =
      (Elliptic.HigherHomology.fibreNormIndex j : ℤ) •
        ![0, 0, 0, Elliptic.HigherHomology.fibreSquareKernelVector j 0,
          Elliptic.HigherHomology.fibreSquareKernelVector j 1,
          Elliptic.HigherHomology.fibreSquareKernelVector j 2] := by
  rw [originalAffineNorm_h2_coordinates, splitFibreClassTwo_coordinates]
  cases j
  · rw [originalNormMatrixTwo_three]
    decide
  · rw [originalNormMatrixTwo_four]
    decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_splitCircleClassTwo
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (originalAffineNorm j 2 (splitCircleClassTwo j)) =
      (Elliptic.HigherHomology.fibreNormIndex j : ℤ) •
        ![0, 0, j.twist 0, 0, j.twist 1, j.twist 2] := by
  rw [originalAffineNorm_h2_coordinates, splitCircleClassTwo_coordinates]
  cases j
  · rw [originalNormMatrixTwo_three]
    decide
  · rw [originalNormMatrixTwo_four]
    decide

private def PeriodFamily.Boundary.EllipticCapKernelWang.deltaVector : Lattice :=
  ![0, 0, 0, 1]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.twist_fourth_zero (j : Elliptic.Kind) :
    j.twist 3 = 0 := by cases j <;> rfl

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearOne_correction_divisible
    (j : Elliptic.Kind) :
    (j.order : ℤ) ∣ (Elliptic.HigherHomology.fibreNormIndex j : ℤ) * sourceShearOne j := by
  let a :=
    (Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
      ![0, 1]
  have he :
    Elliptic.HigherHomology.surfaceH1Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a =
      ![0, 1] :=
    LinearEquiv.apply_symm_apply _ _
  have h := h1Coordinates_cover_columns j a
  rw [originalAffineNorm_splitFibreClassOne, originalAffineNorm_splitCircleClassOne] at h
  have h₃ := congrFun h (3 : Fin 4)
  change
    (j.order : ℤ) * h1Coordinates j a 3 =
      ((j.order : ℤ) *
              (Elliptic.HigherHomology.surfaceH1Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a)
                0 -
            sourceShearOne j *
              (Elliptic.HigherHomology.surfaceH1Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a)
                1) *
          ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * 1) +
        (Elliptic.HigherHomology.surfaceH1Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a)
            1 *
          ((j.order : ℤ) * j.twist 3) at h₃
  rw [he, twist_fourth_zero] at h₃
  change
    (j.order : ℤ) * h1Coordinates j a 3 =
      ((j.order : ℤ) * 0 - sourceShearOne j * 1) *
          ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * 1) +
        1 * ((j.order : ℤ) * 0) at h₃
  refine ⟨-h1Coordinates j a 3, ?_⟩
  linear_combination h₃

private def PeriodFamily.Boundary.EllipticCapKernelWang.h1ShearCorrection (j : Elliptic.Kind) : ℤ :=
  ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * sourceShearOne j) / j.order

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.order_mul_h1ShearCorrection
    (j : Elliptic.Kind) :
    (j.order : ℤ) * h1ShearCorrection j =
      (Elliptic.HigherHomology.fibreNormIndex j : ℤ) * sourceShearOne j := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (sourceShearOne_correction_divisible j)

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.h1Coordinates_formula (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 1) :
    h1Coordinates j a =
      Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
          j.twist +
        ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            h1ShearCorrection j *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) •
          deltaVector := by
  have h := h1Coordinates_cover_columns j a
  rw [originalAffineNorm_splitFibreClassOne, originalAffineNorm_splitCircleClassOne] at h
  have hm : (j.order : ℤ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  ext i
  apply mul_left_cancel₀ hm
  have hi := congrFun h i
  change
    (j.order : ℤ) * h1Coordinates j a i =
      ((j.order : ℤ) *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            sourceShearOne j *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) *
          ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * deltaVector i) +
        Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
          ((j.order : ℤ) * j.twist i) at hi
  change
    (j.order : ℤ) * h1Coordinates j a i =
      (j.order : ℤ) *
        (Elliptic.HigherHomology.surfaceH1Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
            j.twist i +
          ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
                Elliptic.HigherHomology.surfaceH1Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
              h1ShearCorrection j *
                Elliptic.HigherHomology.surfaceH1Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) *
            deltaVector i)
  rw [hi]
  have hk := order_mul_h1ShearCorrection j
  linear_combination
    (Elliptic.HigherHomology.surfaceH1Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
        deltaVector i) *
      hk

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.capKernel_wang_h1_coordinates
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 1) :
    PeriodFamily.FlatTorus.singularH1Equiv
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 1
          ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j 1).symm a).val) =
      Elliptic.HigherHomology.surfaceH1Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
          j.twist +
        ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            h1ShearCorrection j *
              Elliptic.HigherHomology.surfaceH1Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) •
          deltaVector :=
  h1Coordinates_formula j a

private def
    PeriodFamily.Boundary.EllipticCapKernelWang.fibreInvariantPairVector (j : Elliptic.Kind) :
    Fin 6 → ℤ :=
  ![0, 0, 0, Elliptic.HigherHomology.fibreSquareKernelVector j 0,
    Elliptic.HigherHomology.fibreSquareKernelVector j 1,
    Elliptic.HigherHomology.fibreSquareKernelVector j 2]

private def PeriodFamily.Boundary.EllipticCapKernelWang.twistDeltaVector (j : Elliptic.Kind) :
    Fin 6 → ℤ :=
  ![0, 0, j.twist 0, 0, j.twist 1, j.twist 2]

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_formula (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 2) :
    h2Coordinates j a =
      ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            sourceShearTwo j *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) •
          fibreInvariantPairVector j +
        Elliptic.HigherHomology.surfaceH2Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
          twistDeltaVector j := by
  have h := h2Coordinates_cover_columns j a
  rw [originalAffineNorm_splitFibreClassTwo, originalAffineNorm_splitCircleClassTwo] at h
  ext i
  apply mul_left_cancel₀ (Elliptic.HigherHomology.fibreNormIndex_int_ne_zero j)
  have hi := congrFun h i
  change
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ) * h2Coordinates j a i =
      ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            sourceShearTwo j *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) *
          ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * fibreInvariantPairVector j i) +
        Elliptic.HigherHomology.surfaceH2Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
          ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) * twistDeltaVector j i) at hi
  change
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ) * h2Coordinates j a i =
      (Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
        (((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
                Elliptic.HigherHomology.surfaceH2Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
              sourceShearTwo j *
                Elliptic.HigherHomology.surfaceH2Equiv j
                  (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) *
            fibreInvariantPairVector j i +
          Elliptic.HigherHomology.surfaceH2Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
            twistDeltaVector j i)
  rw [hi]
  ring

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.capKernel_wang_h2_coordinates
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 2) :
    PeriodFamily.FlatTorus.singularH2Coordinates
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 2
          ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j 2).symm a).val) =
      ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            sourceShearTwo j *
              Elliptic.HigherHomology.surfaceH2Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) •
          fibreInvariantPairVector j +
        Elliptic.HigherHomology.surfaceH2Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
          twistDeltaVector j :=
  h2Coordinates_formula j a

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.ranges_twist_zero_ne_zero_mo1973_28416
    (j : Elliptic.Kind) : j.twist 0 ≠ 0 := by cases j <;> decide

private theorem
  PeriodFamily.Boundary.EllipticCapKernelWang.ranges_fibre_kernel_zero_ne_zero_mo1973_28420
    (j : Elliptic.Kind) : Elliptic.HigherHomology.fibreSquareKernelVector j 0 ≠ 0 := by
  cases j <;> decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.ranges_h2_two_mo1973_28421
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 2) :
    h2Coordinates j a 2 =
      Elliptic.HigherHomology.surfaceH2Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 *
        j.twist 0 := by
  rw [h2Coordinates_formula]
  simp [fibreInvariantPairVector, twistDeltaVector]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.ranges_h2_three_mo1973_28422
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 2) :
    h2Coordinates j a 3 =
      ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
            Elliptic.HigherHomology.surfaceH2Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
          sourceShearTwo j *
            Elliptic.HigherHomology.surfaceH2Equiv j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) *
        Elliptic.HigherHomology.fibreSquareKernelVector j 0 := by
  rw [h2Coordinates_formula]
  simp [fibreInvariantPairVector, twistDeltaVector]

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.h2Coordinates_injective (j : Elliptic.Kind) :
    Function.Injective (h2Coordinates j) := by
  intro a b hab
  let e :=
    Elliptic.HigherHomology.surfaceH2Equiv j
      (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
  have h₁ : e a 1 = e b 1 := by
    apply mul_right_cancel₀ (ranges_twist_zero_ne_zero_mo1973_28416 j)
    simpa only [ranges_h2_two_mo1973_28421] using congrFun hab (2 : Fin 6)
  have hL := congrFun hab (3 : Fin 6)
  rw [ranges_h2_three_mo1973_28422, ranges_h2_three_mo1973_28422] at hL
  have hcoef := mul_right_cancel₀ (ranges_fibre_kernel_zero_ne_zero_mo1973_28420 j) hL
  rw [h₁] at hcoef
  have h₀ : e a 0 = e b 0 := by
    apply mul_left_cancel₀ (Elliptic.HigherHomology.fibreNormIndex_int_ne_zero j)
    linarith only [hcoef]
  apply e.injective
  funext i
  fin_cases i
  · exact h₀
  · exact h₁

private def PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWang (j : Elliptic.Kind) (n : ℕ) :
    LinearMap.ker
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology RealTorus₄ n
    where
  toFun a := MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a.val
  map_add' a b := map_add _ a.val b.val
  map_smul' k
    a :=
    (map_zsmul
          ((MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist)
                n).toAddMonoidHom.comp
            (LinearMap.ker
                (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j)
                  (n + 1))).subtype.toAddMonoidHom)
          k a).trans
      (int_smul_eq_zsmul (SingularMayerVietoris.SingularHomology RealTorus₄ n).isModule k
          (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a.val)).symm

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWang_eq_cross (j : Elliptic.Kind)
    (n : ℕ)
    (a :
      LinearMap.ker
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1))) :
    capKernelWang j n a =
      crossWang j n (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j n a) := by
  have h :=
    (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j n).symm_apply_apply a
  have hv :=
    congrArg
      (fun b :
          LinearMap.ker
            (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)) =>
        b.val)
      h
  change
    PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross j n
        (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j n a) =
      a.val at hv
  change
    MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n a.val =
      MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) n
        (PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross j n
          (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j n a))
  rw [hv]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWang_two_injective
    (j : Elliptic.Kind) : Function.Injective (capKernelWang j 2) := by
  intro a b hab
  apply (PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv j 2).injective
  apply h2Coordinates_injective j
  rw [h2Coordinates_apply, h2Coordinates_apply, ← capKernelWang_eq_cross, ←
    capKernelWang_eq_cross, hab]

private def PeriodFamily.CapKernelShear.shearOn (r : ℕ)
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus r,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus r,
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus r) :=
  ⟨fun p => (p.1 - χ p.2, p.2),
    (continuous_fst.sub (χ.continuous.comp continuous_snd)).prodMk continuous_snd⟩

private theorem PeriodFamily.CapKernelShear.circleTorus_homology_subsingleton_of_lt {r n : ℕ}
    (h : r + 1 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus r)
        n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt h
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (PeriodTorusHigherHomology.productTorusSuccHomeomorph r).symm n).injective.subsingleton

private def PeriodFamily.CapKernelShear.twoToFour_mo1973_28436 :
    C(PeriodTorusHigherHomology.ProductTorus 2, PeriodTorusHigherHomology.ProductTorus 4) :=
  (PeriodTorusHigherHomology.torusTailMap 3).comp (PeriodTorusHigherHomology.torusTailMap 2)

private def PeriodFamily.CapKernelShear.fourToTwo_mo1973_28437 :
    C(PeriodTorusHigherHomology.ProductTorus 4, PeriodTorusHigherHomology.ProductTorus 2) :=
  ⟨fun x i => x i.succ.succ, continuous_pi fun i => continuous_apply i.succ.succ⟩

private theorem PeriodFamily.CapKernelShear.fourToTwo_twoToFour_mo1973_28438
    (x : PeriodTorusHigherHomology.ProductTorus 2) :
    fourToTwo_mo1973_28437 (twoToFour_mo1973_28436 x) = x := by
  funext i
  rfl

private theorem PeriodFamily.CapKernelShear.circleProduct_retract_mo1973_28439 :
    (PeriodTorusHigherHomology.circleProductMap fourToTwo_mo1973_28437).comp
        (PeriodTorusHigherHomology.circleProductMap twoToFour_mo1973_28436) =
      ContinuousMap.id
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2) := by
  apply ContinuousMap.ext
  intro p
  exact Prod.ext rfl (fourToTwo_twoToFour_mo1973_28438 p.2)

private theorem
  PeriodFamily.CapKernelShear.circleProduct_twoToFour_homology_injective_mo1973_28440 (n : ℕ) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap twoToFour_mo1973_28436) n) := by
  have h :
    Function.LeftInverse
      (SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap fourToTwo_mo1973_28437) n)
      (SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap twoToFour_mo1973_28436) n) := by
    intro a
    change
      ((SingularMayerVietoris.singularHomologyMap
                (PeriodTorusHigherHomology.circleProductMap fourToTwo_mo1973_28437) n).comp
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.circleProductMap twoToFour_mo1973_28436) n))
          a =
        a
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, circleProduct_retract_mo1973_28439,
      PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply]
  exact h.injective

private theorem PeriodFamily.CapKernelShear.positiveCircleCross_two_surjective_mo1973_28441 :
    Function.Surjective
      (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 2)
        2) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt (show 2 < 3 by decide)
  intro a
  obtain ⟨b, rfl⟩ :=
    (PeriodTorusHigherHomology.circleProductHomologyEquiv
          (PeriodTorusHigherHomology.ProductTorus 2) 2).symm.surjective
      a
  refine ⟨b.2, ?_⟩
  rw [PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross,
    (Subsingleton.elim b.1 0), map_zero, zero_add]

private theorem PeriodFamily.CapKernelShear.twoToFour_shear_mo1973_28442
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 2,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    (PeriodTorusHigherHomology.circleProductMap twoToFour_mo1973_28436).comp (shearOn 2 χ) =
      (shear (χ.comp fourToTwo_mo1973_28437)).comp
        (PeriodTorusHigherHomology.circleProductMap twoToFour_mo1973_28436) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  change
    (c - χ x, twoToFour_mo1973_28436 x) =
      (c - χ (fourToTwo_mo1973_28437 (twoToFour_mo1973_28436 x)), twoToFour_mo1973_28436 x)
  rw [fourToTwo_twoToFour_mo1973_28438]

private theorem PeriodFamily.CapKernelShear.shearOn_two_positiveCircleCross_mo1973_28443
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 2,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 2) :
    SingularMayerVietoris.singularHomologyMap (shearOn 2 χ) 3
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 2)
          2 b) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 2) 2
        b := by
  apply circleProduct_twoToFour_homology_injective_mo1973_28440 3
  change
    ((SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.circleProductMap twoToFour_mo1973_28436) 3).comp
          (SingularMayerVietoris.singularHomologyMap (shearOn 2 χ) 3))
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 2)
          2 b) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, twoToFour_shear_mo1973_28442,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    PeriodTorusHigherHomology.positiveCircleCross_naturality]
  apply shear_positiveCircleCross_two (χ.comp fourToTwo_mo1973_28437)
  intro x y
  change
    χ (fourToTwo_mo1973_28437 x + fourToTwo_mo1973_28437 y) =
      χ (fourToTwo_mo1973_28437 x) + χ (fourToTwo_mo1973_28437 y)
  exact hχ _ _

private theorem PeriodFamily.CapKernelShear.shearOn_two_homologyThree
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 2,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2)
        3) :
    SingularMayerVietoris.singularHomologyMap (shearOn 2 χ) 3 a = a := by
  obtain ⟨b, rfl⟩ := positiveCircleCross_two_surjective_mo1973_28441 a
  exact shearOn_two_positiveCircleCross_mo1973_28443 χ hχ b

private def PeriodFamily.CapKernelShear.threeSwapCoordinates :
    ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3) ≃ₜ
      ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2))
    where
  toFun p := (p.2 0, (p.1, fun i => p.2 i.succ))
  invFun p := (p.2.1, Fin.cons p.1 p.2.2)
  left_inv
    p := by
    apply Prod.ext
    · rfl
    · exact Fin.cons_self_tail p.2
  right_inv p := rfl
  continuous_toFun :=
    ((continuous_apply 0).comp continuous_snd).prodMk
      (continuous_fst.prodMk
        (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))
  continuous_invFun :=
    (continuous_fst.comp continuous_snd).prodMk
      ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 2).symm.continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

private def PeriodFamily.CapKernelShear.threeHeadMap
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2),
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2)) :=
  (threeSwapCoordinates : C(_, _)).comp ((shearOn 3 χ).comp (threeSwapCoordinates.symm : C(_, _)))

private theorem PeriodFamily.CapKernelShear.threeHeadMap_fst
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (p :
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2)) :
    (threeHeadMap χ p).1 = p.1 :=
  rfl

private theorem PeriodFamily.CapKernelShear.threeSwapCoordinates_shear
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    (threeSwapCoordinates : C(_, _)).comp (shearOn 3 χ) =
      (threeHeadMap χ).comp (threeSwapCoordinates : C(_, _)) := by
  apply ContinuousMap.ext
  intro p
  change
    threeSwapCoordinates (shearOn 3 χ p) =
      threeSwapCoordinates (shearOn 3 χ (threeSwapCoordinates.symm (threeSwapCoordinates p)))
  rw [Homeomorph.symm_apply_apply]

private def PeriodFamily.CapKernelShear.threeTailCharacter
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle))) :
    C(PeriodTorusHigherHomology.ProductTorus 2,
      (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  χ.comp (PeriodTorusHigherHomology.torusTailMap 2)

private theorem PeriodFamily.CapKernelShear.threeTailCharacter_add
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (x y : PeriodTorusHigherHomology.ProductTorus 2) :
    threeTailCharacter χ (x + y) = threeTailCharacter χ x + threeTailCharacter χ y := by
  change
    χ (PeriodTorusHigherHomology.torusTailMap 2 (x + y)) =
      χ (PeriodTorusHigherHomology.torusTailMap 2 x) +
        χ (PeriodTorusHigherHomology.torusTailMap 2 y)
  rw [PeriodTorusHigherHomology.torusTailMap_add, hχ]

private theorem PeriodFamily.CapKernelShear.threeCharacter_split
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (t : (PeriodTorusHigherHomology.CircleTopology.Circle))
    (y : PeriodTorusHigherHomology.ProductTorus 2) :
    χ (Fin.cons t y) =
      χ (PeriodTorusHigherHomology.torusHeadCircleMap 2 t) + threeTailCharacter χ y := by
  have h :
    (Fin.cons t y : PeriodTorusHigherHomology.ProductTorus 3) =
      PeriodTorusHigherHomology.torusHeadCircleMap 2 t +
        PeriodTorusHigherHomology.torusTailMap 2 y := by
    rw [PeriodTorusHigherHomology.torusHeadCircleMap_apply,
      PeriodTorusHigherHomology.torusTailMap_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [h, hχ]
  rfl

private theorem PeriodFamily.CapKernelShear.threeHeadMap_fibre
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (t : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    PeriodFamily.Homology.headMapFibre (threeHeadMap χ) t =
      (PeriodTorusHigherHomology.rightTranslation
            (-χ (PeriodTorusHigherHomology.torusHeadCircleMap 2 t),
              (0 : PeriodTorusHigherHomology.ProductTorus 2))).comp
        (shearOn 2 (threeTailCharacter χ)) := by
  apply ContinuousMap.ext
  rintro ⟨c, y⟩
  apply Prod.ext
  · change
      c - χ (Fin.cons t y) =
        (c - threeTailCharacter χ y) + -χ (PeriodTorusHigherHomology.torusHeadCircleMap 2 t)
    rw [threeCharacter_split χ hχ]
    abel
  · change y = y + 0
    exact (add_zero y).symm

private theorem PeriodFamily.CapKernelShear.threeHeadBoundary_injective :
    Function.Injective
      (PeriodTorusHigherHomology.circleBoundary
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2)
        3) := by
  let := circleTorus_homology_subsingleton_of_lt (r := 2) (n := 4) (by decide)
  intro a b hab
  apply
    (PeriodTorusHigherHomology.circleProductHomologyEquiv
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2)
        3).injective
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hab

private theorem PeriodFamily.CapKernelShear.threeHeadMap_fibre_homologyThree
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (t : (PeriodTorusHigherHomology.CircleTopology.Circle))
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2)
        3) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.headMapFibre (threeHeadMap χ) t) 3 a =
      a := by
  rw [threeHeadMap_fibre χ hχ, PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.rightTranslation_singularHomologyMap, LinearMap.id_comp]
  exact shearOn_two_homologyThree (threeTailCharacter χ) (threeTailCharacter_add χ hχ) a

private theorem PeriodFamily.CapKernelShear.threeHeadMap_homologyFour
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
            PeriodTorusHigherHomology.ProductTorus 2))
        4) :
    SingularMayerVietoris.singularHomologyMap (threeHeadMap χ) 4 a = a := by
  apply threeHeadBoundary_injective
  rw [PeriodFamily.Homology.circleBoundary_headMap (threeHeadMap χ) (threeHeadMap_fst χ) 3 a]
  exact
    threeHeadMap_fibre_homologyThree χ hχ PeriodTorusHigherHomology.CirclePaths.quarterPoint
      (PeriodTorusHigherHomology.circleBoundary
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 2)
        3 a)

private theorem PeriodFamily.CapKernelShear.shearOn_three_homologyFour
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 3,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3)
        4) :
    SingularMayerVietoris.singularHomologyMap (shearOn 3 χ) 4 a = a := by
  apply (PeriodTorusHigherHomology.homeomorphHomologyEquiv threeSwapCoordinates 4).injective
  simp only [PeriodTorusHigherHomology.homeomorphHomologyEquiv_apply]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    threeSwapCoordinates_shear, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]
  exact threeHeadMap_homologyFour χ hχ _

private theorem PeriodFamily.CapKernelShear.shear_comp_threeSubtorus
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (f : C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 4)) :
    (shear χ).comp (PeriodTorusHigherHomology.circleProductMap f) =
      (PeriodTorusHigherHomology.circleProductMap f).comp (shearOn 3 (χ.comp f)) := by
  apply ContinuousMap.ext
  intro x
  rfl

private theorem PeriodFamily.CapKernelShear.shear_positiveCircleCross_three_map
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (f : C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 4))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    SingularMayerVietoris.singularHomologyMap (shear χ) 4
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          3 (SingularMayerVietoris.singularHomologyMap f 3 b)) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) 3
        (SingularMayerVietoris.singularHomologyMap f 3 b) := by
  have hχf : ∀ x y, (χ.comp f) (x + y) = (χ.comp f) x + (χ.comp f) y := by
    intro x y
    change χ (f (x + y)) = χ (f x) + χ (f y)
    rw [hf, hχ]
  have hnat := PeriodTorusHigherHomology.positiveCircleCross_naturality f 3 b
  calc
    SingularMayerVietoris.singularHomologyMap (shear χ) 4
          (PeriodTorusHigherHomology.positiveCircleCross
            (PeriodTorusHigherHomology.ProductTorus 4) 3
            (SingularMayerVietoris.singularHomologyMap f 3 b)) =
        SingularMayerVietoris.singularHomologyMap (shear χ) 4
          (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.circleProductMap f) 4
            (PeriodTorusHigherHomology.positiveCircleCross
              (PeriodTorusHigherHomology.ProductTorus 3) 3 b)) :=
      congrArg (SingularMayerVietoris.singularHomologyMap (shear χ) 4) hnat.symm
    _ =
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.circleProductMap f) 4
          (SingularMayerVietoris.singularHomologyMap (shearOn 3 (χ.comp f)) 4
            (PeriodTorusHigherHomology.positiveCircleCross
              (PeriodTorusHigherHomology.ProductTorus 3) 3 b)) := by
      rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
        shear_comp_threeSubtorus, PeriodTorusHigherHomology.singularHomologyMap_comp,
        LinearMap.comp_apply]
    _ =
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.circleProductMap f) 4
          (PeriodTorusHigherHomology.positiveCircleCross
            (PeriodTorusHigherHomology.ProductTorus 3) 3 b) :=
      (congrArg
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.circleProductMap f)
          4)
        (shearOn_three_homologyFour (χ.comp f) hχf
          (PeriodTorusHigherHomology.positiveCircleCross
            (PeriodTorusHigherHomology.ProductTorus 3) 3 b)))
    _ =
        PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) 3
          (SingularMayerVietoris.singularHomologyMap f 3 b) :=
      hnat

private theorem PeriodFamily.CapKernelShear.shear_positiveCircleCross_three
    (χ :
      C(PeriodTorusHigherHomology.ProductTorus 4,
        (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3) :
    SingularMayerVietoris.singularHomologyMap (shear χ) 4
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          3 b) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4) 3
        b := by
  have h :
    (SingularMayerVietoris.singularHomologyMap (shear χ) 4).comp
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
          3) =
      PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 4)
        3 := by
    apply (PeriodTorusHigherHomology.coordinateTorusBasis 4 3).ext
    intro i
    simp only [LinearMap.comp_apply, PeriodTorusHigherHomology.coordinateTorusBasis_apply,
      PeriodTorusHigherHomology.coordinateTorusClass]
    exact
      shear_positiveCircleCross_three_map χ hχ
        (PeriodTorusHigherHomology.coordinateTorusMap 4 3 i)
        (PeriodTorusHigherHomology.coordinateTorusMap_add 4 3 i)
        (PeriodTorusHigherHomology.productTorusTopClass 3)
  exact LinearMap.congr_fun h b

private theorem PeriodFamily.CapKernelShear.realShear_positiveCircleCross_three
    (χ : C(RealTorus₄, (PeriodTorusHigherHomology.CircleTopology.Circle)))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    SingularMayerVietoris.singularHomologyMap (realShear χ) 4
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 3 a) =
      PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 3 a := by
  apply (PeriodTorusHigherHomology.homeomorphHomologyEquiv realCircleCoordinates 4).injective
  change
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)))
        4
        (SingularMayerVietoris.singularHomologyMap (realShear χ) 4
          (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 3 a)) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap
          (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
            C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4)))
        4 (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 3 a)
  simp only [realShear_coordinate_homology,
    PeriodTorusHigherHomology.positiveCircleCross_naturality]
  exact
    shear_positiveCircleCross_three (coordinateCharacter χ) (coordinateCharacter_add χ hχ)
      (SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.flatTorusCircleHomeomorph :
          C(RealTorus₄, PeriodTorusHigherHomology.ProductTorus 4))
        3 a)

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.nativeShear_positiveCircleCross_three
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    SingularMayerVietoris.singularHomologyMap (nativeShear j) 4
        (PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 3 a) =
      PeriodTorusHigherHomology.positiveCircleCross RealTorus₄ 3 a := by
  rw [nativeShear_eq_realShear]
  exact
    PeriodFamily.CapKernelShear.realShear_positiveCircleCross_three (twistCircleCharacter j)
      (twistCircleCharacter_add j) a

private def
    PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixThree (j : Elliptic.Kind) :
    LatticeMatrix :=
  ∑ k ∈ Finset.range j.order, (LocalSystemMatrices.exteriorCube j.matrix) ^ k

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffine_h3_coordinates
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 3 a) =
      LocalSystemMatrices.exteriorCube j.matrix *ᵥ
        PeriodFamily.FlatTorus.singularH3Coordinates a := by
  rw [MappingTorusHomology.monodromyHomologyMap,
    PeriodFamily.Boundary.flatTorusAffine_homology_triangle]
  change
    PeriodFamily.FlatTorus.singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) :
            C(RealTorus₄, RealTorus₄))
          3 a) =
      _
  rw [PeriodFamily.FlatTorus.singularH3Coordinates_inducedHomology_triangle,
    SpecialPeriods.EllipticFilling.ellipticGenerator_dual_matrix]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffine_pow_h3_coordinates
    (j : Elliptic.Kind) (k : ℕ) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        ((MappingTorusHomology.monodromyHomologyMap (Elliptic.flatTorusAffine j j.twist) 3 ^ k)
          a) =
      (LocalSystemMatrices.exteriorCube j.matrix) ^ k *ᵥ
        PeriodFamily.FlatTorus.singularH3Coordinates a := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, originalAffine_h3_coordinates, ih, Matrix.mulVec_mulVec,
      ← pow_succ']

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_h3_coordinates
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates (originalAffineNorm j 3 a) =
      originalNormMatrixThree j *ᵥ PeriodFamily.FlatTorus.singularH3Coordinates a := by
  rw [originalAffineNorm_sum_powers, LinearMap.sum_apply, map_sum]
  simp only [originalAffine_pow_h3_coordinates]
  exact (Matrix.sum_mulVec _ _ _).symm

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixThree_three :
    originalNormMatrixThree .three = !![3, 0, 0, 0; -1, 0, 0, 0; 2, 0, 0, 0; 0, -12, -6, 3] := by
  change (∑ k ∈ Finset.range 3, PeriodTorusHigherHomologyExterior.cubeA₁ ^ k) = _
  rw [PeriodTorusHigherHomologyExterior.cubeA₁_eq]
  decide

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalNormMatrixThree_four :
    originalNormMatrixThree .four = !![4, 0, 0, 0; -2, 0, 0, 0; 2, 0, 0, 0; 0, -12, -12, 4] := by
  change (∑ k ∈ Finset.range 4, PeriodTorusHigherHomologyExterior.cubeA₂ ^ k) = _
  rw [PeriodTorusHigherHomologyExterior.cubeA₂_eq]
  decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.crossWang_surfaceCover_three
    (j : Elliptic.Kind) (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    crossWang j 3 (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 a) =
      originalAffineNorm j 3 a :=
  crossWang_surfaceCover_of_shear j 3 a (nativeShear_positiveCircleCross_three j a)

private def PeriodFamily.Boundary.EllipticCapKernelWang.h3Coordinates (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) 3 →ₗ[ℤ]
      Lattice :=
  PeriodFamily.FlatTorus.singularH3Coordinates.toLinearMap.comp (crossWang j 3)

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h3Coordinates_apply (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) 3) :
    h3Coordinates j a = PeriodFamily.FlatTorus.singularH3Coordinates (crossWang j 3 a) :=
  rfl

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.h3Coordinates_surfaceCover (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 3) :
    h3Coordinates j (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 a) =
      PeriodFamily.FlatTorus.singularH3Coordinates (originalAffineNorm j 3 a) := by
  rw [h3Coordinates_apply, crossWang_surfaceCover_three]

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreInputThree :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 :=
  Elliptic.HigherHomology.torusH3Coordinates.symm 1

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreInputThree_coordinates :
    Elliptic.HigherHomology.torusH3Coordinates splitFibreInputThree = 1 :=
  Elliptic.HigherHomology.torusH3Coordinates.apply_symm_apply 1

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreInputThree_product :
    splitFibreInputThree =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 3)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 1 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 3 (Pi.single 2 1))) :=
  Elliptic.HigherHomology.torusH3Coordinates_symm_one

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassThree (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology RealTorus₄ 3 :=
  SingularMayerVietoris.singularHomologyMap
    ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3,
        RealTorus₄))
    3
    (PeriodTorusHigherHomology.circleSectionHomology (PeriodTorusHigherHomology.ProductTorus 3) 3
      splitFibreInputThree)

private def PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassThree (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology RealTorus₄ 3 :=
  SingularMayerVietoris.singularHomologyMap
    ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
      C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3,
        RealTorus₄))
    3
    (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3) 2
      splitFibreInputTwo)

private def PeriodFamily.Boundary.EllipticCapKernelWang.sourceShearThree (j : Elliptic.Kind) : ℤ :=
  Elliptic.HigherHomology.surfaceH3Equiv j
    (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
    (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j)) 0

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitFibreClassThree
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH3Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 (splitFibreClassThree j)) =
      ![1, 0] := by
  change
    Elliptic.HigherHomology.mappingTorusH3Equiv j
        (Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod 3
          (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3
            (splitFibreClassThree j))) =
      _
  rw [splitFibreClassThree, surfaceCover_split_section,
    Elliptic.HigherHomology.mappingTorusH3Equiv_fibre, splitFibreInputThree_coordinates]

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassThree_second
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH3Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j))
        1 =
      Elliptic.HigherHomology.fibreNormIndex j := by
  change
    Elliptic.HigherHomology.mappingTorusH3Equiv j
        (Elliptic.HigherHomology.surfaceMappingTorusHomologyEquiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod 3
          (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3
            (splitCircleClassThree j)))
        1 =
      _
  rw [Elliptic.HigherHomology.mappingTorusH3Equiv_boundary, splitCircleClassThree,
    surfaceCover_split_cross_wang]
  change Elliptic.HigherHomology.fibreHomologyNormTwoCoordinate j splitFibreInputTwo = _
  rw [Elliptic.HigherHomology.fibreHomologyNormTwoCoordinate_apply, splitFibreInputTwo,
    LinearEquiv.apply_symm_apply]
  simp only [Matrix.cons_val_zero, mul_one]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.surfaceCover_splitCircleClassThree
    (j : Elliptic.Kind) :
    Elliptic.HigherHomology.surfaceH3Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod
        (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j)) =
      ![sourceShearThree j, (Elliptic.HigherHomology.fibreNormIndex j : ℤ)] := by
  ext i
  fin_cases i
  · rfl
  · exact surfaceCover_splitCircleClassThree_second j

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitThree_fibre_unsplit :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
          C(PeriodTorusHigherHomology.CircleTopology.Circle ×
              PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 4))
        3
        (PeriodTorusHigherHomology.circleSectionHomology
          (PeriodTorusHigherHomology.ProductTorus 3) 3 splitFibreInputThree) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 4)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 1 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 2 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 3 1))) := by
  rw [PeriodTorusHigherHomology.circleSectionHomology, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 3) 3
        splitFibreInputThree =
      _
  rw [splitFibreInputThree_product,
    PeriodTorusHigherHomologyPontryagin.tripleProduct_natural
      (PeriodTorusHigherHomology.torusTailMap 3) (PeriodTorusHigherHomology.torusTailMap_add 3),
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology,
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology,
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology]
  have hu : (Fin.cons 0 (Pi.single (0 : Fin 3) 1) : Lattice) = Pi.single 1 1 := by decide
  have hw : (Fin.cons 0 (Pi.single (1 : Fin 3) 1) : Lattice) = Pi.single 2 1 := by decide
  have hd : (Fin.cons 0 (Pi.single (2 : Fin 3) 1) : Lattice) = Pi.single 3 1 := by decide
  rw [hu, hw, hd]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitThree_circle_unsplit :
    SingularMayerVietoris.singularHomologyMap
        ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
          C(PeriodTorusHigherHomology.CircleTopology.Circle ×
              PeriodTorusHigherHomology.ProductTorus 3,
            PeriodTorusHigherHomology.ProductTorus 4))
        3
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3)
          2 splitFibreInputTwo) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 4)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 1 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single 2 1))) := by
  rw [PeriodTorusHigherHomology.torusSplit_positiveCircleCross,
    PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology, splitFibreInputTwo_product,
    PeriodTorusHigherHomologyPontryagin.tripleProduct_apply]
  change
    PeriodTorusHigherHomologyPontryagin.product (PeriodTorusHigherHomology.ProductTorus 4) 2 _
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusTailMap 3) 2
          (PeriodTorusHigherHomologyPontryagin.product (PeriodTorusHigherHomology.ProductTorus 3)
            1 _ _)) =
      _
  rw [PeriodTorusHigherHomologyPontryagin.product_natural
      (PeriodTorusHigherHomology.torusTailMap 3) (PeriodTorusHigherHomology.torusTailMap_add 3) 1,
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology,
    PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology]
  have hu : (Fin.cons 0 (Pi.single (0 : Fin 3) 1) : Lattice) = Pi.single 1 1 := by decide
  have hw : (Fin.cons 0 (Pi.single (1 : Fin 3) 1) : Lattice) = Pi.single 2 1 := by decide
  rw [hu, hw]

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.splitThree_basis_coordinates (i : Fin 4) :
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates
        (PeriodTorusHigherHomologyPontryagin.tripleProduct
          (PeriodTorusHigherHomology.ProductTorus 4)
          (FirstHurewicz.loopHomologyClass
            (PeriodTorusHigherHomology.coordinatePeriodLoop 4
              (Pi.single (LocalSystemMatrices.tripleIndices i 0) 1)))
          (FirstHurewicz.loopHomologyClass
            (PeriodTorusHigherHomology.coordinatePeriodLoop 4
              (Pi.single (LocalSystemMatrices.tripleIndices i 1) 1)))
          (FirstHurewicz.loopHomologyClass
            (PeriodTorusHigherHomology.coordinatePeriodLoop 4
              (Pi.single (LocalSystemMatrices.tripleIndices i 2) 1)))) =
      Pi.single i 1 := by
  have h :
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv.symm
        (PeriodTorusHigherHomologyExterior.cubeBasis i) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (PeriodTorusHigherHomology.ProductTorus 4)
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4
            (Pi.single (LocalSystemMatrices.tripleIndices i 0) 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4
            (Pi.single (LocalSystemMatrices.tripleIndices i 1) 1)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 4
            (Pi.single (LocalSystemMatrices.tripleIndices i 2) 1))) := by
    rw [PeriodTorusHigherHomologyExterior.cubeBasis_apply,
      PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_symm_ιMulti]
    simp only [Function.comp_apply, PeriodTorusHigherHomologyExterior.latticeBasis,
      Pi.basisFun_apply]
  rw [← h]
  change
    PeriodTorusHigherHomologyExterior.cubeCoordinates
        (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
          (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv.symm
            (PeriodTorusHigherHomologyExterior.cubeBasis i))) =
      _
  rw [LinearEquiv.apply_symm_apply]
  change
    PeriodTorusHigherHomologyExterior.cubeBasis.equivFun
        (PeriodTorusHigherHomologyExterior.cubeBasis i) =
      _
  ext k
  simp [Pi.single_apply, eq_comm]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitThree_fibre_unsplit_coordinates :
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
            C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                PeriodTorusHigherHomology.ProductTorus 3,
              PeriodTorusHigherHomology.ProductTorus 4))
          3
          (PeriodTorusHigherHomology.circleSectionHomology
            (PeriodTorusHigherHomology.ProductTorus 3) 3 splitFibreInputThree)) =
      Pi.single 3 1 := by
  rw [splitThree_fibre_unsplit]
  exact splitThree_basis_coordinates 3

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitThree_circle_unsplit_coordinates :
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
            C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                PeriodTorusHigherHomology.ProductTorus 3,
              PeriodTorusHigherHomology.ProductTorus 4))
          3
          (PeriodTorusHigherHomology.positiveCircleCross
            (PeriodTorusHigherHomology.ProductTorus 3) 2 splitFibreInputTwo)) =
      Pi.single 0 1 := by
  rw [splitThree_circle_unsplit]
  exact splitThree_basis_coordinates 0

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFlat_inverse_h3_coordinates
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        (PeriodTorusHigherHomology.CircleTopology.Circle ×
          PeriodTorusHigherHomology.ProductTorus 3)
        3) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          ((Elliptic.HigherHomology.splitFlatTorusHomeomorph j).symm :
            C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                PeriodTorusHigherHomology.ProductTorus 3,
              RealTorus₄))
          3 a) =
      LocalSystemMatrices.exteriorCube (Elliptic.HigherHomology.twistBasisMatrix j) *ᵥ
        PeriodTorusHigherHomology.coordinateTorusH3Coordinates
          (SingularMayerVietoris.singularHomologyMap
            ((PeriodTorusHigherHomology.productTorusSuccHomeomorph 3).symm :
              C(PeriodTorusHigherHomology.CircleTopology.Circle ×
                  PeriodTorusHigherHomology.ProductTorus 3,
                PeriodTorusHigherHomology.ProductTorus 4))
            3 a) := by
  rw [PeriodFamily.FlatTorus.singularH3Coordinates_apply,
    PeriodFamily.FlatTorus.singularH3Equiv_apply, splitFlat_inverse_circle_homology]
  exact
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates_matrix
      (Elliptic.HigherHomology.twistBasisMatrix j) _

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitFibreClassThree_coordinates
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH3Coordinates (splitFibreClassThree j) = ![0, 0, 0, 1] := by
  rw [splitFibreClassThree, splitFlat_inverse_h3_coordinates,
    splitThree_fibre_unsplit_coordinates]
  cases j <;> decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.splitCircleClassThree_coordinates
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH3Coordinates (splitCircleClassThree j) =
      ![γ j.twist, 0, 0, 0] := by
  rw [splitCircleClassThree, splitFlat_inverse_h3_coordinates,
    splitThree_circle_unsplit_coordinates]
  cases j <;> decide

private def PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix :
    Elliptic.Kind → ℤ → Matrix (Fin 4) (Fin 2) ℤ
  | .three, c => !![0, 3; 0, -1; 0, 2; 3, -3 * c]
  | .four, c => !![0, -2; 0, 1; 0, -1; 4, -2 * c]

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix_mulVec_three (c : ℤ)
    (a : Fin 2 → ℤ) :
    topWangMatrix .three c *ᵥ a = ![3 * a 1, -a 1, 2 * a 1, 3 * a 0 - 3 * c * a 1] := by
  ext i
  fin_cases i <;> simp [topWangMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.topWangMatrix_mulVec_four (c : ℤ)
    (a : Fin 2 → ℤ) :
    topWangMatrix .four c *ᵥ a = ![-2 * a 1, a 1, -a 1, 4 * a 0 - 2 * c * a 1] := by
  ext i
  fin_cases i <;> simp [topWangMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_splitFibreClassThree
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (originalAffineNorm j 3 (splitFibreClassThree j)) =
      (j.order : ℤ) • ![0, 0, 0, 1] := by
  rw [originalAffineNorm_h3_coordinates, splitFibreClassThree_coordinates]
  cases j
  · rw [originalNormMatrixThree_three]
    decide
  · rw [originalNormMatrixThree_four]
    decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.originalAffineNorm_splitCircleClassThree
    (j : Elliptic.Kind) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (originalAffineNorm j 3 (splitCircleClassThree j)) =
      match j with
      | .three => ![3, -1, 2, 0]
      | .four => ![-4, 2, -2, 0] := by
  rw [originalAffineNorm_h3_coordinates, splitCircleClassThree_coordinates]
  cases j
  · rw [originalNormMatrixThree_three]
    decide
  · rw [originalNormMatrixThree_four]
    decide

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h3Coordinates_cover_columns
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 3) :
    (Elliptic.HigherHomology.fibreNormIndex j : ℤ) • h3Coordinates j a =
      ((Elliptic.HigherHomology.fibreNormIndex j : ℤ) *
              Elliptic.HigherHomology.surfaceH3Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 0 -
            sourceShearThree j *
              Elliptic.HigherHomology.surfaceH3Equiv j
                (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1) •
          PeriodFamily.FlatTorus.singularH3Coordinates
            (originalAffineNorm j 3 (splitFibreClassThree j)) +
        Elliptic.HigherHomology.surfaceH3Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a 1 •
          PeriodFamily.FlatTorus.singularH3Coordinates
            (originalAffineNorm j 3 (splitCircleClassThree j)) := by
  have h :=
    map_cover_columns
      (Elliptic.HigherHomology.surfaceH3Equiv j
        (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod)
      (h3Coordinates j)
      (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 (splitFibreClassThree j))
      (SingularMayerVietoris.singularHomologyMap (surfaceCover j) 3 (splitCircleClassThree j)) a
      (sourceShearThree j) (Elliptic.HigherHomology.fibreNormIndex j : ℤ)
      (surfaceCover_splitFibreClassThree j) (surfaceCover_splitCircleClassThree j)
  simpa only [h3Coordinates_surfaceCover] using h

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h3Coordinates_three
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) .three) 3) :
    h3Coordinates .three a =
      ![3 *
          Elliptic.HigherHomology.surfaceH3Equiv .three
            (SpecialPeriods.EllipticFilling.specialLocalData .three).centralPeriod a 1,
        -Elliptic.HigherHomology.surfaceH3Equiv .three
            (SpecialPeriods.EllipticFilling.specialLocalData .three).centralPeriod a 1,
        2 *
          Elliptic.HigherHomology.surfaceH3Equiv .three
            (SpecialPeriods.EllipticFilling.specialLocalData .three).centralPeriod a 1,
        3 *
            Elliptic.HigherHomology.surfaceH3Equiv .three
              (SpecialPeriods.EllipticFilling.specialLocalData .three).centralPeriod a 0 -
          3 * sourceShearThree .three *
            Elliptic.HigherHomology.surfaceH3Equiv .three
              (SpecialPeriods.EllipticFilling.specialLocalData .three).centralPeriod a 1] := by
  have h := h3Coordinates_cover_columns .three a
  rw [originalAffineNorm_splitFibreClassThree, originalAffineNorm_splitCircleClassThree] at h
  simp only [Elliptic.HigherHomology.fibreNormIndex_three, Nat.cast_one, one_smul, one_mul] at h
  rw [h]
  ext i
  fin_cases i <;> simp [Elliptic.Kind.order] <;> ring

end Mathoverflow1973

end
