/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFinite
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyParity
import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyCompatibility
import LeanPool.NavierStokesAndEuler.Euler.InviscidSobolevEvolution
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyReconstruction
import LeanPool.NavierStokesAndEuler.Euler.QuadraticSourceLimit
import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation
import LeanPool.NavierStokesAndEuler.Euler.SobolevPointMultiplication

/-!
# One all-order correction from the actual small-drift construction

The finite solutions used here are `Budget.solution` from `AllOrderDriftFinite`.
Their existence is proved by the drift-aware finite-Sobolev solver.  The generic
assembly proves compatibility from their literal equations and uniqueness; it
does not require the coarse full-velocity shrinking-radius assumption.

The resulting single field retains the residual and target-error estimates at
every external cutoff and satisfies the actual equation in every finite Sobolev
order.  Smoothness asserted here is spatial smoothness, with a jointly continuous
representative and its genuine first time derivative.
-/

section

/-! Genuine pointwise time differentiation of the generically assembled correction. -/

@[expose] public section

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerVolterraConvolution EulerSobolevPointEvaluation
  EulerSobolevJointEvaluation EulerSobolevPointMultiplication EulerSobolevCoefficientPressure
  EulerQuadraticSourceLimit EulerInviscidSobolevEvolution

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The canonical pointwise nonlinear raw source of the actual common correction. -/
def FiniteFamily.pointRawSource (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (F.rawSourcePath period 6 le_rfl t))

/-- The canonical actual time derivative, defined by bounded evaluation of the genuine continuous
Sobolev source. -/
def FiniteFamily.pointTimeDerivative (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  pointEvaluation period x (restrictOperator period (by omega : 3 ≤ 6)
    (((A.atOrder period 6).coefficients period le_rfl).apply t (F.solution 6 le_rfl t)))

/-- The actual pointwise time derivative is jointly continuous in time and space. -/
theorem FiniteFamily.pointTimeDerivative_joint_continuous (F : FiniteFamily period hT A) :
    Continuous (F.pointTimeDerivative period).uncurry :=
  path_representative_joint_continuous period
    ((restrictOperator period (by omega : 3 ≤ 6)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (sourcePath ((A.atOrder period 6).coefficients period le_rfl) (F.solution 6 le_rfl)))

/-- The pointwise time derivative is the literal raw-source and signed-pressure expression. -/
theorem FiniteFamily.pointTimeDerivative_eq_pressure (F : FiniteFamily period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    F.pointTimeDerivative period t x = -F.pointRawSource period t x -
      (A.metric.coefficient t).coefficient x (F.pointPressure period t x) := by
  unfold FiniteFamily.pointTimeDerivative
  rw [EulerInviscidSobolevEvolution.CorrectionData.source_sobolev]
  simp only [map_sub, map_neg]
  rw [pointEvaluation_coefficient period (by
      omega : 3 ≤ 6) ((A.atOrder period 6).metric.coefficient t)
    ((A.atOrder period 6).metric.jet t)]
  rfl

/-- The canonical common field has its genuine pointwise first time derivative at every interior
time. -/
theorem FiniteFamily.pointField_hasDerivAt (F : FiniteFamily period hT A)
    (x : LiftDomain period) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => F.pointField period (projIcc 0 T hT.le r) x)
      (F.pointTimeDerivative period ⟨t, ht.1.le, ht.2.le⟩ x) t := by
  have hd := sobolev_hasDerivAt period T hT.le
    ((A.atOrder period 6).coefficients period le_rfl) (F.solution 6 le_rfl)
    (F.equation 6 le_rfl) t ht
  have he := (((pointEvaluation period x).comp (restrictOperator period (by
      omega : 3 ≤ 6))).hasFDerivAt).comp_hasDerivAt t hd
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, restrictOperator_truncate,
    FiniteFamily.pointField, FiniteFamily.pointTimeDerivative, extendPath] using he

/-- The actual pointwise correction equation uses the reconstructed signed pressure and literal
matrix multiplication. -/
theorem FiniteFamily.pointField_hasDerivAt_pressure (F : FiniteFamily period hT A)
    (x : LiftDomain period) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => F.pointField period (projIcc 0 T hT.le r) x)
      (-F.pointRawSource period ⟨t, ht.1.le, ht.2.le⟩ x -
        (A.metric.coefficient ⟨t, ht.1.le, ht.2.le⟩).coefficient x
          (F.pointPressure period ⟨t, ht.1.le, ht.2.le⟩ x)) t := by
  simpa only [F.pointTimeDerivative_eq_pressure period] using F.pointField_hasDerivAt period x t ht

end EulerCorrectionAssembly

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderDriftCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerCorrectionOperators
  EulerAllOrderCorrectionData EulerCorrectionAssembly EulerGevreyMetricEstimate
  EulerVolterraConvolution EulerInviscidSobolevEvolution EulerMetricTransport
  EulerTransportDerivatives EulerSobolevPointEvaluation EulerCylinderReflection
  EulerSobolevReflection EulerSobolevCoefficientPressure

open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The drift-aware finite solutions coincide under the actual Sobolev restriction. -/
theorem Budget.solution_compatible (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) :
    (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (B.solution period (q+1) (hq.trans (Nat.le_succ q))) = B.solution period q hq :=
  (B.family period).compatible period (B.comparisonData period) q hq

/-- The common continuous L² correction constructed by the small-drift solver. -/
def Budget.commonPath (B : Budget period hT A) : C(Icc (0 : ℝ) T, LiftL2 period) :=
  (B.family period).commonPath period

/-- Every actual drift-aware finite solution represents this same common field. -/
theorem Budget.solution_value_common (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q)
    (t : Icc (0 : ℝ) T) :
    value period (B.solution period q hq t) = B.commonPath period t :=
  (B.family period).value_common period (B.comparisonData period) q hq t

/-- The common correction has zero initial trace. -/
theorem Budget.commonPath_initial (B : Budget period hT A) :
    B.commonPath period ⟨0, le_rfl, hT.le⟩ = 0 :=
  (B.family period).commonPath_initial period

/-- The common correction satisfies the genuine closed lifted divergence constraint. -/
theorem Budget.commonPath_divergence (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    B.commonPath period t ∈ divergenceFreeSpace period A.κ A.direction :=
  (B.family period).commonPath_divergence period t

/-- The common L² path satisfies the actual projected correction equation. -/
theorem Budget.commonPath_hasDerivAt (B : Budget period hT A)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le (B.commonPath period))
      (value period (((A.atOrder period 6).coefficients period le_rfl).apply
        ⟨t, ht.1.le, ht.2.le⟩
        (B.solution period 6 le_rfl ⟨t, ht.1.le, ht.2.le⟩))) t :=
  (B.family period).commonPath_hasDerivAt period t ht

/-- An actual strong spatial jet of every order for the constructed common field. -/
def Budget.commonJet (B : Budget period hT A) (n : ℕ) (t : Icc (0 : ℝ) T) :
    SpatialJet period standardDirection n (B.commonPath period t) :=
  (B.family period).commonJet period (B.comparisonData period) n t

/-- The common correction, with genuine continuous Sobolev realizations at all orders. -/
def Budget.fieldTower (B : Budget period hT A) : FieldTower period T :=
  (B.family period).fieldTower period (B.comparisonData period)

/-- The tower's underlying field is exactly the constructed common correction. -/
theorem Budget.fieldTower_field (B : Budget period hT A) :
    (B.fieldTower period).field = B.commonPath period := rfl

/-- Every Sobolev realization of the common correction has zero initial data. -/
theorem Budget.fieldTower_initial (B : Budget period hT A) (q : ℕ) :
    (B.fieldTower period).realization q ⟨0, le_rfl, hT.le⟩ = 0 := by
  apply value_injective period
  calc
    value period ((B.fieldTower period).realization q ⟨0, le_rfl, hT.le⟩) =
        (B.fieldTower period).field ⟨0, le_rfl, hT.le⟩ :=
      (B.fieldTower period).value_eq q ⟨0, le_rfl, hT.le⟩
    _ = 0 := B.commonPath_initial period
    _ = value period (0 : SobolevSpace period q) := rfl

/-- A finite drift-aware solution equals the common tower's realization at its order. -/
theorem Budget.solution_eq_realization (B : Budget period hT A) (q : ℕ) (hq : 6 ≤ q) :
    B.solution period q hq = (B.fieldTower period).realization (q+1) :=
  (B.family period).solution_eq_realization period (B.comparisonData period) q hq

/-- Both quantitative finite-solver bounds hold for the actual common realization.
The radius and residual envelope are the drift-aware input budgets. -/
theorem Budget.fieldTower_energy (B : Budget period hT A) (P : ℕ) (t : Icc (0 : ℝ) T) :
    energyNorm period P (by omega : P+6 ≤ (P+6)+1)
        (B.radius t) (B.metric.operatorPath period t)
        ((B.fieldTower period).realization ((P+6)+1) t) ≤
      2*(B.spatial (P+6) (by omega)).full.residual *
        Real.exp (3*B.growthCoefficient*t.val) ∧
    energyNorm period P (by omega : P+6 ≤ (P+6)+1)
        (B.radius t) (B.metric.operatorPath period t)
        ((B.fieldTower period).realization ((P+6)+1) t) ≤ B.delta/2 := by
  rw [← B.solution_eq_realization period (P+6) (by omega)]
  exact B.solution_energy period (P+6) (by omega) P (by omega) (by omega) t

/-- The constructed finite solution has its genuine time derivative in Hq. -/
theorem Budget.solution_sobolev_hasDerivAt (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => truncateOperator period q
      (extendPath T hT.le (B.solution period q hq) r))
      (((A.atOrder period q).coefficients period hq).apply
        ⟨t, ht.1.le, ht.2.le⟩ (B.solution period q hq ⟨t, ht.1.le, ht.2.le⟩)) t :=
  sobolev_hasDerivAt period T hT.le ((A.atOrder period q).coefficients period hq)
    (B.solution period q hq) ((B.family period).equation q hq) t ht

/-- Every finite Sobolev realization of the common correction satisfies the actual
projected nonlinear evolution, not merely an equation for an unrelated finite solve. -/
theorem Budget.fieldTower_hasDerivAt (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le ((B.fieldTower period).realization q))
      (((A.atOrder period q).coefficients period hq).apply
        ⟨t, ht.1.le, ht.2.le⟩
        ((B.fieldTower period).realization (q+1) ⟨t, ht.1.le, ht.2.le⟩)) t := by
  have hs := B.solution_sobolev_hasDerivAt period q hq t ht
  rw [B.solution_eq_realization period q hq] at hs
  have hpath := (B.fieldTower period).truncate period q
  have heq : (fun r => truncateOperator period q
      (extendPath T hT.le ((B.fieldTower period).realization (q+1)) r)) =
      extendPath T hT.le ((B.fieldTower period).realization q) := by
    funext r
    exact congrArg (fun f => f (projIcc 0 T hT.le r)) hpath
  rw [heq] at hs
  exact hs

/-- The common realization's actual derivative is the literal raw source plus signed pressure. -/
theorem Budget.fieldTower_hasDerivAt_pressure (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le ((B.fieldTower period).realization q))
      (-(A.atOrder period q).rawSource period hq ⟨t, ht.1.le, ht.2.le⟩
          ((B.fieldTower period).realization (q+1) ⟨t, ht.1.le, ht.2.le⟩) -
        coefficientSobolevOperator period (A.metric.jet q ⟨t, ht.1.le, ht.2.le⟩)
          ((A.atOrder period q).pressure period hq ⟨t, ht.1.le, ht.2.le⟩
            ((B.fieldTower period).realization (q+1) ⟨t, ht.1.le, ht.2.le⟩))) t := by
  simpa only [CorrectionData.source_sobolev, Data.atOrder] using
    B.fieldTower_hasDerivAt period q hq t ht

/-- Canonical bounded evaluation fixes a pointwise representative of the correction. -/
def Budget.pointField (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  (B.family period).pointField period t x

/-- The pointwise correction is an actual representative of the constructed L² field. -/
theorem Budget.pointField_ae (B : Budget period hT A) (t : Icc (0 : ℝ) T) :
    (B.commonPath period t : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      B.pointField period t :=
  (B.family period).pointField_ae period t

/-- The canonical correction vanishes pointwise at the initial time. -/
theorem Budget.pointField_initial (B : Budget period hT A) (x : LiftDomain period) :
    B.pointField period ⟨0, le_rfl, hT.le⟩ x = 0 := by
  change pointEvaluation period x
    (restrictOperator period (by omega : 3 ≤ 7)
      ((B.family period).solution 6 le_rfl ⟨0, le_rfl, hT.le⟩)) = 0
  simp only [(B.family period).initial, map_zero]

/-- The canonical correction is jointly continuous in time and the cylinder point. -/
theorem Budget.pointField_joint_continuous (B : Budget period hT A) :
    Continuous (B.pointField period).uncurry :=
  (B.family period).pointField_joint_continuous period

/-- The one common correction has a spatially smooth representative at every time. -/
theorem Budget.pointField_smooth (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (B.pointField period t) x) :=
  (B.family period).pointField_smooth period (B.comparisonData period) t x

/-- Its lifted divergence vanishes pointwise. -/
theorem Budget.pointField_divergence (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    (∑ i : Fin 3, (fieldDerivative period (coordinateDirection A.κ A.direction i)
      (B.pointField period t) x) i) = 0 :=
  (B.family period).pointField_divergence period (B.comparisonData period) t x

/-- Odd input data give an odd common correction by the proved PDE uniqueness. -/
theorem Budget.commonPath_odd (B : Budget period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) :
    -reflection period (B.commonPath period t) = B.commonPath period t :=
  (B.family period).commonPath_odd period (B.comparisonData period) P t

/-- The actual common Sobolev realizations retain the prescribed odd parity. -/
theorem Budget.fieldTower_odd (B : Budget period hT A) (P : ParityData period A)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    oddReflection period q ((B.fieldTower period).realization q t) =
      (B.fieldTower period).realization q t :=
  (B.family period).fieldTower_odd period (B.comparisonData period) P q t

/-- The canonical spatially smooth correction is pointwise odd for odd input data. -/
theorem Budget.pointField_odd (B : Budget period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    B.pointField period t (-x) = -B.pointField period t x :=
  (B.family period).pointField_odd period (B.comparisonData period) P t x

/-- The actual pointwise time derivative, obtained from the constructed Sobolev source. -/
def Budget.pointTimeDerivative (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) : Vector3 :=
  (B.family period).pointTimeDerivative period t x

/-- The correction's actual first time derivative is jointly continuous. -/
theorem Budget.pointTimeDerivative_joint_continuous (B : Budget period hT A) :
    Continuous (B.pointTimeDerivative period).uncurry :=
  (B.family period).pointTimeDerivative_joint_continuous period

/-- The actual time derivative equals the raw source and the signed pressure term. -/
theorem Budget.pointTimeDerivative_eq_pressure (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    B.pointTimeDerivative period t x = -(B.family period).pointRawSource period t x -
      (A.metric.coefficient t).coefficient x ((B.family period).pointPressure period t x) :=
  (B.family period).pointTimeDerivative_eq_pressure period t x

/-- The canonical common field has its genuine first time derivative at interior times. -/
theorem Budget.pointField_hasDerivAt (B : Budget period hT A)
    (x : LiftDomain period) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => B.pointField period (projIcc 0 T hT.le r) x)
      (B.pointTimeDerivative period ⟨t, ht.1.le, ht.2.le⟩ x) t :=
  (B.family period).pointField_hasDerivAt period x t ht

/-- The pointwise correction equation contains the actual raw source and signed pressure. -/
theorem Budget.pointField_hasDerivAt_pressure (B : Budget period hT A)
    (x : LiftDomain period) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => B.pointField period (projIcc 0 T hT.le r) x)
      (-(B.family period).pointRawSource period ⟨t, ht.1.le, ht.2.le⟩ x -
        (A.metric.coefficient ⟨t, ht.1.le, ht.2.le⟩).coefficient x
          ((B.family period).pointPressure period ⟨t, ht.1.le, ht.2.le⟩ x)) t :=
  (B.family period).pointField_hasDerivAt_pressure period x t ht

/-- Genuine coherent input bounds, with radius loss determined only by the actual
transport drift, construct one smooth spatial correction with all-cutoff energy
bounds and its actual finite-Sobolev evolution.  Finite existence, compatibility,
energy estimates and the correction equation are conclusions here. -/
theorem exists_smooth_lifted_correction (B : Budget period hT A) :
    ∃ (E : FieldTower period T)
      (g v : Icc (0 : ℝ) T → LiftDomain period → Vector3),
      E.field ⟨0, le_rfl, hT.le⟩ = 0 ∧
      (∀ t, E.field t ∈ divergenceFreeSpace period A.κ A.direction) ∧
      Continuous g.uncurry ∧
      (∀ t x, ContDiff ℝ ∞ (localFieldLift period (g t) x)) ∧
      (∀ t, (E.field t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g t) ∧
      (∀ t x, (∑ i : Fin 3, (fieldDerivative period
        (coordinateDirection A.κ A.direction i) (g t) x) i) = 0) ∧
      Continuous v.uncurry ∧
      (∀ x t (ht : t ∈ Ioo 0 T),
        HasDerivAt (fun r => g (projIcc 0 T hT.le r) x)
          (v ⟨t, ht.1.le, ht.2.le⟩ x) t) ∧
      (∀ (P : ℕ) t,
        energyNorm period P (by omega : P+6 ≤ (P+6)+1)
            (B.radius t) (B.metric.operatorPath period t) (E.realization ((P+6)+1) t) ≤
          2*(B.spatial (P+6) (by omega)).full.residual *
            Real.exp (3*B.growthCoefficient*t.val) ∧
        energyNorm period P (by omega : P+6 ≤ (P+6)+1)
            (B.radius t) (B.metric.operatorPath period t) (E.realization ((P+6)+1) t) ≤
          B.delta/2) ∧
      ∀ (q : ℕ) (hq : 6 ≤ q) t (ht : t ∈ Ioo 0 T),
        HasDerivAt (extendPath T hT.le (E.realization q))
          (((A.atOrder period q).coefficients period hq).apply
            ⟨t, ht.1.le, ht.2.le⟩ (E.realization (q+1) ⟨t, ht.1.le, ht.2.le⟩)) t := by
  exact ⟨B.fieldTower period, B.pointField period, B.pointTimeDerivative period,
    B.commonPath_initial period,
    B.commonPath_divergence period, B.pointField_joint_continuous period,
    B.pointField_smooth period, B.pointField_ae period, B.pointField_divergence period,
    B.pointTimeDerivative_joint_continuous period, B.pointField_hasDerivAt period,
    B.fieldTower_energy period, B.fieldTower_hasDerivAt period⟩

end EulerAllOrderDriftCorrection
