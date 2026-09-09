/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyRealizations
public import LeanPool.NavierStokesAndEuler.Euler.SobolevReflection
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.CorrectionParity
import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionParity

/-! Odd parity of the actual common correction and pressure assembled from finite genuine solutions.
-/

@[expose] public section


noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerAllOrderCorrectionData EulerCylinderReflection
  EulerSobolevReflection EulerCorrectionParity EulerInviscidCorrectionParity

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The prescribed source's actual joint spatial-angular parities.
The metric and linear coefficients are even, the quadratic coefficient is odd,
and the approximate velocity and residual are odd as actual L² fields. -/
structure ParityData (A : Data period T) where
  /-- The actual pressure metric is even. -/
  metric : ∀ t x, (A.metric.coefficient t).coefficient (-x) =
    (A.metric.coefficient t).coefficient x
  /-- The actual linear coefficient is even. -/
  linear : ∀ t x, (A.linear.coefficient t).coefficient (-x) =
    (A.linear.coefficient t).coefficient x
  /-- Each actual quadratic coefficient is odd. -/
  quadratic : ∀ t i x, ((A.quadratic i).coefficient t).coefficient (-x) =
    -((A.quadratic i).coefficient t).coefficient x
  /-- The prescribed approximate velocity is an odd actual field. -/
  approximation : ∀ t, -reflection period (A.approximation.field t) = A.approximation.field t
  /-- The prescribed residual is an odd actual field. -/
  residual : ∀ t, -reflection period (A.residual.field t) = A.residual.field t

/-- Oddness of the actual common L² field forces oddness of every Sobolev realization. -/
theorem fieldTower_realization_odd (f : FieldTower period T)
    (hf : ∀ t, -reflection period (f.field t) = f.field t) (q : ℕ) (t : Icc (0 : ℝ) T) :
    oddReflection period q (f.realization q t) = f.realization q t := by
  apply value_injective period
  rw [value_oddReflection, f.value_eq]
  exact hf t

/-- Genuine PDE uniqueness makes every finite correction odd from the prescribed input parity. -/
theorem FiniteFamily.solution_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    oddReflection period (q+1) (F.solution q hq t) = F.solution q hq t := by
  apply inviscid_correction_odd period hq T hT.le (A.atOrder period q)
    (C.stabilityBudget period q) P.metric P.linear P.quadratic
    (fieldTower_realization_odd period A.approximation P.approximation (q+1))
    (fieldTower_realization_odd period A.residual P.residual q) (F.solution q hq)
    (F.initial q hq) (F.equation q hq) _ (F.divergence q hq) t
  intro s
  change value period (A.approximation.realization (q+1) s) ∈
    divergenceFreeSpace period A.κ A.direction
  rw [A.approximation.value_eq]
  exact C.divergence s

/-- The actual assembled continuous L² correction is odd. -/
theorem FiniteFamily.commonPath_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (t : Icc (0 : ℝ) T) :
    -reflection period (F.commonPath period t) = F.commonPath period t := by
  have h := congrArg (value period (q := 7)) (F.solution_odd period C P 6 le_rfl t)
  rw [value_oddReflection] at h
  exact h

/-- A continuous representative of an actual odd L² field is pointwise odd. -/
theorem continuous_representative_odd (u : LiftL2 period) (g : LiftDomain period → Vector3)
    (hu : -reflection period u = u) (hg : Continuous g)
    (hrep : (u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g) :
    ∀ x, g (-x) = -g x := by
  have hr : reflection period u = -u := by
    simpa only [neg_neg] using congrArg Neg.neg hu
  have ha : (fun x => g (-x)) =ᵐ[liftMeasure period] fun x => -g x := by
    filter_upwards [reflection_ae period u,
      (measurePreserving_reflection period).quasiMeasurePreserving.ae hrep,
      hrep, Lp.coeFn_neg u] with x h1 h2 h3 h4
    rw [hr] at h1
    rw [← h2, ← h3, ← h1, h4]
    rfl
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq ha (hg.comp continuous_neg) hg.neg)

/-- The canonical smooth correction is odd at every spatial and angular point. -/
theorem FiniteFamily.pointField_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    F.pointField period t (-x) = -F.pointField period t x := by
  have hc : Continuous (F.pointField period t) :=
    EulerMetricTransport.smoothField_continuous period (F.pointField period t)
      (F.pointField_smooth period C t)
  exact continuous_representative_odd period (F.commonPath period t) (F.pointField period t)
    (F.commonPath_odd period C P t) hc (F.pointField_ae period t) x

/-- The actual signed coercive pressure is odd at every finite Sobolev order. -/
theorem FiniteFamily.signedPressurePath_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    oddReflection period q (F.signedPressurePath period q hq t) =
      F.signedPressurePath period q hq t := by
  exact inviscid_correction_pressure_odd period hq (A.atOrder period q) t
    (P.metric t) (P.linear t) (P.quadratic t)
    (fieldTower_realization_odd period A.approximation P.approximation (q+1) t)
    (fieldTower_realization_odd period A.residual P.residual q t)
    (F.solution q hq t) (F.solution_odd period C P q hq t)

/-- The actual assembled signed pressure gradient is odd in L². -/
theorem FiniteFamily.commonPressure_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (t : Icc (0 : ℝ) T) :
    -reflection period (F.commonPressure period t) = F.commonPressure period t := by
  have h := congrArg (value period (q := 6)) (F.signedPressurePath_odd period C P 6 le_rfl t)
  rw [value_oddReflection] at h
  exact h

/-- Every realization of the assembled correction tower is odd. -/
theorem FiniteFamily.fieldTower_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    oddReflection period q ((F.fieldTower period C).realization q t) =
      (F.fieldTower period C).realization q t :=
  fieldTower_realization_odd period (F.fieldTower period C) (F.commonPath_odd period C P) q t

/-- Every realization of the actual assembled signed pressure tower is odd. -/
theorem FiniteFamily.pressureTower_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    oddReflection period q ((F.pressureTower period C).realization q t) =
      (F.pressureTower period C).realization q t :=
  fieldTower_realization_odd period (F.pressureTower period C) (F.commonPressure_odd period C P) q t

end EulerCorrectionAssembly
