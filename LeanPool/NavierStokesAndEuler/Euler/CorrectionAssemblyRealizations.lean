/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyPressure

@[expose] public section

/-! Genuine continuous Sobolev realizations of the assembled correction and its actual pressure at
  every order. -/

noncomputable section

namespace EulerCorrectionAssembly

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The assembled correction as one actual L² field with continuous Sobolev realizations at every order. -/
def FiniteFamily.fieldTower (F : FiniteFamily period hT A) (C : ComparisonData period hT A) :
    FieldTower period T where
  field := F.commonPath period
  realization q := (restrictOperator period (by omega : q ≤ (q+6)+1)).compLeftContinuous ℝ
    (Icc (0 : ℝ) T) (F.solution (q+6) (by omega))
  value_eq q t := F.value_common period C (q+6) (by omega) t

/-- The actual signed pressure as one L² field with continuous Sobolev realizations at every order. -/
def FiniteFamily.pressureTower (F : FiniteFamily period hT A) (C : ComparisonData period hT A) :
    FieldTower period T where
  field := F.commonPressure period
  realization q := (restrictOperator period (by omega : q ≤ q+6)).compLeftContinuous ℝ
    (Icc (0 : ℝ) T) (F.signedPressurePath period (q+6) (by omega))
  value_eq q t := F.signedPressurePath_value_common period C (q+6) (by omega) t

/-- Each finite solution is exactly the common tower's realization at that same Sobolev order. -/
theorem FiniteFamily.solution_eq_realization (F : FiniteFamily period hT A) (C : ComparisonData
  period hT A)
    (q : ℕ) (hq : 6 ≤ q) :
    F.solution q hq = (F.fieldTower period C).realization (q+1) := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  exact (F.value_common period C q hq t).trans
    ((F.fieldTower period C).value_eq (q+1) t).symm

/-- Every finite signed pressure is exactly the common pressure tower's realization at that order. -/
theorem FiniteFamily.signedPressurePath_eq_realization (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) :
    F.signedPressurePath period q hq = (F.pressureTower period C).realization q := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  exact (F.signedPressurePath_value_common period C q hq t).trans
    ((F.pressureTower period C).value_eq q t).symm

end EulerCorrectionAssembly
