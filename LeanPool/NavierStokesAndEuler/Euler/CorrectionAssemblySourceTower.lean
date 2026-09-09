/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftCorrection
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressure

@[expose] public section

/-! Continuous all-order realizations of the actual nonlinear source and time derivative. -/

noncomputable section

namespace EulerCorrectionAssembly

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerSobolevCoefficientPressure EulerInviscidSobolevEvolution

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

local instance sourceTowerGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
local instance sourceTowerSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

theorem FiniteFamily.rawSourcePath_value_base (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (F.rawSourcePath period q hq t) =
      value period (F.rawSourcePath period 6 le_rfl t) := by
  exact Nat.le_induction (P := fun n hn => value period (F.rawSourcePath period n hn t) =
      value period (F.rawSourcePath period 6 le_rfl t)) rfl
    (fun n hn ih => (F.rawSourcePath_value_succ period C n hn t).trans ih) q hq

/-- One actual source field, represented continuously at every finite order. -/
def FiniteFamily.rawSourceTower (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) : FieldTower period T where
  field := (valueOperator period 6).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    (F.rawSourcePath period 6 le_rfl)
  realization q := (restrictOperator period (by omega : q ≤ q+6)).compLeftContinuous ℝ
    (Icc (0 : ℝ) T) (F.rawSourcePath period (q+6) (by omega))
  value_eq q t := F.rawSourcePath_value_base period C (q+6) (by omega) t

theorem FiniteFamily.rawSourcePath_eq_realization (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    F.rawSourcePath period q hq t = (F.rawSourceTower period C).realization q t := by
  apply value_injective period
  exact (F.rawSourcePath_value_base period C q hq t).trans
    ((F.rawSourceTower period C).value_eq q t).symm

/-- The literal signed pressure equation defines a continuous all-order
field, subsequently identified with the genuine time derivative. -/
def FiniteFamily.timeDerivativeTower (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) : FieldTower period T where
  field := -(F.rawSourceTower period C).field -
    ⟨fun t => (A.metric.coefficient t).operator (F.commonPressure period t),
      A.metric_continuous.clm_apply (F.commonPressure period).continuous⟩
  realization q := -(F.rawSourceTower period C).realization q -
    ⟨fun t => coefficientSobolevOperator period (A.metric.jet q t)
        ((F.pressureTower period C).realization q t),
      (A.metric.continuous q).clm_apply ((F.pressureTower period C).realization q).continuous⟩
  value_eq q t := by
    change -value period ((F.rawSourceTower period C).realization q t) -
      value period (coefficientSobolevOperator period (A.metric.jet q t)
        ((F.pressureTower period C).realization q t)) = _
    rw [coefficientSobolevOperator_value, (F.rawSourceTower period C).value_eq,
      (F.pressureTower period C).value_eq]
    rfl

/-- The source returned by the constructed finite solver is exactly the
corresponding realization of the common derivative field. -/
theorem FiniteFamily.source_eq_timeDerivativeTower (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    ((A.atOrder period q).coefficients period hq).apply t (F.solution q hq t) =
      (F.timeDerivativeTower period C).realization q t := by
  rw [CorrectionData.source_sobolev]
  change -F.rawSourcePath period q hq t -
    coefficientSobolevOperator period (A.metric.jet q t) (F.signedPressurePath period q hq t) = _
  rw [F.rawSourcePath_eq_realization period C q hq t,
    F.signedPressurePath_eq_realization period C q hq]
  rfl

end EulerCorrectionAssembly

namespace EulerAllOrderDriftCorrection

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData
  EulerCorrectionOperators EulerVolterraConvolution EulerCorrectionAssembly

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

def Budget.rawSourceTower (B : Budget period hT A) : FieldTower period T :=
  (B.family period).rawSourceTower period (B.comparisonData period)

def Budget.timeDerivativeTower (B : Budget period hT A) : FieldTower period T :=
  (B.family period).timeDerivativeTower period (B.comparisonData period)

theorem Budget.rawSource_eq_realization (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    (A.atOrder period q).rawSource period hq t ((B.fieldTower period).realization (q+1) t) =
      (B.rawSourceTower period).realization q t := by
  rw [← B.solution_eq_realization period q hq]
  exact (B.family period).rawSourcePath_eq_realization period (B.comparisonData period) q hq t

theorem Budget.source_eq_timeDerivativeTower (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    ((A.atOrder period q).coefficients period hq).apply t
        ((B.fieldTower period).realization (q+1) t) =
      (B.timeDerivativeTower period).realization q t := by
  rw [← B.solution_eq_realization period q hq]
  exact (B.family period).source_eq_timeDerivativeTower period (B.comparisonData period) q hq t

/-- At every interior time, this continuous all-order field is the actual
time derivative of the constructed common correction. -/
theorem Budget.fieldTower_hasDerivAt_timeDerivativeTower (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le ((B.fieldTower period).realization q))
      ((B.timeDerivativeTower period).realization q ⟨t, ht.1.le, ht.2.le⟩) t := by
  simpa only [B.source_eq_timeDerivativeTower period q hq] using
    B.fieldTower_hasDerivAt period q hq t ht

end EulerAllOrderDriftCorrection
