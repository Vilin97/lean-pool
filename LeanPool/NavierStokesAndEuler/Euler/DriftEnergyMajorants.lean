/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.DriftEnergyConstants
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpSubintervalBound

/-! Continuous energy majorants that retain the actual small transport drift. -/

@[expose] public section


noncomputable section

namespace EulerDriftEnergyMajorants

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerTimeLpSubintervalBound
  EulerVolterraConvolution EulerDriftCorrectionBudget
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The sharp polynomial is evaluated on the actual continuous metric energy paths. -/
def forcingMajorant {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) := by
  let X := energyPath period N hN T R (K.operatorPath period) e
  let Y := lossPath period N hN T R (K.operatorPath period) e
  refine ⟨fun t => EulerDriftEnergyConstants.forcingPolynomial period
    S.full.B S.full.M S.full.B0 S.drift S.full.B1 S.full.A0 S.full.A2
    S.full.residual K.c S.full.Rc (R t) (X t) (Y t), ?_⟩
  have hi : Continuous (fun t => (R t)⁻¹) :=
    R.continuous.inv₀ (fun t => (S.full.radius_pos t).ne')
  unfold EulerDriftEnergyConstants.forcingPolynomial
  fun_prop

/-- The genuine scalar majorant retains full velocity only in terms with no derivative loss. -/
def correctionRhs {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (Rdot : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) :=
  scalarEnergyRhs T (growthPath period S.full hN K e)
    (radiusLossPath R Rdot S.full.radius_pos) (ContinuousMap.const _ (K.multiplier period))
    (energyPath period N hN T R (K.operatorPath period) e)
    (lossPath period N hN T R (K.operatorPath period) e)
    (forcingMajorant period S hN K e)

/-- The source's radius-loss factor uses the drift envelope, with the unchanged full-data growth
constant. -/
theorem correctionRhs_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (Rdot : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    let X := energyPath period N hN T R (K.operatorPath period) e t
    let Y := lossPath period N hN T R (K.operatorPath period) e t
    let C := combinedConstant period S.full K
    correctionRhs period S hN K Rdot e t ≤ C * (X + X ^ 2 + S.full.residual) +
      (Rdot t / R t + C * ((R t)⁻¹ + S.full.Rc) * (S.drift + X)) * Y := by
  obtain ⟨hg0, hg1, hk⟩ := K.constants_nonneg period S.full.B0 S.full.B0_nonneg
  exact EulerDriftEnergyConstants.actual_scalar_bound period
    (K.growth0 period S.full.B0) (K.growth1 period) (K.multiplier period)
    S.full.B S.full.M S.full.B0 S.drift S.full.B1 S.full.A0 S.full.A2 K.c
    S.full.Rc (R t) S.full.residual
    (energyPath period N hN T R (K.operatorPath period) e t)
    (lossPath period N hN T R (K.operatorPath period) e t) (Rdot t / R t)
    hg0 hg1 hk S.full.B_nonneg (zero_le_one.trans S.full.M_one_le)
    S.full.B0_nonneg S.drift_nonneg S.full.B1_nonneg S.full.A0_nonneg
    S.full.A2_nonneg K.c_pos S.full.Rc_nonneg (S.full.radius_pos t)
    S.full.residual_pos.le (energy_nonneg period S.full hN K e t)
    (loss_nonneg period S.full hN K e t)

end EulerDriftEnergyMajorants
