/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyBound
public import LeanPool.NavierStokesAndEuler.Euler.GevreyGrowthCoefficient

@[expose] public section

/-! One explicit cutoff-independent scalar constant absorbs the actual metric growth and nonlinear
  forcing coefficients. -/

noncomputable section

namespace EulerNonlinearEnergyConstants

open EulerCorrectionEnergyBound EulerGevreyCorrectionBound EulerGevreyMetricEstimate
  EulerGevreyGrowthCoefficient EulerH6Nonlinear

variable (period : ℝ) [Fact (0 < period)]

/-- The fixed coefficient of the metric-linear part of the actual nonlinear forcing. -/
def linearCoefficient (B M B0 B1 A0 A2 c : ℝ) : ℝ :=
  (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period 3*B0)+
    transportConstant period B M*B0)*metricAmplification c

/-- The fixed coefficient of the metric-quadratic part of the actual nonlinear forcing. -/
def quadraticCoefficient (B M A2 c : ℝ) : ℝ :=
  (sourceConstant B M*A2*productConstant period 3+transportConstant period B
    M)*(metricAmplification c)^2

/-- The fixed coefficient of the single derivative-loss factor in the actual nonlinear forcing. -/
def lossCoefficient (M c : ℝ) : ℝ := lossConstant period M*(metricAmplification c)^2

/-- One explicit constant independent of the external cutoff controls all actual scalar energy coefficients. -/
def energyConstant (g0 g1 k B M B0 B1 A0 A2 c : ℝ) : ℝ :=
  1+g0+g1+k*sourceConstant B M+k*linearCoefficient period B M B0 B1 A0 A2 c+
    k*quadraticCoefficient period B M A2 c+k*lossCoefficient period M c

/-- The three actual nonlinear forcing coefficients are nonnegative under their genuine norm budgets. -/
theorem coefficients_nonneg (B M B0 B1 A0 A2 c : ℝ)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hc : 0 <
      c) :
    0 ≤ linearCoefficient period B M B0 B1 A0 A2 c ∧
      0 ≤ quadraticCoefficient period B M A2 c ∧ 0 ≤ lossCoefficient period M c := by
  have hs := sourceConstant_nonneg hB hM
  have ht := transportConstant_nonneg period hB hM
  have hl := lossConstant_nonneg period hM
  have hp := productConstant_nonneg period 3
  have hm : 0 ≤ metricAmplification c := (by norm_num : (0 : ℝ) ≤ 1).trans
    (metricAmplification_one_le hc)
  unfold linearCoefficient quadraticCoefficient lossCoefficient
  constructor
  · positivity
  constructor <;> positivity

/-- The actual combined energy constant is strictly positive. -/
theorem energyConstant_pos (g0 g1 k B M B0 B1 A0 A2 c : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hk : 0 ≤ k) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hc : 0 < c) :
    0 < energyConstant period g0 g1 k B M B0 B1 A0 A2 c := by
  obtain ⟨hl,hq,hd⟩ := coefficients_nonneg period B M B0 B1 A0 A2 c hB hM hB0 hB1 hA0 hA2 hc
  have hs := sourceConstant_nonneg hB hM
  unfold energyConstant
  positivity

/-- The actual polynomial energy right-hand side has precisely the source's shrinking-radius form with the explicit constant. -/
theorem actual_scalar_bound (g0 g1 k B M B0 B1 A0 A2 c Rc ρ residual X Y b : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hk : 0 ≤ k) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hc : 0 < c)
    (hRc : 0 ≤ Rc) (hρ : 0 < ρ) (hr : 0 ≤ residual) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    let C := energyConstant period g0 g1 k B M B0 B1 A0 A2 c
    (g0+g1*X)*X+b*Y+k*forcingPolynomial period B M B0 B1 A0 A2 residual c Rc ρ X Y ≤
      C*(X+X^2+residual)+(b+C*(ρ⁻¹+Rc)*(B0+X))*Y := by
  obtain ⟨hl,hq,hd⟩ := coefficients_nonneg period B M B0 B1 A0 A2 c hB hM hB0 hB1 hA0 hA2 hc
  have hs := sourceConstant_nonneg hB hM
  have h := absorb_scalar_coefficients g0 g1 (k*sourceConstant B M)
    (k*linearCoefficient period B M B0 B1 A0 A2 c) (k*quadraticCoefficient period B M A2 c)
    (k*lossCoefficient period M c) residual X Y B0 (ρ⁻¹+Rc)
    (energyConstant period g0 g1 k B M B0 B1 A0 A2 c)
    hg0 hg1 (mul_nonneg hk hs) (mul_nonneg hk hl) (mul_nonneg hk hq) (mul_nonneg hk hd)
    hr hX hY hB0 (add_nonneg (inv_nonneg.mpr hρ.le) hRc) (le_refl _) b
  calc
    _ = (g0+g1*X)*X+b*Y+((k*sourceConstant B M)*residual+
        (k*linearCoefficient period B M B0 B1 A0 A2 c)*X+
        (k*quadraticCoefficient period B M A2 c)*X^2+(k*lossCoefficient period M
          c)*(ρ⁻¹+Rc)*(B0+X)*Y) := by
      unfold forcingPolynomial linearCoefficient quadraticCoefficient lossCoefficient
      ring
    _ ≤ _ := h

end EulerNonlinearEnergyConstants
