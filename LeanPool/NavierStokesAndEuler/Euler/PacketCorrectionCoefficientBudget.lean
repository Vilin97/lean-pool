/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.PacketCoefficientTowerBounds

@[expose] public section

/-!
One quantitative coefficient budget for the actual source correction data.
Every constant is independent of the jet order, truncation level and frequency.
The assumptions are the original deformation and inverse-deformation derivative
bounds; all stored coefficient and pressure estimates are derived from them.
-/

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set Finset EulerSmoothLimit EulerMeanCoefficients EulerPacketCylinderField
  EulerCoefficientPath EulerParameterWordGevrey EulerCoefficientJetPressureBounds
  EulerGevrey EulerJetProductBounds EulerSobolevGevreyOperators
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The coefficient part of the correction energy budget, uniformly at all
orders and all Fourier scales with absolute value at most one. -/
structure CorrectionCoefficientBudget (D : EulerTransversePacketProvider.Data U)
    (P : ℝ) [Fact (0 < P)] where
  Rc : ℝ
  M : ℝ
  B : ℝ
  A0 : ℝ
  A2 : ℝ
  Rc_nonneg : 0 ≤ Rc
  M_one_le : 1 ≤ M
  B_nonneg : 0 ≤ B
  A0_nonneg : 0 ≤ A0
  A2_nonneg : 0 ≤ A2
  inverse_five : ∀ s (hs : 6 ≤ s) t,
    (EulerH6Pressure.CoefficientJet.restrict ((metricTower D P).jet s t) 5 (by
      omega)).pressureConstant
      D.normalLower ≤ M
  inverse_six : ∀ s (hs : 6 ≤ s) t,
    (EulerH6Pressure.CoefficientJet.restrict ((metricTower D P).jet s t) 6 hs).pressureConstant
      D.normalLower ≤ M
  metric_derivatives : ∀ s t l, 1 ≤ l →
    EulerH6Pressure.coefficientBlock P ((metricTower D P).jet s t) 6 l ≤ Rc^l*(l.factorial : ℝ)^2
  metric_base : ∀ s t r, r ≤ 6 → boundLevel P ((metricTower D P).jet s t) r ≤ B
  linear : ∀ s N ρ, 0 < ρ → 4*M*(ρ*Rc) ≤ 1 → ∀ t,
    weightedCoefficient P ((linearTower D P).jet s t) 6 N ρ ≤ A0
  quadratic : ∀ κ, |κ| ≤ 1 → ∀ s N ρ, 0 < ρ → 4*M*(ρ*Rc) ≤ 1 → ∀ t,
    (∑ i : Fin 3, weightedCoefficient P ((quadraticTower D P κ i).jet s t) 6 N ρ) ≤ A2

def correctionMetricEnvelope (R CI : ℝ) : ℝ :=
  sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*CI)

def correctionLinearEnvelope (R C1 CI : ℝ) : ℝ :=
  2*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (6*CI*C1)

def correctionQuadraticEnvelope (R C0 CI : ℝ) : ℝ :=
  6*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*(C0*R))

def correctionCoefficientRadius (R CI : ℝ) : ℝ :=
  max 1 (max (normalizedCoefficientRadius 6 (4*R) (3*CI*CI))
    (sobolevCoefficientRadius (Fin 4) (4*R)))

def correctionPressureEnvelope (c R CI : ℝ) : ℝ :=
  max 1 (max (pressureCost c (correctionMetricEnvelope R CI) 5)
    (pressureCost c (correctionMetricEnvelope R CI) 6))

private theorem series_radius_small (ρ Rc M B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hBR : B ≤ Rc) (hM : 1 ≤ M) (hg : 4*M*(ρ*Rc) ≤ 1) : ρ*B ≤ 1/2 := by
  have hR : 0 ≤ Rc := hB.trans hBR
  have hp : 0 ≤ ρ*Rc := mul_nonneg hρ hR
  have hm := mul_le_mul_of_nonneg_right hM hp
  have hb := mul_le_mul_of_nonneg_left hBR hρ
  nlinarith

variable (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (R C0 C1 CI : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hCI : 0 ≤ CI)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C0*majorant R 0
    n)
  (hF1 : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C1*majorant R
    0 n)
  (hFI : ∀ n t x, ‖iteratedFDeriv ℝ n (D.FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤ CI*majorant
    R 0 n)

include hR hC0 hC1 hCI hF hF1 hFI

/-- All coefficient hypotheses of the correction energy estimate, derived
from genuine source spatial jets.  The radius condition is the same one used
by the projected inverse, rather than a separate cutoff-dependent restriction. -/
def correctionCoefficientBudget : CorrectionCoefficientBudget D P where
  Rc := correctionCoefficientRadius R CI
  M := correctionPressureEnvelope D.normalLower R CI
  B := correctionMetricEnvelope R CI
  A0 := correctionLinearEnvelope R C1 CI
  A2 := correctionQuadraticEnvelope R C0 CI
  Rc_nonneg := zero_le_one.trans (le_max_left _ _)
  M_one_le := le_max_left _ _
  B_nonneg := sobolevCoefficientAmplitude_nonneg 6 (4*R) (3*CI*CI) (by positivity) (by positivity)
  A0_nonneg := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg 6 (4*R) (6*CI*C1) (by positivity) (by positivity))
  A2_nonneg := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg 6 (4*R) (3*CI*(C0*R)) (by positivity) (by positivity))
  inverse_five s hs t := by
    have h := MatrixCoefficient.toCoefficientTower_pressure_bound P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 5 6 (by omega) (by omega)
      D.normalLower D.normalLower_pos t
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  inverse_six s hs t := by
    have h := MatrixCoefficient.toCoefficientTower_pressure_bound P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 6 6 hs le_rfl
      D.normalLower D.normalLower_pos t
    exact h.trans ((le_max_right _ _).trans (le_max_right _ _))
  metric_derivatives s t l hl := by
    exact MatrixCoefficient.toCoefficientTower_normalized_block P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 6
      (correctionCoefficientRadius R CI) ((le_max_left _ _).trans (le_max_right _ _)) l hl t
  metric_base s t r hr :=
    MatrixCoefficient.toCoefficientTower_base_bound P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 6 r hr t
  linear s N ρ hρ hg t := by
    have hsmall := series_radius_small ρ (correctionCoefficientRadius R CI)
      (correctionPressureEnvelope D.normalLower R CI) (sobolevCoefficientRadius (Fin 4) (4*R))
      hρ.le (sobolevCoefficientRadius_nonneg (4*R) (by positivity))
      ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _) hg
    exact MatrixCoefficient.toCoefficientTower_weighted_bound P (linearCoefficient D)
      (4*R) (6*CI*C1) (by positivity) (by positivity)
      (linearCoefficient_bound D R C1 CI hR hC1 hCI hF1 hFI) s 6 N ρ hρ hsmall t
  quadratic κ hκ s N ρ hρ hg t := by
    have hsmall := series_radius_small ρ (correctionCoefficientRadius R CI)
      (correctionPressureEnvelope D.normalLower R CI) (sobolevCoefficientRadius (Fin 4) (4*R))
      hρ.le (sobolevCoefficientRadius_nonneg (4*R) (by positivity))
      ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _) hg
    have h : ∀ i : Fin 3,
        weightedCoefficient P ((quadraticTower D P κ i).jet s t) 6 N ρ ≤
          2*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*(C0*R)) := by
      intro i
      exact MatrixCoefficient.toCoefficientTower_weighted_bound P (quadraticCoefficient D κ i)
        (4*R) (3*CI*(C0*R)) (by positivity) (by positivity)
        (quadraticCoefficient_bound D R C0 CI hR hC0 hCI hF hFI κ hκ i) s 6 N ρ hρ hsmall t
    calc
      _ ≤ ∑ i : Fin 3, 2*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*(C0*R)) :=
        sum_le_sum (fun i _ => h i)
      _ = _ := by simp only
        [sum_const,Fintype.card_fin,card_univ,nsmul_eq_mul,correctionQuadraticEnvelope]; ring

end EulerPacketCorrectionCoefficients
