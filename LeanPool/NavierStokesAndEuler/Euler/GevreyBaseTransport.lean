/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevBaseCommutator
public import LeanPool.NavierStokesAndEuler.Euler.GevreyLowNorms

@[expose] public section

/-! Summation of the actual base transport commutators with no external-cutoff constant. -/

noncomputable section

namespace EulerGevreyBaseTransport

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators EulerBaseWordMetric
    EulerFiniteMetricEnergy
  EulerWeightedCylinderEnergy EulerGevreyMetricComparison EulerSobolevWordLevel
    EulerSobolevBaseCommutator
  EulerBaseTransportL2 EulerGevreyLowNorms

variable (period : ℝ) [Fact (0 < period)]

/-- Restriction commutes with taking an actual derivative word at a lower Sobolev level. -/
theorem restrict_wordAtLevel {s p q n : ℕ} (hq : q ≤ p) (w : Fin n → Fin 4) (hp : n+p ≤ s)
    (u : SobolevSpace period s) :
    restrictOperator period hq (wordAtLevel period p n w hp u) = wordAtLevel period q n w (by
      omega) u := by
  apply value_injective period
  rw [value_restrictOperator, wordAtLevel_value, wordAtLevel_value]

/-- The exact base derivative sum is contained in every truncated actual Gevrey norm. -/
theorem sumNorm_restrict_le_weighted {s q : ℕ} (hq : q ≤ s) (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (u : SobolevSpace period s) :
    sumNorm period (restrictOperator period hq u) ≤ weightedNorm period q N ρ u := by
  have he : sumNorm period (restrictOperator period hq u) = blockNorm period (toJet period u) q 0
    := by
    rw [blockNorm_zero_eq_size (toJet period u) hq]
    rw [sumNorm_eq_jet, ← sobolevSize_eq period (toJet period (restrictOperator period hq u)),
      value_restrictOperator]
  rw [he]
  have hsum := Finset.single_le_sum (s := Finset.range (N+1))
    (fun n _ => mul_nonneg (weight_pos hρ n).le (show 0 ≤ blockNorm period (toJet period u) q n
      from blockNorm_nonneg _))
    (show 0 ∈ Finset.range (N+1) by simp)
  simpa [weight, weightedNorm] using hsum

/-- Exact external-word expansion of the actual Gevrey Sobolev sum. -/
theorem weighted_word_sums {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (u : SobolevSpace period s) :
    (∑ I : ExternalWord N, weight ρ I.1.val * sumNorm period
      (wordAtLevel period q I.1.val I.2 (by have := I.1.isLt; omega) u)) = weightedNorm period q N
        ρ u := by
  rw [Fintype.sum_sigma, weightedNorm, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [blockNorm_baseWords period u (by have := n.isLt; omega : n.val+q ≤ s), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [sumNorm_wordAtLevel]

/-- The literal base transport forcing at every external and base derivative word. -/
def baseTransportForcing {s : ℕ} (N : ℕ) (hN : N+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) : ExternalWord N → BaseWord 6 → LiftL2 period := fun I a =>
  baseCommutator period a.1.val (by have := a.1.isLt; omega) a.2 L hL
    (restrictOperator period (by omega : 7 ≤ s+1) u)
    (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega : I.1.val+7 ≤ s+1) v)

/-- Each base-word forcing family is controlled by the fixed H⁶ norms, with the fixed word-count factor 5461. -/
theorem baseTransportForcing_family_bound {s : ℕ} (N : ℕ) (hN : N+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (I : ExternalWord N) :
    familyNorm (baseTransportForcing period N hN L hL u v I) ≤
      (5461*baseTransportConstant period) * sumNorm period (restrictOperator period (by omega : 6 ≤
        s+1) u) *
        sumNorm period (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega : I.1.val+6 ≤
          s+1) v) := by
  have hb (a : BaseWord 6) : ‖baseTransportForcing period N hN L hL u v I a‖ ≤
      baseTransportConstant period * sumNorm period (restrictOperator period (by omega : 6 ≤ s+1)
        u) *
        sumNorm period (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega : I.1.val+6 ≤
          s+1) v) := by
    have h := baseCommutator_bound period a.1.val (by have := a.1.isLt; omega) a.2 L hL
      (restrictOperator period (by omega : 7 ≤ s+1) u)
      (wordAtLevel period 7 I.1.val I.2 (by have := I.1.isLt; omega : I.1.val+7 ≤ s+1) v)
    rw [restrictOperator_comp, restrict_wordAtLevel] at h
    exact h
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (BaseWord 6))) (fun a _ => hb a)
  exact (familyNorm_le_sum_norm _).trans (hsum.trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, card_baseWord_six, nsmul_eq_mul]; ring))

/-- The actual weighted base transport forcing has no external derivative loss or cutoff-dependent coefficient. -/
theorem baseTransportForcing_weighted_bound {s : ℕ} (N : ℕ) (hN : N+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (baseTransportForcing period N hN L hL
      u v) ≤
      (5461*baseTransportConstant period)*weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v
        := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ExternalWord N))) (fun I _ =>
    mul_le_mul_of_nonneg_left (baseTransportForcing_family_bound period N hN L hL u v I)
      (weight_pos hρ I.1.val).le)
  have he : (∑ I : ExternalWord N, weight ρ I.1.val *
      ((5461*baseTransportConstant period)*sumNorm period (restrictOperator period (by omega : 6 ≤
        s+1) u)*
        sumNorm period (wordAtLevel period 6 I.1.val I.2 (by have := I.1.isLt; omega) v))) =
      (5461*baseTransportConstant period)*sumNorm period (restrictOperator period (by omega : 6 ≤
        s+1) u)*weightedNorm period 6 N ρ v := by
    rw [← weighted_word_sums period 6 N (by omega : N+6 ≤ s+1) ρ v, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun I _ => by ring)
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (sumNorm_restrict_le_weighted period (by omega : 6 ≤ s+1) N ρ hρ u)
    (mul_nonneg (by norm_num) (baseTransportConstant_nonneg period))) (weightedNorm_nonneg period 6
      N ρ hρ v))

end EulerGevreyBaseTransport
