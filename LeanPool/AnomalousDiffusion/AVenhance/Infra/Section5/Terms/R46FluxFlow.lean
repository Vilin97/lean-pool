/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxSupport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.FlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowAverageFluxIdentity

/-! Quantitative control of the pulled-flow Jacobians on the supports
of the transition cutoffs. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem R46FluxFlow.tauCellFactor_ge_five (m : ℕ) (_hm : 1 ≤ m) :
    5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
  unfold Infra.Ingredients.tauCellFactor
  have hp : 0 < epsilon β I.Λ (m - 1) ^ (-delta β) :=
    Real.rpow_pos_of_pos
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) _
  have hceil : 1 ≤
      (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr hp))
  linarith

theorem R46FluxFlow.tau_le_tauPP_quarter (m : ℕ) (hm : 1 ≤ m) :
    tau β I.Λ m ≤ tauPP β I.Λ m / 25 := by
  rw [Infra.Ingredients.tauPP_eq_cellFactor_sq_mul_tau hm]
  have hfactor := R46FluxFlow.tauCellFactor_ge_five I m hm
  have hτ := I.tau_pos' m
  have hsq : 25 ≤ (Infra.Ingredients.tauCellFactor β I.Λ m) ^ 2 := by
    nlinarith [sq_nonneg (Infra.Ingredients.tauCellFactor β I.Λ m - 5)]
  nlinarith

theorem R46FluxFlow.tauP_le_tauPP_fifth (m : ℕ) (hm : 1 ≤ m) :
    tauP β I.Λ m ≤ tauPP β I.Λ m / 5 := by
  rw [Infra.Ingredients.tauPP_eq_cellFactor_mul_tauP hm]
  have hfactor := R46FluxFlow.tauCellFactor_ge_five I m hm
  have hp := Infra.Cutoff.tauP_pos (m := m) I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  nlinarith

/-- A nonzero translated `hatXi` coefficient is supported within one large
cell of its flow's initial time. -/
theorem hatXiML_time_distance_le_tauPP (m : ℕ) (hm : 1 ≤ m)
    (l : ℤ) (t : ℝ) (hne : I.hatXiML m l t ≠ 0) :
    |t - (l : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m := by
  have hnonneg := Infra.Ingredients.hatXiML_mem_Icc I hm l t
  have hpos : 0 < I.hatXiML m l t := lt_of_le_of_ne hnonneg.1 (Ne.symm hne)
  have hle := I.hatXi_le m hm l t
  have hmem : t ∈ Set.Icc
      ((l - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    by_contra hnot
    have hz : indIcc ((l - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
        ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) t = 0 := by
      unfold indIcc
      rw [Set.indicator_of_notMem hnot]
    rw [hz] at hle
    change I.hatXiML m l t ≤ 0 at hle
    linarith
  have hτP := R46FluxFlow.tauP_le_tauPP_fifth I m hm
  have hτPP := I.tauPP_pos' m
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

/-- The flow assigned to an active small cutoff also starts within one large
cell of the target time. -/
theorem lIdx_flow_time_distance_le_tauPP (m : ℕ) (hm : 1 ≤ m)
    (k : ℤ) (t : ℝ) (hξ : I.xiMK m k t ≠ 0) :
    |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m := by
  have hcenter := Infra.Ingredients.taum_prime_supp k I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) hm
  have hτ := I.tau_pos' m
  have hτpp := I.tauPP_pos' m
  have hcell : (k : ℝ) * tau β I.Λ m ∈
      Set.Icc ((k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2)
        ((k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2) := by
    constructor <;> linarith
  have hcenterCell := hcenter hcell
  have hnear := Infra.Section3.xiMK_index_mem_window I hm k t hξ
  have hnear' : |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
    have hτ' : 0 < tau β I.Λ m := hτ
    have hk := hnear
    change (k : ℝ) ∈ Set.Icc
      (t / tau β I.Λ m - 5 / 4) (t / tau β I.Λ m + 5 / 4) at hk
    rw [Set.mem_Icc] at hk
    have hlo := mul_le_mul_of_nonneg_right hk.1 hτ'.le
    have hhi := mul_le_mul_of_nonneg_right hk.2 hτ'.le
    have heqlo : (t / tau β I.Λ m - 5 / 4) * tau β I.Λ m =
        t - 5 / 4 * tau β I.Λ m := by field_simp
    have heqhi : (t / tau β I.Λ m + 5 / 4) * tau β I.Λ m =
        t + 5 / 4 * tau β I.Λ m := by field_simp
    rw [abs_le]
    constructor
    · have h' : (k : ℝ) * tau β I.Λ m ≤ t + 5 / 4 * tau β I.Λ m := by
        rw [← heqhi]
        exact hhi
      linarith
    · have h' : t - 5 / 4 * tau β I.Λ m ≤
          (k : ℝ) * tau β I.Λ m := by
        rw [← heqlo]
        exact hlo
      linarith
  have hdist : |t - (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m| ≤
      tauPP β I.Λ m / 2 + 5 / 4 * tau β I.Λ m := by
    rw [abs_le]
    have hnearB := abs_le.mp hnear'
    constructor <;> nlinarith [hcenterCell.1, hcenterCell.2]
  have hsmall := R46FluxFlow.tau_le_tauPP_quarter I m hm
  calc
    _ ≤ tauPP β I.Λ m / 2 + 5 / 4 * tau β I.Λ m := hdist
    _ ≤ tauPP β I.Λ m := by nlinarith [hsmall]

theorem R46FluxFlow.tauPP_le_inverse_amplitude_rpow (m : ℕ) (hm : 1 ≤ m) :
    tauPP β I.Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) *
      (a β I.Λ (m - 1))⁻¹ * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  have hbound := (Infra.Ingredients.tauPP_bounds I.one_lt_beta I.beta_lt
    I.two_pow_seven_le hm).2
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 < a β I.Λ (m - 1) := by
    rw [a]
    exact Real.rpow_pos_of_pos he _
  have heq : epsilon β I.Λ (m - 1) ^
      (2 - β + 2 * delta β) =
      (a β I.Λ (m - 1))⁻¹ * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    rw [a, ← Real.rpow_neg he.le, ← Real.rpow_add he]
    congr 1
    ring
  rw [heq] at hbound
  simpa only [mul_assoc] using hbound

/-- Componentwise flow-Jacobian distortion from the actual stream-function estimates `flow_close`
field. The stronger `epsilon^(2δ)` factor comes from the exact time scale. -/
theorem flowGrad_entry_close_on_tauPP_window
    (Cmat : ℝ) (hseq : IsStreamSeq I Φ)
    (hflow : FlowBoundsData I Φ hseq Cmat)
    (m : ℕ) (hm : 2 ≤ m) (l : ℤ) (t : ℝ) (x : Vec 2)
    (ht : |t - (l : ℝ) * tauPP β I.Λ m| ≤ tauPP β I.Λ m)
    (i j : Fin 2) :
    |(I.flowGrad hseq m l t x - 1) i j| ≤
      (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  let s := (l : ℝ) * tauPP β I.Λ m
  have hm' : 1 ≤ m - 1 := by omega
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 < a β I.Λ (m - 1) := by
    rw [a]
    exact Real.rpow_pos_of_pos he _
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have he1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hepow : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one he.le he1 (by positivity)
  have hτPP := R46FluxFlow.tauPP_le_inverse_amplitude_rpow I m (by omega)
  have htime : |t - s| ≤ (2 : ℝ) ^ (-25 : ℤ) *
      (a β I.Λ (m - 1))⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hepow
      (show 0 ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ by positivity)
    calc
      |t - s| ≤ tauPP β I.Λ m := by simpa [s] using ht
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ *
          epsilon β I.Λ (m - 1) ^ (2 * delta β) := hτPP
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * (a β I.Λ (m - 1))⁻¹ := by
        nlinarith [hmul]
  have hclose := (hflow.flow_close (m - 1) hm' s (t - s) htime
    (I.xFlowInv hseq m l t x)).1
  have hFlowEq : (fun y : Vec 2 =>
      constructionFlow hseq (m - 1) (s + (t - s)) y s) = I.xFlow hseq m l t := by
    funext y
    have harg : s + (t - s) = t := by ring
    simp only [constructionFlow, Ingredients.xFlow, harg, s]
  have hL : constructionFlowJacobian hseq (m - 1) (t - s) s
      (I.xFlowInv hseq m l t x) =
      fderiv ℝ (I.xFlow hseq m l t) (I.xFlowInv hseq m l t x) := by
    simp only [constructionFlowJacobian]
    rw [hFlowEq]
  have hclose' :
      ‖fderiv ℝ (I.xFlow hseq m l t) (I.xFlowInv hseq m l t x) -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
        2 ^ 23 * |t - s| * a β I.Λ (m - 1) := by
    simpa [hL] using hclose
  have hXdiff : DifferentiableAt ℝ (I.xFlow hseq m l t)
      (I.xFlowInv hseq m l t x) :=
    (xFlow_spatial_contDiff_two I hseq m l t).differentiable (by norm_num) _
  have hentry :
      (I.flowGrad hseq m l t x - 1) i j =
        ((fderiv ℝ (I.xFlow hseq m l t) (I.xFlowInv hseq m l t x) -
          ContinuousLinearMap.id ℝ (Vec 2)) (basisVec i)) j := by
    simp [Ingredients.flowGrad, gradMatrix, Matrix.of_apply, spaceGrad,
      fderiv_apply hXdiff j, Matrix.one_apply, eq_comm]
  have hcoord : |((fderiv ℝ (I.xFlow hseq m l t)
      (I.xFlowInv hseq m l t x) - ContinuousLinearMap.id ℝ (Vec 2))
      (basisVec i)) j| ≤
      ‖fderiv ℝ (I.xFlow hseq m l t) (I.xFlowInv hseq m l t x) -
        ContinuousLinearMap.id ℝ (Vec 2)‖ := by
    calc
      _ ≤ ‖(fderiv ℝ (I.xFlow hseq m l t)
        (I.xFlowInv hseq m l t x) - ContinuousLinearMap.id ℝ (Vec 2))
          (basisVec i)‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm
              ((fderiv ℝ (I.xFlow hseq m l t)
                (I.xFlowInv hseq m l t x) - ContinuousLinearMap.id ℝ (Vec 2))
                (basisVec i)) j
      _ ≤ ‖fderiv ℝ (I.xFlow hseq m l t)
          (I.xFlowInv hseq m l t x) - ContinuousLinearMap.id ℝ (Vec 2)‖ := by
            have hb : ‖basisVec i‖ = 1 := by simp [basisVec, Pi.norm_single]
            simpa [hb] using (fderiv ℝ (I.xFlow hseq m l t)
              (I.xFlowInv hseq m l t x) - ContinuousLinearMap.id ℝ (Vec 2)).le_opNorm
              (basisVec i)
  have ha : 0 ≤ a β I.Λ (m - 1) := hA.le
  calc
    _ = |((fderiv ℝ (I.xFlow hseq m l t)
        (I.xFlowInv hseq m l t x) - ContinuousLinearMap.id ℝ (Vec 2))
        (basisVec i)) j| := by rw [hentry]
    _ ≤ ‖fderiv ℝ (I.xFlow hseq m l t)
        (I.xFlowInv hseq m l t x) - ContinuousLinearMap.id ℝ (Vec 2)‖ := hcoord
    _ ≤ 2 ^ 23 * |t - s| * a β I.Λ (m - 1) := hclose'
    _ ≤ 2 ^ 23 * tauPP β I.Λ m * a β I.Λ (m - 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          (by simpa [s] using ht) (by positivity)
      · exact hA.le
    _ ≤ 2 ^ 23 * ((2 : ℝ) ^ (-25 : ℤ) *
        (a β I.Λ (m - 1))⁻¹ * epsilon β I.Λ (m - 1) ^ (2 * delta β)) *
        a β I.Λ (m - 1) := by
      gcongr
    _ = (1 / 4 : ℝ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
      field_simp [ne_of_gt hA]
      norm_num

end AVenhance.Infra.Section5
end
