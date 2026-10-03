/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusivityComparison
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersNonneg
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! # TUpgrade Consumers V

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

theorem iterate_V_upgrade_of_theta (β Ccut : ℝ) :
    ∃ c Ck : ℝ, 0 < c ∧ c < Ck ∧
    ∀ (I : Ingredients β) (_hz : I.Czeta ≤ Ccut) (_hxi : I.Cxi ≤ Ccut)
      (_hh : I.Chat ≤ Ccut)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (κ : ℝ) (M : ℕ) {m : ℕ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (_hT : I.IsTIterates hΦ m (I.kappaAt κ m (M - m)) (I.kappaAt κ (m - 1)
        (M - (m - 1))) θ₀ θprev T)
    (_hθ : IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaAt κ (m - 1) (M - (m - 1))) (fun _ _ =>
        0) θ₀ θprev)
    (_hm : 2 ≤ m) (_hmM : m ≤ M) (_hPerm : κ ∈ permittedInterval β I.Λ M)
    (Cθ Rθ C₀ N : ℝ)
    (_hN : 0 ≤ N)
    (_hRθ : 0 < Rθ)
    (_hC₀ : iterateReducedSourceConstant β Ccut c Ck 40 (2 ^ 10) Cθ ≤ C₀)
    (_hradius : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ)
    (_hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀ ^ 3)⁻¹)
    (_hbase : iterateCoordinateEnergyProfile θprev (I.kappaAt κ (m - 1) (M - (m - 1))) N
      (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) 0),
    Infra.Section5.Integration.VIncrementContract I m
      (I.kappaSeq κ M (m - 1)) T C₀ Rθ N := by
  obtain ⟨c, Ck, hc, hcC, hrec⟩ := AVenhance.l_recurse β Ccut
  refine ⟨c, Ck, hc, hcC, ?_⟩
  intro I hz hxi hh Φ hΦ κ M m θ₀ θprev T hT hθ hm hmM hPerm
    Cθ Rθ C₀ N hN hRθ hC₀ hradius hsmall hbase
  have hM : 1 ≤ M := by omega
  have hκ : 0 < κ := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le) _)).trans_le hPerm.1
  have hpermissible : κ ∈ permissibleSet β I.Λ :=
    Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM, hPerm⟩⟩
  have hA5 := hrec I hz hxi hh κ hpermissible M hM hPerm
  obtain ⟨_, _, hreg⟩ := AVenhance.stream_regularity β
  have hA3 := fun j hj t n hn => (hreg I Φ hΦ j hj t).2.1 n hn
  have hsource : iterateSourceConstant
      (iterateBudgetUniversalConstant (iterateKmatConstant β Ccut) Ck c
        ((2 : ℝ) ^ (-25 : ℤ)) 40
        (iterateMeanScaleConstant β Ccut (iterateRatioConstant β Ck))) (2 ^ 10) Cθ ≤ C₀ :=
    (le_max_right _ _).trans hC₀
  have hC1 : 1 ≤ C₀ := (iterate_source_constant_bounds _ _ _).1.trans hsource
  have hthreshold : iterateDischargeThreshold β Ccut Ck ≤ C₀ :=
    (le_max_left _ _).trans hC₀
  have hinputs := iterate_chain_upgrade_inputs I hz hh hm hmM hκ hPerm
    (hc.trans hcC).le hC1 hthreshold hsmall (fun j hj hjM => (hA5.2 j hj hjM).2)
  have hcut : 0 ≤ Ccut := (by linarith only [I.one_le_Czeta] : 0 ≤ I.Czeta).trans hz
  have hK : 0 ≤ iterateKmatConstant β Ccut := by
    unfold iterateKmatConstant
    positivity
  have hCm : 0 ≤ iterateMeanScaleConstant β Ccut (iterateRatioConstant β Ck) := by
    unfold iterateMeanScaleConstant iterateRatioConstant
    positivity
  have hκm := Infra.Section3.kappaAt_pos I hκ m (M - m)
  have hpoint := hA5.1 (m - 1) (by omega) (by omega)
  have hmean : ∀ j k, |(timeAvgMat (I.Kmat (I.kappaSeq κ M m) m) -
      I.kappaSeq κ M (m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      I.kappaSeq κ M (m - 1) * iterateMeanScaleConstant β Ccut (iterateRatioConstant β Ck) *
        epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    intro j k
    have hn := iterate_mean_coefficient_bound I κ (by omega : 1 ≤ m) hmM hκm hinputs.2.1
    have he : |(timeAvgMat (I.Kmat (I.kappaSeq κ M m) m) -
        I.kappaSeq κ M (m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
        iterateMeanErrorBound I (I.kappaSeq κ M m) m := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ j).trans hn)
    exact he.trans hinputs.2.2
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hscale := iterate_T_source_scale he hRθ hC1 hradius hsmall
  have hquarter : C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
      max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ)) ≤ 1 / 4 := by
    rw [hscale.1, mul_one]
    exact hscale.2.2
  have hflow := fun l => iterate_flowGrad_joint_smooth I hΦ m l
  have hflowp := fun t (_ : 0 < t) l => iterate_flowGrad_periodic I hΦ m l t
  have hzero := fun t x l hn j k => iterate_flowGrad_zero_bound I hΦ (l := l) (t := t) hm hn x j k
  have hpositive := fun t x l hn (w : List (Fin 2)) (_ : 1 ≤ w.length) j k =>
    iterate_flowGrad_word_bound I hΦ (l := l) (t := t) hm hn w x j k
  intro i hi0 hi v w hvw t ht ht1
  have hweight : 0 ≤ iterateAmplitude
      (C₀ ^ 3 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
        max 1 (epsilon β I.Λ (m - 1) ^ (2 + gamma β) * Rθ ^ (-2 : ℤ))) i *
      iterateAnalyticWeight v.length i
        (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) := by
    unfold iterateAmplitude iterateAnalyticWeight
    split_ifs <;> positivity
  simp only [mul_assoc] at hweight ⊢
  apply iterate_amplitude_bound_of_strict_enlargements hweight
  intro B hNB
  have hb : iterateCoordinateEnergyProfile θprev (I.kappaSeq κ M (m - 1)) B
      (max (C₀ * epsilon β I.Λ (m - 1) ^ (-1 - gamma β / 2)) (C₀ / Rθ)) 0 := by
    rw [hscale.2.1]
    exact iterate_coordinate_profile_amplitude_mono hN hNB.le hbase
  have hV := iterate_V_abstract_amplitude_of_diffusivity_and_flow
    (hκscale := iterate_kappaAt_abs_le_previous I hκ (by omega) hmM) I hΦ hT hθ hm hκm
    hflow hflowp hA3 (hN.trans_lt hNB) hc (hc.trans hcC).le hK (by norm_num) hCm
    (by norm_num) hRθ hpoint.1 hpoint.2 hsource
    (hquarter.trans (by norm_num)) hinputs.1 hmean hzero hpositive hb
  simpa only [Ingredients.kappaSeq, mul_assoc] using hV i hi0 hi v w hvw t ht ht1

end AVenhance.Infra.Section4
