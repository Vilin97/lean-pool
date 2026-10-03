/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SMatRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTThetaUpgrade
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingProfilesFromFlow

/-! # Coefficient jets of the `e_{m-1}` matrix (`e.monster.est.tiny`)

The matrix `B_t(y) = K_m(t) - κ_{m-1} I + s_{m-1}(t, y)` multiplying `∇(T_{N*-1} - T_{N*})` in
`iterateError` has all spatial jets bounded by
`κ_{m-1} C_B · n! · (2^{10} ε_{m-1}^{-1} ε_{m-1}^{-2δ})^n`.

This is the first conjunct of `iterate_TForcing_profiles_from_flow` (`Section4`), reproduced
without its (here unneeded) mean hypothesis `hmean`, with the flow interfaces discharged by the
unconditional flow bounds `iterate_flowGrad_zero_bound` / `iterate_flowGrad_word_bound`, and
`|K_m| ≤ K κ_{m-1}` from `iterate_chain_upgrade_inputs`. -/

@[expose] public section

open Homogenization
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5

/-- First conjunct of `iterate_TForcing_profiles_from_flow`, with no mean hypothesis. -/
theorem sc_coeff_profile_of_flow {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    {κm κprev K Cflow r₀ ρ : ℝ} (hκ : 0 ≤ κprev)
    (hK : 0 ≤ K) (hCf : 0 ≤ Cflow)
    (hr : 0 ≤ r₀) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hflow : ∀ t l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t))
    (hKm : ∀ t j k, |I.Kmat κm m t j k| ≤ K * κprev)
    (hκscale : |κm| ≤ κprev) (hrad1 : 1 ≤ r₀ / ρ)
    (hzero : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ j k,
      |(I.flowGrad hΦ m l t x - 1) j k| ≤ Cflow * ρ)
    (hpositive : ∀ t x l, I.hatXiML m l t ≠ 0 → ∀ p : List (Fin 2), 1 ≤ p.length → ∀ j k,
      |iterateSpatialWord p (fun y => (I.flowGrad hΦ m l t y - 1) j k) x| ≤
        Cflow * (p.length.factorial : ℝ) * r₀ ^ p.length) :
    ∀ t x p j k, |iterateMatrixWord
      (fun y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y)
        p x j k| ≤
      κprev * (K + 1 + (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))) *
        (p.length.factorial : ℝ) * (2 * (r₀ / ρ)) ^ p.length := by
  have hs := iterate_sMat_small_profile_of_flow I hΦ hm κm κprev K Cflow r₀ ρ
    hK hCf hr hρ hρ1 hflow hKm hzero hpositive hκ hκscale hrad1
  have hrad : 0 ≤ 2 * (r₀ / ρ) := by positivity
  have hSM (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t) :=
    AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t (hflow t)
  have hfullsmall t p x j k : |iterateMatrixWord (I.sMat hΦ m κm t) p x j k| ≤
      κprev * (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1)) * 1 *
        (p.length.factorial : ℝ) * (2 * (r₀ / ρ)) ^ p.length := by
    have hb := mul_le_mul_of_nonneg_left hρ1
      (show 0 ≤ κprev * (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1)) *
          (p.length.factorial : ℝ) * (2 * (r₀ / ρ)) ^ p.length by positivity)
    have hp := hs t x p j k
    nlinarith only [hb, hp]
  have hKcenter t j k : |(I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k| ≤
      κprev * (K + 1) * 1 := by
    have hi : |(1 : Matrix (Fin 2) (Fin 2) ℝ) j k| ≤ 1 := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    have hb := mul_le_mul_of_nonneg_left hi hκ
    have ht := abs_sub (I.Kmat κm m t j k) (κprev * (1 : Matrix (Fin 2) (Fin 2) ℝ) j k)
    change |I.Kmat κm m t j k - κprev * (1 : Matrix (Fin 2) (Fin 2) ℝ) j k| ≤ _
    rw [abs_mul, abs_of_nonneg hκ] at ht
    nlinarith only [ht, hb, hKm t j k]
  intro t x p j k
  have hb := iterate_constant_plus_small_matrix_profile (hSM t) _ hκ
    (by positivity : 0 ≤ 2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))
    (by positivity : 0 ≤ K + 1)
    (by norm_num : (0 : ℝ) ≤ 1) hrad (hKcenter t) (hfullsmall t) p x j k
  refine hb.trans (le_of_eq ?_)
  ring

/-- Coefficient jets of the matrix of `iterateError`, with constants chosen before `I`. -/
theorem sc_coeff_profile (β C₀ : ℝ) : ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C₁ : ℝ,
    ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C₁ ≤ (I.Λ : ℝ) →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
    ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
    ∀ m : ℕ, 2 ≤ m → m ≤ M →
    ∀ (t : ℝ) (x : Vec 2) (p : List (Fin 2)) (j k : Fin 2),
      |iterateMatrixWord (fun y => I.Kmat (I.kappaSeq κ M m) m t -
          I.kappaSeq κ M (m - 1) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m (I.kappaSeq κ M m) t y) p x j k| ≤
        I.kappaSeq κ M (m - 1) * CB * (p.length.factorial : ℝ) *
          (2 * ((2 ^ 10 / epsilon β I.Λ (m - 1)) / epsilon β I.Λ (m - 1) ^ (2 * delta β))) ^
            p.length := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro I
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb
  by_cases hC : 1 ≤ C₀
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro I hz
    have := I.one_le_Czeta
    exact absurd (this.trans hz) hC
  obtain ⟨c, Ck, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  have hδ := Infra.Ingredients.delta_pos hb.1 hb.2
  set C₀' : ℝ := max 1 (iterateDischargeThreshold β C₀ Ck) with hC₀'
  have hC₀'1 : 1 ≤ C₀' := le_max_left _ _
  have hC₀'thr : iterateDischargeThreshold β C₀ Ck ≤ C₀' := le_max_right _ _
  set Kc : ℝ := iterateKmatConstant β C₀ with hKc
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]; unfold iterateKmatConstant; positivity
  refine ⟨Kc + 1 + (2 * Kc * 40 + 4 * (Kc + 1) * 40 * (40 + 1)), by positivity,
    max 128 ((4 * C₀' ^ 3) ^ (1 / (2 * delta β))), ?_⟩
  intro I hz hx hh hΛ₀ Φ hΦ κ hκp M hM hperm m hm hmM t x p j k
  have hΛ128 : (128 : ℝ) ≤ (I.Λ : ℝ) := le_trans (le_max_left _ _) hΛ₀
  have hΛ : 2 ^ 7 ≤ I.Λ := by exact_mod_cast hΛ128
  have hΛbig : (4 * C₀' ^ 3) ^ (1 / (2 * delta β)) ≤ (I.Λ : ℝ) :=
    le_trans (le_max_right _ _) hΛ₀
  have hΛpos : (0 : ℝ) < I.Λ := by linarith only [hΛ128]
  have hκ : 0 < κ := (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le) _)).trans_le hperm.1
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := LeftToShow.kappaSeq_pos I hκ M (m - 1)
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  -- smallness of `ε_{m-1}^{2δ}` from the Λ-threshold
  have hsmall : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ (4 * C₀' ^ 3)⁻¹ := by
    have hεΛ : epsilon β I.Λ (m - 1) ≤ (I.Λ : ℝ)⁻¹ :=
      LeftToShow.epsilon_le_inv_Lambda hb.1 hb.2 hΛ (by omega)
    have hpw : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ ((I.Λ : ℝ)⁻¹) ^ (2 * delta β) :=
      Real.rpow_le_rpow he.le hεΛ (by positivity)
    have h4 : 0 ≤ 4 * C₀' ^ 3 := by positivity
    have hΛδ : 4 * C₀' ^ 3 ≤ (I.Λ : ℝ) ^ (2 * delta β) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg h4 _) hΛbig (by positivity : 0 ≤ 2 * delta β)
      rwa [← Real.rpow_mul h4, one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one] at this
    have hinv : ((I.Λ : ℝ)⁻¹) ^ (2 * delta β) = ((I.Λ : ℝ) ^ (2 * delta β))⁻¹ :=
      Real.inv_rpow hΛpos.le _
    have hpowpos : 0 < (I.Λ : ℝ) ^ (2 * delta β) := Real.rpow_pos_of_pos hΛpos _
    have hC3 : 0 < 4 * C₀' ^ 3 := by positivity
    refine hpw.trans ?_
    rw [hinv]
    exact inv_anti₀ hC3 hΛδ
  -- the diffusivity ratio, the `K_m` bound
  have hA5 := hrec I hz hx hh κ (Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM, hperm⟩⟩) M hM hperm
  have hinputs := iterate_chain_upgrade_inputs I hz hh hm hmM hκ hperm (hc.trans hcC).le
    hC₀'1 hC₀'thr hsmall (fun j hj hjM => (hA5.2 j hj hjM).2)
  have hKm : ∀ t j k, |I.Kmat (I.kappaSeq κ M m) m t j k| ≤ Kc * I.kappaSeq κ M (m - 1) :=
    hinputs.1
  have hρ : 0 < epsilon β I.Λ (m - 1) ^ (2 * delta β) := Real.rpow_pos_of_pos he _
  have hρ1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one he.le he1 (by positivity)
  have hflow : ∀ t l, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l t) := fun t l =>
    (iterate_flowGrad_joint_smooth I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hrad1 : 1 ≤ (2 ^ 10 / epsilon β I.Λ (m - 1)) / epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    rw [le_div_iff₀ hρ, one_mul, le_div_iff₀ he]
    have : epsilon β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 := by
      nlinarith only [he, he1, hρ, hρ1]
    linarith only [this]
  have hprof := sc_coeff_profile_of_flow I hΦ (by omega : 1 ≤ m)
    (κm := I.kappaSeq κ M m) (K := Kc) (Cflow := 40) (r₀ := 2 ^ 10 / epsilon β I.Λ (m - 1))
    (ρ := epsilon β I.Λ (m - 1) ^ (2 * delta β)) hκprev.le hKc0 (by norm_num)
    (by positivity) hρ hρ1 hflow hKm
    (iterate_kappaSeq_abs_le_previous I hκ (by omega) hmM) hrad1
    (fun t x l hn j k => (iterate_flowGrad_zero_bound I hΦ hm hn x j k))
    (fun t x l hn p _ j k => iterate_flowGrad_word_bound I hΦ hm hn p x j k)
  have h := hprof t x p j k
  refine h.trans (le_of_eq ?_)
  ring

end AVenhance.Infra.Section5.Contracts

end
