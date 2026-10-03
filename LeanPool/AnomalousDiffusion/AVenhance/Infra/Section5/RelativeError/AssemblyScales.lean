/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyReal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LaterStart

/-! # scale facts for the main-theorem assembly  The choice of the threshold `Λ₀` making
`∑ C ε_j^δ ≤ 1/2`, the centre `κ^{(M)} = ε_M^{2β/(q+1)}` of the `M`-th permitted interval, its
convergence to `0⁺`, and the eventual smallness of `η_M/κ^{(M)}` for `η_M = C ε_{M+1}^β`.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance Homogenization

section Epsilon

variable {β : ℝ} {Λ : ℕ}

/-- `ε_m → 0`. -/
theorem epsilon_tendsto_zero (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    Tendsto (fun m => epsilon β Λ m) atTop (𝓝 0) := by
  have hΛ1 : (1 : ℝ) < Λ := by
    have : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    linarith
  have hρ : (Λ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hΛ1
  have hlim : Tendsto (fun m : ℕ => ((Λ : ℝ)⁻¹) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith)) hρ
  refine squeeze_zero (fun m => (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le) (fun m => ?_) hlim
  have h := Infra.Ingredients.epsilon_le_lambda_pow (β := β) (Λ := Λ) (m := m) hβ hβ' hΛ
  rwa [Real.rpow_neg (by linarith), Real.rpow_natCast, ← inv_pow] at h

/-- `ε_k^δ ≤ (Λ^{-δ})^k`. -/
theorem epsilon_rpow_le (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {δ : ℝ} (hδ : 0 ≤ δ)
    (k : ℕ) : epsilon β Λ k ^ δ ≤ ((Λ : ℝ) ^ (-δ)) ^ k := by
  have hΛ0 : (0 : ℝ) < Λ := by
    have : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    linarith
  have h := Infra.Ingredients.epsilon_le_lambda_pow (β := β) (Λ := Λ) (m := k) hβ hβ' hΛ
  calc epsilon β Λ k ^ δ ≤ ((Λ : ℝ) ^ (-(k : ℝ))) ^ δ :=
        Real.rpow_le_rpow (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le h hδ
    _ = ((Λ : ℝ) ^ (-δ)) ^ k := by
        rw [← Real.rpow_mul hΛ0.le, ← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]
        congr 1
        ring

/-- The threshold on `Λ`: `Λ ≥ 2^7`, `C ≤ Λ`, and `C ∑_{i<n} ε_{j+i}^δ ≤ 1/2` for all `j ≥ 1`. -/
theorem exists_lambda_threshold (β C : ℝ) (hβ : 1 < β) (hβ' : β < 4 / 3) (hC : 1 ≤ C) :
    ∃ Λ₀ : ℝ, ∀ Λ : ℕ, Λ₀ ≤ Λ → 2 ^ 7 ≤ Λ ∧ C ≤ Λ ∧
      ∀ j : ℕ, 1 ≤ j → ∀ n : ℕ,
        C * ∑ i ∈ Finset.range n, epsilon β Λ (j + i) ^ delta β ≤ 1 / 2 := by
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  refine ⟨max (max 128 C) ((4 * C) ^ (1 / delta β)), fun Λ hΛ => ?_⟩
  have h128 : (128 : ℝ) ≤ Λ := (le_max_left _ _).trans ((le_max_left _ _).trans hΛ)
  have hCΛ : C ≤ (Λ : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ)
  have hbig : (4 * C) ^ (1 / delta β) ≤ (Λ : ℝ) := (le_max_right _ _).trans hΛ
  have hΛ7 : 2 ^ 7 ≤ Λ := by exact_mod_cast h128
  refine ⟨hΛ7, hCΛ, fun j hj n => ?_⟩
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have h4C : 0 ≤ 4 * C := by linarith
  have hpow : 4 * C ≤ (Λ : ℝ) ^ delta β := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg h4C _) hbig hδ.le
    rwa [← Real.rpow_mul h4C, one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one] at this
  have hρeq : (Λ : ℝ) ^ (-delta β) = ((Λ : ℝ) ^ delta β)⁻¹ := Real.rpow_neg hΛ0.le _
  have hΛδ : 0 < (Λ : ℝ) ^ delta β := Real.rpow_pos_of_pos hΛ0 _
  have hρ0 : 0 ≤ (Λ : ℝ) ^ (-delta β) := Real.rpow_nonneg hΛ0.le _
  have hρ : (Λ : ℝ) ^ (-delta β) ≤ 1 / 2 := by
    rw [hρeq, inv_eq_one_div, div_le_div_iff₀ hΛδ (by norm_num)]
    linarith
  have hCρ : C * (Λ : ℝ) ^ (-delta β) ≤ 1 / 4 := by
    rw [hρeq, ← div_eq_mul_inv, div_le_div_iff₀ hΛδ (by norm_num)]
    linarith
  have hsum : ∑ i ∈ Finset.range n, epsilon β Λ (j + i) ^ delta β ≤
      ∑ i ∈ Finset.range n, ((Λ : ℝ) ^ (-delta β)) ^ (j + i) :=
    Finset.sum_le_sum fun i _ => epsilon_rpow_le hβ hβ' hΛ7 hδ.le _
  exact (mul_le_mul_of_nonneg_left hsum (by linarith)).trans
    (weighted_geom_tail_le (by linarith) hρ0 hρ hCρ hj n)

end Epsilon

section Centre

variable {β : ℝ} {Λ : ℕ}

/-- The centre `ε_M^{2β/(q+1)}` of the `M`-th permitted interval. -/
def kappaCentre (β : ℝ) (Λ M : ℕ) : ℝ := epsilon β Λ M ^ (2 * β / (q β + 1))

theorem kappaCentre_pos (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (M : ℕ) :
    0 < kappaCentre β Λ M :=
  Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos hβ hβ' hΛ) _

theorem kappaCentre_mem_permittedInterval (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (M : ℕ) : kappaCentre β Λ M ∈ permittedInterval β Λ M := by
  have h := kappaCentre_pos hβ hβ' hΛ M
  exact ⟨by unfold kappaCentre at h ⊢; linarith, by unfold kappaCentre at h ⊢; linarith⟩

theorem kappaCentre_mem_permissibleSet (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {M : ℕ} (hM : 1 ≤ M) : kappaCentre β Λ M ∈ permissibleSet β Λ :=
  Set.mem_iUnion₂.2 ⟨M, hM, kappaCentre_mem_permittedInterval hβ hβ' hΛ M⟩

/-- `κ^{(M)} → 0⁺`. -/
theorem kappaCentre_tendsto (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    Tendsto (fun M => kappaCentre β Λ M) atTop (𝓝[>] 0) := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  exact tendsto_rpow_nhdsGT (fun m => Infra.Cutoff.epsilon_pos hβ hβ' hΛ)
    (epsilon_tendsto_zero hβ hβ' hΛ) (by positivity)

/-- The exponent `qβ - 2β/(q+1)` is positive. -/
theorem stream_tail_exponent_pos (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < q β * β - 2 * β / (q β + 1) := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hq1 : 0 < q β + 1 := by linarith
  have h : 2 * β / (q β + 1) < q β * β := by
    rw [div_lt_iff₀ hq1]
    have hq2 : 2 < q β * (q β + 1) := by nlinarith only [hq]
    have := mul_lt_mul_of_pos_right hq2 (by linarith : 0 < β)
    linarith only [this]
  linarith

/-- The supergeometric constant is nonnegative. -/
theorem supergeoConstant_nonneg' (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 ≤ Infra.Ingredients.supergeoConstant β := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  unfold Infra.Ingredients.supergeoConstant
  have : 0 ≤ q β := by linarith only [hq]
  positivity

/-- `ε_{M+1} ≤ (1+A) ε_M^q` for `M ≥ 1`. -/
theorem epsilon_succ_le (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) {M : ℕ} (hM : 1 ≤ M) :
    epsilon β Λ (M + 1) ≤
      (1 + Infra.Ingredients.supergeoConstant β) * epsilon β Λ M ^ q β := by
  have hA := supergeoConstant_nonneg' hβ hβ'
  have hscale := (Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ hM).2
  refine hscale.trans (mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _))
  exact add_le_add (le_refl 1) (mul_le_of_le_one_right hA
    (Infra.Construction.epsilon_le_one hβ hβ' hΛ))

/-- Eventually `Ctail ε_{M+1}^β / κ^{(M)} ≤ 1/10`. -/
theorem eta_div_kappaCentre_eventually (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {Ctail : ℝ} (hCt : 0 ≤ Ctail) :
    ∀ᶠ M in atTop, Ctail * epsilon β Λ (M + 1) ^ β / kappaCentre β Λ M ≤ 1 / 10 := by
  set A := Infra.Ingredients.supergeoConstant β with hA_def
  have hA : 0 ≤ A := supergeoConstant_nonneg' hβ hβ'
  have hexp := stream_tail_exponent_pos hβ hβ'
  have hev := eventually_mul_rpow_le (epsilon_tendsto_zero hβ hβ' hΛ) hexp
    (Ctail * (1 + A) ^ β) (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [hev, eventually_ge_atTop 1] with M hM hM1
  have hε := Infra.Cutoff.epsilon_pos hβ hβ' hΛ (m := M)
  have hκ := kappaCentre_pos hβ hβ' hΛ M
  have hsucc := Real.rpow_le_rpow (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le
    (epsilon_succ_le hβ hβ' hΛ hM1) (by linarith : 0 ≤ β)
  rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le] at hsucc
  rw [div_le_iff₀ hκ]
  have hsplit : epsilon β Λ M ^ (q β * β) =
      epsilon β Λ M ^ (q β * β - 2 * β / (q β + 1)) * kappaCentre β Λ M := by
    unfold kappaCentre
    rw [← Real.rpow_add hε]
    congr 1
    ring
  calc Ctail * epsilon β Λ (M + 1) ^ β
      ≤ Ctail * ((1 + A) ^ β * epsilon β Λ M ^ (q β * β)) :=
        mul_le_mul_of_nonneg_left hsucc hCt
    _ = Ctail * (1 + A) ^ β * epsilon β Λ M ^ (q β * β - 2 * β / (q β + 1)) *
          kappaCentre β Λ M := by rw [hsplit]; ring
    _ ≤ 1 / 10 * kappaCentre β Λ M := mul_le_mul_of_nonneg_right hM hκ.le

end Centre

end AVenhance.Infra.Section5.RelativeError
