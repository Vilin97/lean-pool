/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsFields

/-! # Pointwise bound for `∇θTilde_m - F ∇T_{m-1}`

Combines the exact decomposition `ansatz_spaceGrad_sub_leadingGrad` with the pointwise bound on the
three remainder fields: the partition of unity `∑_{k odd} ξ_{m,k} = 1` with `0 ≤ ξ ≤ 1` turns the
`k`-uniform bound into a bound for the weighted sum. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem xiMK_nonneg' (I : Ingredients β) (m : ℕ) (k : ℤ) (t : ℝ) : 0 ≤ I.xiMK m k t := by
  unfold Ingredients.xiMK scaledCutoff
  exact (indIcc_nonneg' (-(3 / 4)) (3 / 4) _).trans (I.ind_le_xi _)

/-- The componentwise bound on the leading-gradient error with the `∇HTilde_m` part removed, at
`(t, x)`, `t ≥ 0`. -/
theorem ansatz_error_sub_Hm_component_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2)
    (hHt : DifferentiableAt ℝ (I.Hm hΦ m κm T t) x)
    {gT : ℝ} {h : Fin 2 → ℝ} (hg : ∀ p, |spaceGrad (T t) x p| ≤ gT)
    (hh : ∀ i p, |spaceHess (T t) x i p| ≤ h p) (i : Fin 2) :
    |(spaceGrad (I.ansatz hΦ m κm T t) x - LeftToShow.leadingGrad I hΦ m κm T t x -
        spaceGrad (I.Hm hΦ m κm T t) x) i| ≤
      (20 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) * gT +
        epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
          (4 * (h 0 + h 1) + 16 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) * gT)) := by
  classical
  have hm1 : 1 ≤ m := by omega
  rw [ansatz_spaceGrad_sub_leadingGrad I hΦ hm1 κm hTt x hHt, add_sub_cancel_right]
  set U := (Infra.Section3.xiMK_odd_support_finite I hm1 t).toFinset with hU
  set B := 20 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
        gT + epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
          (4 * (h 0 + h 1) + 16 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) * gT) with hB
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ U, |I.xiMK m k.1 t *
      (leadingErrFlowInv I hΦ m κm T k.1 t x + leadingErrFlowFwd I hΦ m κm T k.1 t x +
        leadingErrHessian I hΦ m κm T k.1 t x) i| ≤ I.xiMK m k.1 t * B := by
    intro k hk
    have hk' : I.xiMK m k.1 t ≠ 0 := by simpa [hU] using hk
    rw [abs_mul, abs_of_nonneg (xiMK_nonneg' I m k.1 t)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Pi.add_apply] using
        leadingErr_sum_component_le hΦ hm hκ T k.1 hk' x hg hh i)
      (xiMK_nonneg' I m k.1 t)
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [← Finset.sum_mul, Infra.Section3.xiMK_odd_partition_finset I hm1 t, one_mul]

/-- The componentwise bound on the leading-gradient error at `(t, x)`, `t ≥ 0`. -/
theorem ansatz_error_component_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2)
    (hHt : DifferentiableAt ℝ (I.Hm hΦ m κm T t) x)
    {gT : ℝ} {h : Fin 2 → ℝ} (hg : ∀ p, |spaceGrad (T t) x p| ≤ gT)
    (hh : ∀ i p, |spaceHess (T t) x i p| ≤ h p) (i : Fin 2) :
    |(spaceGrad (I.ansatz hΦ m κm T t) x - LeftToShow.leadingGrad I hΦ m κm T t x) i| ≤
      (20 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) * gT +
        epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
          (4 * (h 0 + h 1) + 16 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) * gT)) +
      |spaceGrad (I.Hm hΦ m κm T t) x i| := by
  have key := ansatz_error_sub_Hm_component_le hΦ hm hκ hTt x hHt hg hh i
  have hsplit : (spaceGrad (I.ansatz hΦ m κm T t) x -
        LeftToShow.leadingGrad I hΦ m κm T t x) i =
      (spaceGrad (I.ansatz hΦ m κm T t) x - LeftToShow.leadingGrad I hΦ m κm T t x -
        spaceGrad (I.Hm hΦ m κm T t) x) i + spaceGrad (I.Hm hΦ m κm T t) x i := by
    simp
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add key le_rfl)

end AVenhance.Infra.Section5.RelativeError
