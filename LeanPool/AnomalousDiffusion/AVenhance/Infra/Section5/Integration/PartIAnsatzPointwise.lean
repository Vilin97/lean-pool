/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsError
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebra
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingEnergyReduction

/-! # Pointwise bound for the corrector part of the ansatz

Source: `enhance.tex` (`e.tildethetam.to.Tm.A.temptemp`).  At a fixed time `t`,
`θTilde_m - T_{m-1} - HTilde_m = ∑_{k odd} ξ_{m,k} ΧTilde_{m,k} · G_{l_k}` is bounded pointwise by
`4 ‖Χ‖_∞ (|∂₁T| + |∂₂T|)`: `G_{l_k} = (∇X ∘ X⁻¹)∇T` with `|(∇X∘X⁻¹)_{ij}| ≤ 2` on
`supp ξ_{m,k}`, and `∑_k ξ_{m,k} = 1`, `0 ≤ ξ_{m,k}`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError

/-- A bilinear pairing of a bounded vector with a matrix-vector product of entrywise bound `2`. -/
theorem vecDot_mulVec_abs_le {χ g : Vec 2} {F : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hχ : ∀ j, |χ j| ≤ c) (hF : ∀ i j, |F i j| ≤ 2) :
    |vecDot χ (F.mulVec g)| ≤ 4 * c * (|g 0| + |g 1|) := by
  have hrow : ∀ j : Fin 2, |χ j * (F j 0 * g 0 + F j 1 * g 1)| ≤ c * (2 * (|g 0| + |g 1|)) := by
    intro j
    rw [abs_mul]
    refine mul_le_mul (hχ j) ?_ (abs_nonneg _) hc
    calc |F j 0 * g 0 + F j 1 * g 1| ≤ |F j 0 * g 0| + |F j 1 * g 1| := abs_add_le _ _
      _ = |F j 0| * |g 0| + |F j 1| * |g 1| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * |g 0| + 2 * |g 1| :=
          add_le_add (mul_le_mul_of_nonneg_right (hF j 0) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (hF j 1) (abs_nonneg _))
      _ = 2 * (|g 0| + |g 1|) := by ring
  simp only [vecDot, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  calc |χ 0 * (F 0 0 * g 0 + F 0 1 * g 1) + χ 1 * (F 1 0 * g 0 + F 1 1 * g 1)|
      ≤ |χ 0 * (F 0 0 * g 0 + F 0 1 * g 1)| + |χ 1 * (F 1 0 * g 0 + F 1 1 * g 1)| :=
        abs_add_le _ _
    _ ≤ c * (2 * (|g 0| + |g 1|)) + c * (2 * (|g 0| + |g 1|)) :=
        add_le_add (hrow 0) (hrow 1)
    _ = 4 * c * (|g 0| + |g 1|) := by ring

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The sup norm of the corrector `Χ_{m,k}`, in the form of `CorrectorBounds`. -/
def chiSup (κ : ℝ) (m : ℕ) : ℝ :=
  (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ * |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m|

theorem chiSup_nonneg {κ : ℝ} (hκ : 0 < κ) (m : ℕ) : 0 ≤ chiSup I κ m := by
  have he := epsilon_pos' I m
  unfold chiSup
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (abs_nonneg _)

/-- Entries of the flow gradient are bounded by `2` on `supp ξ_{m,k}`. -/
theorem flowGrad_abs_le_two (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) (k : ℤ) {t : ℝ}
    (hξ : I.xiMK m k t ≠ 0) (x : Vec 2) (i j : Fin 2) :
    |I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j| ≤ 2 := by
  have h1 := flowGrad_sub_one_le (I := I) hΦ hm k hξ x i j
  have hε1 := epsilon_le_one' I (m - 1)
  have hε0 := epsilon_pos' I (m - 1)
  have hδ := delta_pos' I
  have h2 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one hε0.le hε1 (by linarith)
  have h3 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      simp
    · rw [Matrix.one_apply_ne hij]
      simp
  have h4 : I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j =
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t x - 1) i j + (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    rw [Matrix.sub_apply]
    ring
  rw [h4]
  exact (abs_add_le _ _).trans (by linarith)

/-- Pointwise bound on one pairing `ΧTilde_{m,k} · G_{l_k}` on `supp ξ_{m,k}`. -/
theorem ansatzPairing_abs_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (k : ℤ)
    (hξ : I.xiMK m k t ≠ 0) (x : Vec 2) :
    |ansatzPairing I hΦ m κm T k t x| ≤
      4 * chiSup I κm m * (|spaceGrad (T t) x 0| + |spaceGrad (T t) x 1|) := by
  have hT := (hTt.differentiable (by simp) x).hasFDerivAt
  have hX := (((contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t).differentiable (by simp))
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
  have hG := G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x hT hX
    (xFlow_xFlowInv I hΦ m _ t x)
  unfold ansatzPairing
  rw [hG]
  exact vecDot_mulVec_abs_le (chiSup_nonneg I hκ m)
    (fun j => Infra.Section3.chiMK_component_abs_le I (by omega) κm hκ k t _ j)
    (flowGrad_abs_le_two I hΦ hm k hξ x)

/-- **Pointwise bound** for the corrector part of the ansatz at a fixed time. -/
theorem ansatz_sub_T_sub_Hm_abs_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) (x : Vec 2) :
    |I.ansatz hΦ m κm T t x - T t x - I.Hm hΦ m κm T t x| ≤
      4 * chiSup I κm m * (|spaceGrad (T t) x 0| + |spaceGrad (T t) x 1|) := by
  classical
  have hm1 : 1 ≤ m := by omega
  set U := (Infra.Section3.xiMK_odd_support_finite I hm1 t).toFinset with hU
  set B := 4 * chiSup I κm m * (|spaceGrad (T t) x 0| + |spaceGrad (T t) x 1|) with hB
  have hfun := congrFun (ansatz_eq_finset_sum I hΦ hm1 κm T t) x
  have hsum : I.ansatz hΦ m κm T t x - T t x - I.Hm hΦ m κm T t x =
      ∑ q ∈ U, I.xiMK m q.1 t * ansatzPairing I hΦ m κm T q.1 t x := by
    rw [hfun]
    ring
  have hone : ∑ q ∈ U, I.xiMK m q.1 t = 1 := Infra.Section3.xiMK_odd_partition_finset I hm1 t
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q ∈ U, |I.xiMK m q.1 t * ansatzPairing I hΦ m κm T q.1 t x|
      ≤ ∑ q ∈ U, I.xiMK m q.1 t * B := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [abs_mul, abs_of_nonneg (xiMK_nonneg' I m q.1 t)]
        by_cases hq : I.xiMK m q.1 t = 0
        · simp [hq]
        · exact mul_le_mul_of_nonneg_left (ansatzPairing_abs_le I hΦ hm hκ hTt q.1 hq x)
            (xiMK_nonneg' I m q.1 t)
    _ = B := by rw [← Finset.sum_mul, hone, one_mul]

end AVenhance.Infra.Section5.Integration
