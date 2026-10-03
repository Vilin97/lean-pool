/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered

/-! # Entrywise bounds for the defect matrices and `∇G`

On the support of `ξ_{m,k}` (`m ≥ 2`, `κ_m > 0`), with `e = ε_{m-1}^{2δ}` and `P = a_m ε_m²`:

* `|(D_k)_{ij}| ≤ 2 e P`, `|(E_k)_{ij}| ≤ 4 e P`;
* `|(G_{l_k})_j| ≤ 4 |∇T|`;
* `|(∇G_{l_k})_{ij}| ≤ 2 (h₀ + h₁) + 8 (2^16 ε_{m-1}⁻¹) |∇T|`.

No oddness of `k` is needed: the flow estimates only use `ξ_{m,k}(t) ≠ 0`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem scf_e_le_one {m : ℕ} : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
  Real.rpow_le_one (epsilon_pos' I _).le (epsilon_le_one' I _) (by linarith [delta_pos' I])

theorem scf_e_nonneg {m : ℕ} : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
  Real.rpow_nonneg (epsilon_pos' I _).le _

theorem scf_P_nonneg {m : ℕ} : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 := by
  have := a_nonneg' I m
  positivity

/-- Entries of `Χ_{m,k}` gradient: `|∂_aΧ_j| ≤ P/κ`. -/
theorem scf_grad_chi_le {m : ℕ} (hm : 2 ≤ m) {κm : ℝ} (hκ : 0 < κm) (k : ℤ) (t : ℝ)
    (y : Vec 2) (u v : Fin 2) :
    |gradMatrix (fun z => I.chiMK κm m k t z) y u v| ≤
      a β I.Λ m * epsilon β I.Λ m ^ 2 / κm :=
  LeftToShow.gradMatrix_chiMK_entry_abs_le I (by omega) hκ k t y u v

theorem scf_sdDefect4_entry_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {k : ℤ} {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (y : Vec 2) (i j : Fin 2) :
    |sdDefect4 I hΦ m κm k t y i j| ≤
      2 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (a β I.Λ m * epsilon β I.Λ m ^ 2) := by
  unfold sdDefect4
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hκ]
  have hM := abs_matMul_le (M := gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) y - 1)
    (N := gradMatrix (fun z => I.chiMK κm m k t z) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))
    (fun u v => gradMatrix_xFlowInv_sub_one_le hΦ hm k hξ y u v)
    (fun u v => scf_grad_chi_le I hm hκ k t _ u v) i j
  calc κm * _ ≤ κm * (2 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
        (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) :=
        mul_le_mul_of_nonneg_left hM hκ.le
    _ = _ := by field_simp

theorem scf_one_sub_transpose_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {k : ℤ} {t : ℝ}
    (hξ : I.xiMK m k t ≠ 0) (y : Vec 2) (i a : Fin 2) :
    |(1 - (flowGradK I hΦ m k t y).transpose) i a| ≤
      epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
  have h : (1 - (flowGradK I hΦ m k t y).transpose) i a =
      -((I.flowGrad hΦ m (lIdx β I.Λ m k) t y - 1) a i) := by
    simp only [flowGradK, Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply]
    by_cases hia : i = a
    · subst hia; simp
    · have : ¬ a = i := fun h => hia h.symm
      simp [hia, this]
  rw [h, abs_neg]
  exact flowGrad_sub_one_le hΦ hm k hξ y a i

theorem scf_sdDefect5_entry_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ}
    (hκ : 0 < κm) {k : ℤ} {t : ℝ} (hξ : I.xiMK m k t ≠ 0) (y : Vec 2) (i j : Fin 2) :
    |sdDefect5 I hΦ m κm k t y i j| ≤
      2 * epsilon β I.Λ (m - 1) ^ (2 * delta β) * (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2)) := by
  unfold sdDefect5
  have hz := Infra.Section3.zetaProd_mem_Icc I (by omega : 1 ≤ m) k t
  have hψ : |(I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t) *
      psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)| ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 := by
    have hz' : 0 ≤ I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t := hz.1
    rw [abs_mul, abs_of_nonneg hz']
    calc _ ≤ 1 * (a β I.Λ m * epsilon β I.Λ m ^ 2) :=
          mul_le_mul hz.2 (Infra.Section4.amnr_psi_abs_le I m k _) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hN : ∀ u v : Fin 2, |((I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
        psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) • sigmaMat +
      κm • gradMatrix (fun z => I.chiMK κm m k t z) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) u v|
      ≤ 2 * (a β I.Λ m * epsilon β I.Λ m ^ 2) := by
    intro u v
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    have h1 : |(I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
        psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) * sigmaMat u v| ≤
        a β I.Λ m * epsilon β I.Λ m ^ 2 := by
      rw [abs_mul]
      calc _ ≤ (a β I.Λ m * epsilon β I.Λ m ^ 2) * 1 :=
            mul_le_mul hψ (sa_sigma_abs_le u v) (abs_nonneg _) (scf_P_nonneg I)
        _ = _ := mul_one _
    have h2 : |κm * gradMatrix (fun z => I.chiMK κm m k t z)
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y) u v| ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 := by
      rw [abs_mul, abs_of_pos hκ]
      calc κm * _ ≤ κm * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) :=
            mul_le_mul_of_nonneg_left (scf_grad_chi_le I hm hκ k t _ u v) hκ.le
        _ = _ := by field_simp
    have := abs_add_le_of_le h1 h2
    linarith
  exact abs_matMul_le (fun u v => scf_one_sub_transpose_le I hΦ hm hξ y u v) hN i j

theorem scf_G_abs_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {T : ℝ → Vec 2 → ℝ}
    {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) {k : ℤ} (hξ : I.xiMK m k t ≠ 0) (x : Vec 2)
    {gT : ℝ} (hg : ∀ p, |spaceGrad (T t) x p| ≤ gT) (j : Fin 2) :
    |G I hΦ m T (lIdx β I.Λ m k) t x j| ≤ 2 * 2 * gT := by
  have hT := (hTt.differentiable (by simp) x).hasFDerivAt
  have hX := (((contDiff_xFlow_slice I hΦ m (lIdx β I.Λ m k) t).differentiable (by simp))
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
  rw [G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x hT hX (xFlow_xFlowInv I hΦ m _ t x)]
  exact abs_mulVec_le (abs_le_two_of_sub_one (scf_e_le_one I)
    (fun u v => flowGrad_sub_one_le hΦ hm k hξ x u v)) hg j

theorem scf_gradG_abs_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {T : ℝ → Vec 2 → ℝ}
    {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) {k : ℤ} (hξ : I.xiMK m k t ≠ 0) (x : Vec 2)
    {gT : ℝ} {h : Fin 2 → ℝ} (hg : ∀ p, |spaceGrad (T t) x p| ≤ gT)
    (hh : ∀ i p, |spaceHess (T t) x i p| ≤ h p) (i j : Fin 2) :
    |gradG I hΦ m T (lIdx β I.Λ m k) t x i j| ≤
      2 * (h 0 + h 1) + 8 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹) * gT := by
  have hgg : gradG I hΦ m T (lIdx β I.Λ m k) t x i j =
      spaceGrad (fun y => G I hΦ m T (lIdx β I.Λ m k) t y j) x i := rfl
  rw [hgg, spaceGrad_G_component I hΦ m T (lIdx β I.Λ m k) hTt x i j]
  have hFl2 := abs_le_two_of_sub_one (scf_e_le_one I)
    (fun u v => flowGrad_sub_one_le hΦ hm k hξ x u v)
  have hA2 := abs_le_two_of_sub_one (scf_e_le_one I)
    (fun u v => gradMatrix_xFlowInv_sub_one_le hΦ hm k hξ x u v)
  set D := 2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹ with hD
  have hq : ∀ p, |∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x i q *
      xFlowHess I hΦ m (lIdx β I.Λ m k) t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) p j q| ≤
      4 * D := by
    intro p
    simp only [Fin.sum_univ_two]
    have := abs_add_le_of_le (abs_mul_le_of_le (hA2 i 0)
      (abs_xFlowHess_le hΦ hm k hξ (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) p j 0))
          (abs_mul_le_of_le (hA2 i 1)
      (abs_xFlowHess_le hΦ hm k hξ (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) p j 1))
    linarith
  have hp : ∀ p, |I.flowGrad hΦ m (lIdx β I.Λ m k) t x j p * spaceHess (T t) x i p +
      (∑ q : Fin 2, gradMatrix (fun z => I.xFlowInv hΦ m (lIdx β I.Λ m k) t z) x i q *
        xFlowHess I hΦ m (lIdx β I.Λ m k) t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) p j q) *
        spaceGrad (T t) x p| ≤ 2 * h p + 4 * D * gT := by
    intro p
    have := abs_add_le_of_le (abs_mul_le_of_le (hFl2 j p) (hh i p))
      (abs_mul_le_of_le (hq p) (hg p))
    linarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun p _ => hp p).trans_eq ?_)
  simp only [Fin.sum_univ_two]
  ring

end AVenhance.Infra.Section5.Contracts
end
