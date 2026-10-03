/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxEstimate

/-! # Slicewise `L²` bound of `cutoff1`

`‖cutoff1(t)‖²_{L²(𝕋²)} ≤ P² ‖∇T(t)‖²_{L²(𝕋²)}`, from the pointwise bound
`sb_cutoff1_abs_le` (a Bochner integral dominated by an integrable function needs no integrability
of the dominated function). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sb_l2NormSq_cutoff1_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κ : ℝ} (hκ : 0 ≤ κ)
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) :
    l2NormSq (cutoff1 I hΦ m κ T t) ≤
      (64 * Real.pi * I.Cxi * (a β I.Λ m * epsilon β I.Λ m) *
        Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12)))) ^ 2 *
        gradNormSq (fun x => spaceGrad (T t) x) := by
  set P : ℝ := 64 * Real.pi * I.Cxi * (a β I.Λ m * epsilon β I.Λ m) *
        Real.exp (-(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12))) with hP
  have hVc : Continuous (fun x => spaceGrad (T t) x) := by
    apply continuous_pi
    intro i
    exact (hTt.continuous_fderiv (by simp)).clm_apply continuous_const
  have hvi : IntegrableOn (fun x => vecNormSq (spaceGrad (T t) x)) unitCube :=
    LeftToShow.integrableOn_unitCube_of_continuous
      (LeftToShow.continuous_vecNormSq_two.comp hVc)
  unfold l2NormSq gradNormSq
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (hvi.const_mul (P ^ 2)) (Filter.Eventually.of_forall fun x => ?_)
  have hp := sb_cutoff1_abs_le I hΦ hm hκ hTt x
  have hg0 : 0 ≤ Real.sqrt (vecNormSq (spaceGrad (T t) x)) := Real.sqrt_nonneg _
  have hvn : 0 ≤ vecNormSq (spaceGrad (T t) x) := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    change 0 ≤ spaceGrad (T t) x 0 * spaceGrad (T t) x 0 + spaceGrad (T t) x 1 * spaceGrad (T t) x 1
    nlinarith [mul_self_nonneg (spaceGrad (T t) x 0), mul_self_nonneg (spaceGrad (T t) x 1)]
  have hsq : (cutoff1 I hΦ m κ T t x) ^ 2 ≤ P ^ 2 * vecNormSq (spaceGrad (T t) x) := by
    have h1 : (cutoff1 I hΦ m κ T t x) ^ 2 =
        |cutoff1 I hΦ m κ T t x| ^ 2 := (sq_abs _).symm
    rw [h1]
    calc _ ≤ (P * Real.sqrt (vecNormSq (spaceGrad (T t) x))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hp 2
      _ = P ^ 2 * vecNormSq (spaceGrad (T t) x) := by
          rw [mul_pow, Real.sq_sqrt hvn]
  exact hsq

end AVenhance.Infra.Section5.Contracts
end
