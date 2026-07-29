/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CanonicalJensenBound
public import LeanPool.Odlyzko.ExplicitFormula.CanonicalLogDerivativeBound
public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaMovingJensen
public import LeanPool.Odlyzko.ExplicitFormula.ZeroFreeCircleSelection

/-!
# Completed Zeta Canonical Log Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta canonical jensen coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaCanonicalJensenCoefficient : ℝ :=
  1 / Real.log (6 / 5)

open Classical in
theorem completedZetaCanonicalJensenCoefficient_pos :
    0 < completedZetaCanonicalJensenCoefficient := by
  unfold completedZetaCanonicalJensenCoefficient
  positivity

open Classical in
theorem norm_logDeriv_poleClearedCompletedZeta_le_of_local_separation
    {t δ A : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hcenter :
      Real.log (completedZetaMovingCircleBound K 6 t) -
          Real.log
            ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall (2 + t * I) 3)
    (hfz : poleClearedCompletedDedekindZetaContinuation K z ≠ 0)
    (hsep : ∀ p ∈ ball (2 + t * I) 5,
      poleClearedCompletedDedekindZetaContinuation K p = 0 →
      δ ≤ ‖z - p‖) :
    ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K) z‖ ≤
      (A * completedZetaCanonicalJensenCoefficient / δ +
        A * completedZetaCanonicalJensenCoefficient) +
      32 * A := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  let c : ℂ := 2 + t * I
  let M : ℝ := completedZetaMovingCircleBound K 6 t
  have hMone : 1 ≤ M := one_le_completedZetaMovingCircleBound K 6 t
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
  have hΞ : AnalyticOnNhd ℂ Ξ (closedBall c 6) :=
    (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).mono
      (subset_univ _)
  have hc : Ξ c ≠ 0 := by
    have hs : 1 < c.re := by simp [c]
    exact poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (by simp_all)
  obtain ⟨R, ⟨hR4, hR5⟩, hboundary⟩ :=
    AnalyticOnNhd.exists_zeroFree_sphere
      (show (0 : ℝ) ≤ 4 by norm_num) (show (4 : ℝ) < 5 by norm_num)
      (hΞ.mono (closedBall_subset_closedBall (by norm_num))) hc
  have hRpos : 0 < R := by linarith
  have hR6 : R < 6 := by linarith
  have houter :
      ∀ w ∈ sphere c 6, ‖Ξ w‖ ≤ M := by
    intro w hw
    exact norm_poleClearedCompletedZeta_le_movingCircleBound K 6 t
      (by grind)
  have hboundR : ∀ w ∈ sphere c R, ‖Ξ w‖ ≤ M := by
    intro w hw
    apply norm_le_on_closedBall_of_norm_le_on_sphere
      (show (0 : ℝ) < 6 by norm_num) hΞ houter
    rw [mem_closedBall, mem_sphere] at *
    linarith
  let F : ℂ → ℂ := fun w ↦ Ξ (c + w)
  have hF : AnalyticOnNhd ℂ F (closedBall 0 6) := by
    intro w hw
    have hcw : c + w ∈ closedBall c 6 := by simp_all
    have hshift : AnalyticAt ℂ (fun x : ℂ ↦ c + x) w := by
      fun_prop
    exact AnalyticAt.comp
      (g := Ξ) (f := fun x : ℂ ↦ c + x) (x := w)
      (hΞ (c + w) hcw) hshift
  have hFboundary : ∀ w ∈ sphere 0 R, F w ≠ 0 := by
    intro w hw
    apply hboundary (c + w)
    simp_all
  have hFouter : ∀ w ∈ sphere 0 6, ‖F w‖ ≤ M := by
    intro w hw
    apply houter (c + w)
    simp_all
  let B : ℝ := A * completedZetaCanonicalJensenCoefficient
  have hmass :
      ((∑ᶠ u, MeromorphicOn.divisor F (ball 0 R) u : ℤ) : ℝ) ≤ B := by
    have hJ :=
      AnalyticOnNhd.sum_divisor_ball_le hRpos hR6 hMone hF
        (by simpa [F] using hc) hFboundary hFouter
    have hnum :
        Real.log (M / ‖F 0‖) ≤ A := by
      rw [Real.log_div (ne_of_gt hMpos)
        (norm_ne_zero_iff.mpr (by simpa [F] using hc))]
      simpa [F, M, c] using hcenter
    have hlogpos : 0 < Real.log (6 / 5) := by positivity
    have hden :
        Real.log (6 / 5) ≤ Real.log (6 / R) := by
      apply Real.strictMonoOn_log.monotoneOn
      · norm_num
      · simp_all
      · apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6)
          (by linarith) (by linarith)
    have hdenpos : 0 < Real.log (6 / R) := hlogpos.trans_le hden
    calc
      ((∑ᶠ u, MeromorphicOn.divisor F (ball 0 R) u : ℤ) : ℝ) ≤
          Real.log (M / ‖F 0‖) / Real.log (6 / R) := hJ
      _ ≤ A / Real.log (6 / R) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ ≤ A / Real.log (6 / 5) := by
        exact div_le_div₀ hA.le le_rfl hlogpos hden
      _ = B := by
        simp [B, completedZetaCanonicalJensenCoefficient]
        ring
  have hsepF :
      ∀ u ∈ (MeromorphicOn.divisor F (ball 0 R)).support,
        δ ≤ ‖(z - c) - u‖ := by
    intro u hu
    have huBall : u ∈ ball 0 R := divisor_ball_support_subset hu
    have hzero : F u = 0 :=
      AnalyticOnNhd.eq_zero_of_mem_divisor_support
        (hF.mono ((ball_subset_ball hR6.le).trans ball_subset_closedBall)) hu
    have hcu : c + u ∈ ball c 5 := by
      rw [mem_ball, dist_eq]
      have : ‖u‖ < R := by simp_all
      simpa using this.trans hR5
    have := hsep (c + u) hcu (by grind)
    (convert this using 1; ring_nf)
  have hlocal :=
    norm_logDeriv_le_of_canonical_factorization_centered
      (f := Ξ) (c := c) (z := z)
      hRpos (show (0 : ℝ) ≤ 3 by norm_num) (by linarith)
      hδ hMpos hA
      (hΞ.mono (closedBall_subset_closedBall hR6.le))
      hc hboundary hboundR (by grind)
      (by grind) hfz hsepF hmass
  have hBnonneg : 0 ≤ B := by
    exact mul_nonneg hA.le completedZetaCanonicalJensenCoefficient_pos.le
  calc
    ‖logDeriv Ξ z‖ ≤
        (B / δ + B / (R - 3)) +
          4 * A * (R + 3) / (R - 3) ^ 2 := hlocal
    _ ≤ (B / δ + B) + 32 * A := by
      have hgapPos : 0 < R - 3 := by linarith
      have hfrac : B / (R - 3) ≤ B := by
        exact (div_le_iff₀ hgapPos).2
          (by nlinarith)
      have hbor :
          4 * A * (R + 3) / (R - 3) ^ 2 ≤ 32 * A := by
        rw [div_le_iff₀ (sq_pos_of_pos hgapPos)]
        nlinarith [sq_nonneg (R - 4)]
      grind
    _ = (A * completedZetaCanonicalJensenCoefficient / δ +
          A * completedZetaCanonicalJensenCoefficient) + 32 * A := by grind

end NumberField.Odlyzko
