/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CanonicalAnalyticFactorization
public import LeanPool.Odlyzko.ExplicitFormula.DiskMaximumNorm
public import LeanPool.Odlyzko.ExplicitFormula.ZeroFreeLogDerivativeBound

/-!
# Canonical Log Derivative Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Metric Set

namespace NumberField.Odlyzko

open Classical in
theorem norm_logDeriv_le_of_canonical_factorization
    {f : ℂ → ℂ} {z : ℂ} {r R δ M A B : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hδ : 0 < δ) (hM : 0 < M) (hA : 0 < A)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hc : f 0 ≠ 0)
    (hboundary : ∀ w ∈ sphere 0 R, f w ≠ 0)
    (hbound : ∀ w ∈ sphere 0 R, ‖f w‖ ≤ M)
    (hcenter : Real.log M - Real.log ‖f 0‖ ≤ A)
    (hz : z ∈ closedBall 0 r) (hfz : f z ≠ 0)
    (hsep : ∀ u ∈
      (MeromorphicOn.divisor f (ball 0 R)).support,
        δ ≤ ‖z - u‖)
    (hmass :
      ((∑ᶠ u, MeromorphicOn.divisor f (ball 0 R) u : ℤ) : ℝ) ≤ B) :
    ‖logDeriv f z‖ ≤
      (B / δ + B / (R - r)) +
        4 * A * (R + r) / (R - r) ^ 2 := by
  let D := MeromorphicOn.divisor f (ball 0 R)
  let P := centeredCanonicalZeroProduct 0 R D
  obtain ⟨g, hg, hgn, heq, hgboundary, hcenterNorm⟩ :=
    AnalyticOnNhd.exists_canonicalZeroFactor_on_ball_zero
      hR hf hc hboundary
  have hDfin : D.support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  have hDnonneg : ∀ u, 0 ≤ D u := by
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hf.mono ball_subset_closedBall) u
  have hDinside : ∀ u ∈ D.support, u ∈ ball 0 R :=
    divisor_ball_support_subset
  have hzBall : z ∈ ball 0 R := by
    rw [mem_ball, mem_closedBall] at *
    grind
  have hzD : z ∉ D.support := by
    intro hzSupport
    have := hsep z hzSupport
    simp at this
    linarith
  have hgz : g z ≠ 0 :=
    hgn z (ball_subset_closedBall hzBall)
  have heqz : f z = P z * g z := by
    simpa [P, D] using heq (ball_subset_closedBall hzBall)
  have hPz : P z ≠ 0 := by simp_all
  have hPanalytic : AnalyticOnNhd ℂ P (closedBall 0 R) := by
    exact analyticOnNhd_centeredCanonicalZeroProduct hDnonneg hDinside
  have hlogEq :
      logDeriv f z = logDeriv P z + logDeriv g z := by
    have heqBall : EqOn f (P * g) (ball 0 R) := by
      intro w hw
      simpa [P, D] using heq (ball_subset_closedBall hw)
    rw [logDeriv_apply, heqBall.deriv isOpen_ball hzBall,
      heqBall hzBall, logDeriv_apply]
    exact logDeriv_mul z hPz hgz
      ((hPanalytic z (ball_subset_closedBall hzBall)).differentiableAt)
      ((hg z (ball_subset_closedBall hzBall)).differentiableAt)
  have hPbound :
      ‖logDeriv P z‖ ≤ B / δ + B / (R - r) := by
    rw [logDeriv_centeredCanonicalZeroProduct
      hDfin hR hDinside hzBall hzD]
    exact norm_finsum_canonicalLogDeriv_le_of_finsum_le
      hDfin hDnonneg hδ hR hr hrR hDinside hz
      (by grind) (by grind)
  have hgBound : ∀ w ∈ ball 0 R, ‖g w‖ ≤ M := by
    intro w hw
    apply norm_le_on_closedBall_of_norm_le_on_sphere hR hg
      (fun v hv ↦ (hgboundary v hv).le.trans (hbound v hv))
    exact ball_subset_closedBall hw
  have hcenterG : Real.log M - Real.log ‖g 0‖ ≤ A := by
    have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hc
    have hg0pos : 0 < ‖g 0‖ :=
      norm_pos_iff.mpr (hgn 0 (mem_closedBall_self hR.le))
    have hlogle : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hf0pos) (Set.mem_Ioi.mpr hg0pos) hcenterNorm
    linarith
  have hgLog :
      ‖logDeriv g z‖ ≤
        4 * A * (R + r) / (R - r) ^ 2 :=
    norm_logDeriv_le_of_zeroFree_on_ball
      hR hr hrR hM hA
      (hg.mono ball_subset_closedBall)
      (fun w hw ↦ hgn w (ball_subset_closedBall hw))
      hgBound hcenterG hz
  rw [hlogEq]
  exact (norm_add_le _ _).trans (add_le_add hPbound hgLog)

open Classical in
theorem norm_logDeriv_le_of_canonical_factorization_centered
    {f : ℂ → ℂ} {c z : ℂ} {r R δ M A B : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hδ : 0 < δ) (hM : 0 < M) (hA : 0 < A)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0)
    (hboundary : ∀ w ∈ sphere c R, f w ≠ 0)
    (hbound : ∀ w ∈ sphere c R, ‖f w‖ ≤ M)
    (hcenter : Real.log M - Real.log ‖f c‖ ≤ A)
    (hz : z ∈ closedBall c r) (hfz : f z ≠ 0)
    (hsep : ∀ u ∈
      (MeromorphicOn.divisor (fun w ↦ f (c + w)) (ball 0 R)).support,
        δ ≤ ‖(z - c) - u‖)
    (hmass :
      ((∑ᶠ u,
        MeromorphicOn.divisor (fun w ↦ f (c + w)) (ball 0 R) u : ℤ) : ℝ) ≤ B) :
    ‖logDeriv f z‖ ≤
      (B / δ + B / (R - r)) +
        4 * A * (R + r) / (R - r) ^ 2 := by
  let F : ℂ → ℂ := fun w ↦ f (c + w)
  let w : ℂ := z - c
  have hF : AnalyticOnNhd ℂ F (closedBall 0 R) := by
    intro v hv
    have hcv : c + v ∈ closedBall c R := by simp_all
    have hshift : AnalyticAt ℂ (fun x : ℂ ↦ c + x) v := by
      fun_prop
    exact AnalyticAt.comp
      (g := f) (f := fun x : ℂ ↦ c + x) (x := v)
      (hf (c + v) hcv) hshift
  have hw : w ∈ closedBall 0 r := by
    simpa [w, mem_closedBall, dist_eq] using hz
  have hFbound : ∀ v ∈ sphere 0 R, ‖F v‖ ≤ M := by
    intro v hv
    apply hbound
    simp_all
  have hFboundary : ∀ v ∈ sphere 0 R, F v ≠ 0 := by
    intro v hv
    apply hboundary
    simp_all
  have hlocal :=
    norm_logDeriv_le_of_canonical_factorization
      hR hr hrR hδ hM hA hF (by simpa [F] using hc)
      hFboundary hFbound (by simpa [F] using hcenter)
      hw (by simpa [F, w] using hfz)
      (by grind)
      (by simpa [F] using hmass)
  have hzBall : z ∈ ball c R := by
    rw [mem_ball, mem_closedBall] at *
    grind
  have hfDiff : DifferentiableAt ℂ f z :=
    (hf z (ball_subset_closedBall hzBall)).differentiableAt
  have hshiftDiff :
      DifferentiableAt ℂ (fun x : ℂ ↦ c + x) w := by
    fun_prop
  have hcomp :=
    logDeriv_comp (f := f) (g := fun x : ℂ ↦ c + x) (x := w)
      (by simpa [w] using hfDiff) hshiftDiff
  have hcw : c + w = z := by
    grind
  rw [deriv_const_add_id, mul_one, hcw] at hcomp
  change ‖logDeriv F w‖ ≤ _ at hlocal
  rw [show F = f ∘ (fun x : ℂ ↦ c + x) by grind, hcomp] at hlocal
  grind

end NumberField.Odlyzko
