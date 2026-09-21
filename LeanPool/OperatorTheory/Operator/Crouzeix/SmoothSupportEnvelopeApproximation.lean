/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Quantitative approximation by smooth support envelopes

For a nonempty finite point set, the rounded log-sum-exp support envelope is
not only an outer neighborhood of its convex hull: it lies in the closed
metric thickening whose radius is the uniform log-sum-exp overshoot.  The
proof uses the nearest-point characterization for closed convex sets and the
direction of the displacement from a nearest point.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Complex Metric Set
open scoped InnerProductSpace

/-- Looking in the direction of a nonzero displacement recovers its norm. -/
theorem polytopeDirectionalValue_sub_at_arg
    {z w : ℂ} (hzw : z ≠ w) :
    polytopeDirectionalValue z (z - w).arg -
        polytopeDirectionalValue w (z - w).arg = ‖z - w‖ := by
  have hsub : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hnorm : ‖z - w‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
  unfold polytopeDirectionalValue
  rw [Complex.cos_arg hsub, Complex.sin_arg]
  field_simp [hnorm]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- The real inner product with a displacement is its norm times the
directional-value difference in the displacement direction. -/
theorem real_inner_eq_norm_mul_polytopeDirectionalValue_sub_at_arg
    (z v w : ℂ) :
    ⟪z - v, w - v⟫_ℝ =
      ‖z - v‖ *
        (polytopeDirectionalValue w (z - v).arg -
          polytopeDirectionalValue v (z - v).arg) := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  have hcos : ‖z - v‖ * Real.cos (z - v).arg = z.re - v.re := by
    simpa only [Complex.sub_re] using Complex.norm_mul_cos_arg (z - v)
  have hsin : ‖z - v‖ * Real.sin (z - v).arg = z.im - v.im := by
    simpa only [Complex.sub_im] using Complex.norm_mul_sin_arg (z - v)
  rw [← hcos, ← hsin]
  unfold polytopeDirectionalValue
  ring

/-- The rounded support envelope lies in the closed thickening of the finite
convex hull by the exact uniform support overshoot. -/
theorem smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho) ⊆
      Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ)) := by
  let P : Set ℂ := convexHull ℝ (u : Set ℂ)
  let R : ℝ := delta * Real.log (u.card : ℝ) + rho
  have hPcompact : IsCompact P := by
    exact u.finite_toSet.isCompact_convexHull ℝ
  have hPnonempty : P.Nonempty := by
    obtain ⟨a, ha⟩ := hu
    exact ⟨a, (subset_convexHull ℝ (u : Set ℂ)) ha⟩
  have hPconvex : Convex ℝ P := convex_convexHull ℝ _
  have hcard : (1 : ℝ) ≤ (u.card : ℝ) := by
    exact_mod_cast hu.card_pos
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg (mul_nonneg hdelta.le (Real.log_nonneg hcard)) hrho
  intro z hz
  obtain ⟨v, hvP, hvmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hPnonempty
      hPcompact.isComplete hPconvex z
  have hprojection : ∀ w ∈ P, ⟪z - v, w - v⟫_ℝ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hPconvex hvP).mp hvmin
  have hzR : dist z v ≤ R := by
    by_cases hzv : z = v
    · subst z
      simpa only [dist_self] using hR
    · let theta : ℝ := (z - v).arg
      have hdir (w : ℂ) (hw : w ∈ P) :
          polytopeDirectionalValue w theta ≤
            polytopeDirectionalValue v theta := by
        have hinner := hprojection w hw
        rw [real_inner_eq_norm_mul_polytopeDirectionalValue_sub_at_arg]
          at hinner
        apply sub_nonpos.mp
        dsimp only [theta]
        exact nonpos_of_mul_nonpos_right hinner
          (norm_pos_iff.mpr (sub_ne_zero.mpr hzv))
      have hsoft : polytopeSoftSupport u delta theta ≤
          polytopeDirectionalValue v theta +
            delta * Real.log (u.card : ℝ) := by
        apply polytopeSoftSupport_le_of_forall_directionalValue_le
          hu hdelta
        intro w hw
        exact hdir w ((subset_convexHull ℝ (u : Set ℂ)) hw)
      have hzenvelope : polytopeDirectionalValue z theta ≤
          polytopeRoundedSupport u delta rho theta := by
        exact hz theta
      have hnorm : ‖z - v‖ ≤ R := by
        rw [← polytopeDirectionalValue_sub_at_arg hzv]
        unfold polytopeRoundedSupport at hzenvelope
        dsimp only [R]
        linarith
      simpa only [dist_eq_norm] using hnorm
  rw [hPcompact.cthickening_eq_biUnion_closedBall hR]
  exact mem_biUnion hvP hzR

/-- The rounded support envelope of a nonempty finite point set is compact. -/
theorem isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    IsCompact
      (smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho)) := by
  have htarget : IsCompact
      (Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ))) :=
    (u.finite_toSet.isCompact_convexHull ℝ).cthickening
  exact htarget.of_isClosed_subset
    (isClosed_smoothSupportClosedEnvelope _)
    (smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
      hu hdelta hrho)

/-- The open rounded-support carrier is bounded. -/
theorem isBounded_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    Bornology.IsBounded
      (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by
  exact
    (isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport
      hu hdelta hrho).isBounded.subset interior_subset

/-- Positive rounding makes the open support envelope nonempty. -/
theorem nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (smoothSupportOpenEnvelope
      (polytopeRoundedSupport u delta rho)).Nonempty := by
  obtain ⟨z, hz⟩ := hu
  exact ⟨z,
    convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hdelta hrho ((subset_convexHull ℝ (u : Set ℂ)) hz)⟩

/-- For positive rounding, the closed support envelope is exactly the closure
of its open carrier. -/
theorem closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    closure
        (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho)) =
      smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho) := by
  have hnonempty :
      (interior (smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho))).Nonempty := by
    exact nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hu hdelta hrho
  unfold smoothSupportOpenEnvelope
  calc
    closure (interior (smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho))) =
        closure (smoothSupportClosedEnvelope
          (polytopeRoundedSupport u delta rho)) :=
      Convex.closure_interior_eq_closure_of_nonempty_interior
        (convex_smoothSupportClosedEnvelope _) hnonempty
    _ = smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho) :=
      (isClosed_smoothSupportClosedEnvelope _).closure_eq

/-- The closure of the open rounded-support carrier obeys the same explicit
outer thickening bound. -/
theorem closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    closure
        (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho)) ⊆
      Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ)) := by
  rw [closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
    hu hdelta hrho]
  exact
    smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
      hu hdelta hrho.le

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
