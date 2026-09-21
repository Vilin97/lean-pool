/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.AttachmentMap

/-!
# The flat cutoff used in the protected extension

This module formalizes the scalar cutoff from the last part of
`lem:protected-extension`.  It is independent of the still-missing
Lipschitz-free-space construction.
-/

namespace ScottishBook155

open ENNReal WithLp

/-- The cutoff which is zero through `L`, affine between `L` and `H`, and one
from `H` onward. -/
noncomputable def flatCutoff (L H s : ℝ) : ℝ :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one ((s - L) / (H - L)) : ℝ)

theorem flatCutoff_of_le {L H s : ℝ} (hLH : L < H) (hs : s ≤ L) :
    flatCutoff L H s = 0 := by
  rw [flatCutoff, Set.projIcc_of_le_left]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_nonneg.mpr hLH.le)

theorem flatCutoff_of_ge {L H s : ℝ} (hLH : L < H) (hs : H ≤ s) :
    flatCutoff L H s = 1 := by
  rw [flatCutoff, Set.projIcc_of_right_le]
  apply (le_div_iff₀ (sub_pos.mpr hLH)).2
  linarith

theorem flatCutoff_mem_Icc (L H s : ℝ) : flatCutoff L H s ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one ((s - L) / (H - L))).property

/-- The exact Lipschitz estimate used for the flat retraction. -/
theorem flatCutoff_abs_sub_le {L H : ℝ} (hLH : L < H) (s t : ℝ) :
    |flatCutoff L H s - flatCutoff L H t| ≤
      (1 / (H - L)) * |s - t| := by
  calc
    |flatCutoff L H s - flatCutoff L H t| ≤
        |(s - L) / (H - L) - (t - L) / (H - L)| := by
      simpa [flatCutoff] using
        (Set.abs_projIcc_sub_projIcc
          (a := (0 : ℝ)) (b := 1)
          (c := (s - L) / (H - L)) (d := (t - L) / (H - L)) zero_le_one)
    _ = |s - t| / (H - L) := by
      rw [div_sub_div_same, abs_div, abs_of_pos (sub_pos.mpr hLH)]
      congr 2
      ring
    _ = (1 / (H - L)) * |s - t| := by ring

/-- The nonlinear map into the old target which becomes flat on all source
coordinates at most `L`. -/
noncomputable def sourceRetraction
    {M N : Type*} [AddCommGroup N] [Module ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ) (m : M) (s : ℝ) : N :=
  V m + flatCutoff L H s • (y - V a)

theorem sourceRetraction_of_le
    {M N : Type*} [AddCommGroup N] [Module ℝ N]
    {V : M → N} {a m : M} {y : N} {L H s : ℝ}
    (hLH : L < H) (hs : s ≤ L) :
    sourceRetraction V a y L H m s = V m := by
  simp [sourceRetraction, flatCutoff_of_le hLH hs]

/-- The norm estimate proving that the source retraction is nonexpansive for
the sum norm, provided the attachment gap is at most `H - L`. -/
theorem sourceRetraction_norm_sub_le
    {M N : Type*} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H)
    (hV : ∀ m n, ‖V m - V n‖ ≤ ‖m - n‖)
    (hgap : ‖y - V a‖ ≤ H - L)
    (m n : M) (s t : ℝ) :
    ‖sourceRetraction V a y L H m s - sourceRetraction V a y L H n t‖ ≤
      ‖m - n‖ + |s - t| := by
  let cs := flatCutoff L H s
  let ct := flatCutoff L H t
  have hcut : |cs - ct| ≤ (1 / (H - L)) * |s - t| :=
    flatCutoff_abs_sub_le hLH s t
  have hdenom : 0 < H - L := sub_pos.mpr hLH
  calc
    ‖sourceRetraction V a y L H m s - sourceRetraction V a y L H n t‖ =
        ‖(V m - V n) + (cs - ct) • (y - V a)‖ := by
      change ‖(V m + cs • (y - V a)) - (V n + ct • (y - V a))‖ = _
      congr 1
      calc
        (V m + cs • (y - V a)) - (V n + ct • (y - V a)) =
            (V m - V n) + (cs • (y - V a) - ct • (y - V a)) := by abel
        _ = (V m - V n) + (cs - ct) • (y - V a) := by rw [sub_smul]
    _ ≤ ‖V m - V n‖ + ‖(cs - ct) • (y - V a)‖ := norm_add_le _ _
    _ = ‖V m - V n‖ + |cs - ct| * ‖y - V a‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖m - n‖ + |cs - ct| * ‖y - V a‖ := by
      exact add_le_add (hV m n) le_rfl
    _ ≤ ‖m - n‖ + ((1 / (H - L)) * |s - t|) * ‖y - V a‖ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcut (norm_nonneg _))
    _ ≤ ‖m - n‖ + ((1 / (H - L)) * |s - t|) * (H - L) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hgap
          (mul_nonneg (one_div_nonneg.mpr hdenom.le) (abs_nonneg _)))
    _ = ‖m - n‖ + |s - t| * ((1 / (H - L)) * (H - L)) := by ring
    _ = ‖m - n‖ + |s - t| := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hdenom), mul_one]

theorem sourceRetraction_hits_attachment
    {M N : Type*} [AddCommGroup N] [Module ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ} (hLH : L < H) :
    sourceRetraction V a y L H a H = y := by
  simp [sourceRetraction, flatCutoff_of_ge hLH le_rfl]

theorem sourceRetraction_base
    {M N : Type*} [AddCommGroup N] [Module ℝ N]
    {V : M → N} {a m : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hL : 0 ≤ L) :
    sourceRetraction V a y L H m 0 = V m :=
  sourceRetraction_of_le hLH hL

/-- The source retraction agrees with the prescribed attachment map on the
whole attachment set. -/
theorem sourceRetraction_attachment
    {M N : Type*} [AddCommGroup N] [Module ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hL : 0 ≤ L) (p : M ⊕ Unit) :
    sourceRetraction V a y L H (attachmentPoint a H p).fst
      (attachmentPoint a H p).snd = attachmentMap V y p := by
  cases p with
  | inl m => simpa [attachmentPoint, attachmentMap] using
      sourceRetraction_base (V := V) (a := a) (m := m) (y := y) hLH hL
  | inr star => simpa [attachmentPoint, attachmentMap] using
      sourceRetraction_hits_attachment (V := V) (a := a) (y := y) hLH

/-- Metric form of the source-retraction estimate on the sum-norm source. -/
theorem sourceRetraction_dist_le
    {M N : Type*} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x z : OneSum M) :
    dist (sourceRetraction V a y L H x.fst x.snd)
      (sourceRetraction V a y L H z.fst z.snd) ≤ dist x z := by
  have hdist : dist x z = dist x.fst z.fst + |x.snd - z.snd| := by
    rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
    simp [Real.dist_eq]
  rw [dist_eq_norm, hdist, dist_eq_norm]
  apply sourceRetraction_norm_sub_le hLH
  · intro m n
    simpa [dist_eq_norm] using hV m n
  · simpa [dist_eq_norm] using hgap

end ScottishBook155
