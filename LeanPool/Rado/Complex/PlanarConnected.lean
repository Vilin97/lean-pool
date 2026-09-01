/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

/-!
# Planar connectivity for the standard configuration

The fixed configuration used in the main assembly: inside the ball `B(0, 8)`
we remove the two closed unit disks centered at `±4`. The remainder must be
path-connected (this feeds the clopen argument showing `Y = X ∖ (K₀ ∪ K₁)` is
connected, Anghel–Stan proof of Theorem 7, Step 0a of `Rado/PLAN.md`).

Also provided: the annuli `1 ≤ |z ∓ 4| ≤ 2` sit inside `B(0, 8)`, and related
trivial inclusions used when instantiating the configuration in a chart.
-/

open Set Metric Complex

namespace Rado

/-! ### Metric helpers -/

private lemma dist_lt_of_sq_lt {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 < r ^ 2) : dist z w < r := by
  rw [Complex.dist_eq_re_im]
  exact (Real.sqrt_lt' hr).mpr h

private lemma lt_dist_of_sq_lt {z w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : r ^ 2 < (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) : r < dist z w := by
  rw [Complex.dist_eq_re_im]
  exact (Real.lt_sqrt hr).mpr h

private lemma abs_im_sub_le_dist (z w : ℂ) : |z.im - w.im| ≤ dist z w := by
  rw [dist_eq_norm]
  simpa using Complex.abs_im_le_norm (z - w)

private lemma abs_re_sub_le_dist (z w : ℂ) : |z.re - w.re| ≤ dist z w := by
  rw [dist_eq_norm]
  simpa using Complex.abs_re_le_norm (z - w)

private lemma dist_neg_four_four : dist (-4 : ℂ) (4 : ℂ) = 8 := by
  have h : ((-4 : ℂ).re - (4 : ℂ).re) ^ 2 + ((-4 : ℂ).im - (4 : ℂ).im) ^ 2 = 8 ^ 2 := by
    norm_num
  rw [Complex.dist_eq_re_im, h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]

private lemma not_mem_closedBall_of_im {z w : ℂ} (hw : w.im = 0) (h : 1 < |z.im|) :
    z ∉ closedBall w 1 := by
  intro hmem
  rw [mem_closedBall] at hmem
  have h2 := abs_im_sub_le_dist z w
  rw [hw, sub_zero] at h2
  linarith

private lemma not_mem_closedBall_of_re {z w : ℂ} (h : 1 < |z.re - w.re|) :
    z ∉ closedBall w 1 := by
  intro hmem
  rw [mem_closedBall] at hmem
  have h2 := abs_re_sub_le_dist z w
  linarith

/-! ### Path-connectivity of products and annuli -/

private lemma isPathConnected_prod {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {s : Set α} {t : Set β} (hs : IsPathConnected s) (ht : IsPathConnected t) :
    IsPathConnected (s ×ˢ t) := by
  obtain ⟨a, ha, hsj⟩ := hs
  obtain ⟨b, hb, htj⟩ := ht
  refine ⟨(a, b), mem_prod.mpr ⟨ha, hb⟩, ?_⟩
  rintro ⟨x, y⟩ hp
  rw [mem_prod] at hp
  obtain ⟨hx, hy⟩ := hp
  obtain ⟨γ, hγ⟩ := hsj hx
  obtain ⟨δ, hδ⟩ := htj hy
  refine ⟨γ.prod δ, fun τ ↦ ?_⟩
  simp only [Path.prod_coe]
  exact mem_prod.mpr ⟨hγ τ, hδ τ⟩

/-- An open annulus `r < |z - c| < R` (with `0 ≤ r < R`) in `ℂ` is path-connected:
it is the image of `(r, R) × 𝕊¹` under `(s, v) ↦ c + s • v`. -/
private lemma isPathConnected_annulus {c : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    IsPathConnected {z : ℂ | r < dist z c ∧ dist z c < R} := by
  have hsphere : IsPathConnected (sphere (0 : ℂ) 1) :=
    isPathConnected_sphere (by rw [rank_real_complex]; exact Cardinal.one_lt_two) 0 zero_le_one
  have hIoo : IsPathConnected (Ioo r R) :=
    (convex_Ioo r R).isPathConnected (nonempty_Ioo.mpr hrR)
  have himg :=
    (isPathConnected_prod hIoo hsphere).image
      (show Continuous fun p : ℝ × ℂ ↦ c + p.1 • p.2 from
        continuous_const.add (continuous_fst.smul continuous_snd))
  have heq : (fun p : ℝ × ℂ ↦ c + p.1 • p.2) '' (Ioo r R ×ˢ sphere (0 : ℂ) 1)
      = {z : ℂ | r < dist z c ∧ dist z c < R} := by
    ext z
    constructor
    · rintro ⟨⟨s, v⟩, hp, rfl⟩
      rw [mem_prod] at hp
      obtain ⟨hs, hv⟩ := hp
      rw [mem_Ioo] at hs
      rw [mem_sphere_zero_iff_norm] at hv
      have hs0 : 0 < s := lt_of_le_of_lt hr hs.1
      have hd : dist (c + s • v) c = s := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs,
          abs_of_pos hs0]
      change r < dist (c + s • v) c ∧ dist (c + s • v) c < R
      rw [hd]
      exact hs
    · rintro ⟨h1, h2⟩
      have hd0 : 0 < dist z c := lt_of_le_of_lt hr h1
      have hnorm : ‖z - c‖ ≠ 0 := by
        rw [← dist_eq_norm]
        exact ne_of_gt hd0
      refine ⟨(dist z c, ‖z - c‖⁻¹ • (z - c)), mem_prod.mpr ⟨mem_Ioo.mpr ⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
      · change c + dist z c • (‖z - c‖⁻¹ • (z - c)) = z
        rw [dist_eq_norm, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
        ring
  rw [heq] at himg
  exact himg

/-! ### The pieces of the cover and their inclusion in the configuration set -/

private lemma P1_subset :
    ball (0 : ℂ) 8 ∩ {z : ℂ | 1 < z.im}
      ⊆ ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) := by
  rintro z ⟨hb, him⟩
  have him' : (1 : ℝ) < z.im := him
  have habs : (1 : ℝ) < |z.im| := lt_of_lt_of_le him' (le_abs_self _)
  refine ⟨hb, ?_⟩
  rintro (h | h)
  · exact not_mem_closedBall_of_im (by norm_num) habs h
  · exact not_mem_closedBall_of_im (by norm_num) habs h

private lemma P2_subset :
    ball (0 : ℂ) 8 ∩ {z : ℂ | z.im < -1}
      ⊆ ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) := by
  rintro z ⟨hb, him⟩
  have him' : z.im < -1 := him
  have habs : (1 : ℝ) < |z.im| :=
    lt_of_lt_of_le (by linarith : (1 : ℝ) < -z.im) (neg_le_abs _)
  refine ⟨hb, ?_⟩
  rintro (h | h)
  · exact not_mem_closedBall_of_im (by norm_num) habs h
  · exact not_mem_closedBall_of_im (by norm_num) habs h

private lemma P3_subset :
    ball (0 : ℂ) 8 ∩ {z : ℂ | z.re < -5}
      ⊆ ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) := by
  rintro z ⟨hb, hre⟩
  have hre' : z.re < -5 := hre
  refine ⟨hb, ?_⟩
  rintro (h | h)
  · refine not_mem_closedBall_of_re ?_ h
    simp only [Complex.neg_re, Complex.re_ofNat, sub_neg_eq_add]
    linarith [neg_le_abs (z.re + 4)]
  · refine not_mem_closedBall_of_re ?_ h
    simp only [Complex.re_ofNat]
    linarith [neg_le_abs (z.re - 4)]

private lemma P4_subset :
    ball (0 : ℂ) 8 ∩ {z : ℂ | 5 < z.re}
      ⊆ ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) := by
  rintro z ⟨hb, hre⟩
  have hre' : (5 : ℝ) < z.re := hre
  refine ⟨hb, ?_⟩
  rintro (h | h)
  · refine not_mem_closedBall_of_re ?_ h
    simp only [Complex.neg_re, Complex.re_ofNat, sub_neg_eq_add]
    linarith [le_abs_self (z.re + 4)]
  · refine not_mem_closedBall_of_re ?_ h
    simp only [Complex.re_ofNat]
    linarith [le_abs_self (z.re - 4)]

private lemma P5_subset :
    ball (0 : ℂ) 8 ∩ ({z : ℂ | -3 < z.re} ∩ {z : ℂ | z.re < 3})
      ⊆ ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) := by
  rintro z ⟨hb, hre1, hre2⟩
  have hre1' : (-3 : ℝ) < z.re := hre1
  have hre2' : z.re < 3 := hre2
  refine ⟨hb, ?_⟩
  rintro (h | h)
  · refine not_mem_closedBall_of_re ?_ h
    simp only [Complex.neg_re, Complex.re_ofNat, sub_neg_eq_add]
    linarith [le_abs_self (z.re + 4)]
  · refine not_mem_closedBall_of_re ?_ h
    simp only [Complex.re_ofNat]
    linarith [neg_le_abs (z.re - 4)]

private lemma Ap_subset :
    {z : ℂ | 1 < dist z (4 : ℂ) ∧ dist z (4 : ℂ) < 3}
      ⊆ ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) := by
  rintro z ⟨h1, h2⟩
  have h40 : dist (4 : ℂ) 0 = 4 := by
    rw [dist_zero_right]
    norm_num
  have hb : z ∈ ball (0 : ℂ) 8 := by
    rw [mem_ball]
    have ht := dist_triangle z (4 : ℂ) 0
    linarith
  refine ⟨hb, ?_⟩
  rintro (h | h)
  · rw [mem_closedBall] at h
    have ht := dist_triangle (-4 : ℂ) z (4 : ℂ)
    rw [dist_neg_four_four, dist_comm (-4 : ℂ) z] at ht
    linarith
  · rw [mem_closedBall] at h
    linarith

private lemma Am_subset :
    {z : ℂ | 1 < dist z (-4 : ℂ) ∧ dist z (-4 : ℂ) < 3}
      ⊆ ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) := by
  rintro z ⟨h1, h2⟩
  have h40 : dist (-4 : ℂ) 0 = 4 := by
    rw [dist_zero_right, norm_neg]
    norm_num
  have hb : z ∈ ball (0 : ℂ) 8 := by
    rw [mem_ball]
    have ht := dist_triangle z (-4 : ℂ) 0
    linarith
  refine ⟨hb, ?_⟩
  rintro (h | h)
  · rw [mem_closedBall] at h
    linarith
  · rw [mem_closedBall] at h
    have ht := dist_triangle (-4 : ℂ) z (4 : ℂ)
    rw [dist_neg_four_four, dist_comm (-4 : ℂ) z] at ht
    linarith

/-- The standard punctured configuration: a large ball minus two small closed
disks is path-connected. -/
theorem isPathConnected_ball_diff_two_disks :
    IsPathConnected
      (ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1)) := by
  -- ball memberships of the witness points
  have hb0 : (0 : ℂ) ∈ ball (0 : ℂ) 8 := mem_ball_self (by norm_num)
  have hb2I : (2 * I : ℂ) ∈ ball (0 : ℂ) 8 :=
    mem_ball.mpr (dist_lt_of_sq_lt (by norm_num) (by norm_num))
  have hbm2I : (-(2 * I) : ℂ) ∈ ball (0 : ℂ) 8 :=
    mem_ball.mpr (dist_lt_of_sq_lt (by norm_num) (by norm_num))
  have hb42I : (4 + 2 * I : ℂ) ∈ ball (0 : ℂ) 8 :=
    mem_ball.mpr (dist_lt_of_sq_lt (by norm_num) (by norm_num))
  have hbm42I : (-4 + 2 * I : ℂ) ∈ ball (0 : ℂ) 8 :=
    mem_ball.mpr (dist_lt_of_sq_lt (by norm_num) (by norm_num))
  have hb6 : (6 : ℂ) ∈ ball (0 : ℂ) 8 :=
    mem_ball.mpr (dist_lt_of_sq_lt (by norm_num) (by norm_num))
  have hbm6 : (-6 : ℂ) ∈ ball (0 : ℂ) 8 :=
    mem_ball.mpr (dist_lt_of_sq_lt (by norm_num) (by norm_num))
  -- memberships of the witness points in the pieces
  have hm5_2I : (2 * I : ℂ) ∈ ball (0 : ℂ) 8 ∩ ({z : ℂ | -3 < z.re} ∩ {z : ℂ | z.re < 3}) :=
    ⟨hb2I, by norm_num [mem_ofPred_eq], by norm_num [mem_ofPred_eq]⟩
  have hm5_m2I : (-(2 * I) : ℂ) ∈ ball (0 : ℂ) 8 ∩ ({z : ℂ | -3 < z.re} ∩ {z : ℂ | z.re < 3}) :=
    ⟨hbm2I, by norm_num [mem_ofPred_eq], by norm_num [mem_ofPred_eq]⟩
  have hm1_2I : (2 * I : ℂ) ∈ ball (0 : ℂ) 8 ∩ {z : ℂ | 1 < z.im} :=
    ⟨hb2I, by norm_num [mem_ofPred_eq]⟩
  have hm1_42I : (4 + 2 * I : ℂ) ∈ ball (0 : ℂ) 8 ∩ {z : ℂ | 1 < z.im} :=
    ⟨hb42I, by norm_num [mem_ofPred_eq]⟩
  have hm1_m42I : (-4 + 2 * I : ℂ) ∈ ball (0 : ℂ) 8 ∩ {z : ℂ | 1 < z.im} :=
    ⟨hbm42I, by norm_num [mem_ofPred_eq]⟩
  have hm2_m2I : (-(2 * I) : ℂ) ∈ ball (0 : ℂ) 8 ∩ {z : ℂ | z.im < -1} :=
    ⟨hbm2I, by norm_num [mem_ofPred_eq]⟩
  have hm3_m6 : (-6 : ℂ) ∈ ball (0 : ℂ) 8 ∩ {z : ℂ | z.re < -5} :=
    ⟨hbm6, by norm_num [mem_ofPred_eq]⟩
  have hm4_6 : (6 : ℂ) ∈ ball (0 : ℂ) 8 ∩ {z : ℂ | 5 < z.re} :=
    ⟨hb6, by norm_num [mem_ofPred_eq]⟩
  have hmAp_42I : (4 + 2 * I : ℂ) ∈ {z : ℂ | 1 < dist z (4 : ℂ) ∧ dist z (4 : ℂ) < 3} :=
    ⟨lt_dist_of_sq_lt (by norm_num) (by norm_num),
      dist_lt_of_sq_lt (by norm_num) (by norm_num)⟩
  have hmAp_6 : (6 : ℂ) ∈ {z : ℂ | 1 < dist z (4 : ℂ) ∧ dist z (4 : ℂ) < 3} :=
    ⟨lt_dist_of_sq_lt (by norm_num) (by norm_num),
      dist_lt_of_sq_lt (by norm_num) (by norm_num)⟩
  have hmAm_m42I : (-4 + 2 * I : ℂ) ∈ {z : ℂ | 1 < dist z (-4 : ℂ) ∧ dist z (-4 : ℂ) < 3} :=
    ⟨lt_dist_of_sq_lt (by norm_num) (by norm_num),
      dist_lt_of_sq_lt (by norm_num) (by norm_num)⟩
  have hmAm_m6 : (-6 : ℂ) ∈ {z : ℂ | 1 < dist z (-4 : ℂ) ∧ dist z (-4 : ℂ) < 3} :=
    ⟨lt_dist_of_sq_lt (by norm_num) (by norm_num),
      dist_lt_of_sq_lt (by norm_num) (by norm_num)⟩
  -- path-connectivity of the pieces
  have hcP1 : IsPathConnected (ball (0 : ℂ) 8 ∩ {z : ℂ | 1 < z.im}) :=
    ((convex_ball _ _).inter (convex_halfSpace_im_gt 1)).isPathConnected ⟨_, hm1_2I⟩
  have hcP2 : IsPathConnected (ball (0 : ℂ) 8 ∩ {z : ℂ | z.im < -1}) :=
    ((convex_ball _ _).inter (convex_halfSpace_im_lt (-1))).isPathConnected ⟨_, hm2_m2I⟩
  have hcP3 : IsPathConnected (ball (0 : ℂ) 8 ∩ {z : ℂ | z.re < -5}) :=
    ((convex_ball _ _).inter (convex_halfSpace_re_lt (-5))).isPathConnected ⟨_, hm3_m6⟩
  have hcP4 : IsPathConnected (ball (0 : ℂ) 8 ∩ {z : ℂ | 5 < z.re}) :=
    ((convex_ball _ _).inter (convex_halfSpace_re_gt 5)).isPathConnected ⟨_, hm4_6⟩
  have hcP5 : IsPathConnected
      (ball (0 : ℂ) 8 ∩ ({z : ℂ | -3 < z.re} ∩ {z : ℂ | z.re < 3})) :=
    ((convex_ball _ _).inter
      ((convex_halfSpace_re_gt (-3)).inter (convex_halfSpace_re_lt 3))).isPathConnected
      ⟨_, hm5_2I⟩
  have hcAp : IsPathConnected {z : ℂ | 1 < dist z (4 : ℂ) ∧ dist z (4 : ℂ) < 3} :=
    isPathConnected_annulus zero_le_one (by norm_num)
  have hcAm : IsPathConnected {z : ℂ | 1 < dist z (-4 : ℂ) ∧ dist z (-4 : ℂ) < 3} :=
    isPathConnected_annulus zero_le_one (by norm_num)
  -- chain the pieces into a path-connected union
  have h1 := hcP5.union hcP1 ⟨_, hm5_2I, hm1_2I⟩
  have h2 := h1.union hcP2 ⟨_, mem_union_left _ hm5_m2I, hm2_m2I⟩
  have h3 := h2.union hcAp
    ⟨_, mem_union_left _ (mem_union_right _ hm1_42I), hmAp_42I⟩
  have h4 := h3.union hcAm
    ⟨_, mem_union_left _ (mem_union_left _ (mem_union_right _ hm1_m42I)), hmAm_m42I⟩
  have h5 := h4.union hcP4
    ⟨_, mem_union_left _ (mem_union_right _ hmAp_6), hm4_6⟩
  have h6 := h5.union hcP3
    ⟨_, mem_union_left _ (mem_union_right _ hmAm_m6), hm3_m6⟩
  -- the union equals the configuration set
  convert h6 using 1
  apply Subset.antisymm
  · -- coverage: every point of the configuration set lies in one of the pieces
    rintro z ⟨hb, hnot⟩
    rw [mem_union, not_or] at hnot
    obtain ⟨hm', hp'⟩ := hnot
    have hm : 1 < dist z (-4 : ℂ) := not_le.mp fun h ↦ hm' (mem_closedBall.mpr h)
    have hp : 1 < dist z (4 : ℂ) := not_le.mp fun h ↦ hp' (mem_closedBall.mpr h)
    simp only [mem_union]
    rcases lt_or_ge 1 z.im with him | him1
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hb, him⟩)))))
    rcases lt_or_ge z.im (-1) with him | him2
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hb, him⟩))))
    rcases lt_or_ge z.re (-5) with hre | hre1
    · exact Or.inr ⟨hb, hre⟩
    rcases lt_or_ge 5 z.re with hre | hre2
    · exact Or.inl (Or.inr ⟨hb, hre⟩)
    rcases lt_or_ge z.re 3 with hre3 | hre3
    · rcases lt_or_ge (-3) z.re with hre4 | hre4
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hb, hre4, hre3⟩)))))
      · -- z.re ∈ [-5, -3]: the annulus around -4
        refine Or.inl (Or.inl (Or.inr ⟨hm, ?_⟩))
        apply dist_lt_of_sq_lt (by norm_num : (0 : ℝ) < 3)
        simp only [Complex.neg_re, Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat,
          neg_zero, sub_zero, sub_neg_eq_add]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ z.re + 5)
            (by linarith : (0 : ℝ) ≤ -3 - z.re),
          mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.im)
            (by linarith : (0 : ℝ) ≤ 1 + z.im)]
    · -- z.re ∈ [3, 5]: the annulus around 4
      refine Or.inl (Or.inl (Or.inl (Or.inr ⟨hp, ?_⟩)))
      apply dist_lt_of_sq_lt (by norm_num : (0 : ℝ) < 3)
      simp only [Complex.re_ofNat, Complex.im_ofNat, sub_zero]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ z.re - 3)
          (by linarith : (0 : ℝ) ≤ 5 - z.re),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.im)
          (by linarith : (0 : ℝ) ≤ 1 + z.im)]
  · -- every piece lies in the configuration set
    exact union_subset (union_subset (union_subset (union_subset (union_subset
      (union_subset P5_subset P1_subset) P2_subset) Ap_subset) Am_subset) P4_subset)
      P3_subset

/-- Non-crossing: the two closed configuration disks are disjoint. -/
theorem config_disks_disjoint :
    Disjoint (closedBall (-4 : ℂ) 1) (closedBall (4 : ℂ) 1) :=
  closedBall_disjoint_closedBall (by rw [dist_neg_four_four]; norm_num)

/-- The closed annuli of outer radius 2 around `±4` lie in `B(0, 8)` and stay
disjoint from each other. -/
theorem config_annuli_subset :
    closedBall (-4 : ℂ) 2 ∪ closedBall (4 : ℂ) 2 ⊆ ball (0 : ℂ) 8 := by
  have h4 : dist (4 : ℂ) 0 = 4 := by
    rw [dist_zero_right]
    norm_num
  have hm4 : dist (-4 : ℂ) 0 = 4 := by
    rw [dist_zero_right, norm_neg]
    norm_num
  rintro z (hz | hz)
  · rw [mem_closedBall] at hz
    rw [mem_ball]
    have ht := dist_triangle z (-4 : ℂ) 0
    linarith
  · rw [mem_closedBall] at hz
    rw [mem_ball]
    have ht := dist_triangle z (4 : ℂ) 0
    linarith

theorem config_annuli_disjoint :
    Disjoint (closedBall (-4 : ℂ) 2) (closedBall (4 : ℂ) 2) :=
  closedBall_disjoint_closedBall (by rw [dist_neg_four_four]; norm_num)

end Rado
