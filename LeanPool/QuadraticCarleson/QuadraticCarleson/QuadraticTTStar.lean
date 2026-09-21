/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Mathlib.Analysis.Real.Pi.Bounds
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticL2Decay

/-!
# Uniform quadratic correlation estimates

This file proves the direct quadratic cancellation estimates and the two-region
whole-line kernel majorant (6.7) in the `c = 2` specialization of Lemma 6.2 of
arXiv:2412.15766, for smooth amplitudes on same-sign annular overlaps. Both
comparable and separated scales are included. The final theorems use the
paper's exact `2π` exponential normalization and give an explicit dyadic
decay specialization. The maximal L² operator estimate still requires the
linearization, `TT*` representation, and maximal-function argument.
-/

open MeasureTheory Set
open scoped Interval

namespace QuadraticCarleson

/-- The angular form of the exact quadratic correlation integral. -/
noncomputable def angularQuadraticCorrelation
    (lam μ x y l r : ℝ) (p : ℝ → ℂ) : ℂ :=
  ∫ t in l..r, p t * quadraticExponential (lam - μ)
    (2 * (μ * y - lam * x)) (lam * x ^ 2 - μ * y ^ 2) t

theorem angularQuadraticCorrelation_norm_le_nonstationary
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {δ P Q : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hslope : ∀ t ∈ Icc l r, δ ≤ |quadraticTTStarSlope lam μ x y t|)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ Q) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤
      2 * P / δ + (r - l) * (Q / δ + P * (2 * |lam - μ|) / δ ^ 2) := by
  have h := norm_integral_quadraticExponential_mul_le
    (lam - μ) (2 * (μ * y - lam * x)) (lam * x ^ 2 - μ * y ^ 2)
    l r hlr hp hp' hδ hP hQ (fun t ht ↦ ?_) hbound hbound'
  · simpa only [angularQuadraticCorrelation, abs_mul,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using h
  convert hslope t ht using 2
  unfold quadraticTTStarSlope
  ring

theorem angularQuadraticCorrelation_norm_le_split
    {lam μ : ℝ} (hmod : lam ≠ μ) (x y l r : ℝ) (hlr : l ≤ r) {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {δ P Q : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ Q) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤
      P * (δ / |lam - μ|) + 4 * P / δ +
        (r - l) * (Q / δ + P * (2 * |lam - μ|) / δ ^ 2) := by
  simpa only [angularQuadraticCorrelation, abs_mul,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using
      norm_integral_quadraticExponential_mul_le_split (sub_ne_zero.mpr hmod)
        (2 * (μ * y - lam * x)) (lam * x ^ 2 - μ * y ^ 2)
        l r hlr hp hp' hδ hP hQ hbound hbound'

/-- A monotone-slope estimate on a normalized interval.  The curvature bound
is precisely the one supplied by nearly equal modulations. -/
theorem angularQuadraticCorrelation_norm_le_four_div
    (lam μ x y l r : ℝ) (hlr : l ≤ r) (hlen : r - l ≤ 1)
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hslope : ∀ t ∈ Icc l r, δ ≤ |quadraticTTStarSlope lam μ x y t|)
    (hcurvature : 2 * |lam - μ| ≤ δ)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤ 4 * P / δ := by
  have h := angularQuadraticCorrelation_norm_le_nonstationary lam μ x y l r hlr
    hp hp' hδ hP hP hslope hbound hbound'
  have hc : P * (2 * |lam - μ|) / δ ^ 2 ≤ P / δ := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hδ) hδ]
    have hh := mul_le_mul_of_nonneg_left hcurvature (mul_nonneg hP hδ.le)
    nlinarith
  calc
    _ ≤ 2 * P / δ + (r - l) *
        (P / δ + P * (2 * |lam - μ|) / δ ^ 2) := h
    _ ≤ 2 * P / δ + 1 * (P / δ + P / δ) := by
      gcongr
    _ = _ := by ring

/-- On the unit scale, the large modulation-difference case has genuine
power decay. The threshold in the exceptional interval is `H * u²`; the
condition `1 ≤ H * u⁵` makes all three integration-by-parts errors small.
This deliberately uses only the weaker cancellation estimate already proved
above, so no van der Corput theorem is needed. -/
theorem angularQuadraticCorrelation_norm_le_separated_modulations
    (lam μ x y l r : ℝ) (hlr : l ≤ r) (hlen : r - l ≤ 1)
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {H u B P : ℝ} (hH : 0 < H) (hu : 0 < u) (hu1 : u ≤ 1)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hdecay : 1 ≤ H * u ^ 5)
    (hlower : H * u / 2 ≤ |lam - μ|)
    (hupper : |lam - μ| ≤ B * H)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤ (7 + 2 * B) * P * u := by
  have ha : 0 < |lam - μ| := (by positivity : 0 < H * u / 2).trans_le hlower
  have hmod : lam ≠ μ := sub_ne_zero.mp (abs_pos.mp ha)
  have hδ : 0 < H * u ^ 2 := by positivity
  have hu53 : u ^ 5 ≤ u ^ 3 := pow_le_pow_of_le_one hu.le hu1 (by omega)
  have hdecay3 : 1 ≤ H * u ^ 3 :=
    hdecay.trans (mul_le_mul_of_nonneg_left hu53 hH.le)
  have hi : 1 / (H * u ^ 2) ≤ u := by
    rw [div_le_iff₀ hδ]
    nlinarith [hdecay3]
  have hi4 : 1 / (H * u ^ 4) ≤ u := by
    rw [div_le_iff₀ (by positivity : 0 < H * u ^ 4)]
    nlinarith [hdecay]
  have hexceptional : (H * u ^ 2) / |lam - μ| ≤ 2 * u := by
    rw [div_le_iff₀ ha]
    have hh := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ 2 * u)
    nlinarith
  have hcurvature : (2 * |lam - μ|) / (H * u ^ 2) ^ 2 ≤ 2 * B * u := by
    calc
      _ ≤ (2 * (B * H)) / (H * u ^ 2) ^ 2 := by gcongr
      _ = (2 * B) * (1 / (H * u ^ 4)) := by field_simp
      _ ≤ (2 * B) * u := mul_le_mul_of_nonneg_left hi4 (by positivity)
  have h := angularQuadraticCorrelation_norm_le_split hmod x y l r hlr hp hp'
    hδ hP hP hbound hbound'
  calc
    _ ≤ P * ((H * u ^ 2) / |lam - μ|) + 4 * P / (H * u ^ 2) +
        (r - l) * (P / (H * u ^ 2) +
          P * (2 * |lam - μ|) / (H * u ^ 2) ^ 2) := h
    _ = P * ((H * u ^ 2) / |lam - μ|) + (4 * P) * (1 / (H * u ^ 2)) +
        (r - l) * (P * (1 / (H * u ^ 2)) +
          P * ((2 * |lam - μ|) / (H * u ^ 2) ^ 2)) := by ring
    _ ≤ P * (2 * u) + (4 * P) * u +
        1 * (P * u + P * (2 * B * u)) := by
      gcongr
    _ = _ := by ring

/-- Uniform off-diagonal correlation decay at a normalized spatial scale.

This combines the two cases of the proof of Lemma 6.2 for the quadratic
phase. `H` measures the oscillatory height, `u` the excluded spatial
neighborhood, and `B` the permitted comparison of the two modulation
parameters. Taking `u = H^(-1/5)` gives a positive power of decay. The
amplitude and its derivative have the same bound after normalization. -/
theorem angularQuadraticCorrelation_norm_le_off_diagonal
    (lam μ x y l r : ℝ) (hlr : l ≤ r) (hlen : r - l ≤ 1)
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {H u B P : ℝ} (hH : 0 < H) (hu : 0 < u) (hu1 : u ≤ 1)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hdecay : 1 ≤ H * u ^ 5)
    (hlam : H ≤ lam) (hupper : |lam - μ| ≤ B * H)
    (hseparation : u ≤ |y - x|)
    (hsupport : ∀ t ∈ Icc l r, |t - y| ≤ 1)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤ (7 + 2 * B) * P * u := by
  by_cases hclose : |lam - μ| ≤ lam * |y - x| / 2
  · have hlampos : 0 < lam := hH.trans_le hlam
    have hdpos : 0 < |y - x| := hu.trans_le hseparation
    have hδ : 0 < lam * |y - x| := mul_pos hlampos hdpos
    have hslope (t : ℝ) (ht : t ∈ Icc l r) :
        lam * |y - x| ≤ |quadraticTTStarSlope lam μ x y t| :=
      quadraticTTStarSlope_lower_bound_near_modulations hlampos.le (hsupport t ht)
        (by simpa only [mul_one] using hclose)
    have h := angularQuadraticCorrelation_norm_le_four_div lam μ x y l r hlr hlen
      hp hp' hδ hP hslope (by linarith) hbound hbound'
    have hu52 : u ^ 5 ≤ u ^ 2 := pow_le_pow_of_le_one hu.le hu1 (by omega)
    have hdecay2 : 1 ≤ H * u ^ 2 :=
      hdecay.trans (mul_le_mul_of_nonneg_left hu52 hH.le)
    have hproduct : H * u ≤ lam * |y - x| :=
      mul_le_mul hlam hseparation hu.le hlampos.le
    have hinv : 1 / (lam * |y - x|) ≤ u := by
      rw [div_le_iff₀ hδ]
      have hh := mul_le_mul_of_nonneg_left hproduct hu.le
      nlinarith [hdecay2]
    calc
      _ ≤ 4 * P / (lam * |y - x|) := h
      _ = (4 * P) * (1 / (lam * |y - x|)) := by ring
      _ ≤ (4 * P) * u := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ (7 + 2 * B) * P * u := by gcongr; linarith
  · apply angularQuadraticCorrelation_norm_le_separated_modulations lam μ x y l r
      hlr hlen hp hp' hH hu hu1 hB hP hdecay _ hupper hbound hbound'
    have hproduct : H * u ≤ lam * |y - x| :=
      mul_le_mul hlam hseparation hu.le (hH.trans_le hlam).le
    linarith

/-- Exact change of scale for the quadratic correlation. -/
theorem angularQuadraticCorrelation_scale
    (lam μ x y l r R : ℝ) (hR : R ≠ 0) (p : ℝ → ℂ) :
    R • angularQuadraticCorrelation (lam * R ^ 2) (μ * R ^ 2)
      (x / R) (y / R) (l / R) (r / R) (fun t ↦ p (R * t)) =
      angularQuadraticCorrelation lam μ x y l r p := by
  have hphase (t : ℝ) :
      quadraticExponential (lam * R ^ 2 - μ * R ^ 2)
        (2 * (μ * R ^ 2 * (y / R) - lam * R ^ 2 * (x / R)))
        (lam * R ^ 2 * (x / R) ^ 2 - μ * R ^ 2 * (y / R) ^ 2) t =
      quadraticExponential (lam - μ) (2 * (μ * y - lam * x))
        (lam * x ^ 2 - μ * y ^ 2) (R * t) := by
    unfold quadraticExponential
    apply congrArg (fun v : ℝ ↦ Complex.exp ((v : ℂ) * Complex.I))
    field_simp
  unfold angularQuadraticCorrelation
  simp_rw [hphase]
  rw [intervalIntegral.smul_integral_comp_mul_left
    (fun t ↦ p t * quadraticExponential (lam - μ) (2 * (μ * y - lam * x))
      (lam * x ^ 2 - μ * y ^ 2) t)]
  simp only [mul_div_cancel₀ _ hR]

/-- The off-diagonal correlation estimate at every positive spatial scale.
The hypotheses are invariant under dilation, as required by the maximal
fixed-height argument. -/
theorem angularQuadraticCorrelation_norm_le_off_diagonal_scaled
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {R : ℝ} (hR : 0 < R)
    (hlen : r - l ≤ R) {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {H u B P : ℝ} (hH : 0 < H) (hu : 0 < u) (hu1 : u ≤ 1)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hdecay : 1 ≤ H * u ^ 5)
    (hlam : H ≤ lam * R ^ 2) (hupper : |lam - μ| * R ^ 2 ≤ B * H)
    (hseparation : u * R ≤ |y - x|)
    (hsupport : ∀ t ∈ Icc l r, |t - y| ≤ R)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P / R) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤ (7 + 2 * B) * P * R * u := by
  let q : ℝ → ℂ := fun t ↦ p (R * t)
  let q' : ℝ → ℂ := fun t ↦ R • p' (R * t)
  have hmap (t : ℝ) (ht : t ∈ Icc (l / R) (r / R)) : R * t ∈ Icc l r := by
    constructor
    · have hh := (div_le_iff₀ hR).mp ht.1
      simpa only [mul_comm] using hh
    · have hh := (le_div_iff₀ hR).mp ht.2
      simpa only [mul_comm] using hh
  have hq (t : ℝ) (ht : t ∈ Icc (l / R) (r / R)) : HasDerivAt q (q' t) t := by
    have hd : HasDerivAt (fun t : ℝ ↦ R * t) R t := by
      simpa using (hasDerivAt_id t).const_mul R
    exact (hp (R * t) (hmap t ht)).scomp t hd
  have hq' : ContinuousOn q' (Icc (l / R) (r / R)) := by
    exact (hp'.comp (continuous_const.mul continuous_id).continuousOn hmap).const_smul R
  have hqbound (t : ℝ) (ht : t ∈ Icc (l / R) (r / R)) : ‖q t‖ ≤ P :=
    hbound (R * t) (hmap t ht)
  have hqbound' (t : ℝ) (ht : t ∈ Icc (l / R) (r / R)) : ‖q' t‖ ≤ P := by
    change ‖R • p' (R * t)‖ ≤ P
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    calc
      _ ≤ R * (P / R) := mul_le_mul_of_nonneg_left (hbound' _ (hmap t ht)) hR.le
      _ = P := mul_div_cancel₀ P hR.ne'
  have h := angularQuadraticCorrelation_norm_le_off_diagonal
    (lam * R ^ 2) (μ * R ^ 2) (x / R) (y / R) (l / R) (r / R)
    (div_le_div_of_nonneg_right hlr hR.le) (by
      rw [← sub_div, div_le_one hR]
      exact hlen) hq hq' hH hu hu1 hB hP hdecay hlam (by
        rw [← sub_mul, abs_mul, abs_of_nonneg (sq_nonneg R)]
        exact hupper) (by
          rw [← sub_div, abs_div, abs_of_pos hR, le_div_iff₀ hR]
          exact hseparation) (fun t ht ↦ ?_) hqbound hqbound'
  · rw [← angularQuadraticCorrelation_scale lam μ x y l r R hR.ne' p,
      norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    calc
      _ ≤ R * ((7 + 2 * B) * P * u) := mul_le_mul_of_nonneg_left h hR.le
      _ = _ := by ring
  have hh := hsupport (R * t) (hmap t ht)
  have hid : t - y / R = (R * t - y) / R := by field_simp
  rw [hid, abs_div, abs_of_pos hR, div_le_one hR]
  exact hh

/-- Integration by parts with amplitude and curvature measured at scale `R`.
This form also handles widely separated spatial scales. -/
theorem angularQuadraticCorrelation_norm_le_nonstationary_scaled
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {R : ℝ} (hR : 0 < R)
    (hlen : r - l ≤ R) {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {δ P B : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (_hB : 0 ≤ B)
    (hslope : ∀ t ∈ Icc l r, δ ≤ |quadraticTTStarSlope lam μ x y t|)
    (hcurvature : 2 * |lam - μ| * R ≤ B * δ)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P / R) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤ (3 + B) * P / δ := by
  have h := angularQuadraticCorrelation_norm_le_nonstationary lam μ x y l r hlr
    hp hp' hδ hP (div_nonneg hP hR.le) hslope hbound hbound'
  have herror : R * (P * (2 * |lam - μ|) / δ ^ 2) ≤ B * P / δ := by
    calc
      _ = P * (2 * |lam - μ| * R) / δ ^ 2 := by ring
      _ ≤ P * (B * δ) / δ ^ 2 := by gcongr
      _ = _ := by field_simp
  calc
    _ ≤ 2 * P / δ + (r - l) * (P / R / δ + P * (2 * |lam - μ|) / δ ^ 2) := h
    _ ≤ 2 * P / δ + R * (P / R / δ + P * (2 * |lam - μ|) / δ ^ 2) := by
      gcongr
    _ = 2 * P / δ + P / δ + R * (P * (2 * |lam - μ|) / δ ^ 2) := by
      field_simp
      ring
    _ ≤ 2 * P / δ + P / δ + B * P / δ := add_le_add_right herror _
    _ = _ := by ring

/-- At separated spatial scales the quadratic slope cannot vanish on the
overlap of the two annuli. This is the first case in the proof of (6.7). -/
theorem quadraticTTStarSlope_lower_bound_separated_scales
    {lam μ x y t R S H : ℝ} (hR : 0 < R) (hS : 0 < S) (hH : 0 < H)
    (hμ : 0 ≤ μ) (hscales : 32 * R ≤ S)
    (hlam : H ≤ lam * R ^ 2) (hmuheight : μ * S ^ 2 ≤ 4 * H)
    (hx : R / 4 ≤ |t - x|) (hy : |t - y| ≤ S) :
    H / (4 * R) ≤ |quadraticTTStarSlope lam μ x y t| := by
  have hlampos : 0 < lam := by
    have : 0 < lam * R ^ 2 := hH.trans_le hlam
    exact ((mul_pos_iff.mp this).resolve_right (by
      rintro ⟨_, hneg⟩
      exact (sq_nonneg R).not_gt hneg)).1
  have hfirst : H / (4 * R) ≤ lam * |t - x| := by
    calc
      _ ≤ lam * (R / 4) := by
        rw [div_le_iff₀ (by positivity : 0 < 4 * R)]
        nlinarith [hlam]
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hlampos.le
  have hsecond : μ * |t - y| ≤ H / (8 * R) := by
    calc
      _ ≤ μ * S := mul_le_mul_of_nonneg_left hy hμ
      _ ≤ H / (8 * R) := by
        rw [le_div_iff₀ (by positivity : 0 < 8 * R)]
        have hh := mul_le_mul_of_nonneg_left hscales (mul_nonneg hμ hS.le)
        nlinarith [hmuheight]
  have hid : quadraticTTStarSlope lam μ x y t =
      2 * (lam * (t - x) - μ * (t - y)) := by
    unfold quadraticTTStarSlope
    ring
  have htriangle := abs_add_le (lam * (t - x) - μ * (t - y)) (μ * (t - y))
  rw [sub_add_cancel, abs_mul, abs_of_pos hlampos,
    abs_mul, abs_of_nonneg hμ] at htriangle
  rw [hid, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hid' : H / (4 * R) = 2 * (H / (8 * R)) := by ring
  linarith

/-- Power cancellation for widely separated annular scales at the same
oscillatory height. The resulting factor `1 / H` is stronger than the
comparable-scale estimate. -/
theorem angularQuadraticCorrelation_norm_le_separated_scales
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {R S H : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hH : 0 < H)
    (hlen : r - l ≤ R) (hμ : 0 ≤ μ) (hscales : 32 * R ≤ S)
    (hlam : H ≤ lam * R ^ 2) (hlamupper : lam * R ^ 2 ≤ 4 * H)
    (hmuheight : μ * S ^ 2 ≤ 4 * H)
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {P : ℝ} (hP : 0 ≤ P)
    (hx : ∀ t ∈ Icc l r, R / 4 ≤ |t - x|)
    (hy : ∀ t ∈ Icc l r, |t - y| ≤ S)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P / R) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤ 268 * P * R / H := by
  have hlampos : 0 < lam := by
    have : 0 < lam * R ^ 2 := hH.trans_le hlam
    exact ((mul_pos_iff.mp this).resolve_right (by
      rintro ⟨_, hneg⟩
      exact (sq_nonneg R).not_gt hneg)).1
  have hRS : R ≤ S := by linarith
  have hμsmall : μ * R ^ 2 ≤ 4 * H :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRS 2) hμ).trans hmuheight
  have habs : |lam - μ| ≤ lam + μ := by
    rw [abs_le]
    constructor <;> linarith
  have hcurvature : 2 * |lam - μ| * R ≤ 64 * (H / (4 * R)) := by
    have hh := mul_le_mul_of_nonneg_right habs (sq_nonneg R)
    have habsheight : |lam - μ| * R ^ 2 ≤ 8 * H := by nlinarith
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 4 * R)]
    nlinarith [habsheight]
  have h := angularQuadraticCorrelation_norm_le_nonstationary_scaled
    lam μ x y l r hlr hR hlen hp hp' (by positivity : 0 < H / (4 * R))
    hP (by norm_num : (0 : ℝ) ≤ 64)
    (fun t ht ↦ quadraticTTStarSlope_lower_bound_separated_scales
      hR hS hH hμ hscales hlam hmuheight (hx t ht) (hy t ht))
    hcurvature hbound hbound'
  convert h using 1
  field_simp
  ring

/-- Uniform off-diagonal fixed-height decay, including both comparable and
widely separated spatial scales. The smaller radius is `R`, the larger is
`S`; the height and smoothness assumptions are those of the annular `TT*`
amplitude. -/
theorem angularQuadraticCorrelation_norm_le_fixed_height_off_diagonal
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {R S H u : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hH : 0 < H)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hlen : r - l ≤ R) (hμ : 0 ≤ μ) (hscales : R ≤ S)
    (hlam : H ≤ lam * R ^ 2) (hlamupper : lam * R ^ 2 ≤ 4 * H)
    (hmuheight : μ * S ^ 2 ≤ 4 * H) (hseparation : u * S ≤ |y - x|)
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {P : ℝ} (hP : 0 ≤ P)
    (hx : ∀ t ∈ Icc l r, R / 4 ≤ |t - x|)
    (hy : ∀ t ∈ Icc l r, |t - y| ≤ S)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P / R) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤ 8403968 * P * R * u := by
  by_cases hfar : 32 * R ≤ S
  · have h := angularQuadraticCorrelation_norm_le_separated_scales
      lam μ x y l r hlr hR hS hH hlen hμ hfar hlam hlamupper hmuheight
      hp hp' hP hx hy hbound hbound'
    have hu51 : u ^ 5 ≤ u := by
      simpa only [pow_one] using pow_le_pow_of_le_one hu.le hu1 (show 1 ≤ 5 by decide)
    have hdecay1 : 1 ≤ H * u :=
      hdecay.trans (mul_le_mul_of_nonneg_left hu51 hH.le)
    have hinv : 1 / H ≤ u := by rw [div_le_iff₀ hH]; nlinarith
    calc
      _ ≤ 268 * P * R / H := h
      _ = (268 * P * R) * (1 / H) := by ring
      _ ≤ (268 * P * R) * u := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ _ := by gcongr; norm_num
  · have hcomparable : S ≤ 32 * R := le_of_lt (lt_of_not_ge hfar)
    have hlampos : 0 < lam := by
      have hh : 0 < lam * R ^ 2 := hH.trans_le hlam
      exact ((mul_pos_iff.mp hh).resolve_right (by
        rintro ⟨_, hneg⟩
        exact (sq_nonneg R).not_gt hneg)).1
    have hlamS : H ≤ lam * S ^ 2 :=
      hlam.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hR.le hscales 2) hlampos.le)
    have hlamSupper : lam * S ^ 2 ≤ 4096 * H := by
      have hh := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hS.le hcomparable 2) hlampos.le
      nlinarith [hlamupper]
    have habs : |lam - μ| ≤ lam + μ := by
      rw [abs_le]
      constructor <;> linarith
    have hdiff : |lam - μ| * S ^ 2 ≤ 4100 * H := by
      have hh := mul_le_mul_of_nonneg_right habs (sq_nonneg S)
      nlinarith [hlamSupper, hmuheight]
    have hPcompare : P / R ≤ (32 * P) / S := by
      rw [div_le_div_iff₀ hR hS]
      have hh := mul_le_mul_of_nonneg_left hcomparable hP
      nlinarith
    have h := angularQuadraticCorrelation_norm_le_off_diagonal_scaled
      lam μ x y l r hlr hS (hlen.trans hscales) hp hp' hH hu hu1
      (by norm_num : (0 : ℝ) ≤ 4100) (by positivity : 0 ≤ 32 * P)
      hdecay hlamS hdiff hseparation hy
      (fun t ht ↦ (hbound t ht).trans (by nlinarith))
      (fun t ht ↦ (hbound' t ht).trans hPcompare)
    calc
      _ ≤ (7 + 2 * 4100) * (32 * P) * S * u := h
      _ = (262624 * P * u) * S := by ring
      _ ≤ (262624 * P * u) * (32 * R) :=
        mul_le_mul_of_nonneg_left hcomparable (by positivity)
      _ = _ := by ring

/-- The two-region correlation majorant for the quadratic fixed-height
argument. The near-diagonal region has width `u * S`; its complement gains
the factor `u`. For an annular product amplitude `P = A / (R * S)`, the
prefactor `P * R` is exactly `A / S`, as in equation (6.7). -/
theorem angularQuadraticCorrelation_norm_le_fixed_height
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {R S H u : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hH : 0 < H)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hlen : r - l ≤ R) (hμ : 0 ≤ μ) (hscales : R ≤ S)
    (hlam : H ≤ lam * R ^ 2) (hlamupper : lam * R ^ 2 ≤ 4 * H)
    (hmuheight : μ * S ^ 2 ≤ 4 * H)
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {P : ℝ} (hP : 0 ≤ P)
    (hx : ∀ t ∈ Icc l r, R / 4 ≤ |t - x|)
    (hy : ∀ t ∈ Icc l r, |t - y| ≤ S)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P / R) :
    ‖angularQuadraticCorrelation lam μ x y l r p‖ ≤
      P * R * (if |y - x| < u * S then 1 else 8403968 * u) := by
  split_ifs with hnear
  · rw [mul_one]
    calc
      _ ≤ P * |r - l| := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun t ht ↦ by
          rw [norm_mul, norm_quadraticExponential, mul_one]
          exact hbound t (by simpa only [uIcc_of_le hlr] using uIoc_subset_uIcc ht))
      _ ≤ P * R := by
        rw [abs_of_nonneg (sub_nonneg.mpr hlr)]
        exact mul_le_mul_of_nonneg_left hlen hP
  · have h := angularQuadraticCorrelation_norm_le_fixed_height_off_diagonal
      lam μ x y l r hlr hR hS hH hu hu1 hdecay hlen hμ hscales
      hlam hlamupper hmuheight (le_of_not_gt hnear) hp hp' hP hx hy hbound hbound'
    convert h using 1
    ring

/-- The angular correlation agrees with the paper's exact `e(t) = exp(2πit)`
normalization after multiplying both modulations by `2π`. -/
theorem integral_quadraticTTStar_eq_angularQuadraticCorrelation
    (lam μ x y l r : ℝ) (p : ℝ → ℂ) :
    (∫ t in l..r, p t * phase (quadraticTTStarPhase lam μ x y t)) =
      angularQuadraticCorrelation (2 * Real.pi * lam) (2 * Real.pi * μ) x y l r p := by
  unfold angularQuadraticCorrelation
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [phase_quadraticTTStar_eq]
  congr 1
  congr 1 <;> ring

/-- The quadratic two-region fixed-height kernel bound in the source paper's
exact exponential normalization. This proves the oscillatory estimate used
in equation (6.7), for one interval of the annular support intersection.

The subsequent linearization, kernel representation of `TT*`, and maximal
function estimates needed to turn this into an operator bound are separate
analytic steps; they are not hypotheses hidden inside this statement. -/
theorem norm_integral_quadraticTTStar_fixed_height
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {R S H u : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hH : 0 < H)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hlen : r - l ≤ R) (hμ : 0 ≤ μ) (hscales : R ≤ S)
    (hlam : H ≤ lam * R ^ 2) (hlamupper : lam * R ^ 2 ≤ 4 * H)
    (hmuheight : μ * S ^ 2 ≤ 4 * H)
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {P : ℝ} (hP : 0 ≤ P)
    (hx : ∀ t ∈ Icc l r, R / 4 ≤ |t - x|)
    (hy : ∀ t ∈ Icc l r, |t - y| ≤ S)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P / R) :
    ‖∫ t in l..r, p t * phase (quadraticTTStarPhase lam μ x y t)‖ ≤
      P * R * (if |y - x| < u * S then 1 else 8403968 * u) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hπ1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hheight : 1 ≤ (2 * Real.pi * H) * u ^ 5 := by
    calc
      _ ≤ H * u ^ 5 := hdecay
      _ ≤ (2 * Real.pi) * (H * u ^ 5) :=
        le_mul_of_one_le_left (by positivity) hπ1
      _ = _ := by ring
  have hlam' : 2 * Real.pi * H ≤ (2 * Real.pi * lam) * R ^ 2 := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlam hπ.le
  have hlamupper' : (2 * Real.pi * lam) * R ^ 2 ≤ 4 * (2 * Real.pi * H) := by
    calc
      _ = (2 * Real.pi) * (lam * R ^ 2) := by ring
      _ ≤ (2 * Real.pi) * (4 * H) := mul_le_mul_of_nonneg_left hlamupper hπ.le
      _ = _ := by ring
  have hmuheight' : (2 * Real.pi * μ) * S ^ 2 ≤ 4 * (2 * Real.pi * H) := by
    calc
      _ = (2 * Real.pi) * (μ * S ^ 2) := by ring
      _ ≤ (2 * Real.pi) * (4 * H) := mul_le_mul_of_nonneg_left hmuheight hπ.le
      _ = _ := by ring
  rw [integral_quadraticTTStar_eq_angularQuadraticCorrelation]
  exact angularQuadraticCorrelation_norm_le_fixed_height
    (2 * Real.pi * lam) (2 * Real.pi * μ) x y l r hlr hR hS
    (mul_pos hπ hH) hu hu1 hheight hlen (mul_nonneg hπ.le hμ) hscales
    hlam' hlamupper' hmuheight' hp hp' hP hx hy hbound hbound'

/-- An explicit dyadic power-decay specialization: height `2^(5n)` permits
both a diagonal neighborhood of relative width `2^(-n)` and an off-diagonal
gain `2^(-n)`. -/
theorem norm_integral_quadraticTTStar_fixed_height_dyadic
    (n : ℕ) (lam μ x y l r : ℝ) (hlr : l ≤ r) {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S)
    (hlen : r - l ≤ R) (hμ : 0 ≤ μ) (hscales : R ≤ S)
    (hlam : (2 : ℝ) ^ (5 * n) ≤ lam * R ^ 2)
    (hlamupper : lam * R ^ 2 ≤ 4 * (2 : ℝ) ^ (5 * n))
    (hmuheight : μ * S ^ 2 ≤ 4 * (2 : ℝ) ^ (5 * n))
    {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {P : ℝ} (hP : 0 ≤ P)
    (hx : ∀ t ∈ Icc l r, R / 4 ≤ |t - x|)
    (hy : ∀ t ∈ Icc l r, |t - y| ≤ S)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ P / R) :
    ‖∫ t in l..r, p t * phase (quadraticTTStarPhase lam μ x y t)‖ ≤
      P * R * (if |y - x| < S / (2 : ℝ) ^ n then 1 else 8403968 / (2 : ℝ) ^ n) := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hu1 : 1 / (2 : ℝ) ^ n ≤ 1 := by
    rw [div_le_one hpow]
    exact one_le_pow₀ (by norm_num)
  have hdecay : 1 ≤ (2 : ℝ) ^ (5 * n) * (1 / (2 : ℝ) ^ n) ^ 5 := by
    have hid : (2 : ℝ) ^ (5 * n) = ((2 : ℝ) ^ n) ^ 5 := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hid]
    field_simp
    norm_num
  have h := norm_integral_quadraticTTStar_fixed_height
    lam μ x y l r hlr hR hS (by positivity : 0 < (2 : ℝ) ^ (5 * n))
    (by positivity : 0 < 1 / (2 : ℝ) ^ n) hu1 hdecay hlen hμ hscales
    hlam hlamupper hmuheight hp hp' hP hx hy hbound hbound'
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h

/-- The whole-line `TT*` correlation majorant for a smooth amplitude supported
in one same-sign annular overlap. This includes the outer support restriction
and requires no interval decomposition or integrability assumption from its
caller. The positive-half cutoff product in (6.6) has exactly this support. -/
theorem norm_integral_quadraticTTStar_fixed_height_supported
    (lam μ x y : ℝ) {R S H u : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hH : 0 < H)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hμ : 0 ≤ μ) (hscales : R ≤ S)
    (hlam : H ≤ lam * R ^ 2) (hlamupper : lam * R ^ 2 ≤ 4 * H)
    (hmuheight : μ * S ^ 2 ≤ 4 * H)
    {p p' : ℝ → ℂ}
    (hp : ∀ t, HasDerivAt p (p' t) t) (hp' : Continuous p')
    {P : ℝ} (hP : 0 ≤ P)
    (hsupport : Function.support p ⊆
      {t | R / 4 ≤ x - t ∧ x - t ≤ R ∧ 0 ≤ y - t ∧ y - t ≤ S})
    (hbound : ∀ t, ‖p t‖ ≤ P) (hbound' : ∀ t, ‖p' t‖ ≤ P / R) :
    ‖∫ t, p t * phase (quadraticTTStarPhase lam μ x y t)‖ ≤
      if |y - x| ≤ 2 * S then
        P * R * (if |y - x| < u * S then 1 else 8403968 * u)
      else 0 := by
  by_cases hspatial : |y - x| ≤ 2 * S
  · simp only [hspatial, ↓reduceIte]
    let l : ℝ := max (x - R) (y - S)
    let r : ℝ := min (x - R / 4) y
    have hsupp (t : ℝ) (ht : p t ≠ 0) : t ∈ Icc l r := by
      have hh := hsupport ht
      change max (x - R) (y - S) ≤ t ∧ t ≤ min (x - R / 4) y
      rw [max_le_iff, le_min_iff]
      constructor <;> constructor <;> linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]
    by_cases hlr : l ≤ r
    · have hzero (t : ℝ) (ht : t ∉ Icc l r) : p t = 0 := by
        by_contra hn
        exact ht (hsupp t hn)
      have hid : (∫ t, p t * phase (quadraticTTStarPhase lam μ x y t)) =
          ∫ t in l..r, p t * phase (quadraticTTStarPhase lam μ x y t) := by
        calc
          _ = ∫ t in Icc l r, p t * phase (quadraticTTStarPhase lam μ x y t) :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero
              (fun t ht ↦ by rw [hzero t ht, zero_mul])).symm
          _ = ∫ t in Ioc l r, p t * phase (quadraticTTStarPhase lam μ x y t) :=
            integral_Icc_eq_integral_Ioc
          _ = _ := (intervalIntegral.integral_of_le hlr).symm
      have hllen : x - R ≤ l := le_max_left _ _
      have hlright : y - S ≤ l := le_max_right _ _
      have hrl : r ≤ x - R / 4 := min_le_left _ _
      have hrr : r ≤ y := min_le_right _ _
      rw [hid]
      apply norm_integral_quadraticTTStar_fixed_height
        lam μ x y l r hlr hR hS hH hu hu1 hdecay (by linarith) hμ hscales
        hlam hlamupper hmuheight (fun t _ ↦ hp t) hp'.continuousOn hP
        (fun t ht ↦ ?_) (fun t ht ↦ ?_) (fun t _ ↦ hbound t) (fun t _ ↦ hbound' t)
      · have hh := neg_le_abs (t - x)
        linarith [ht.2]
      · rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
    · have hzero : p = 0 := by
        funext t
        by_contra hn
        have ht := hsupp t hn
        exact hlr (ht.1.trans ht.2)
      rw [hzero]
      simp only [Pi.zero_apply, zero_mul, integral_zero, norm_zero]
      split_ifs <;> positivity
  · simp only [hspatial, ↓reduceIte]
    have hzero : p = 0 := by
      funext t
      by_contra hn
      have hh := hsupport hn
      apply hspatial
      rw [abs_le]
      constructor <;> linarith [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]
    rw [hzero]
    simp

/-- Reflection gives the same whole-line majorant for the negative-half
annular cutoff. Together with the preceding theorem this covers both signs
of the spatial cutoff in the linearized `TT*` kernel. -/
theorem norm_integral_quadraticTTStar_fixed_height_supported_negative
    (lam μ x y : ℝ) {R S H u : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hH : 0 < H)
    (hu : 0 < u) (hu1 : u ≤ 1) (hdecay : 1 ≤ H * u ^ 5)
    (hμ : 0 ≤ μ) (hscales : R ≤ S)
    (hlam : H ≤ lam * R ^ 2) (hlamupper : lam * R ^ 2 ≤ 4 * H)
    (hmuheight : μ * S ^ 2 ≤ 4 * H)
    {p p' : ℝ → ℂ}
    (hp : ∀ t, HasDerivAt p (p' t) t) (hp' : Continuous p')
    {P : ℝ} (hP : 0 ≤ P)
    (hsupport : Function.support p ⊆
      {t | R / 4 ≤ t - x ∧ t - x ≤ R ∧ 0 ≤ t - y ∧ t - y ≤ S})
    (hbound : ∀ t, ‖p t‖ ≤ P) (hbound' : ∀ t, ‖p' t‖ ≤ P / R) :
    ‖∫ t, p t * phase (quadraticTTStarPhase lam μ x y t)‖ ≤
      if |y - x| ≤ 2 * S then
        P * R * (if |y - x| < u * S then 1 else 8403968 * u)
      else 0 := by
  let q : ℝ → ℂ := fun t ↦ p (-t)
  let q' : ℝ → ℂ := fun t ↦ -p' (-t)
  have hq (t : ℝ) : HasDerivAt q (q' t) t := by
    have hn : HasDerivAt (fun t : ℝ ↦ -t) (-1) t := hasDerivAt_neg' t
    simpa only [q, q', neg_one_smul, Function.comp_def] using (hp (-t)).scomp t hn
  have hq' : Continuous q' := (hp'.comp continuous_neg).neg
  have hqsupport : Function.support q ⊆
      {t | R / 4 ≤ -x - t ∧ -x - t ≤ R ∧ 0 ≤ -y - t ∧ -y - t ≤ S} := by
    intro t ht
    have hh := hsupport ht
    change R / 4 ≤ -x - t ∧ -x - t ≤ R ∧ 0 ≤ -y - t ∧ -y - t ≤ S
    rcases hh with ⟨h₁, h₂, h₃, h₄⟩
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have h := norm_integral_quadraticTTStar_fixed_height_supported
    lam μ (-x) (-y) hR hS hH hu hu1 hdecay hμ hscales hlam hlamupper hmuheight
    hq hq' hP hqsupport (fun t ↦ hbound (-t)) (fun t ↦ by
      simpa only [q', norm_neg] using hbound' (-t))
  have hphase (t : ℝ) : quadraticTTStarPhase lam μ (-x) (-y) t =
      quadraticTTStarPhase lam μ x y (-t) := by
    unfold quadraticTTStarPhase
    ring
  simp_rw [q, hphase] at h
  rw [integral_neg_eq_self
    (fun t ↦ p t * phase (quadraticTTStarPhase lam μ x y t)) volume] at h
  simpa only [neg_sub_neg, abs_sub_comm x y] using h

end QuadraticCarleson
