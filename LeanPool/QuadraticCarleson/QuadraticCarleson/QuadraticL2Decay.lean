/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import LeanPool.QuadraticCarleson.QuadraticCarleson.Bohr
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Quadratic analytic inputs for fixed-height L² decay

These are prerequisites for the direct `c = 2` specialization of the proof of
Lemma 6.2 of arXiv:2412.15766, specifically its phase in (6.6) and exceptional
set in (6.8). The resulting genuine real-parameter maximal L² estimate is proved
in `QuadraticFixedHeightAveragingNorm`, with L² stability and a Lipschitz operator
form in `QuadraticFixedHeightL2Stability`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace QuadraticCarleson

/-- The real phase of the quadratic `TT*` kernel, before the factor `2π`. -/
def quadraticTTStarPhase (lam μ x y t : ℝ) : ℝ :=
  lam * (x - t) ^ 2 - μ * (y - t) ^ 2

/-- Its first derivative is affine. -/
def quadraticTTStarSlope (lam μ x y t : ℝ) : ℝ :=
  2 * ((lam - μ) * t + μ * y - lam * x)

theorem hasDerivAt_quadraticTTStarPhase (lam μ x y t : ℝ) :
    HasDerivAt (quadraticTTStarPhase lam μ x y)
      (quadraticTTStarSlope lam μ x y t) t := by
  apply (((((hasDerivAt_const t x).sub (hasDerivAt_id t)).pow 2).const_mul lam).sub
    ((((hasDerivAt_const t y).sub (hasDerivAt_id t)).pow 2).const_mul μ)).congr_deriv
  dsimp [quadraticTTStarSlope]
  ring

theorem hasDerivAt_quadraticTTStarSlope (lam μ x y t : ℝ) :
    HasDerivAt (quadraticTTStarSlope lam μ x y) (2 * (lam - μ)) t := by
  unfold quadraticTTStarSlope
  simpa only [id_eq, mul_one] using
    ((((hasDerivAt_id t).const_mul (lam - μ)).add_const (μ * y)).sub_const
      (lam * x)).const_mul 2

theorem quadraticTTStarPhase_eq_polynomial (lam μ x y t : ℝ) :
    quadraticTTStarPhase lam μ x y t =
      (lam - μ) * t ^ 2 + 2 * (μ * y - lam * x) * t + (lam * x ^ 2 - μ * y ^ 2) := by
  unfold quadraticTTStarPhase
  ring

theorem quadraticTTStarSlope_eq_center {lam μ : ℝ} (h : lam ≠ μ) (x y t : ℝ) :
    quadraticTTStarSlope lam μ x y t =
      2 * (lam - μ) * (t - (lam * x - μ * y) / (lam - μ)) := by
  unfold quadraticTTStarSlope
  field_simp [sub_ne_zero.mpr h]
  ring

/-- The quadratic exceptional set is exactly one closed interval, for either
ordering or sign of the two modulations. -/
theorem quadraticTTStarSlope_sublevel_eq_Icc {lam μ : ℝ} (h : lam ≠ μ)
    (x y η : ℝ) :
    {t | |quadraticTTStarSlope lam μ x y t| ≤ η} =
      Icc ((lam * x - μ * y) / (lam - μ) - η / (2 * |lam - μ|))
        ((lam * x - μ * y) / (lam - μ) + η / (2 * |lam - μ|)) := by
  ext t
  have hpos : 0 < 2 * |lam - μ| := mul_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr h))
  rw [mem_ofPred, quadraticTTStarSlope_eq_center h, abs_mul, abs_mul,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num), ← le_div_iff₀' hpos, abs_le, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Exact exceptional-set measure, the `c = 2` form of the geometric step
in (6.8). Intersecting with the amplitude support can only reduce this value. -/
theorem volume_quadraticTTStarSlope_sublevel {lam μ : ℝ} (h : lam ≠ μ)
    (x y η : ℝ) :
    volume {t | |quadraticTTStarSlope lam μ x y t| ≤ η} =
      ENNReal.ofReal (η / |lam - μ|) := by
  rw [quadraticTTStarSlope_sublevel_eq_Icc h, Real.volume_Icc]
  congr 1
  ring

theorem volume_quadraticTTStarSlope_sublevel_inter_le {lam μ : ℝ} (h : lam ≠ μ)
    (x y η : ℝ) (s : Set ℝ) :
    volume (s ∩ {t | |quadraticTTStarSlope lam μ x y t| ≤ η}) ≤
      ENNReal.ofReal (η / |lam - μ|) := by
  rw [← volume_quadraticTTStarSlope_sublevel h x y η]
  exact measure_mono inter_subset_right

/-- When the modulations agree, the slope is constant and is nonzero away
from the spatial diagonal. -/
theorem quadraticTTStarSlope_same_modulation (lam x y t : ℝ) :
    quadraticTTStarSlope lam lam x y t = 2 * lam * (y - x) := by
  unfold quadraticTTStarSlope
  ring

/-- Angular normalization used for the weighted integration-by-parts estimate. -/
noncomputable def quadraticExponential (a b c t : ℝ) : ℂ :=
  Complex.exp (((a * t ^ 2 + b * t + c : ℝ) : ℂ) * Complex.I)

@[simp]
theorem norm_quadraticExponential (a b c t : ℝ) :
    ‖quadraticExponential a b c t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_quadraticExponential (a b c t : ℝ) :
    HasDerivAt (quadraticExponential a b c)
      ((((2 * a * t + b : ℝ) : ℂ) * Complex.I) * quadraticExponential a b c t) t := by
  have h : HasDerivAt (fun u : ℝ ↦ a * u ^ 2 + b * u + c)
      (2 * a * t + b) t := by
    apply (((((hasDerivAt_id t).pow 2).const_mul a).add
      ((hasDerivAt_id t).const_mul b)).add_const c).congr_deriv
    simp only [id_eq]
    ring
  exact ((h.ofReal_comp.mul_const Complex.I).cexp).congr_deriv (by
    dsimp [quadraticExponential]
    ring)

/-- This identifies the angular normalization with exactly the `TT*` phase. -/
theorem phase_quadraticTTStar_eq (lam μ x y t : ℝ) :
    phase (quadraticTTStarPhase lam μ x y t) =
      quadraticExponential (2 * Real.pi * (lam - μ))
        (4 * Real.pi * (μ * y - lam * x))
        (2 * Real.pi * (lam * x ^ 2 - μ * y ^ 2)) t := by
  unfold phase quadraticExponential
  congr 2
  push_cast
  rw [quadraticTTStarPhase_eq_polynomial]
  push_cast
  ring

/-- Weighted quadratic cancellation on an interval with no stationary point.

The right side uses only an amplitude bound, a derivative bound, the length
of the interval, and a lower bound on the phase derivative. It applies on
each of the at most two complementary intervals of the exceptional set. -/
theorem norm_integral_quadraticExponential_mul_le
    (a b c l r : ℝ) (hlr : l ≤ r) {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {δ P Q : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hslope : ∀ t ∈ Icc l r, δ ≤ |2 * a * t + b|)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ Q) :
    ‖∫ t in l..r, p t * quadraticExponential a b c t‖ ≤
      2 * P / δ + (r - l) * (Q / δ + P * |2 * a| / δ ^ 2) := by
  let d : ℝ → ℂ := fun t ↦ ((2 * a * t + b : ℝ) : ℂ) * Complex.I
  let d' : ℂ := ((2 * a : ℝ) : ℂ) * Complex.I
  let u : ℝ → ℂ := fun t ↦ p t / d t
  let u' : ℝ → ℂ := fun t ↦ p' t / d t - p t * d' / d t ^ 2
  let v : ℝ → ℂ := quadraticExponential a b c
  let v' : ℝ → ℂ := fun t ↦ d t * v t
  have hd (t : ℝ) : HasDerivAt d d' t := by
    simpa only [d, d', id_eq, mul_one] using
      (((hasDerivAt_id t).const_mul (2 * a)).add_const b).ofReal_comp.mul_const Complex.I
  have hdnorm (t : ℝ) : ‖d t‖ = |2 * a * t + b| := by
    dsimp [d]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hd'norm : ‖d'‖ = |2 * a| := by
    dsimp [d']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hdnz (t : ℝ) (ht : t ∈ Icc l r) : d t ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hdnorm]
    exact hδ.trans_le (hslope t ht)
  have hu (t : ℝ) (ht : t ∈ Icc l r) : HasDerivAt u (u' t) t := by
    apply ((hp t ht).div (hd t) (hdnz t ht)).congr_deriv
    dsimp [u']
    field_simp
  have hv (t : ℝ) : HasDerivAt v (v' t) t :=
    hasDerivAt_quadraticExponential a b c t
  have hpc : ContinuousOn p (Icc l r) := fun t ht ↦ (hp t ht).continuousAt.continuousWithinAt
  have hdc : Continuous d := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt)
  have huc : ContinuousOn u (Icc l r) := hpc.div hdc.continuousOn hdnz
  have hu'c : ContinuousOn u' (Icc l r) :=
    (hp'.div hdc.continuousOn hdnz).sub
      ((hpc.mul continuousOn_const).div (hdc.pow 2).continuousOn
        (fun t ht ↦ pow_ne_zero 2 (hdnz t ht)))
  have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun t ↦ (hv t).continuousAt)
  have hv'c : Continuous v' := hdc.mul hvc
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht ↦ hu t (by simpa [uIcc_of_le hlr] using ht))
    (fun t _ ↦ hv t)
    ((by simpa [uIcc_of_le hlr] using hu'c : ContinuousOn u' (uIcc l r)).intervalIntegrable)
    (hv'c.intervalIntegrable l r)
  have hid : (∫ t in l..r, p t * v t) =
      u r * v r - u l * v l - ∫ t in l..r, u' t * v t := by
    rw [← hparts]
    apply intervalIntegral.integral_congr
    intro t ht
    have hn := hdnz t (by simpa [uIcc_of_le hlr] using ht)
    dsimp [u, v']
    field_simp
  have hubound (t : ℝ) (ht : t ∈ Icc l r) : ‖u t‖ ≤ P / δ := by
    dsimp [u]
    rw [norm_div, hdnorm]
    exact div_le_div₀ hP (hbound t ht) hδ (hslope t ht)
  have hu'bound (t : ℝ) (ht : t ∈ Icc l r) :
      ‖u' t‖ ≤ Q / δ + P * |2 * a| / δ ^ 2 := by
    calc
      ‖u' t‖ ≤ ‖p' t / d t‖ + ‖p t * d' / d t ^ 2‖ := norm_sub_le _ _
      _ = ‖p' t‖ / |2 * a * t + b| + ‖p t‖ * |2 * a| / |2 * a * t + b| ^ 2 := by
        simp only [norm_div, norm_pow, norm_mul, hdnorm, hd'norm]
      _ ≤ Q / δ + P * |2 * a| / δ ^ 2 := by
        gcongr
        · exact hbound' t ht
        · exact hslope t ht
        · exact hbound t ht
        · exact hslope t ht
  have hvnorm (t : ℝ) : ‖v t‖ = 1 := norm_quadraticExponential a b c t
  have hint : ‖∫ t in l..r, u' t * v t‖ ≤
      (Q / δ + P * |2 * a| / δ ^ 2) * (r - l) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := r) (f := fun t ↦ u' t * v t)
      (C := Q / δ + P * |2 * a| / δ ^ 2) (fun t ht ↦ ?_)
    · simpa [abs_of_nonneg (sub_nonneg.mpr hlr)] using hh
    rw [norm_mul, hvnorm, mul_one]
    exact hu'bound t (by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc ht)
  change ‖∫ t in l..r, p t * v t‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖u r * v r - u l * v l‖ + ‖∫ t in l..r, u' t * v t‖ := norm_sub_le _ _
    _ ≤ (‖u r‖ + ‖u l‖) + ‖∫ t in l..r, u' t * v t‖ := by
      gcongr
      simpa [norm_mul, hvnorm] using norm_sub_le (u r * v r) (u l * v l)
    _ ≤ (P / δ + P / δ) + (Q / δ + P * |2 * a| / δ ^ 2) * (r - l) := by
      gcongr
      · exact hubound r ⟨hlr, le_rfl⟩
      · exact hubound l ⟨le_rfl, hlr⟩
    _ = _ := by ring

/-- The contribution of the small-derivative region, with arbitrary measurable
or nonmeasurable support restriction. This is the first integral in the final
split of the proof of Lemma 6.2, now with an exact constant. -/
theorem norm_integral_quadraticTTStar_sublevel_le
    {lam μ : ℝ} (h : lam ≠ μ) (x y : ℝ) {η P : ℝ}
    (hη : 0 ≤ η) (hP : 0 ≤ P) (s : Set ℝ) (p : ℝ → ℂ)
    (hp : ∀ t ∈ s, ‖p t‖ ≤ P) :
    ‖∫ t in s ∩ {t | |quadraticTTStarSlope lam μ x y t| ≤ η},
        p t * phase (quadraticTTStarPhase lam μ x y t)‖ ≤ P * (η / |lam - μ|) := by
  have hm := volume_quadraticTTStarSlope_sublevel_inter_le h x y η s
  have hfinite : volume (s ∩ {t | |quadraticTTStarSlope lam μ x y t| ≤ η}) < ⊤ :=
    lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  calc
    _ ≤ P * (volume (s ∩ {t | |quadraticTTStarSlope lam μ x y t| ≤ η})).toReal := by
      apply norm_setIntegral_le_of_norm_le_const hfinite
      intro t ht
      rw [norm_mul, norm_phase, mul_one]
      exact hp t ht.1
    _ ≤ P * (ENNReal.ofReal (η / |lam - μ|)).toReal := by
      apply mul_le_mul_of_nonneg_left _ hP
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    _ = _ := by rw [ENNReal.toReal_ofReal (div_nonneg hη (abs_nonneg _))]

/-- In the nearly equal modulation case, spatial separation prevents a
stationary point throughout the amplitude support. -/
theorem quadraticTTStarSlope_lower_bound_near_modulations
    {lam μ x y t R : ℝ} (hlam : 0 ≤ lam)
    (ht : |t - y| ≤ R)
    (hclose : |lam - μ| * R ≤ lam * |y - x| / 2) :
    lam * |y - x| ≤ |quadraticTTStarSlope lam μ x y t| := by
  have hid : quadraticTTStarSlope lam μ x y t =
      2 * (lam * (y - x) + (lam - μ) * (t - y)) := by
    unfold quadraticTTStarSlope
    ring
  have htriangle := abs_add_le (lam * (y - x) + (lam - μ) * (t - y))
    (-((lam - μ) * (t - y)))
  rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_nonneg hlam] at htriangle
  have herror : |(lam - μ) * (t - y)| ≤ lam * |y - x| / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans hclose
  rw [hid, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  linarith

/-- The complementary-interval cancellation estimate in the paper's exact
phase normalization. No restriction on the ordering or sign of modulations
is needed once a lower bound on the slope has been established. -/
theorem norm_integral_quadraticTTStar_mul_le
    (lam μ x y l r : ℝ) (hlr : l ≤ r) {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {η P Q : ℝ} (hη : 0 < η) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hslope : ∀ t ∈ Icc l r, η ≤ |quadraticTTStarSlope lam μ x y t|)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ Q) :
    ‖∫ t in l..r, p t * phase (quadraticTTStarPhase lam μ x y t)‖ ≤
      2 * P / (2 * Real.pi * η) + (r - l) *
        (Q / (2 * Real.pi * η) + P * |4 * Real.pi * (lam - μ)| /
          (2 * Real.pi * η) ^ 2) := by
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have h := norm_integral_quadraticExponential_mul_le
    (2 * Real.pi * (lam - μ)) (4 * Real.pi * (μ * y - lam * x))
    (2 * Real.pi * (lam * x ^ 2 - μ * y ^ 2)) l r hlr hp hp'
    (mul_pos hπ hη) hP hQ (fun t ht ↦ ?_) hbound hbound'
  · simpa only [← phase_quadraticTTStar_eq,
      show 2 * (2 * Real.pi * (lam - μ)) = 4 * Real.pi * (lam - μ) by ring] using h
  have hid : 2 * (2 * Real.pi * (lam - μ)) * t + 4 * Real.pi * (μ * y - lam * x) =
      (2 * Real.pi) * quadraticTTStarSlope lam μ x y t := by
    unfold quadraticTTStarSlope
    ring
  rw [hid, abs_mul, abs_of_pos hπ]
  exact mul_le_mul_of_nonneg_left (hslope t ht) hπ.le

/-- A global quadratic cancellation estimate, including the stationary point.
The freely chosen threshold `δ` balances the exceptional interval against
the two nonstationary intervals. This quantitative form is sufficient for
power decay; no general van der Corput or Stein--Wainger theorem is assumed. -/
theorem norm_integral_quadraticExponential_mul_le_split
    {a : ℝ} (ha : a ≠ 0) (b c l r : ℝ) (hlr : l ≤ r) {p p' : ℝ → ℂ}
    (hp : ∀ t ∈ Icc l r, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc l r))
    {δ P Q : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hbound : ∀ t ∈ Icc l r, ‖p t‖ ≤ P)
    (hbound' : ∀ t ∈ Icc l r, ‖p' t‖ ≤ Q) :
    ‖∫ t in l..r, p t * quadraticExponential a b c t‖ ≤
      P * (δ / |a|) + 4 * P / δ +
        (r - l) * (Q / δ + P * |2 * a| / δ ^ 2) := by
  let z : ℝ := -b / (2 * a)
  let ρ : ℝ := δ / (2 * |a|)
  let s : ℝ := max l (min r (z - ρ))
  let t : ℝ := max l (min r (z + ρ))
  let W : ℝ := Q / δ + P * |2 * a| / δ ^ 2
  let f : ℝ → ℂ := fun u ↦ p u * quadraticExponential a b c u
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hls : l ≤ s := le_max_left _ _
  have hst : s ≤ t := max_le_max_left l (min_le_min_left r (by linarith))
  have htr : t ≤ r := max_le hlr (min_le_left _ _)
  have hsr : s ≤ r := hst.trans htr
  have hlt : l ≤ t := hls.trans hst
  have hlen : t - s ≤ 2 * ρ := by
    dsimp [s, t]
    simp only [max_def, min_def]
    split_ifs <;> linarith
  have hs_left (h : l < s) : s ≤ z - ρ := by
    have : l < min r (z - ρ) := (lt_max_iff.mp h).resolve_left (lt_irrefl _)
    dsimp [s]
    rw [max_eq_right this.le]
    exact min_le_right _ _
  have ht_right (h : t < r) : z + ρ ≤ t := by
    have hmin : min r (z + ρ) < r := (le_max_right l _).trans_lt h
    have hzr : z + ρ < r := (min_lt_iff.mp hmin).resolve_left (lt_irrefl _)
    dsimp [t]
    rw [min_eq_right hzr.le]
    exact le_max_right _ _
  have hslope (u : ℝ) : |2 * a * u + b| = 2 * |a| * |u - z| := by
    have hid : 2 * a * u + b = (2 * a) * (u - z) := by
      dsimp [z]
      field_simp
      ring
    rw [hid, abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hthreshold : 2 * |a| * ρ = δ := by
    dsimp [ρ]
    field_simp
  have hsub {v w : ℝ} (hlv : l ≤ v) (hwr : w ≤ r) : Icc v w ⊆ Icc l r :=
    Icc_subset_Icc hlv hwr
  have hnonstationary {v w : ℝ} (hvw : v ≤ w) (hlv : l ≤ v) (hwr : w ≤ r)
      (hd : ∀ u ∈ Icc v w, δ ≤ |2 * a * u + b|) :
      ‖∫ u in v..w, f u‖ ≤ 2 * P / δ + (w - v) * W := by
    exact norm_integral_quadraticExponential_mul_le a b c v w hvw
      (fun u hu ↦ hp u (hsub hlv hwr hu)) (hp'.mono (hsub hlv hwr)) hδ hP hQ hd
      (fun u hu ↦ hbound u (hsub hlv hwr hu))
      (fun u hu ↦ hbound' u (hsub hlv hwr hu))
  have hleft : ‖∫ u in l..s, f u‖ ≤ 2 * P / δ + (s - l) * W := by
    rcases hls.eq_or_lt with h | h
    · rw [← h]
      simp only [intervalIntegral.integral_same, norm_zero, sub_self, zero_mul, add_zero]
      positivity
    apply hnonstationary hls le_rfl hsr
    intro u hu
    rw [hslope, ← hthreshold]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (abs_nonneg _))
    have hu' : u ≤ z - ρ := hu.2.trans (hs_left h)
    have habs := neg_le_abs (u - z)
    linarith
  have hright : ‖∫ u in t..r, f u‖ ≤ 2 * P / δ + (r - t) * W := by
    rcases htr.eq_or_lt with h | h
    · rw [h]
      simp only [intervalIntegral.integral_same, norm_zero, sub_self, zero_mul, add_zero]
      positivity
    apply hnonstationary htr hlt le_rfl
    intro u hu
    rw [hslope, ← hthreshold]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (abs_nonneg _))
    have hu' : z + ρ ≤ u := (ht_right h).trans hu.1
    have habs := le_abs_self (u - z)
    linarith
  have hmiddle : ‖∫ u in s..t, f u‖ ≤ P * (δ / |a|) := by
    calc
      _ ≤ P * |t - s| := intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu ↦ by
        rw [uIoc_of_le hst] at hu
        dsimp [f]
        rw [norm_mul, norm_quadraticExponential, mul_one]
        exact hbound u ⟨hls.trans hu.1.le, hu.2.trans htr⟩)
      _ ≤ P * (2 * ρ) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hst)]
        exact mul_le_mul_of_nonneg_left hlen hP
      _ = _ := by dsimp [ρ]; ring
  have hfc : ContinuousOn f (Icc l r) :=
    (show ContinuousOn p (Icc l r) from
      fun u hu ↦ (hp u hu).continuousAt.continuousWithinAt).mul
      (continuous_iff_continuousAt.mpr
        (fun u ↦ (hasDerivAt_quadraticExponential a b c u).continuousAt)).continuousOn
  have hfint {v w : ℝ} (hvw : v ≤ w) (hlv : l ≤ v) (hwr : w ≤ r) :
      IntervalIntegrable f volume v w := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hvw]
    exact hfc.mono (hsub hlv hwr)
  have hsplit : (∫ u in l..r, f u) =
      (∫ u in l..s, f u) + (∫ u in s..t, f u) + (∫ u in t..r, f u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hfint hls le_rfl hsr) (hfint hst hls htr),
      intervalIntegral.integral_add_adjacent_intervals
        (hfint hlt le_rfl htr) (hfint htr hlt le_rfl)]
  change ‖∫ u in l..r, f u‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ (‖∫ u in l..s, f u‖ + ‖∫ u in s..t, f u‖) + ‖∫ u in t..r, f u‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2 * P / δ + (s - l) * W + P * (δ / |a|)) +
        (2 * P / δ + (r - t) * W) := add_le_add (add_le_add hleft hmiddle) hright
    _ ≤ _ := by
      change _ ≤ P * (δ / |a|) + 4 * P / δ + (r - l) * W
      have hgap : 0 ≤ (t - s) * W := mul_nonneg (sub_nonneg.mpr hst) hW
      calc
        _ = (P * (δ / |a|) + 4 * P / δ + (r - l) * W) - (t - s) * W := by ring
        _ ≤ _ := sub_le_self _ hgap

end QuadraticCarleson
