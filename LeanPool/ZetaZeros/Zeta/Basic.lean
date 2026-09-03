/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Real.Pi.Bounds
public import LeanPool.ZetaZeros.Numeric.MontgomeryTaylor
public import LeanPool.ZetaZeros.Zeta.Defs

/-!
# First properties of the extremal test function and the rescaling

The extremal test function is strictly positive on its support — which is what makes its square
root smooth, and hence the whole kernel construction possible — and the rescaling sends a zero to
a real point exactly when that zero lies on the critical line.

From those, the normalised cutoff test function `η_ψ` and its square `f_ψ` are shown to be smooth,
compactly supported in `(-1/2, 1/2)` and even — and then so is the self-convolution `Q_ψ`, on
`(-1, 1)`, together with its second derivative.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

/-- `√2 < 3/2`, which places `√2 x` inside `(-π/2, π/2)` for `|x| ≤ 1/2`. -/
private lemma sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  have h : Real.sqrt 2 < Real.sqrt (9 / 4) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h

/-- The extremal test function is strictly positive on `[-1/2, 1/2]`. -/
@[zz_tag "lem_f0_pos"]
theorem extremalTest_pos {x : ℝ} (hx : |x| ≤ 1 / 2) : 0 < extremalTest x := by
  rw [extremalTest, ite_eq_left hx]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) :=
    mul_pos hs2 sin_inv_sqrt_two_pos
  have hb : |Real.sqrt 2 * x| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hs2]
    nlinarith [sqrt_two_lt_three_halves, abs_nonneg x, hx, Real.pi_gt_three]
  obtain ⟨h1, h2⟩ := abs_lt.mp hb
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩) hden

/-- The rescaling sends a zero to a real point exactly when the zero is on the critical line. -/
@[zz_tag "lem_Z_T_real"]
theorem rescale_im_eq_zero_iff {T : ℝ} (hT : 1 < T) (ρ : ℂ) :
    (rescale T ρ).im = 0 ↔ ρ.re = 1 / 2 := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hc : Real.log T / (2 * Real.pi) ≠ 0 := by positivity
  have h12 : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have him : (rescale T ρ).im = (ρ.re - 1 / 2) * (Real.log T / (2 * Real.pi)) := by
    simp only [rescale, h12, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
    ring
  rw [him, mul_eq_zero]
  simp [hc, sub_eq_zero]

/-! ### The normalised cutoff test function is smooth, compactly supported and even

The delicate point is `±1/2`: there `√f₀` is not smooth, because `f₀` jumps
from a positive value down to `0`. What saves it is that a `δ`-cutoff VANISHES on a neighbourhood of
every such point, so the product is locally constant there.

Stated without `0 < δ < 1/4` and without positivity of `A_ψ`: neither is needed. When `A_ψ = 0` the
division gives `η_ψ = 0`, which is smooth, supported anywhere and even. -/

/-- Positivity of the normalising denominator of `f₀`, read off from `extremalTest_pos` at `0`
rather than re-proved, so the library holds only one proof of it. -/
theorem sqrt_two_mul_sin_pos : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := by
  have h := extremalTest_pos (x := 0) (by norm_num)
  rw [extremalTest, ite_eq_left (by norm_num : |(0 : ℝ)| ≤ 1 / 2), mul_zero, Real.cos_zero] at h
  exact one_div_pos.mp h

/-- Off `[-1/2, 1/2]` the cutoff kills the product, so on ALL of `ℝ` the test function agrees with
the expression that has `f₀`'s `if` removed. That representative is smooth wherever
`cos (√2 x) > 0`, and the cutoff handles everywhere else. -/
theorem cutoffTest_eq_unfolded {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) :
    cutoffTest psi = fun x => psi x * Real.sqrt (Real.cos (Real.sqrt 2 * x) /
      (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) / Real.sqrt (cutoffNormaliser psi) := by
  funext x
  by_cases hx : |x| ≤ 1 / 2
  · simp only [cutoffTest, extremalTest, ite_eq_left hx]
  · have hz : psi x = 0 := h.support x (not_le.mp hx).le
    simp only [cutoffTest, extremalTest, ite_eq_right hx, hz, zero_mul, zero_div]

/-- **`η_ψ` is smooth.** -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTest_contDiff {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffTest psi) := by
  have hk := sqrt_two_mul_sin_pos
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [cutoffTest_eq_unfolded h, contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |x| ≤ 1 / 2
  · have hcos : 0 < Real.cos (Real.sqrt 2 * x) := by
      apply Real.cos_pos_of_mem_Ioo
      have habs : |Real.sqrt 2 * x| < Real.pi / 2 := by
        have hrw : |Real.sqrt 2 * x| = Real.sqrt 2 * |x| := by
          rw [abs_mul, abs_of_pos hs2pos]
        rw [hrw]
        nlinarith [sqrt_two_lt_three_halves, abs_nonneg x, Real.pi_gt_three]
      rw [abs_lt] at habs
      exact ⟨habs.1, habs.2⟩
    have hne : Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)) ≠ 0 :=
      ne_of_gt (div_pos hcos hk)
    have hinner : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => Real.cos (Real.sqrt 2 * y) /
        (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) x :=
      ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffAt).div_const _
    exact ((h.smooth.contDiffAt).mul (hinner.sqrt hne)).div_const _
  · have hopen : IsOpen {y : ℝ | 1 / 2 < |y|} := isOpen_lt continuous_const continuous_abs
    have hev : (fun y : ℝ => psi y * Real.sqrt (Real.cos (Real.sqrt 2 * y) /
        (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) / Real.sqrt (cutoffNormaliser psi))
        =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds (not_le.mp hx)] with y hy
      simp [h.support y (le_of_lt hy)]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

/-- **`η_ψ` vanishes off `(-1/2, 1/2)`.** -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTest_eq_zero_of_half_le_abs {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi)
    {x : ℝ} (hx : 1 / 2 ≤ |x|) : cutoffTest psi x = 0 := by
  simp [cutoffTest, h.support x hx]

/-- **`η_ψ` has compact support** -- the `C_c` half of `C_c^∞`. -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTest_hasCompactSupport {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) :
    HasCompactSupport (cutoffTest psi) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)) ?_
  intro x hx
  refine cutoffTest_eq_zero_of_half_le_abs h ?_
  by_contra hlt
  exact hx (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hlt))))

/-- **`η_ψ` is even.** -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTest_neg {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) (x : ℝ) :
    cutoffTest psi (-x) = cutoffTest psi x := by
  have hf : extremalTest (-x) = extremalTest x := by
    simp [extremalTest, abs_neg, mul_neg, Real.cos_neg]
  simp [cutoffTest, hf, h.even x]

/-- **`f_ψ` is smooth.** -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTestSq_contDiff {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffTestSq psi) := by
  have hpow : cutoffTestSq psi = fun x => cutoffTest psi x ^ 2 := rfl
  rw [hpow]
  exact (cutoffTest_contDiff h).pow 2

/-- **`f_ψ` vanishes off `(-1/2, 1/2)`.** -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTestSq_eq_zero_of_half_le_abs {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi)
    {x : ℝ} (hx : 1 / 2 ≤ |x|) : cutoffTestSq psi x = 0 := by
  simp [cutoffTestSq, Pi.pow_apply, cutoffTest_eq_zero_of_half_le_abs h hx]

/-- **`f_ψ` has compact support.** -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTestSq_hasCompactSupport {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) :
    HasCompactSupport (cutoffTestSq psi) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)) ?_
  intro x hx
  refine cutoffTestSq_eq_zero_of_half_le_abs h ?_
  by_contra hlt
  exact hx (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hlt))))

/-- **`f_ψ` is even.** -/
@[zz_tag "lem_eta_psi_smooth"]
theorem cutoffTestSq_neg {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) (x : ℝ) :
    cutoffTestSq psi (-x) = cutoffTestSq psi x := by
  simp [cutoffTestSq, Pi.pow_apply, cutoffTest_neg h x]

/-! ### The self-convolution `Q_psi`: smoothness, support, parity

`Q_psi` is `f_psi` convolved with itself, so Mathlib's convolution theory applies once `f_psi` is
known smooth with compact support, which is `cutoffTestSq_contDiff` and
`cutoffTestSq_hasCompactSupport`.

The support claim doubles: `f_psi` lives in `(-1/2, 1/2)`, so the convolution lives in `(-1, 1)`.
The elementary reason is that the integrand `f_psi t * f_psi (x - t)` is identically zero when
`1 <= |x|`: either `|t| >= 1/2`, killing the first factor, or `|t| < 1/2` and then
`|x - t| >= |x| - |t| > 1/2`, killing the second.

For `Q_psi''` the support and parity are inherited rather than recomputed: derivatives cannot
enlarge the support (`tsupport_deriv_subset`), and `iteratedDeriv_comp_neg` turns evenness of
`Q_psi` into evenness of an even-order derivative. -/

section QPsi

variable {delta : ℝ} {psi : ℝ → ℝ}

/-- Outside `[-c, c]` the absolute value is at least `c`. Used repeatedly to turn a
`HasCompactSupport.intro` obligation into the pointwise vanishing statement. -/
theorem le_abs_of_notMem_Icc {c x : ℝ} (hx : x ∉ Set.Icc (-c) c) : c ≤ |x| := by
  rcases le_or_gt c |x| with hle | hlt
  · exact hle
  · exact absurd (Set.mem_Icc.mpr (abs_le.mp hlt.le)) hx

/-- `Q_psi` is Mathlib's convolution of `f_psi` with itself. Definitional, but it is what makes the
convolution smoothness theorem applicable. -/
theorem cutoffSelfConv_eq_convolution (psi : ℝ → ℝ) :
    cutoffSelfConv psi =
      convolution (cutoffTestSq psi) (cutoffTestSq psi) (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rfl

/-- **`Q_psi` is smooth.** -/
@[zz_tag "lem_Q_psi_support"]
theorem contDiff_cutoffSelfConv (h : IsCutoff delta psi) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffSelfConv psi) := by
  rw [cutoffSelfConv_eq_convolution]
  exact HasCompactSupport.contDiff_convolution_right
    (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume)
    (hcg := cutoffTestSq_hasCompactSupport h)
    (hf := (cutoffTestSq_contDiff h).continuous.locallyIntegrable (μ := volume))
    (hg := cutoffTestSq_contDiff h)

/-- **`Q_psi` vanishes off `(-1, 1)`.** -/
@[zz_tag "lem_Q_psi_support"]
theorem cutoffSelfConv_eq_zero_of_one_le_abs (h : IsCutoff delta psi) {x : ℝ} (hx : 1 ≤ |x|) :
    cutoffSelfConv psi x = 0 := by
  have key : ∀ t : ℝ, cutoffTestSq psi t * cutoffTestSq psi (x - t) = 0 := by
    intro t
    rcases le_or_gt (1 / 2 : ℝ) |t| with ht | ht
    · rw [cutoffTestSq_eq_zero_of_half_le_abs h ht, zero_mul]
    · have h2 : 1 / 2 ≤ |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        linarith
      rw [cutoffTestSq_eq_zero_of_half_le_abs h h2, mul_zero]
  simp [cutoffSelfConv, key]

/-- **`Q_psi` has compact support.** -/
@[zz_tag "lem_Q_psi_support"]
theorem hasCompactSupport_cutoffSelfConv (h : IsCutoff delta psi) :
    HasCompactSupport (cutoffSelfConv psi) :=
  HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun _ hx =>
    cutoffSelfConv_eq_zero_of_one_le_abs h (le_abs_of_notMem_Icc (by simpa using hx))

/-- **`Q_psi` is even.** -/
@[zz_tag "lem_Q_psi_support"]
theorem cutoffSelfConv_neg (h : IsCutoff delta psi) (x : ℝ) :
    cutoffSelfConv psi (-x) = cutoffSelfConv psi x := by
  have hneg := integral_neg_eq_self
    (fun t : ℝ => cutoffTestSq psi t * cutoffTestSq psi (x - t)) volume
  rw [cutoffSelfConv, cutoffSelfConv, ← hneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  change cutoffTestSq psi t * cutoffTestSq psi (-x - t)
      = cutoffTestSq psi (-t) * cutoffTestSq psi (x - -t)
  rw [cutoffTestSq_neg h t, show (-x - t) = -(x - -t) by ring, cutoffTestSq_neg h]

/-- **`Q_psi` is Lipschitz continuous at `0`** -- Lipschitz with some constant on some
neighbourhood of `0`, which is what "Lipschitz continuous at `0`" means here. -/
@[zz_tag "lem_Q_psi_support"]
theorem exists_lipschitzOnWith_cutoffSelfConv (h : IsCutoff delta psi) :
    ∃ K, ∃ t ∈ nhds (0 : ℝ), LipschitzOnWith K (cutoffSelfConv psi) t :=
  ((contDiff_cutoffSelfConv h).of_le (by exact_mod_cast le_top)).contDiffAt.exists_lipschitzOnWith

/-- **`Q_psi''` is smooth.** -/
@[zz_tag "lem_Q_psi_support"]
theorem contDiff_iteratedDeriv_two_cutoffSelfConv (h : IsCutoff delta psi) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 (cutoffSelfConv psi)) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv 2 (contDiff_cutoffSelfConv h)

/-- **`Q_psi''` vanishes off `[-1, 1]`.** A derivative cannot enlarge the support. -/
@[zz_tag "lem_Q_psi_support"]
theorem iteratedDeriv_two_cutoffSelfConv_eq_zero (h : IsCutoff delta psi) {x : ℝ} (hx : 1 < |x|) :
    iteratedDeriv 2 (cutoffSelfConv psi) x = 0 := by
  have hsupp : Function.support (cutoffSelfConv psi) ⊆ Set.Icc (-1 : ℝ) 1 := fun y hy => by
    by_contra hmem
    exact hy (cutoffSelfConv_eq_zero_of_one_le_abs h (le_abs_of_notMem_Icc (by simpa using hmem)))
  have hout : x ∉ tsupport (cutoffSelfConv psi) := fun hmem => by
    have hle : |x| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp (closure_minimal hsupp isClosed_Icc hmem))
    linarith
  have hchain : x ∉ Function.support (deriv (deriv (cutoffSelfConv psi))) := fun hmem =>
    hout (tsupport_deriv_subset (support_deriv_subset hmem))
  simpa [iteratedDeriv_succ, iteratedDeriv_one, Function.notMem_support] using hchain

/-- **`Q_psi''` is even**, being an even-order derivative of an even function. -/
@[zz_tag "lem_Q_psi_support"]
theorem iteratedDeriv_two_cutoffSelfConv_neg (h : IsCutoff delta psi) (x : ℝ) :
    iteratedDeriv 2 (cutoffSelfConv psi) (-x) = iteratedDeriv 2 (cutoffSelfConv psi) x := by
  have heven : (fun y : ℝ => cutoffSelfConv psi (-y)) = cutoffSelfConv psi :=
    funext fun y => cutoffSelfConv_neg h y
  have hcn := iteratedDeriv_comp_neg 2 (cutoffSelfConv psi) x
  rw [heven] at hcn
  simpa using hcn.symm

/-- **`Q_psi''` is Lipschitz continuous at `0`.** -/
@[zz_tag "lem_Q_psi_support"]
theorem exists_lipschitzOnWith_iteratedDeriv_two_cutoffSelfConv (h : IsCutoff delta psi) :
    ∃ K, ∃ t ∈ nhds (0 : ℝ), LipschitzOnWith K (iteratedDeriv 2 (cutoffSelfConv psi)) t :=
  ((contDiff_iteratedDeriv_two_cutoffSelfConv h).of_le
    (by exact_mod_cast le_top)).contDiffAt.exists_lipschitzOnWith

end QPsi

end ZetaZeros
