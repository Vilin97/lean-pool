/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import LeanPool.ExpChaotic.Covering
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Density of repelling periodic points

Section 6: contracting inverse branches and the fixed-point theorem give repelling points.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

public section

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-! ## Section 6: repelling periodic points and the density benchmarks

The full backward orbit means the union over all iterates. A single one-step
preimage of a point is not asserted to be dense. Repelling means that there is
a positive period for which the derivative of the return iterate has norm greater
than one.

The proof uses real orbit centres equal to `expIterate n 10`. The first inverse
branch returns to the original open set; iterated logarithms contract along the
real orbit; two final logarithms close the return. Lipschitz constants suffice
for construction, and differentiability of the inverse at its fixed point then
gives the strict multiplier bound.
-/

/-- A noncritical holomorphic map has a Lipschitz inverse on a small image disk. -/
theorem exists_lipschitz_local_inverse {f : ℂ → ℂ} {a : ℂ}
    (hf : HasStrictDerivAt f (deriv f a) a) (hne : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ C : ℝ≥0, ∃ s : ℝ, 0 < s ∧
      g (f a) = a ∧ LipschitzOnWith C g (ball (f a) s) ∧
      ∀ z ∈ ball (f a) s, f (g z) = z := by
  -- The strict inverse-function theorem supplies an inverse and a local Lipschitz bound.
  let g := hf.localInverse f (deriv f a) a hne
  have hga : g (f a) = a := hf.eventually_left_inverse hne |>.self_of_nhds
  have hg := hf.to_localInverse hne
  obtain ⟨C, V, hV, hCV⟩ := hg.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hV (hf.eventually_right_inverse hne))
  exact ⟨g, C, s, hs, hga, hCV.mono (fun z hz => (hsub hz).1),
    fun z hz => (hsub hz).2⟩

/-- The `n`-fold iterate of the principal logarithm.
Inverse identities below are asserted only on the indicated disks, where this branch applies. -/
abbrev logIterate (n : ℕ) : ℂ → ℂ := Complex.log^[n]

/-- The principal logarithm contracts by a factor of at most `1/2` on a radius-eight
disk about `exp x`, for real `x ≥ 10`. This disk lies in `Re z ≥ 2`, so `|1/z| ≤ 1/2`. -/
theorem log_lipschitz_real_ball {x : ℂ} (hx : x.im = 0) (hx10 : 10 ≤ x.re) :
    LipschitzOnWith (1 / 2) Complex.log (ball (Complex.exp x) 8) := by
  have hrez : ∀ z ∈ ball (Complex.exp x) 8, (2 : ℝ) ≤ z.re := by
    intro z hz
    have hdist : ‖z - Complex.exp x‖ < 8 := by simpa [mem_ball, dist_eq_norm] using hz
    have h := (Complex.abs_re_le_norm (z - Complex.exp x)).trans_lt hdist
    simp only [Complex.sub_re, Complex.exp_re, hx, Real.cos_zero, mul_one] at h
    linarith [(abs_lt.mp h).1, Real.add_one_le_exp x.re]
  have hslit : ∀ z ∈ ball (Complex.exp x) 8, z ∈ Complex.slitPlane := by
    intro z hz
    exact Or.inl (by linarith [hrez z hz])
  apply (convex_ball (Complex.exp x) 8).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z hz => (Complex.hasDerivAt_log (hslit z hz)).hasDerivWithinAt)
  intro z hz
  change ‖z⁻¹‖ ≤ (1 / 2 : ℝ)
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) ((hrez z hz).trans (Complex.re_le_norm z))

/-- The principal logarithm sends the radius-eight disk about `exp x` into the
radius-eight disk about `x`, for real `x ≥ 10`. -/
theorem log_maps_real_ball {x : ℂ} (hx : x.im = 0) (hx10 : 10 ≤ x.re) :
    MapsTo Complex.log (ball (Complex.exp x) 8) (ball x 8) := by
  intro z hz
  have h := (log_lipschitz_real_ball hx hx10).norm_sub_le hz
    (mem_ball_self (by norm_num : (0 : ℝ) < 8))
  have heq : Complex.log (Complex.exp x) = x :=
    Complex.log_exp (by rw [hx]; linarith [Real.pi_pos]) (by rw [hx]; exact Real.pi_pos.le)
  rw [heq] at h
  have hz' : ‖z - Complex.exp x‖ < 8 := by simpa [mem_ball, dist_eq_norm] using hz
  rw [mem_ball, dist_eq_norm]
  norm_num at h
  linarith

/-- Principal logarithms pull disks back along a far right real orbit. -/
theorem logIterate_real_ball {x : ℂ} (hx : x.im = 0) (hx10 : 10 ≤ x.re) (n : ℕ) :
    logIterate n (expIterate n x) = x ∧
    MapsTo (logIterate n) (ball (expIterate n x) 8) (ball x 8) ∧
    LipschitzOnWith ((1 / 2 : ℝ≥0) ^ n) (logIterate n) (ball (expIterate n x) 8) ∧
    ∀ z ∈ ball (expIterate n x) 8, expIterate n (logIterate n z) = z := by
  -- Each principal logarithm stays in the preceding real-centred disk and halves distances.
  induction n with
  | zero =>
      refine ⟨rfl, fun z hz => hz, ?_, fun z _ => rfl⟩
      simpa using (LipschitzWith.id.lipschitzOnWith : LipschitzOnWith 1 id (ball x 8))
  | succ n ih =>
      have hyn := (expIterate_real_orbit hx n).1
      have hy10 : 10 ≤ (expIterate n x).re := by
        linarith [(expIterate_real_orbit hx n).2, Nat.cast_nonneg (α := ℝ) n]
      have hmaps := log_maps_real_ball hyn hy10
      have hlip := log_lipschitz_real_ball hyn hy10
      have hlog : Complex.log (expIterate (n + 1) x) = expIterate n x := by
        rw [expIterate_succ]
        exact Complex.log_exp (by rw [hyn]; linarith [Real.pi_pos])
          (by rw [hyn]; exact Real.pi_pos.le)
      have hli : logIterate (n + 1) = logIterate n ∘ Complex.log :=
        Function.iterate_succ Complex.log n
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hli, comp_apply, hlog, ih.1]
      · simpa only [expIterate_succ, hli] using ih.2.1.comp hmaps
      · simpa only [expIterate_succ, hli, pow_succ] using ih.2.2.1.comp hlip hmaps
      · intro z hz
        have hzin := hmaps (by simpa only [expIterate_succ] using hz)
        have hz0 : z ≠ 0 := by
          intro heq
          subst z
          have hz' : ‖expIterate (n + 1) x‖ < 8 := by simpa [mem_ball, dist_eq_norm] using hz
          have hreal := (expIterate_real_orbit hx (n + 1)).2
          have hnorm := Complex.re_le_norm (expIterate (n + 1) x)
          linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
        rw [hli, comp_apply, expIterate_succ, ih.2.2.2 _ hzin, Complex.exp_log hz0]

/-- The principal logarithm is `1`-Lipschitz on the closed half-plane `Im z ≥ 1`. -/
theorem log_lipschitz_upper :
    LipschitzOnWith 1 Complex.log {z : ℂ | 1 ≤ z.im} := by
  apply (convex_halfSpace_im_ge 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z hz => (Complex.hasDerivAt_log (Or.inr (by
      have hz' : 1 ≤ z.im := hz
      linarith : z.im ≠ 0))).hasDerivWithinAt)
  intro z hz
  change ‖z⁻¹‖ ≤ (1 : ℝ)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (hz.trans (Complex.im_le_norm z))

/-- The closing step in Lemma 6.2. A bounded branch of logarithm can be translated
vertically and logged again into any radius-eight disk sufficiently far to the right. -/
theorem exists_closing_inverse {D : Set ℂ} {a : ℂ} {L : ℂ → ℂ} {C : ℝ≥0}
    (hL : LipschitzOnWith C L D)
    (hclose : ∀ z ∈ D, ‖L z - L a‖ ≤ 1)
    (hinv : ∀ z ∈ D, Complex.exp (L z) = z) :
    ∃ ρ : ℝ, ∀ x : ℝ, ρ ≤ x → ∃ ψ : ℂ → ℂ,
      LipschitzOnWith C ψ D ∧ MapsTo ψ D (ball (x : ℂ) 8) ∧
      ∀ z ∈ D, expIterate 2 (ψ z) = z := by
  refine ⟨|(L a).re| + 2 * Real.pi + 4, fun x hx => ?_⟩
  -- A single integer translation works uniformly for the whole bounded logarithm branch.
  let k : ℤ := ⌈(2 * Real.exp x - (L a).im) / (2 * Real.pi)⌉
  let T : ℂ → ℂ := fun z => L z + (k : ℂ) * (2 * Real.pi * Complex.I)
  have hp : 0 < 2 * Real.pi := by positivity
  have hxexp : 1 ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x, abs_nonneg (L a).re, Real.pi_pos]
  have him : ∀ z, (T z).im = (L z).im + (k : ℝ) * (2 * Real.pi) := by
    intro z
    simp [T, Complex.mul_im, Complex.mul_re]
  have hre : ∀ z, (T z).re = (L z).re := by intro z; simp [T]
  have hklo : 2 * Real.exp x - (L a).im ≤ (k : ℝ) * (2 * Real.pi) :=
    (div_le_iff₀ hp).mp (Int.le_ceil _)
  have hkhi : (k : ℝ) * (2 * Real.pi) < 2 * Real.exp x - (L a).im + 2 * Real.pi := by
    have h := mul_lt_mul_of_pos_right
      (Int.ceil_lt_add_one ((2 * Real.exp x - (L a).im) / (2 * Real.pi))) hp
    simpa only [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul] using h
  -- The translated branch stays high in the upper half-plane, where log is 1-Lipschitz.
  have htlo : ∀ z ∈ D, Real.exp x ≤ (T z).im := by
    intro z hz
    have h := (Complex.abs_im_le_norm (L z - L a)).trans (hclose z hz)
    simp only [Complex.sub_im] at h
    rw [him]
    linarith [(abs_le.mp h).1]
  have hthi : ∀ z ∈ D, (T z).im < 2 * Real.exp x + 2 * Real.pi + 1 := by
    intro z hz
    have h := (Complex.abs_im_le_norm (L z - L a)).trans (hclose z hz)
    simp only [Complex.sub_im] at h
    rw [him]
    linarith [(abs_le.mp h).2]
  have htre : ∀ z ∈ D, |(T z).re| ≤ |(L a).re| + 1 := by
    intro z hz
    rw [hre]
    have h := (Complex.abs_re_le_norm (L z - L a)).trans (hclose z hz)
    simp only [Complex.sub_re] at h
    calc |(L z).re| = |((L z).re - (L a).re) + (L a).re| := by congr 1; ring
      _ ≤ |(L z).re - (L a).re| + |(L a).re| := by
        simpa only [Real.norm_eq_abs] using norm_add_le ((L z).re - (L a).re) (L a).re
      _ ≤ _ := by linarith
  have htpos : ∀ z ∈ D, 0 < (T z).im := fun z hz => (Real.exp_pos x).trans_le (htlo z hz)
  have htne : ∀ z ∈ D, T z ≠ 0 := by
    intro z hz heq
    have := htpos z hz
    simp [heq] at this
  have hTlip : LipschitzOnWith C T D := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro z hz w hw
    simpa [T] using hL.norm_sub_le hz hw
  -- The resulting branch has a uniform Lipschitz bound and is a right inverse of exp squared.
  refine ⟨Complex.log ∘ T, ?_, ?_, ?_⟩
  · simpa using log_lipschitz_upper.comp hTlip (fun z hz => hxexp.trans (htlo z hz))
  · intro z hz
    have hnlo : Real.exp x ≤ ‖T z‖ := (htlo z hz).trans (Complex.im_le_norm _)
    have hnhi : ‖T z‖ ≤ Real.exp (x + 2) := by
      have h := Complex.norm_le_abs_re_add_abs_im (T z)
      rw [abs_of_pos (htpos z hz)] at h
      have hmx : |(L a).re| + 2 * Real.pi + 2 ≤ Real.exp x := by
        linarith [Real.add_one_le_exp x]
      have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
      rw [Real.exp_add]
      have hmul := mul_le_mul_of_nonneg_left hthree (Real.exp_pos x).le
      linarith [htre z hz, hthi z hz]
    have hlo : x ≤ Real.log ‖T z‖ := by simpa using Real.log_le_log (Real.exp_pos x) hnlo
    have hhi : Real.log ‖T z‖ ≤ x + 2 := by
      simpa using Real.log_le_log (norm_pos_iff.mpr (htne z hz)) hnhi
    rw [mem_ball, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (Complex.log (T z) - (x : ℂ))
    simp only [Complex.sub_re, Complex.log_re, Complex.ofReal_re,
      Complex.sub_im, Complex.log_im, Complex.ofReal_im, sub_zero] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)] at h
    dsimp only [comp_apply]
    linarith [Complex.abs_arg_le_pi (T z), Real.pi_lt_four]
  · intro z hz
    have hT : Complex.exp (T z) = z := by
      calc Complex.exp (T z) = Complex.exp (L z) :=
          Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩
        _ = z := hinv z hz
    simpa only [comp_apply, expIterate_succ, expIterate_zero,
      Complex.exp_log (htne z hz)] using hT

/-- A strictly contracting inverse branch produces a repelling fixed point. -/
theorem exists_repelling_fixedPoint_of_inverse
    {f h : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hlip : LipschitzOnWith (1 / 2) h (closedBall a r))
    (hmaps : MapsTo h (closedBall a r) (ball a (r / 2)))
    (hinv : ∀ z ∈ closedBall a r, f (h z) = z)
    (hf : Differentiable ℂ f) (hf0 : ∀ z, deriv f z ≠ 0) :
    ∃ p ∈ ball a r, f p = p ∧ 1 < ‖deriv f p‖ := by
  -- Apply Banach on the complete closed disk; the smaller image disk makes the fixed point
  -- interior.
  have hself : MapsTo h (closedBall a r) (closedBall a r) :=
    fun z hz => ball_subset_closedBall ((ball_subset_ball (by linarith)) (hmaps hz))
  have hcontract : ContractingWith (1 / 2) (hself.restrict h _ _) :=
    ⟨by norm_num, hlip.mapsToRestrict hself⟩
  obtain ⟨p, hp, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hself hcontract (mem_closedBall_self hr.le)
      (edist_ne_top a (h a))
  have hhp : h p = p := hfix
  have hpball : p ∈ ball a r := by
    have hh := hmaps hp
    rw [hhp] at hh
    exact (ball_subset_ball (by linarith)) hh
  -- At the interior fixed point the inverse identity can be differentiated.
  have hpnhds : closedBall a r ∈ 𝓝 p :=
    mem_of_superset (isOpen_ball.mem_nhds hpball) ball_subset_closedBall
  have hcont : ContinuousAt h p := (hlip.continuousOn p hp).continuousAt hpnhds
  have hright : ∀ᶠ z in 𝓝 p, f (h z) = z :=
    Filter.mem_of_superset hpnhds (fun z hz => hinv z hz)
  have hd : HasDerivAt h (deriv f p)⁻¹ p :=
    HasDerivAt.of_local_left_inverse hcont
      (by rw [hhp]; exact (hf p).hasDerivAt) (hf0 p) hright
  -- The inverse derivative has norm at most 1/2, so the forward multiplier has norm at least two.
  have hbound := hd.le_of_lipschitzOn hpnhds hlip
  rw [norm_inv] at hbound
  have hpos : 0 < ‖deriv f p‖ := norm_pos_iff.mpr (hf0 p)
  rw [← one_div] at hbound
  have hmul := (div_le_iff₀ hpos).mp hbound
  refine ⟨p, hpball, ?_, ?_⟩
  · simpa only [hhp] using hinv p hp
  · norm_num at hmul
    linarith

/-- A uniform family of two-step inverse branches on a small closed disk. -/
theorem closing_inverse_on_small_ball {a : ℂ} (ha : a ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ ∃ C : ℝ≥0, ∃ ρ : ℝ,
      ∀ x : ℝ, ρ ≤ x → ∃ ψ : ℂ → ℂ,
        LipschitzOnWith C ψ (closedBall a r) ∧
        MapsTo ψ (closedBall a r) (ball (x : ℂ) 8) ∧
        ∀ z ∈ closedBall a r, expIterate 2 (ψ z) = z := by
  have hsd : HasStrictDerivAt Complex.exp (deriv Complex.exp (Complex.log a)) (Complex.log a) := by
    simpa only [Complex.deriv_exp] using Complex.hasStrictDerivAt_exp (Complex.log a)
  obtain ⟨L, C, s, hs, _, hL, hinv⟩ := exists_lipschitz_local_inverse hsd
    (by simpa only [Complex.deriv_exp] using Complex.exp_ne_zero (Complex.log a))
  rw [Complex.exp_log ha] at hL hinv
  -- Shrink the source disk so the chosen logarithm branch varies by at most one.
  let r : ℝ := min ε (min (s / 2) (1 / ((C : ℝ) + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r ≤ ε := min_le_left _ _
  have hrs : r ≤ s / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r * ((C : ℝ) + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  have hsub : closedBall a r ⊆ ball a s :=
    closedBall_subset_ball (by linarith)
  have hsmall : ∀ z ∈ closedBall a r, ‖L z - L a‖ ≤ 1 := by
    intro z hz
    have h := hL.norm_sub_le (hsub hz) (mem_ball_self hs)
    have hz' : ‖z - a‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
    have hh := mul_le_mul_of_nonneg_left hz' C.coe_nonneg
    nlinarith
  obtain ⟨ρ, hρ⟩ := exists_closing_inverse
    (hL.mono hsub) hsmall (fun z hz => hinv z (hsub hz))
  exact ⟨r, hr, hrε, C, ρ, hρ⟩

/-- A point mapping to a far right real point is approximated by repelling periodic points. -/
theorem exists_repelling_near_real_preimage {a : ℂ} (ha : a ≠ 0)
    {m : ℕ} (hm : expIterate m a = 10) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ ball a ε, ∃ N : ℕ,
      0 < N ∧ expIterate N p = p ∧ 1 < ‖deriv (expIterate N) p‖ := by
  obtain ⟨r, hr, hrε, C, ρ, hclosing⟩ := closing_inverse_on_small_ball ha hε
  have hsd : HasStrictDerivAt (expIterate m) (deriv (expIterate m) a) a :=
    ((differentiable_expIterate m).analyticAt a).hasStrictDerivAt
  obtain ⟨g, A, s, hs, hga, hglip, hginv⟩ :=
    exists_lipschitz_local_inverse hsd (deriv_expIterate_ne_zero m a)
  rw [hm] at hga hglip hginv
  -- The logarithmic contraction eventually dominates both fixed local Lipschitz constants.
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n * 8 < s := by
    have h := hlim.mul_const 8
    simp only [zero_mul] at h
    exact h.eventually (gt_mem_nhds hs)
  have hsmallA : ∀ᶠ n : ℕ in atTop, (A : ℝ) * ((1 / 2 : ℝ) ^ n * 8) < r / 2 := by
    have h := (hlim.mul_const 8).const_mul (A : ℝ)
    simp only [mul_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  have hsmallAC : ∀ᶠ n : ℕ in atTop, (A : ℝ) * (1 / 2 : ℝ) ^ n * (C : ℝ) < 1 / 2 := by
    have h := (hlim.const_mul (A : ℝ)).mul_const (C : ℝ)
    simp only [mul_zero, zero_mul] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hfar : ∀ᶠ n : ℕ in atTop, ρ ≤ (expIterate n (10 : ℂ)).re := by
    obtain ⟨d, hd⟩ := exists_nat_gt (ρ - 10)
    refine eventually_atTop.2 ⟨d, fun n hn => ?_⟩
    have hcast : (d : ℝ) ≤ n := by exact_mod_cast hn
    have h := (expIterate_real_orbit (p := (10 : ℂ)) (by norm_num) n).2
    norm_num at h
    linarith
  -- Choose one time satisfying all size, contraction and location requirements.
  obtain ⟨n, hnsmall, hnA, hnAC, hnfar⟩ := (hsmall.and (hsmallA.and (hsmallAC.and hfar))).exists
  obtain ⟨ψ, hψlip, hψmaps, hψinv⟩ := hclosing (expIterate n (10 : ℂ)).re hnfar
  have hnreal : (((expIterate n (10 : ℂ)).re : ℝ) : ℂ) = expIterate n (10 : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (expIterate_real_orbit (p := (10 : ℂ)) (by norm_num) n).1.symm
  rw [hnreal] at hψmaps
  obtain ⟨hlogcenter, hlogmaps, hloglip, hloginv⟩ :=
    logIterate_real_ball (x := (10 : ℂ)) (by norm_num) (by norm_num) n
  have hlogbound : ∀ z ∈ ball (expIterate n (10 : ℂ)) 8,
      ‖logIterate n z - 10‖ ≤ (1 / 2 : ℝ) ^ n * 8 := by
    intro z hz
    have h := hloglip.norm_sub_le hz (mem_ball_self (by norm_num : (0 : ℝ) < 8))
    rw [hlogcenter] at h
    have hz' : ‖z - expIterate n (10 : ℂ)‖ ≤ 8 := by
      exact le_of_lt (by simpa [mem_ball, dist_eq_norm] using hz)
    have h' : ‖logIterate n z - 10‖ ≤
        (1 / 2 : ℝ) ^ n * ‖z - expIterate n (10 : ℂ)‖ := by
      simpa using h
    exact h'.trans (mul_le_mul_of_nonneg_left hz' (by positivity))
  have hinto : MapsTo (logIterate n ∘ ψ) (closedBall a r) (ball (10 : ℂ) s) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    exact (hlogbound _ (hψmaps hz)).trans_lt hnsmall
  -- Return via two logarithms, n principal logarithms, and the local inverse of expIterate m.
  let H : ℂ → ℂ := g ∘ logIterate n ∘ ψ
  have hHlip : LipschitzOnWith (1 / 2) H (closedBall a r) := by
    have h := hglip.comp (hloglip.comp hψlip hψmaps) hinto
    apply h.weaken
    exact_mod_cast (show (A : ℝ) * ((1 / 2 : ℝ) ^ n * (C : ℝ)) ≤ 1 / 2 by nlinarith [hnAC])
  have hHmaps : MapsTo H (closedBall a r) (ball a (r / 2)) := by
    intro z hz
    have h := hglip.norm_sub_le (hinto hz) (mem_ball_self hs)
    rw [hga] at h
    rw [mem_ball, dist_eq_norm]
    change ‖g (logIterate n (ψ z)) - a‖ < r / 2
    exact (h.trans (mul_le_mul_of_nonneg_left (hlogbound _ (hψmaps hz)) A.coe_nonneg)).trans_lt hnA
  -- Reverse those three inverse steps to identify the forward return time as 2 + n + m.
  have hHinv : ∀ z ∈ closedBall a r, expIterate (2 + n + m) (H z) = z := by
    intro z hz
    calc
      expIterate (2 + n + m) (H z) =
          expIterate 2 (expIterate n (expIterate m (g (logIterate n (ψ z))))) := by
        dsimp [H]
        exact (Function.iterate_add_apply exponentialMap (2 + n) m _).trans
          (Function.iterate_add_apply exponentialMap 2 n _)
      _ = z := by rw [hginv (logIterate n (ψ z)) (hinto hz), hloginv _ (hψmaps hz), hψinv z hz]
  obtain ⟨p, hp, hperiod, hrepel⟩ :=
    exists_repelling_fixedPoint_of_inverse hr hHlip hHmaps hHinv
      (differentiable_expIterate _) (deriv_expIterate_ne_zero _)
  exact ⟨p, (ball_subset_ball hrε) hp, 2 + n + m, by omega, hperiod, hrepel⟩

/-- A nonempty open subset of the plane contains a nonzero point. -/
theorem exists_nonzero_mem_open {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U, z ≠ 0 := by
  obtain ⟨z, hz⟩ := hUne
  by_cases hzero : z = 0
  · subst z
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU 0 hz
    refine ⟨(r / 2 : ℝ), hsub ?_, ?_⟩
    · simpa [mem_ball, dist_eq_norm, abs_of_pos hr] using
        (show r / 2 < r by linarith)
    · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (half_pos hr))
  · exact ⟨z, hz, hzero⟩

/-- **Theorem 6.1.** Every nonempty open set contains a repelling periodic point. -/
theorem exists_repelling_periodic_mem_open {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, ∃ n : ℕ,
      0 < n ∧ expIterate n p = p ∧ 1 < ‖deriv (expIterate n) p‖ := by
  obtain ⟨b, hb, hb0⟩ := exists_nonzero_mem_open hU hUne
  have hVopen : IsOpen (U \ {0}) := hU.sdiff isClosed_singleton
  have hVne : (U \ {0}).Nonempty := ⟨b, hb, by simpa using hb0⟩
  -- The covering theorem supplies a preimage of 10 inside the chosen open set.
  obtain ⟨m, _, a, ha, hm⟩ := exists_iterate_eq_nonzero hVopen hVne
    (w := 10) (by norm_num)
  have ha0 : a ≠ 0 := by simpa using ha.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU a ha.1
  obtain ⟨p, hp, n, hn, hperiod, hrepel⟩ := exists_repelling_near_real_preimage ha0 hm hε
  exact ⟨p, hball hp, n, hn, hperiod, hrepel⟩

/-- Repelling periodic points of the exponential are dense in the complex plane. -/
theorem dense_repelling_periodic_points :
    Dense {p : ℂ | ∃ n : ℕ,
      0 < n ∧ expIterate n p = p ∧ 1 < ‖deriv (expIterate n) p‖} := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨p, hp, hperiod⟩ := exists_repelling_periodic_mem_open hU hUne
  exact ⟨p, hp, hperiod⟩

/-- Periodic points of the exponential are dense in the plane. -/
theorem dense_periodic_points :
    Dense {p : ℂ | ∃ n : ℕ, 0 < n ∧ expIterate n p = p} := by
  apply dense_repelling_periodic_points.mono
  rintro p ⟨n, hn, hperiod, _⟩
  exact ⟨n, hn, hperiod⟩

/-- The periodic-point benchmark using mathlib's standard `periodicPts` set. -/
theorem dense_periodicPts_exp : Dense (Function.periodicPts Complex.exp) := by
  apply dense_periodic_points.mono
  rintro p ⟨n, hn, hp⟩
  exact Function.mk_mem_periodicPts hn hp

end

end ExponentialJuliaSetMisiurewicz
