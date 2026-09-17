/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import LeanPool.ExpChaotic.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Derivative growth and quantitative open mapping

Lemmas 1–3 in the proof architecture adapted from John Harrison's HOL Light formalization.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-! ## The six lemmas in the HOL Light proof -/

/-- Derivative recursion for the iterates of the exponential. -/
theorem deriv_expIterate_succ (n : ℕ) (z : ℂ) :
    deriv (expIterate (n + 1)) z =
      deriv (expIterate n) z *
        Complex.exp (expIterate n z) := by
  have h :
      HasDerivAt (Complex.exp ∘ expIterate n)
        (deriv (expIterate n) z *
          Complex.exp (expIterate n z)) z :=
    hasDerivAt_exp_comp
      ((differentiable_expIterate n).differentiableAt.hasDerivAt)
  have hfun :
      expIterate (n + 1) =
        Complex.exp ∘ expIterate n := by
    funext w
    exact expIterate_succ n w
  rw [hfun]
  exact h.deriv

/-- The imaginary part of an exponential is controlled by the imaginary
part of its argument and the norm of the exponential. -/
theorem abs_im_exp_le (w : ℂ) :
    |(Complex.exp w).im| ≤
      |w.im| * ‖Complex.exp w‖ := by
  rw [Complex.exp_im, Complex.norm_exp]
  rw [abs_mul, abs_of_pos (Real.exp_pos w.re)]
  have hsin : |Real.sin w.im| ≤ |w.im| := by
    exact Real.abs_sin_le_abs
  nlinarith [Real.exp_pos w.re, hsin]

/-- The absolute value of the imaginary part is at most the complex norm. -/
theorem abs_im_le_norm_aux (w : ℂ) :
    |w.im| ≤ ‖w‖ := by
  exact Complex.abs_im_le_norm w

/-- **Lemma 1.** The imaginary part of an exponential iterate is bounded by the norm of
its derivative. HOL Light: `LEMMA_1`. -/
theorem lemma1_im_le_norm_deriv {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    |(expIterate n z).im| ≤ ‖deriv (expIterate n) z‖ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero =>
      rw [deriv_expIterate_succ]
      simp only [add_zero, iterate_one, iterate_zero, deriv_id', expIterate_zero, one_mul]
      exact Complex.abs_im_le_norm (Complex.exp z)
  | succ m ih =>
      have hindex : 1 + (m + 1) = (1 + m) + 1 := by
        omega
      rw [hindex, deriv_expIterate_succ, norm_mul]
      calc
        |(expIterate ((1 + m) + 1) z).im|
            =
            |(Complex.exp (expIterate (1 + m) z)).im| := by
              rw [expIterate_succ]
        _ ≤ |(expIterate (1 + m) z).im| *
              ‖Complex.exp (expIterate (1 + m) z)‖ :=
              abs_im_exp_le (expIterate (1 + m) z)
        _ ≤ ‖deriv (expIterate (1 + m)) z‖ *
              ‖Complex.exp (expIterate (1 + m) z)‖ := by
              exact mul_le_mul_of_nonneg_right (ih (by omega)) (norm_nonneg _)

/-- **Lemma 2(a).** In the central strip, the real part increases by at least
`1 - log 2`. HOL Light: `LEMMA_2a`. -/
theorem lemma2a_real_growth {z : ℂ} (hz : z ∈ centralStrip) :
    z.re + (1 - Real.log 2) ≤ (Complex.exp z).re := by
  change |z.im| ≤ Real.pi / 3 at hz
  rw [Complex.exp_re]
  have him_nonneg : 0 ≤ |z.im| := abs_nonneg z.im
  have him_le_pi : |z.im| ≤ Real.pi := by
    have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    nlinarith
  have hcos :
      (1 / 2 : ℝ) ≤ Real.cos z.im := by
    rw [← Real.cos_abs]
    have hthird_nonneg : 0 ≤ Real.pi / 3 := by
      positivity
    have hthird_le_pi : Real.pi / 3 ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have habs_mem :
        |z.im| ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · exact abs_nonneg z.im
      · exact le_trans hz hthird_le_pi
    have hthird_mem :
        Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
      exact ⟨hthird_nonneg, hthird_le_pi⟩
    have hanti :
        AntitoneOn Real.cos (Set.Icc (0 : ℝ) Real.pi) :=
      Real.strictAntiOn_cos.antitoneOn
    have hmono :
        Real.cos (Real.pi / 3) ≤ Real.cos |z.im| :=
      hanti habs_mem hthird_mem hz
    simpa [Real.cos_pi_div_three] using hmono
  have hexp :
      z.re + (1 - Real.log 2) ≤ Real.exp z.re / 2 := by
    have h :=
      Real.add_one_le_exp (z.re - Real.log 2)
    have hlog : Real.exp (Real.log 2) = 2 := by
      rw [Real.exp_log]
      norm_num
    rw [Real.exp_sub, hlog] at h
    nlinarith
  calc
    z.re + (1 - Real.log 2)
        ≤ Real.exp z.re / 2 := hexp
    _ ≤ Real.exp z.re * Real.cos z.im := by
          nlinarith [Real.exp_pos z.re]

/-- **Lemma 2(b).** Every non-real orbit eventually leaves the central strip.
HOL Light: `LEMMA_2b`. -/
theorem lemma2b_eventually_leaves_strip {z : ℂ} (hz : ¬ OnRealAxis z) :
    ∃ n : ℕ, expIterate n z ∉ centralStrip := by
  by_contra hcontra
  push Not at hcontra
  have hstrip : ∀ n : ℕ, |(expIterate n z).im| ≤ Real.pi / 3 := fun n => hcontra n
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  -- Harrison's key estimate: |Im f^{n+1}| ≥ (2/5) e^{Re f^n} |Im f^n|
  have key : ∀ n : ℕ,
      (2 / 5 : ℝ) * Real.exp ((expIterate n z).re) * |(expIterate n z).im|
        ≤ |(expIterate (n + 1) z).im| := by
    intro n
    have hb : |(expIterate n z).im| ≤ Real.pi / 2 := by
      have := hstrip n; linarith
    have hsin : 2 / Real.pi * |(expIterate n z).im|
        ≤ |Real.sin ((expIterate n z).im)| := Real.mul_abs_le_abs_sin hb
    have hE : (0 : ℝ) < Real.exp ((expIterate n z).re) := Real.exp_pos _
    have h25 : (2 / 5 : ℝ) ≤ 2 / Real.pi := by
      rw [div_le_div_iff₀ (by norm_num) hpi]; linarith
    have heq : |(expIterate (n + 1) z).im|
        = Real.exp ((expIterate n z).re) * |Real.sin ((expIterate n z).im)| := by
      rw [expIterate_succ, Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [heq]
    calc (2 / 5 : ℝ) * Real.exp ((expIterate n z).re) * |(expIterate n z).im|
        = Real.exp ((expIterate n z).re) * ((2 / 5 : ℝ) * |(expIterate n z).im|) := by ring
      _ ≤ Real.exp ((expIterate n z).re) * (2 / Real.pi * |(expIterate n z).im|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h25 (abs_nonneg _)) hE.le
      _ ≤ Real.exp ((expIterate n z).re) * |Real.sin ((expIterate n z).im)| :=
            mul_le_mul_of_nonneg_left hsin hE.le
  -- the orbit never becomes real
  have hne : ∀ n : ℕ, (expIterate n z).im ≠ 0 := by
    intro n
    induction n with
    | zero => simpa [expIterate, OnRealAxis] using hz
    | succ n ih =>
        have hpos : 0 < |(expIterate n z).im| := abs_pos.mpr ih
        have hE : (0 : ℝ) < Real.exp ((expIterate n z).re) := Real.exp_pos _
        have hlt : 0 < |(expIterate (n + 1) z).im| :=
          lt_of_lt_of_le (by positivity) (key n)
        intro hc
        rw [hc] at hlt
        simp at hlt
  -- Lemma 2a iterated: the real part grows linearly
  have hre : ∀ n : ℕ, z.re + n * (1 - Real.log 2) ≤ (expIterate n z).re := by
    intro n
    induction n with
    | zero => simp [expIterate]
    | succ n ih =>
        have h2a := lemma2a_real_growth (hcontra n)
        rw [← expIterate_succ] at h2a
        push_cast
        linarith
  -- Linear real growth eventually makes the imaginary-part expansion factor exceed two.
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlogpos : (0 : ℝ) < 1 - Real.log 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log 5 - z.re) / (1 - Real.log 2))
  have hNre : ∀ n : ℕ, N ≤ n → Real.log 5 ≤ (expIterate n z).re := by
    intro n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (Real.log 5 - z.re) / (1 - Real.log 2) < (n : ℝ) := lt_of_lt_of_le hN hcast
    rw [div_lt_iff₀ hlogpos] at h1
    have := hre n
    linarith
  -- past N the imaginary part at least doubles
  have hdouble : ∀ n : ℕ, N ≤ n →
      2 * |(expIterate n z).im| ≤ |(expIterate (n + 1) z).im| := by
    intro n hn
    have hexp : (5 : ℝ) ≤ Real.exp ((expIterate n z).re) := by
      have h := Real.exp_le_exp.mpr (hNre n hn)
      rwa [Real.exp_log (by norm_num)] at h
    have hk := key n
    nlinarith [abs_nonneg ((expIterate n z).im)]
  have hgeom : ∀ d : ℕ,
      2 ^ d * |(expIterate N z).im| ≤ |(expIterate (N + d) z).im| := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have hidx : N + (d + 1) = (N + d) + 1 := by omega
        have h := hdouble (N + d) (Nat.le_add_right N d)
        rw [hidx]
        calc (2 : ℝ) ^ (d + 1) * |(expIterate N z).im|
            = 2 * (2 ^ d * |(expIterate N z).im|) := by ring
          _ ≤ 2 * |(expIterate (N + d) z).im| := by linarith
          _ ≤ |(expIterate ((N + d) + 1) z).im| := h
  -- Geometric growth of a nonzero imaginary part contradicts the fixed strip height.
  have hposN : 0 < |(expIterate N z).im| := abs_pos.mpr (hne N)
  obtain ⟨d, hd⟩ :=
    pow_unbounded_of_one_lt (Real.pi / 3 / |(expIterate N z).im|) (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hposN] at hd
  have h2 := hgeom d
  have h3 := hstrip (N + d)
  linarith

/-- The image of an *open set* under an injective holomorphic map is open. -/
theorem isOpen_image_of_injOn
    {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hinj : Set.InjOn g U) :
    IsOpen (g '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, rfl⟩
  have hnhds : U ∈ 𝓝 z := hU.mem_nhds hz
  have hana : AnalyticAt ℂ g z := hg.analyticAt hnhds
  rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
  · exfalso
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hconst.and hnhds)
    have hmem : z + (δ / 2 : ℝ) ∈ ball z δ := by
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat, mem_ball, dist_self_add_left,
        Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
      rw [abs_of_pos (by linarith)]
      linarith
    obtain ⟨heq, hin⟩ := hsub hmem
    have hzz : z + (δ / 2 : ℝ) = z := hinj hin hz heq
    have hne : ((δ / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      linarith
    exact hne (by linear_combination hzz - (rfl : z = z))
  · exact hmap (Filter.image_mem_map hnhds)

/-- The image of the ball under an injective holomorphic map is open. -/
theorem lemma3_isOpen_image
    {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r)) :
    IsOpen (g '' ball b r) :=
  isOpen_image_of_injOn isOpen_ball hg hinj

/-- The inverse of an injective holomorphic map with non-vanishing derivative is itself
complex differentiable, with the reciprocal derivative. This is the Lean analogue of HOL
Light's `HOLOMORPHIC_ON_INVERSE`, which Mathlib does not currently provide. Continuity of the
inverse comes from the open mapping property, after which `HasDerivAt.of_local_left_inverse`
supplies the derivative. -/
theorem lemma3_hasDerivAt_invFunOn
    {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r))
    (hne : ∀ z ∈ ball b r, deriv g z ≠ 0)
    {w : ℂ} (hw : w ∈ g '' ball b r) :
    HasDerivAt (Function.invFunOn g (ball b r))
      (deriv g (Function.invFunOn g (ball b r) w))⁻¹ w := by
  have hleft : ∀ u ∈ ball b r, Function.invFunOn g (ball b r) (g u) = u := by
    intro u hu
    have hex : ∃ a ∈ ball b r, g a = g u := ⟨u, hu, rfl⟩
    exact hinj (Function.invFunOn_mem hex) hu (Function.invFunOn_eq hex)
  obtain ⟨z, hz, rfl⟩ := hw
  have hhz : Function.invFunOn g (ball b r) (g z) = z := hleft z hz
  have hcont : ContinuousAt (Function.invFunOn g (ball b r)) (g z) := by
    rw [continuousAt_def]
    intro V hV
    rw [hhz] at hV
    obtain ⟨W, hWsub, hWopen, hzW⟩ := _root_.mem_nhds_iff.mp hV
    have hUopen : IsOpen (W ∩ ball b r) := hWopen.inter isOpen_ball
    have hUsub : W ∩ ball b r ⊆ ball b r := Set.inter_subset_right
    have hgU : IsOpen (g '' (W ∩ ball b r)) :=
      isOpen_image_of_injOn hUopen (hg.mono hUsub) (hinj.mono hUsub)
    refine Filter.mem_of_superset (hgU.mem_nhds ⟨z, ⟨hzW, hz⟩, rfl⟩) ?_
    rintro y ⟨u, hu, rfl⟩
    have hfix : Function.invFunOn g (ball b r) (g u) = u := hleft u hu.2
    rw [Set.mem_preimage, hfix]
    exact hWsub hu.1
  have hd : HasDerivAt g (deriv g z) z :=
    (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hfg : ∀ᶠ y in 𝓝 (g z), g (Function.invFunOn g (ball b r) y) = y := by
    filter_upwards [(lemma3_isOpen_image hg hinj).mem_nhds ⟨z, hz, rfl⟩] with y hy
    exact Function.invFunOn_eq hy
  rw [hhz]
  exact HasDerivAt.of_local_left_inverse hcont (by rw [hhz]; exact hd) (hne z hz) hfg

/-- **Lemma 3.** Quantitative open mapping estimate, following Harrison's `LEMMA_3`.
The proof uses his closest-point device: `t` is the distance from `g b` to the complement of
the image, so `ball (g b) t` lies in the image and is convex, which is exactly what the mean
value inequality needs. -/
theorem lemma3_ball_image_of_deriv_lower_bound
    {g : ℂ → ℂ} {b : ℂ} {r m : ℝ}
    (hr : 0 < r) (hm : 0 ≤ m)
    (hgc : ContinuousOn g (closedBall b r))
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r))
    (hderiv : ∀ z ∈ ball b r, m ≤ ‖deriv g z‖) :
    ball (g b) (r * m) ⊆ g '' ball b r := by
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · rw [← hm0, mul_zero, Metric.ball_zero]
    exact Set.empty_subset _
  set A : Set ℂ := g '' ball b r with hA
  set h : ℂ → ℂ := Function.invFunOn g (ball b r) with hh
  have hne : ∀ z ∈ ball b r, deriv g z ≠ 0 := by
    intro z hz hcontra
    have := hderiv z hz
    rw [hcontra, norm_zero] at this
    linarith
  have hAopen : IsOpen A := lemma3_isOpen_image hg hinj
  have hbmem : g b ∈ A := ⟨b, Metric.mem_ball_self hr, rfl⟩
  have hhb : h (g b) = b := by
    have hex : ∃ a ∈ ball b r, g a = g b := ⟨b, Metric.mem_ball_self hr, rfl⟩
    exact hinj (Function.invFunOn_mem hex) (Metric.mem_ball_self hr) (Function.invFunOn_eq hex)
  -- the complement of the image is non-empty, because `g` is bounded on the closed ball
  have hAcne : (Aᶜ).Nonempty := by
    have hcomp : IsCompact (g '' closedBall b r) :=
      (isCompact_closedBall b r).image_of_continuousOn hgc
    obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall (g b)
    refine ⟨g b + ((|R| + 1 : ℝ) : ℂ), ?_⟩
    intro hmem
    have hsub : A ⊆ g '' closedBall b r :=
      Set.image_mono Metric.ball_subset_closedBall
    have := hR (hsub hmem)
    rw [Metric.mem_closedBall] at this
    simp only [dist_self_add_left, Complex.norm_real, Real.norm_eq_abs] at this
    rw [abs_of_pos (by positivity)] at this
    cases abs_cases R with
    | inl hc => linarith [hc.1]
    | inr hc => linarith [hc.1]
  have hAcclosed : IsClosed (Aᶜ) := hAopen.isClosed_compl
  set t : ℝ := Metric.infDist (g b) (Aᶜ) with hT
  have ht : 0 < t := by
    refine (Metric.infDist_pos_iff_notMem_closure hAcne).mp ?_
    rw [hAcclosed.closure_eq]
    simpa using hbmem
  have hballsub : ball (g b) t ⊆ A := by
    intro w hw
    by_contra hwA
    have hle : t ≤ dist (g b) w := Metric.infDist_le_dist_of_mem hwA
    rw [Metric.mem_ball, dist_comm] at hw
    linarith
  -- if the closest complement point is far enough away we are done
  by_cases hcase : r * m ≤ t
  · exact fun w hw => hballsub (Metric.ball_subset_ball hcase hw)
  -- otherwise derive a contradiction
  push Not at hcase
  exfalso
  obtain ⟨c, hcA, hcdist⟩ := hAcclosed.exists_infDist_eq_dist hAcne (g b)
  -- the inverse is `1/m`-Lipschitz on the convex set `ball (g b) t`
  have hlip : ∀ w ∈ ball (g b) t, dist (h w) b ≤ dist w (g b) / m := by
    intro w hw
    have hder : ∀ v ∈ ball (g b) t,
        HasFDerivWithinAt h
          (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g (h v))⁻¹)
          (ball (g b) t) v := fun v hv =>
      ((lemma3_hasDerivAt_invFunOn hg hinj hne (hballsub hv)).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ v ∈ ball (g b) t,
        ‖ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (deriv g (h v))⁻¹‖ ≤ 1 / m := by
      intro v hv
      have hmem : h v ∈ ball b r := Function.invFunOn_mem (hballsub hv)
      have hb := hderiv _ hmem
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_inv, norm_one, one_mul, one_div]
      gcongr
    have := (convex_ball (g b) t).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hder hbound (Metric.mem_ball_self ht) hw
    rw [hhb] at this
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖h w - b‖ ≤ 1 / m * ‖w - g b‖ := this
      _ = ‖w - g b‖ / m := by ring
  -- `c` is a limit of image points inside `ball (g b) t`
  have hcclosure : c ∈ closure (ball (g b) t) := by
    rw [closure_ball _ (ne_of_gt ht)]
    rw [Metric.mem_closedBall, dist_comm]
    exact le_of_eq hcdist.symm
  obtain ⟨w, hwmem, hwlim⟩ := mem_closure_iff_seq_limit.mp hcclosure
  -- their preimages live in a compact sub-ball
  have hzmem : ∀ n, h (w n) ∈ closedBall b (t / m) := by
    intro n
    rw [Metric.mem_closedBall]
    have := hlip (w n) (hwmem n)
    have hd : dist (w n) (g b) < t := by simpa [Metric.mem_ball] using hwmem n
    calc dist (h (w n)) b ≤ dist (w n) (g b) / m := this
      _ ≤ t / m := by gcongr
  have hsub : closedBall b (t / m) ⊆ ball b r := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    have : t / m < r := by
      rw [div_lt_iff₀ hmpos]
      linarith [hcase]
    linarith
  obtain ⟨zstar, hzstar, φ, hφ, hlim⟩ :=
    (isCompact_closedBall b (t / m)).tendsto_subseq hzmem
  have hzstarmem : zstar ∈ ball b r := hsub hzstar
  -- the limit maps to `c`, contradicting `c ∉ A`
  have hgcont : ContinuousAt g zstar :=
    hg.continuousOn.continuousAt (isOpen_ball.mem_nhds hzstarmem)
  have hlim1 : Filter.Tendsto (fun n => g (h (w (φ n)))) Filter.atTop (𝓝 (g zstar)) :=
    hgcont.tendsto.comp hlim
  have heq : ∀ n, g (h (w (φ n))) = w (φ n) := fun n =>
    Function.invFunOn_eq (hballsub (hwmem (φ n)))
  have hlim2 : Filter.Tendsto (fun n => g (h (w (φ n)))) Filter.atTop (𝓝 c) := by
    simp only [heq]
    exact hwlim.comp hφ.tendsto_atTop
  have : g zstar = c := tendsto_nhds_unique hlim1 hlim2
  exact hcA ⟨zstar, hzstarmem, this⟩

end

end ExponentialJuliaSetMisiurewicz
