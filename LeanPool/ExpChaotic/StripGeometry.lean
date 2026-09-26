/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import LeanPool.ExpChaotic.Expansion
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.CompletePartialOrder

/-!
# Strip geometry and the negative real axis

Lemmas 4–5 combine expansion, connectedness, and explicit exponential geometry.

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

/-! ### Lemma 4 -/

/-- If an orbit point is real, all later orbit points are real. -/
theorem expIterate_im_eq_zero_of_le {z : ℂ} {n : ℕ} (h : (expIterate n z).im = 0) :
    ∀ m, n ≤ m → (expIterate m z).im = 0 := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have hidx : n + (d + 1) = (n + d) + 1 := by omega
      rw [hidx, expIterate_succ, Complex.exp_im, ih (by omega), Real.sin_zero, mul_zero]

/-- If the imaginary part of an orbit point is an integer multiple of `π`, the next point
is real. -/
theorem expIterate_im_succ_eq_zero_of_int {z : ℂ} {n : ℕ} {k : ℤ}
    (h : (expIterate n z).im = k * Real.pi) :
    (expIterate (n + 1) z).im = 0 := by
  rw [expIterate_succ, Complex.exp_im, h, Real.sin_int_mul_pi, mul_zero]

/-- Chain rule for iterates: `expIterate (a + b) = expIterate a ∘ expIterate b`. -/
theorem deriv_expIterate_add (a b : ℕ) (z : ℂ) :
    deriv (expIterate (a + b)) z
      = deriv (expIterate a) (expIterate b z) * deriv (expIterate b) z := by
  have hfun : expIterate (a + b) = expIterate a ∘ expIterate b := by
    funext w
    simp [expIterate, Function.iterate_add_apply]
  rw [hfun]
  exact ((((differentiable_expIterate a) (expIterate b z)).hasDerivAt).comp z
    (((differentiable_expIterate b) z).hasDerivAt)).deriv

/-! ### Strengthening: reaching the negative real axis

An orbit point whose imaginary part is an *odd* multiple of `π` has negative real image,
since `cos ((2m+1)π) = -1`. Getting an odd multiple needs an imaginary spread of `2π`
rather than `π`, which both branches of Lemma 4 in fact supply. -/

/-- Some forward image of `V` lands on the negative real axis. -/
@[expose]
def EventuallyMeetsNegativeRealAxis (V : Set ℂ) : Prop :=
  ∃ n : ℕ, ∃ z ∈ V, (expIterate n z).im = 0 ∧ (expIterate n z).re < 0

/-- An odd multiple of `π` in the imaginary part gives a negative real exponential. -/
theorem exp_neg_real_of_odd_mul_pi {z : ℂ} {k : ℤ} (hk : Odd k)
    (h : z.im = (k : ℝ) * Real.pi) :
    (Complex.exp z).im = 0 ∧ (Complex.exp z).re < 0 := by
  obtain ⟨m, hm⟩ := hk
  have hcast : (k : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi) + Real.pi := by
    rw [hm]; push_cast; ring
  constructor
  · rw [Complex.exp_im, h, Real.sin_int_mul_pi, mul_zero]
  · rw [Complex.exp_re, h, hcast, Real.cos_int_mul_two_pi_add_pi]
    nlinarith [Real.exp_pos z.re]

/-- Two distinct points with the same exponential have imaginary parts at least `2π` apart. -/
theorem two_pi_le_abs_im_sub_of_exp_eq {a b : ℂ}
    (h : Complex.exp a = Complex.exp b) (hne : a ≠ b) :
    2 * Real.pi ≤ |a.im - b.im| := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hkne : k ≠ 0 := by
    intro h0
    rw [h0] at hk
    simp only [Int.cast_zero, zero_mul, add_zero] at hk
    exact hne hk
  have him : a.im - b.im = (k : ℝ) * (2 * Real.pi) := by
    rw [hk]
    simp [Complex.add_im, Complex.mul_im, Complex.mul_re]
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs (by omega)
    have hcast : ((|k| : ℤ) : ℝ) = |(k : ℝ)| := by push_cast; ring
    calc (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hk1
      _ = |(k : ℝ)| := hcast
  nlinarith [Real.pi_pos]

/-- Two distinct points with the same exponential have imaginary parts at least `π` apart
(indeed `2π`). This is the non-injective branch of Harrison's argument. -/
theorem pi_le_abs_im_sub_of_exp_eq {a b : ℂ}
    (h : Complex.exp a = Complex.exp b) (hne : a ≠ b) :
    Real.pi ≤ |a.im - b.im| := by
  have hsep := two_pi_le_abs_im_sub_of_exp_eq h hne
  linarith [Real.pi_pos]

/-- If infinitely many images miss the central strip, some image has imaginary diameter
at least `2π`. If every iterate is injective, derivative growth and Lemma 3 produce a
large image disk. Otherwise, the first failure of injectivity gives a pair separated
by a nonzero period of the exponential. -/
theorem lemma4_exists_im_far_apart_two_pi
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      2 * Real.pi ≤ |(expIterate n w).im - (expIterate n z).im| := by
  classical
  have hpi3 : (1 : ℝ) < Real.pi / 3 := by
    have := Real.pi_gt_three; linarith
  by_cases hall : ∀ n : ℕ, Set.InjOn (expIterate n) V
  · -- every iterate is injective on `V`
    set p : ℕ → Prop := fun n => Disjoint (expIterate n '' V) centralStrip with hp
    have hpinf : (Set.ofPred p).Infinite := hinf
    set r : ℕ → ℕ := fun n => Nat.nth p (n + 1) with hr
    have hrmem : ∀ n, Disjoint (expIterate (r n) '' V) centralStrip := fun n =>
      Nat.nth_mem_of_infinite hpinf (n + 1)
    have hrmono : ∀ n, r n < r (n + 1) := fun n =>
      (Nat.nth_lt_nth hpinf).mpr (by omega)
    have hrpos : ∀ n, 0 < r n := by
      intro n
      have h0 : Nat.nth p 0 < Nat.nth p (n + 1) := (Nat.nth_lt_nth hpinf).mpr (by omega)
      simp only [hr]
      omega
    have hout : ∀ n, ∀ z ∈ V, Real.pi / 3 < |(expIterate (r n) z).im| := by
      intro n z hz
      by_contra hc
      push Not at hc
      exact Set.disjoint_left.mp (hrmem n) ⟨z, hz, rfl⟩ hc
    -- geometric growth of the derivative along the chosen times
    have hgrow : ∀ n, ∀ z ∈ V, (Real.pi / 3) ^ n ≤ ‖deriv (expIterate (r n)) z‖ := by
      intro n
      induction n with
      | zero =>
          intro z hz
          have h1 := lemma1_im_le_norm_deriv (hrpos 0) z
          have h2 := hout 0 z hz
          simp only [pow_zero]
          linarith
      | succ n ih =>
          intro z hz
          have hlt := hrmono n
          have hk : 1 ≤ r (n + 1) - r n := by omega
          have hsplit : r (n + 1) = (r (n + 1) - r n) + r n := by omega
          have hchain : deriv (expIterate (r (n + 1))) z
              = deriv (expIterate (r (n + 1) - r n)) (expIterate (r n) z)
                * deriv (expIterate (r n)) z := by
            conv_lhs => rw [hsplit]
            exact deriv_expIterate_add _ _ z
          have hpt : expIterate (r (n + 1) - r n) (expIterate (r n) z)
              = expIterate (r (n + 1)) z := by
            conv_rhs => rw [hsplit]
            simp [expIterate, Function.iterate_add_apply]
          have h1 : Real.pi / 3
              ≤ ‖deriv (expIterate (r (n + 1) - r n)) (expIterate (r n) z)‖ := by
            have hl := lemma1_im_le_norm_deriv hk (expIterate (r n) z)
            rw [hpt] at hl
            have h2 := hout (n + 1) z hz
            linarith
          have h2 := ih z hz
          rw [hchain, norm_mul]
          have hnn : (0 : ℝ) ≤ (Real.pi / 3) ^ n := by positivity
          calc (Real.pi / 3) ^ (n + 1) = (Real.pi / 3) * (Real.pi / 3) ^ n := by ring
            _ ≤ ‖deriv (expIterate (r (n + 1) - r n)) (expIterate (r n) z)‖
                  * ‖deriv (expIterate (r n)) z‖ :=
                mul_le_mul h1 h2 hnn (norm_nonneg _)
    -- a ball inside `V`, blown up by Lemma 3
    obtain ⟨z0, hz0⟩ := hVne
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hVopen z0 hz0
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Real.pi / ρ) hpi3
    rw [div_lt_iff₀ hρ] at hn
    have hR : Real.pi < ρ * (Real.pi / 3) ^ n := by nlinarith
    have hinj3 : Set.InjOn (expIterate (r n)) (ball z0 ρ) := (hall (r n)).mono hball
    have himg := lemma3_ball_image_of_deriv_lower_bound hρ
      (by positivity : (0 : ℝ) ≤ (Real.pi / 3) ^ n)
      ((continuous_expIterate (r n)).continuousOn)
      ((differentiable_expIterate (r n)).differentiableOn)
      hinj3 (fun z hz => hgrow n z (hball hz))
    have hp1 : expIterate (r n) z0 + Complex.I * ((Real.pi : ℝ) : ℂ)
        ∈ ball (expIterate (r n) z0) (ρ * (Real.pi / 3) ^ n) := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      exact hR
    have hp2 : expIterate (r n) z0 - Complex.I * ((Real.pi : ℝ) : ℂ)
        ∈ ball (expIterate (r n) z0) (ρ * (Real.pi / 3) ^ n) := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      exact hR
    obtain ⟨w, hw, hwval⟩ := himg hp1
    obtain ⟨z, hz, hzval⟩ := himg hp2
    refine ⟨r n, w, z, hball hw, hball hz, ?_⟩
    rw [hwval, hzval]
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    rw [show (expIterate (r n) z0).im + Real.pi
        - ((expIterate (r n) z0).im - Real.pi) = 2 * Real.pi by ring]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  · -- some iterate fails to be injective on `V`
    push Not at hall
    have hex : ∃ n : ℕ, ¬ Set.InjOn (expIterate n) V := hall
    have hspec : ¬ Set.InjOn (expIterate (Nat.find hex)) V := Nat.find_spec hex
    have hzero : Nat.find hex ≠ 0 := by
      intro h0
      apply hspec
      rw [h0]
      intro a _ b _ hab
      simpa [expIterate] using hab
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hminj : Set.InjOn (expIterate m) V :=
      not_not.mp (Nat.find_min hex (by omega : m < Nat.find hex))
    rw [hm, Set.InjOn] at hspec
    push Not at hspec
    obtain ⟨w, hw, z, hz, heq, hne⟩ := hspec
    have hne' : expIterate m w ≠ expIterate m z := fun hc => hne (hminj hw hz hc)
    have hexp : Complex.exp (expIterate m w) = Complex.exp (expIterate m z) := by
      rw [← expIterate_succ, ← expIterate_succ]
      exact heq
    exact ⟨m, w, z, hw, hz, two_pi_le_abs_im_sub_of_exp_eq hexp hne'⟩

/-- Some forward image of `V` contains two points whose imaginary parts differ by at least `π`,
given that infinitely many forward images avoid the central strip. -/
theorem lemma4_exists_im_far_apart
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      Real.pi ≤ |(expIterate n w).im - (expIterate n z).im| := by
  obtain ⟨n, w, z, hw, hz, hsep⟩ := lemma4_exists_im_far_apart_two_pi hVopen hVne hinf
  exact ⟨n, w, z, hw, hz, le_trans (by linarith [Real.pi_pos]) hsep⟩

/-- With an imaginary spread of `2π`, the intermediate value theorem finds a point whose
imaginary part is an *odd* multiple of `π`: the interval contains two consecutive multiples,
and one of them is odd. -/
theorem lemma4_exists_im_odd_mul_pi
    {V : Set ℂ} (hVconn : IsConnected V)
    (h : ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      2 * Real.pi ≤ |(expIterate n w).im - (expIterate n z).im|) :
    ∃ (n : ℕ) (y : ℂ) (k : ℤ),
      y ∈ V ∧ Odd k ∧ (expIterate n y).im = (k : ℝ) * Real.pi := by
  obtain ⟨n, w, z, hw, hz, hfar⟩ := h
  set F : ℂ → ℝ := fun y => (expIterate n y).im with hF
  have hcont : ContinuousOn F V :=
    (Complex.continuous_im.comp (continuous_expIterate n)).continuousOn
  have hpi : 0 < Real.pi := Real.pi_pos
  have main : ∀ a b : ℂ, a ∈ V → b ∈ V → 2 * Real.pi ≤ F b - F a →
      ∃ (y : ℂ) (k : ℤ), y ∈ V ∧ Odd k ∧ F y = (k : ℝ) * Real.pi := by
    intro a b ha hb hgap
    have hdiv : F a / Real.pi * Real.pi = F a := div_mul_cancel₀ _ (ne_of_gt hpi)
    have hlow0 : F a ≤ ((⌈F a / Real.pi⌉ : ℤ) : ℝ) * Real.pi := by
      have hc := Int.le_ceil (F a / Real.pi)
      have h2 := mul_le_mul_of_nonneg_right hc (le_of_lt hpi)
      rwa [hdiv] at h2
    have hhigh0 : ((⌈F a / Real.pi⌉ : ℤ) : ℝ) * Real.pi < F a + Real.pi := by
      have hc := Int.ceil_lt_add_one (F a / Real.pi)
      have h2 := mul_lt_mul_of_pos_right hc hpi
      rw [add_mul, one_mul, hdiv] at h2
      exact h2
    obtain ⟨k, hkodd, hk1, hk2⟩ :
        ∃ k : ℤ, Odd k ∧ F a ≤ (k : ℝ) * Real.pi ∧ (k : ℝ) * Real.pi ≤ F b := by
      rcases Int.even_or_odd ⌈F a / Real.pi⌉ with hev | hodd
      · refine ⟨⌈F a / Real.pi⌉ + 1, Even.add_one hev, ?_, ?_⟩
        · push_cast
          nlinarith
        · push_cast
          nlinarith
      · exact ⟨⌈F a / Real.pi⌉, hodd, hlow0, by nlinarith⟩
    obtain ⟨y, hy, hyval⟩ :=
      hVconn.isPreconnected.intermediate_value ha hb hcont ⟨hk1, hk2⟩
    exact ⟨y, k, hy, hkodd, hyval⟩
  rcases le_total (F z) (F w) with hle | hle
  · have hgap : 2 * Real.pi ≤ F w - F z := by
      rw [abs_of_nonneg (by linarith)] at hfar; linarith
    obtain ⟨y, k, hy, hodd, hval⟩ := main z w hz hw hgap
    exact ⟨n, y, k, hy, hodd, hval⟩
  · have hgap : 2 * Real.pi ≤ F z - F w := by
      rw [abs_of_nonpos (by linarith)] at hfar; linarith
    obtain ⟨y, k, hy, hodd, hval⟩ := main w z hw hz hgap
    exact ⟨n, y, k, hy, hodd, hval⟩

/-- **Negative-axis strengthening, conditional form.** If infinitely many forward images of
`V` avoid the central strip, then some forward image meets the *negative* real axis. -/
theorem negativeRealAxis_of_infinite_strip_misses
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    EventuallyMeetsNegativeRealAxis V := by
  obtain ⟨n, y, k, hy, hodd, hval⟩ :=
    lemma4_exists_im_odd_mul_pi hVconn
      (lemma4_exists_im_far_apart_two_pi hVopen hVne hinf)
  obtain ⟨him, hre⟩ := exp_neg_real_of_odd_mul_pi hodd hval
  refine ⟨n + 1, y, hy, ?_, ?_⟩
  · rw [expIterate_succ]; exact him
  · rw [expIterate_succ]; exact hre

/-- From two far-apart imaginary parts, the intermediate value theorem on the connected set
`V` produces a point whose imaginary part is an exact integer multiple of `π`. -/
theorem lemma4_exists_im_int_mul_pi
    {V : Set ℂ} (hVconn : IsConnected V)
    (h : ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      Real.pi ≤ |(expIterate n w).im - (expIterate n z).im|) :
    ∃ (n : ℕ) (y : ℂ) (k : ℤ), y ∈ V ∧ (expIterate n y).im = k * Real.pi := by
  obtain ⟨n, w, z, hw, hz, hfar⟩ := h
  set F : ℂ → ℝ := fun y => (expIterate n y).im with hF
  have hcont : ContinuousOn F V :=
    (Complex.continuous_im.comp (continuous_expIterate n)).continuousOn
  have hpi : 0 < Real.pi := Real.pi_pos
  -- work with the pair in increasing order
  rcases le_total (F z) (F w) with hle | hle
  · have hgap : Real.pi ≤ F w - F z := by
      rw [abs_of_nonneg (by linarith)] at hfar; linarith
    set k : ℤ := ⌈F z / Real.pi⌉ with hk
    have hdiv : F z / Real.pi * Real.pi = F z := div_mul_cancel₀ _ (ne_of_gt hpi)
    have hlow : F z ≤ (k : ℝ) * Real.pi := by
      have hc := Int.le_ceil (F z / Real.pi)
      have h2 := mul_le_mul_of_nonneg_right hc (le_of_lt hpi)
      rwa [hdiv] at h2
    have hhigh : (k : ℝ) * Real.pi ≤ F w := by
      have hc := Int.ceil_lt_add_one (F z / Real.pi)
      have h2 := mul_lt_mul_of_pos_right hc hpi
      rw [add_mul, one_mul, hdiv] at h2
      linarith
    obtain ⟨y, hy, hyval⟩ := hVconn.isPreconnected.intermediate_value hz hw hcont
      ⟨hlow, hhigh⟩
    exact ⟨n, y, k, hy, hyval⟩
  · have hgap : Real.pi ≤ F z - F w := by
      rw [abs_of_nonpos (by linarith)] at hfar; linarith
    set k : ℤ := ⌈F w / Real.pi⌉ with hk
    have hdiv : F w / Real.pi * Real.pi = F w := div_mul_cancel₀ _ (ne_of_gt hpi)
    have hlow : F w ≤ (k : ℝ) * Real.pi := by
      have hc := Int.le_ceil (F w / Real.pi)
      have h2 := mul_le_mul_of_nonneg_right hc (le_of_lt hpi)
      rwa [hdiv] at h2
    have hhigh : (k : ℝ) * Real.pi ≤ F z := by
      have hc := Int.ceil_lt_add_one (F w / Real.pi)
      have h2 := mul_lt_mul_of_pos_right hc hpi
      rw [add_mul, one_mul, hdiv] at h2
      linarith
    obtain ⟨y, hy, hyval⟩ := hVconn.isPreconnected.intermediate_value hw hz hcont
      ⟨hlow, hhigh⟩
    exact ⟨n, y, k, hy, hyval⟩

/-- **Lemma 4.** Only finitely many forward images of a non-empty open connected set can
be disjoint from the central strip. HOL Light: `LEMMA_4`. -/
theorem lemma4_eventually_meets_centralStrip
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, (expIterate n '' V ∩ centralStrip).Nonempty := by
  by_contra hcon
  push Not at hcon
  have hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hempty⟩ := hcon (N + 1)
    have hmem : n ∈ {n : ℕ | Disjoint (expIterate n '' V) centralStrip} := by
      exact Set.disjoint_iff_inter_eq_empty.mpr hempty
    have := hN hmem
    omega
  obtain ⟨n, y, k, hy, hk⟩ :=
    lemma4_exists_im_int_mul_pi hVconn (lemma4_exists_im_far_apart hVopen hVne hinf)
  obtain ⟨M, hM, hempty⟩ := hcon (n + 1)
  have h0 : (expIterate (n + 1) y).im = 0 := expIterate_im_succ_eq_zero_of_int hk
  have hM0 : (expIterate M y).im = 0 := expIterate_im_eq_zero_of_le h0 M hM
  have hmem : expIterate M y ∈ expIterate M '' V ∩ centralStrip := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    change |(expIterate M y).im| ≤ Real.pi / 3
    rw [hM0, abs_zero]
    positivity
  rw [hempty] at hmem
  exact hmem

/-! ### Lemma 5 -/

/-- The frontier of the central strip consists of points with `|Im z| = π/3`. -/
theorem frontier_centralStrip_subset :
    frontier centralStrip ⊆ {z : ℂ | |z.im| = Real.pi / 3} := by
  have hcont : Continuous fun z : ℂ => |z.im| :=
    continuous_abs.comp Complex.continuous_im
  exact frontier_le_subset_eq hcont continuous_const

/-- **The geometric heart of Lemma 5.** On the frontier of the central strip, inside the
right half-plane, the exponential throws points clear of the wide strip: `|sin| = √3/2`
there, and `e^4 · √3/2` already exceeds `2π`. -/
theorem abs_im_exp_gt_two_pi_of_frontier
    {z : ℂ} (hfr : |z.im| = Real.pi / 3) (hre : 4 < z.re) :
    2 * Real.pi < |(Complex.exp z).im| := by
  have hsin : |Real.sin z.im| = Real.sqrt 3 / 2 := by
    rcases abs_eq (by positivity : (0 : ℝ) ≤ Real.pi / 3) |>.mp hfr with h | h
    · rw [h, abs_of_pos (by rw [Real.sin_pi_div_three]; positivity),
        Real.sin_pi_div_three]
    · rw [h, Real.sin_neg, abs_neg,
        abs_of_pos (by rw [Real.sin_pi_div_three]; positivity),
        Real.sin_pi_div_three]
  have hexp : Real.exp 4 ≤ Real.exp z.re := Real.exp_le_exp.mpr (le_of_lt hre)
  have he4 : (16 : ℝ) ≤ Real.exp 4 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hsq : (4 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith [h1]
    have hid : Real.exp 1 ^ 4 = (Real.exp 1 ^ 2) ^ 2 := by ring
    rw [h4, hid]
    nlinarith [hsq]
  have hsqrt : (1.7 : ℝ) < Real.sqrt 3 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 3]
  have hpi : Real.pi < 4 := Real.pi_lt_four
  rw [Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos _), hsin]
  nlinarith [Real.exp_pos z.re, Real.sqrt_nonneg 3]

/-- A connected set disjoint from the frontier of an open set, and meeting it, lies inside it.
This is the Lean form of HOL Light's `CONNECTED_INTER_FRONTIER`. -/
theorem IsPreconnected.subset_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hv : IsPreconnected v) (hu : IsOpen u)
    (hdisj : Disjoint (frontier u) v) (hne : (v ∩ u).Nonempty) :
    v ⊆ u := by
  have hclopen : IsClopen ((Subtype.val : v → X) ⁻¹' u) := isClopen_preimage_val hu hdisj
  have hpre : PreconnectedSpace v := isPreconnected_iff_preconnectedSpace.mp hv
  obtain ⟨x, hxv, hxu⟩ := hne
  have hnonempty : ((Subtype.val : v → X) ⁻¹' u).Nonempty := ⟨⟨x, hxv⟩, hxu⟩
  have huniv := hclopen.eq_univ hnonempty
  intro y hy
  have hmem : (⟨y, hy⟩ : v) ∈ ((Subtype.val : v → X) ⁻¹' u) := by rw [huniv]; trivial
  exact hmem

/-- A connected set meeting both `u` and its complement must meet the frontier of `u`.
This is HOL Light's `CONNECTED_INTER_FRONTIER`. -/
theorem IsPreconnected.inter_frontier_nonempty
    {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hv : IsPreconnected v) (h1 : (v ∩ u).Nonempty) (h2 : (v \ u).Nonempty) :
    (v ∩ frontier u).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hnofr : ∀ x ∈ v, x ∉ frontier u := by
    intro x hx hfr
    exact absurd (Set.mem_inter hx hfr) (by rw [hcon]; exact Set.notMem_empty x)
  have hcover : v ⊆ interior u ∪ interior uᶜ := by
    intro x hx
    by_cases hi : x ∈ interior u
    · exact Or.inl hi
    refine Or.inr ?_
    rw [interior_compl, Set.mem_compl_iff]
    intro hcl
    exact hnofr x hx ⟨hcl, hi⟩
  have hmem1 : (v ∩ interior u).Nonempty := by
    obtain ⟨x, hxv, hxu⟩ := h1
    refine ⟨x, hxv, ?_⟩
    by_contra hi
    exact hnofr x hxv ⟨subset_closure hxu, hi⟩
  have hmem2 : (v ∩ interior uᶜ).Nonempty := by
    obtain ⟨x, hxv, hxu⟩ := h2
    refine ⟨x, hxv, ?_⟩
    rw [interior_compl, Set.mem_compl_iff]
    intro hcl
    exact hnofr x hxv ⟨hcl, fun hi => hxu (interior_subset hi)⟩
  obtain ⟨x, hxv, hx1, hx2⟩ :=
    hv (interior u) (interior uᶜ) isOpen_interior isOpen_interior hcover hmem1 hmem2
  exact (interior_subset hx2) (interior_subset hx1)

/-- The set `w` of Harrison's proof: points of the wide strip whose exponential also lies
in the wide strip. -/
def doubleStrip : Set ℂ :=
  {z | |z.im| ≤ 2 * Real.pi ∧ |(Complex.exp z).im| ≤ 2 * Real.pi}

/-- A frontier point of the wide strip satisfies `|Im z| = 2π`. -/
theorem frontier_wideStrip_subset :
    frontier wideStrip ⊆ {z : ℂ | |z.im| = 2 * Real.pi} :=
  frontier_le_subset_eq (continuous_abs.comp Complex.continuous_im) continuous_const

/-- On the frontier of the preimage of the wide strip, `|Im (exp z)| = 2π`. -/
theorem frontier_expStrip_subset :
    frontier {z : ℂ | |(Complex.exp z).im| ≤ 2 * Real.pi}
      ⊆ {z : ℂ | |(Complex.exp z).im| = 2 * Real.pi} :=
  frontier_le_subset_eq
    (continuous_abs.comp (Complex.continuous_im.comp Complex.continuous_exp)) continuous_const

/-- The frontier of the central strip misses `w ∩ h`: this is where the estimate bites. -/
theorem disjoint_frontier_centralStrip :
    Disjoint (frontier centralStrip) (doubleStrip ∩ rightHalfPlane) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨hw, hh⟩
  have hfr : |z.im| = Real.pi / 3 := frontier_centralStrip_subset hz
  exact absurd hw.2 (not_le.mpr (abs_im_exp_gt_two_pi_of_frontier hfr hh))

/-- If `|Im z| = 2π` then `exp z` is real. -/
theorem im_exp_eq_zero_of_abs_im_eq_two_pi {z : ℂ} (h : |z.im| = 2 * Real.pi) :
    (Complex.exp z).im = 0 := by
  rw [Complex.exp_im]
  rcases abs_eq (by positivity : (0 : ℝ) ≤ 2 * Real.pi) |>.mp h with h' | h'
  · rw [h', show (2 : ℝ) * Real.pi = ((2 : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, mul_zero]
  · rw [h', show -((2 : ℝ) * Real.pi) = ((-2 : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, mul_zero]

/-- Points of the central strip in the right half-plane stay in the right half-plane. -/
theorem rightHalfPlane_exp_of_mem {z : ℂ}
    (hs : z ∈ centralStrip) (hh : z ∈ rightHalfPlane) :
    Complex.exp z ∈ rightHalfPlane := by
  have h2a := lemma2a_real_growth hs
  have hlog : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hre : (4 : ℝ) < z.re := hh
  change (4 : ℝ) < (Complex.exp z).re
  linarith

/-- The derivative of an iterate never vanishes. -/
theorem deriv_expIterate_ne_zero (n : ℕ) (z : ℂ) : deriv (expIterate n) z ≠ 0 := by
  induction n with
  | zero =>
      have h : expIterate 0 = id := by funext w; rfl
      rw [h, deriv_id]
      exact one_ne_zero
  | succ n ih =>
      rw [deriv_expIterate_succ]
      exact mul_ne_zero ih (Complex.exp_ne_zero _)

/-- Every iterate is an open map, so images of open sets are open. -/
theorem isOpen_image_expIterate {V : Set ℂ} (hV : IsOpen V) (n : ℕ) :
    IsOpen (expIterate n '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨z, hz, rfl⟩
  have hnhds : V ∈ 𝓝 z := hV.mem_nhds hz
  have hana : AnalyticAt ℂ (expIterate n) z :=
    (differentiable_expIterate n).differentiableOn.analyticAt hnhds
  rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
  · exfalso
    have heq : expIterate n =ᶠ[𝓝 z] fun _ => expIterate n z := hconst
    have : deriv (expIterate n) z = 0 := by
      rw [heq.deriv_eq, deriv_const]
    exact deriv_expIterate_ne_zero n z this
  · exact hmap (Filter.image_mem_map hnhds)

/-! ### The `π`-strips, for the negative-axis argument -/

/-- `|Im z| = π` makes the exponential a negative real number. -/
theorem neg_real_of_abs_im_eq_pi {z : ℂ} (h : |z.im| = Real.pi) :
    (Complex.exp z).im = 0 ∧ (Complex.exp z).re < 0 := by
  rcases abs_eq (le_of_lt Real.pi_pos) |>.mp h with h' | h'
  · refine exp_neg_real_of_odd_mul_pi (k := 1) ⟨0, by ring⟩ ?_
    rw [h']; push_cast; ring
  · refine exp_neg_real_of_odd_mul_pi (k := -1) ⟨-1, by ring⟩ ?_
    rw [h']; push_cast; ring

/-- The closed strip of imaginary height `π` used for the negative-real-axis argument. -/
def piStrip : Set ℂ := {z | |z.im| ≤ Real.pi}

/-- Points whose imaginary parts, before and after one exponential,
have absolute value at most `π`. -/
def piDoubleStrip : Set ℂ :=
  {z | |z.im| ≤ Real.pi ∧ |(Complex.exp z).im| ≤ Real.pi}

/-- A frontier point of `piStrip` satisfies `|Im z| = π`. -/
theorem frontier_piStrip_subset :
    frontier piStrip ⊆ {z : ℂ | |z.im| = Real.pi} :=
  frontier_le_subset_eq (continuous_abs.comp Complex.continuous_im) continuous_const

/-- On the frontier of the preimage of `piStrip`, `|Im (exp z)| = π`. -/
theorem frontier_expPiStrip_subset :
    frontier {z : ℂ | |(Complex.exp z).im| ≤ Real.pi}
      ⊆ {z : ℂ | |(Complex.exp z).im| = Real.pi} :=
  frontier_le_subset_eq
    (continuous_abs.comp (Complex.continuous_im.comp Complex.continuous_exp)) continuous_const

/-- The frontier estimate still bites with `π` in place of `2π`. -/
theorem disjoint_frontier_centralStrip_pi :
    Disjoint (frontier centralStrip) (piDoubleStrip ∩ rightHalfPlane) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨hw, hh⟩
  have hfr : |z.im| = Real.pi / 3 := frontier_centralStrip_subset hz
  have hbig := abs_im_exp_gt_two_pi_of_frontier hfr hh
  have : |(Complex.exp z).im| ≤ Real.pi := hw.2
  nlinarith [Real.pi_pos]

/-- **Lemma 5, negative-axis form.** If infinitely many images of `V` lie in the right
half-plane, some image meets the *negative* real axis.

The `π`-strips replace Harrison's `2π`-strips: on their frontiers `|Im z| = π`, where the
exponential is negative real rather than positive. The final step no longer appeals to the
standing hypothesis at all — the image is open, hence contains a non-real point, whose orbit
would have to stay in the central strip forever, contradicting Lemma 2b. -/
theorem lemma5_negative_real_axis
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hfrequent : Set.Infinite {n : ℕ | MapsTo (expIterate n) V rightHalfPlane}) :
    EventuallyMeetsNegativeRealAxis V := by
  by_contra hcon
  have hnoneg : ∀ (n : ℕ), ∀ z ∈ V,
      ¬ ((expIterate n z).im = 0 ∧ (expIterate n z).re < 0) := by
    intro n z hz hval
    exact hcon ⟨n, z, hz, hval.1, hval.2⟩
  set W2 : Set ℂ := {z : ℂ | |(Complex.exp z).im| ≤ Real.pi} with hW2
  have himgconn : ∀ n : ℕ, IsPreconnected (expIterate n '' V) := fun n =>
    hVconn.isPreconnected.image _ (continuous_expIterate n).continuousOn
  -- Avoiding the negative axis forces every image to avoid both relevant strip frontiers.
  have hA : ∀ n : ℕ, Disjoint (expIterate n '' V) (frontier piStrip) := by
    intro n
    rw [Set.disjoint_right]
    rintro x hx ⟨z, hz, rfl⟩
    have h2 : |(expIterate n z).im| = Real.pi := frontier_piStrip_subset hx
    obtain ⟨h3, h4⟩ := neg_real_of_abs_im_eq_pi h2
    rw [← expIterate_succ] at h3 h4
    exact hnoneg (n + 1) z hz ⟨h3, h4⟩
  have hB : ∀ n : ℕ, Disjoint (expIterate n '' V) (frontier W2) := by
    intro n
    rw [Set.disjoint_right]
    rintro x hx ⟨z, hz, rfl⟩
    have h2 : |(Complex.exp (expIterate n z)).im| = Real.pi := frontier_expPiStrip_subset hx
    rw [← expIterate_succ] at h2
    obtain ⟨h3, h4⟩ := neg_real_of_abs_im_eq_pi h2
    rw [← expIterate_succ] at h3 h4
    exact hnoneg (n + 2) z hz ⟨h3, h4⟩
  -- A connected image avoiding a frontier lies entirely on one side of it.
  have hdich : ∀ (n : ℕ) (U : Set ℂ), Disjoint (expIterate n '' V) (frontier U) →
      expIterate n '' V ⊆ U ∨ Disjoint (expIterate n '' V) U := by
    intro n U hfr
    by_cases hsub : expIterate n '' V ⊆ U
    · exact Or.inl hsub
    refine Or.inr ?_
    by_contra hdisj
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨x, hx1, hx2⟩ := hdisj
    have hdn : (expIterate n '' V \ U).Nonempty := Set.sdiff_nonempty.mpr hsub
    obtain ⟨p, hp1, hp2⟩ :=
      IsPreconnected.inter_frontier_nonempty (himgconn n) ⟨x, hx1, hx2⟩ hdn
    exact Set.disjoint_left.mp hfr hp1 hp2
  obtain ⟨N, hN⟩ := lemma4_eventually_meets_centralStrip hVopen hVconn hVne
  have hpi := Real.pi_pos
  -- Lemma 4 rules out the exterior side for all sufficiently late images.
  have hds : ∀ n, N ≤ n → expIterate n '' V ⊆ piDoubleStrip := by
    intro n hn
    have hsub1 : expIterate n '' V ⊆ piStrip := by
      rcases hdich n piStrip (hA n) with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx1, hx2⟩ := hN n hn
        refine Set.disjoint_left.mp h hx1 ?_
        change |x.im| ≤ Real.pi
        have hx3 : |x.im| ≤ Real.pi / 3 := hx2
        linarith
    have hsub2 : expIterate n '' V ⊆ W2 := by
      rcases hdich n W2 (hB n) with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx1, hx2⟩ := hN (n + 1) (by omega)
        obtain ⟨z, hz, rfl⟩ := hx1
        refine Set.disjoint_left.mp h ⟨z, hz, rfl⟩ ?_
        change |(Complex.exp (expIterate n z)).im| ≤ Real.pi
        rw [← expIterate_succ]
        have hx3 : |(expIterate (n + 1) z).im| ≤ Real.pi / 3 := hx2
        linarith
    exact fun x hx => ⟨hsub1 hx, hsub2 hx⟩
  -- In the right half-plane, the double-strip constraint forces the central-strip constraint.
  have hcs : ∀ k, N ≤ k → expIterate k '' V ⊆ piDoubleStrip ∩ rightHalfPlane →
      expIterate k '' V ⊆ centralStrip := by
    intro k hk hsub
    have hfrdisj : Disjoint (expIterate k '' V) (frontier centralStrip) := by
      rw [Set.disjoint_right]
      intro x hfr hx
      exact Set.disjoint_left.mp disjoint_frontier_centralStrip_pi hfr (hsub hx)
    rcases hdich k centralStrip hfrdisj with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx1, hx2⟩ := hN k hk
      exact Set.disjoint_left.mp h hx1 hx2
  obtain ⟨n, hnmem, hnge⟩ := hfrequent.exists_gt N
  have hnge' : N ≤ n := le_of_lt hnge
  have hmaps : MapsTo (expIterate n) V rightHalfPlane := hnmem
  -- Once an image is far enough right, all its later images would remain in the central strip.
  have hall : ∀ m : ℕ,
      expIterate (n + m) '' V ⊆ piDoubleStrip ∩ rightHalfPlane ∩ centralStrip := by
    intro m
    induction m with
    | zero =>
        have h1 : expIterate (n + 0) '' V ⊆ piDoubleStrip := by
          simpa using hds n hnge'
        have h2 : expIterate (n + 0) '' V ⊆ rightHalfPlane := by
          rintro x ⟨z, hz, rfl⟩
          simpa using hmaps hz
        have h3 := hcs (n + 0) (by omega) (fun x hx => ⟨h1 hx, h2 hx⟩)
        exact fun x hx => ⟨⟨h1 hx, h2 hx⟩, h3 hx⟩
    | succ m ih =>
        have hidx : n + (m + 1) = (n + m) + 1 := by omega
        have h1 : expIterate (n + (m + 1)) '' V ⊆ piDoubleStrip := hds _ (by omega)
        have h2 : expIterate (n + (m + 1)) '' V ⊆ rightHalfPlane := by
          rintro x ⟨z, hz, rfl⟩
          rw [hidx, expIterate_succ]
          have hz1 := ih ⟨z, hz, rfl⟩
          exact rightHalfPlane_exp_of_mem hz1.2 hz1.1.2
        have h3 := hcs _ (by omega : N ≤ n + (m + 1)) (fun x hx => ⟨h1 hx, h2 hx⟩)
        exact fun x hx => ⟨⟨h1 hx, h2 hx⟩, h3 hx⟩
  -- the image is open, so it contains a non-real point, whose orbit cannot stay in the strip
  obtain ⟨z0, hz0⟩ := hVne
  obtain ⟨εb, hεb, hbsub⟩ :=
    Metric.isOpen_iff.mp (isOpen_image_expIterate hVopen n) (expIterate n z0) ⟨z0, hz0, rfl⟩
  have hex : ∃ q ∈ expIterate n '' V, q.im ≠ 0 := by
    have hnormI : ‖Complex.I * ((εb / 2 : ℝ) : ℂ)‖ = εb / 2 := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    by_cases hb : 0 ≤ (expIterate n z0).im
    · refine ⟨expIterate n z0 + Complex.I * ((εb / 2 : ℝ) : ℂ), hbsub ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnormI]
        linarith
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        exact ne_of_gt (by linarith)
    · push Not at hb
      refine ⟨expIterate n z0 - Complex.I * ((εb / 2 : ℝ) : ℂ), hbsub ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, hnormI]
        linarith
      · simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        exact ne_of_lt (by linarith)
  obtain ⟨q, ⟨u, hu, rfl⟩, hqim⟩ := hex
  have hstrip : ∀ m : ℕ, expIterate m (expIterate n u) ∈ centralStrip := by
    intro m
    have hmem := (hall m) ⟨u, hu, rfl⟩
    have heq : expIterate m (expIterate n u) = expIterate (n + m) u := by
      change exponentialMap^[m] (exponentialMap^[n] u) = exponentialMap^[n + m] u
      rw [Nat.add_comm, Function.iterate_add_apply]
    rw [heq]
    exact hmem.2
  obtain ⟨m, hm⟩ := lemma2b_eventually_leaves_strip
    (show ¬ OnRealAxis (expIterate n u) from hqim)
  exact hm (hstrip m)

/-- **Lemma 5.** If infinitely many images of a non-empty open connected set are contained
in the right half-plane, then an image meets the real axis. HOL Light: `LEMMA_5`. -/
theorem lemma5_real_axis_of_frequently_in_rightHalfPlane
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hfrequent : Set.Infinite {n : ℕ | MapsTo (expIterate n) V rightHalfPlane}) :
    EventuallyMeetsRealAxis V := by
  obtain ⟨n, z, hz, hreal, _⟩ := lemma5_negative_real_axis hVopen hVconn hVne hfrequent
  exact ⟨n, z, hz, hreal⟩

end

end ExponentialJuliaSetMisiurewicz
