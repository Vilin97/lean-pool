/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import LeanPool.ExpChaotic.RealAxis

/-!
# Eventual compact covering and backward-orbit density

Section 5: real-axis expansion and two logarithms give eventual covering of compact sets.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-! ## Section 5: eventual covering of compact sets

We use radius-eight disks instead of radius-`2π` disks to keep the estimates simple.
Since Lemma 6 already supplies an orbit reaching the real axis in every open disk,
we only need expansion along real orbits, rather than general escaping orbits.
-/

/-- A small disk centred on the real axis is expanded by a prescribed factor. -/
theorem exp_ball_real_expands {x : ℂ} (hx : x.im = 0)
    {r m : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hm : 0 ≤ m)
    (hxm : m ≤ x.re) :
    ball (Complex.exp x) (r * m) ⊆ Complex.exp '' ball x r := by
  -- On this small real-centred disk, exp is injective and its derivative has norm at least m.
  apply lemma3_ball_image_of_deriv_lower_bound hr hm
    Complex.continuous_exp.continuousOn Complex.differentiable_exp.differentiableOn
  · intro a ha b hb hab
    have haim : |a.im| < 1 := by
      have h := (Complex.abs_im_le_norm (a - x)).trans_lt
        (show ‖a - x‖ < r by simpa [Metric.mem_ball, dist_eq_norm] using ha)
      simpa [Complex.sub_im, hx] using h.trans_le hr1
    have hbim : |b.im| < 1 := by
      have h := (Complex.abs_im_le_norm (b - x)).trans_lt
        (show ‖b - x‖ < r by simpa [Metric.mem_ball, dist_eq_norm] using hb)
      simpa [Complex.sub_im, hx] using h.trans_le hr1
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi _ _ _ _ hab <;>
      linarith [abs_lt.mp haim, abs_lt.mp hbim, Real.pi_gt_three]
  · intro z hz
    rw [Complex.deriv_exp, Complex.norm_exp]
    have h := (Complex.abs_re_le_norm (z - x)).trans_lt
      (show ‖z - x‖ < r by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hre : x.re - r < z.re := by
      have := (abs_lt.mp h).1
      simp only [Complex.sub_re] at this
      linarith
    linarith [Real.add_one_le_exp z.re]

/-- Iterated images of a disk on a sufficiently far right real orbit contain unit disks. -/
theorem eventually_unit_ball_subset_iterate_real {x : ℂ} (hx : x.im = 0)
    (hx2 : 2 ≤ x.re) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n ≥ N, ball (expIterate n x) 1 ⊆ expIterate n '' ball x r := by
  -- Double the guaranteed radius at each step, capping it at one to preserve injectivity.
  have hballs : ∀ n : ℕ,
      ball (expIterate n x) (min (r * 2 ^ n) 1) ⊆ expIterate n '' ball x r := by
    intro n
    induction n with
    | zero =>
        simpa using (ball_subset_ball (min_le_left r 1) : ball x (min r 1) ⊆ ball x r)
    | succ n ih =>
        have hpos : 0 < min (r * (2 : ℝ) ^ n) 1 := by positivity
        have hg := exp_ball_real_expands (expIterate_real_orbit hx n).1
          hpos (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 2)
          (by linarith [(expIterate_real_orbit hx n).2, Nat.cast_nonneg (α := ℝ) n])
        have hrad : min (r * (2 : ℝ) ^ (n + 1)) 1 ≤ min (r * 2 ^ n) 1 * 2 := by
          rw [pow_succ, ← mul_assoc]
          rcases le_total (r * (2 : ℝ) ^ n) 1 with h | h
          · rw [min_eq_left h]
            exact min_le_left _ _
          · rw [min_eq_right h]
            exact (min_le_right _ _).trans (by norm_num)
        intro y hy
        rw [expIterate_succ] at hy
        obtain ⟨z, hz, rfl⟩ := hg ((ball_subset_ball hrad) hy)
        obtain ⟨w, hw, rfl⟩ := ih hz
        exact ⟨w, hw, expIterate_succ n w⟩
  -- Eventually the cap is reached and every subsequent image contains a unit disk.
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / r)
  refine ⟨N, fun n hn => ?_⟩
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := n)))
  have hlarge : 1 ≤ r * (2 : ℝ) ^ n := by
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have : 1 / r < (2 : ℝ) ^ n := lt_of_lt_of_le hN (hcast.trans hpow)
    exact (le_of_lt ((div_lt_iff₀ hr).mp this)).trans_eq (mul_comm _ _)
  simpa only [min_eq_right hlarge] using hballs n

/-- Two exponentials of a radius-eight disk sufficiently far along the real axis
cover any prescribed annulus. Integer translates of a logarithm supply the preimages. -/
theorem mem_exp_exp_ball_real {w : ℂ} (hw : w ≠ 0) {M x : ℝ}
    (hwM : |Real.log ‖w‖| ≤ M) (hx : M + 2 * Real.pi ≤ x) :
    w ∈ expIterate 2 '' ball (x : ℂ) 8 := by
  -- Choose a logarithm of w with imaginary part between exp x and exp x + 2π.
  let k : ℤ := ⌈(Real.exp x - (Complex.log w).im) / (2 * Real.pi)⌉
  let t : ℂ := Complex.log w + (k : ℂ) * (2 * Real.pi * Complex.I)
  have hp : 0 < 2 * Real.pi := by positivity
  have htim : t.im = (Complex.log w).im + (k : ℝ) * (2 * Real.pi) := by
    simp [t, Complex.mul_re, Complex.mul_im]
  have htre : t.re = Real.log ‖w‖ := by simp [t, Complex.log_re]
  have htlo : Real.exp x ≤ t.im := by
    have h := (div_le_iff₀ hp).mp
      (Int.le_ceil ((Real.exp x - (Complex.log w).im) / (2 * Real.pi)))
    rw [htim]
    change Real.exp x ≤ (Complex.log w).im + (k : ℝ) * (2 * Real.pi)
    linarith
  have hthi : t.im < Real.exp x + 2 * Real.pi := by
    have h := (mul_lt_mul_of_pos_right
      (Int.ceil_lt_add_one ((Real.exp x - (Complex.log w).im) / (2 * Real.pi))) hp)
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul] at h
    rw [htim]
    change (Complex.log w).im + (k : ℝ) * (2 * Real.pi) < _
    linarith
  have htpos : 0 < t.im := (Real.exp_pos x).trans_le htlo
  have htne : t ≠ 0 := by
    intro h
    simp [h] at htpos
  -- Taking one further logarithm puts its real part between x and x + 1.
  have hnormlo : Real.exp x ≤ ‖t‖ := htlo.trans (Complex.im_le_norm t)
  have hnormhi : ‖t‖ ≤ Real.exp (x + 1) := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im t
    rw [htre, abs_of_pos htpos] at hnorm
    have hmx : M + 2 * Real.pi ≤ Real.exp x :=
      hx.trans (le_trans (by linarith : x ≤ x + 1) (Real.add_one_le_exp x))
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    rw [Real.exp_add]
    have hmul := mul_le_mul_of_nonneg_left htwo (le_of_lt (Real.exp_pos x))
    linarith
  have hrelo : x ≤ Real.log ‖t‖ := by
    simpa using Real.log_le_log (Real.exp_pos x) hnormlo
  have hrehi : Real.log ‖t‖ ≤ x + 1 := by
    simpa using Real.log_le_log (norm_pos_iff.mpr htne) hnormhi
  -- Its imaginary part is bounded by π, placing the two-step preimage in the desired disk.
  refine ⟨Complex.log t, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hnorm := Complex.norm_le_abs_re_add_abs_im (Complex.log t - (x : ℂ))
    simp only [Complex.sub_re, Complex.log_re, Complex.ofReal_re,
      Complex.sub_im, Complex.log_im, Complex.ofReal_im, sub_zero] at hnorm
    rw [abs_of_nonneg (sub_nonneg.mpr hrelo)] at hnorm
    linarith [Complex.abs_arg_le_pi t, Real.pi_lt_four]
  · have hexpt : Complex.exp t = w := by
      calc
        Complex.exp t = Complex.exp (Complex.log w) := by
          apply Complex.exp_eq_exp_iff_exists_int.mpr
          exact ⟨k, rfl⟩
        _ = w := Complex.exp_log hw
    simpa only [expIterate_succ, expIterate_zero, Complex.exp_log htne] using hexpt

/-- Compactness makes the preceding elementary covering estimate uniform. -/
theorem compact_subset_exp_exp_ball_real {K : Set ℂ}
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ ρ : ℝ, ∀ x : ℝ, ρ ≤ x → K ⊆ expIterate 2 '' ball (x : ℂ) 8 := by
  have hcont : ContinuousOn (fun z : ℂ => |Real.log ‖z‖|) K := by
    apply ContinuousOn.abs
    apply ContinuousOn.log continuous_norm.continuousOn
    intro z hz
    exact norm_ne_zero_iff.mpr (fun h => hK0 (h ▸ hz))
  obtain ⟨M, hM⟩ := hK.bddAbove_image hcont
  refine ⟨M + 2 * Real.pi, fun x hx w hw => ?_⟩
  exact mem_exp_exp_ball_real (fun h => hK0 (h ▸ hw)) (hM ⟨w, hw, rfl⟩) hx

/-- Every sufficiently late image of a disk centred on a far right real point
covers a given compact subset of the punctured plane. -/
theorem eventually_covers_compact_of_real_ball {K : Set ℂ}
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K)
    {x : ℂ} (hx : x.im = 0) (hx2 : 2 ≤ x.re) {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' ball x r := by
  obtain ⟨N, hN⟩ := eventually_unit_ball_subset_iterate_real hx hx2 hr
  obtain ⟨ρ, hρ⟩ := compact_subset_exp_exp_ball_real hK hK0
  obtain ⟨d, hd⟩ := exists_nat_gt (max 8 ρ - x.re)
  -- After reaching a unit disk, one iterate gives radius eight and two more cover K.
  have htail : ∀ k ≥ max N d, K ⊆ expIterate (k + 3) '' ball x r := by
    intro k hk w hw
    have hkN : N ≤ k := (le_max_left _ _).trans hk
    have hkd : (d : ℝ) ≤ k := by exact_mod_cast (le_max_right N d).trans hk
    have hxk : max 8 ρ ≤ (expIterate k x).re := by
      linarith [(expIterate_real_orbit hx k).2]
    have hxnext : ρ ≤ (expIterate (k + 1) x).re := by
      have h := (expIterate_real_orbit hx (k + 1)).2
      push_cast at h
      linarith [le_max_right (8 : ℝ) ρ]
    have hlarge : ball (expIterate (k + 1) x) 8 ⊆
        Complex.exp '' ball (expIterate k x) 1 := by
      simpa only [one_mul, expIterate_succ] using
        exp_ball_real_expands (expIterate_real_orbit hx k).1
          (by norm_num : (0 : ℝ) < 1) le_rfl (by norm_num : (0 : ℝ) ≤ 8)
          ((le_max_left _ _).trans hxk)
    have hxreal : (((expIterate (k + 1) x).re : ℝ) : ℂ) = expIterate (k + 1) x := by
      apply Complex.ext
      · rfl
      · simpa using (expIterate_real_orbit hx (k + 1)).1.symm
    have hcover := hρ (expIterate (k + 1) x).re hxnext hw
    rw [hxreal] at hcover
    obtain ⟨a, ha, haw⟩ := hcover
    obtain ⟨b, hb, hba⟩ := hlarge ha
    obtain ⟨c, hc, hcb⟩ := hN k hkN hb
    refine ⟨c, hc, ?_⟩
    calc
      expIterate (k + 3) c = expIterate 2 (Complex.exp (expIterate k c)) := by
        rw [show k + 3 = 2 + (k + 1) by omega]
        exact (Function.iterate_add_apply exponentialMap 2 (k + 1) c).trans
          (congrArg (expIterate 2) (expIterate_succ k c))
      _ = w := by rw [hcb, hba, haw]
  refine ⟨max N d + 3, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [show max N d + 3 + k = (max N d + k) + 3 by omega] using
    htail (max N d + k) (Nat.le_add_right _ _)

/-- **Corollary 5.5 (open sets spread everywhere).** Every sufficiently late
iterated image of a nonempty open set contains any given compact set omitting zero.
Only real-axis Lemma 6 and the quantitative open-mapping Lemma 3 are needed. -/
theorem eventually_covers_compact
    {U K : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' U := by
  obtain ⟨c, hc⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hconn : IsConnected (ball c r) :=
    ⟨⟨c, Metric.mem_ball_self hr⟩, (convex_ball c r).isPreconnected⟩
  -- First reach the real axis, then advance to a real point where disk expansion applies.
  obtain ⟨m, a, ha, hreal⟩ := lemma6_every_domain_eventually_meets_real_axis
    isOpen_ball hconn ⟨c, Metric.mem_ball_self hr⟩
  obtain ⟨j, hj⟩ := exists_re_gt_four_of_real hreal
  let x : ℂ := expIterate j (expIterate m a)
  have hx : x.im = 0 := (expIterate_real_orbit hreal j).1
  have hxmem : x ∈ expIterate (j + m) '' U :=
    ⟨a, hball ha, Function.iterate_add_apply exponentialMap j m a⟩
  -- Openness supplies a disk about that image point; its covering property pulls back to U.
  obtain ⟨s, hs, hsmall⟩ := Metric.isOpen_iff.mp (isOpen_image_expIterate hU (j + m)) x hxmem
  obtain ⟨N, hN⟩ := eventually_covers_compact_of_real_ball hK hK0 hx (by dsimp [x]; linarith) hs
  refine ⟨N + (j + m), fun n hn w hw => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨b, hb, hbw⟩ := hN (N + k) (Nat.le_add_right _ _) hw
  obtain ⟨z, hz, hzb⟩ := hsmall hb
  refine ⟨z, hz, ?_⟩
  calc
    expIterate (N + (j + m) + k) z = expIterate (N + k) (expIterate (j + m) z) := by
      rw [show N + (j + m) + k = (N + k) + (j + m) by omega]
      exact Function.iterate_add_apply exponentialMap (N + k) (j + m) z
    _ = w := by rw [hzb, hbw]

/-- The compact covering theorem specialised to an open ball of positive radius. -/
theorem eventually_covers_compact_ball {c : ℂ} {r : ℝ} (hr : 0 < r)
    {K : Set ℂ} (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' ball c r :=
  eventually_covers_compact isOpen_ball ⟨c, mem_ball_self hr⟩ hK hK0

/-- Every nonzero point belongs to every sufficiently late image of an open set. -/
theorem eventually_hits_nonzero {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {w : ℂ} (hw : w ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, expIterate n z = w := by
  obtain ⟨N, hN⟩ := eventually_covers_compact hU hUne
    (isCompact_singleton (x := w)) (by simpa using hw.symm)
  exact ⟨N, fun n hn => hN n hn (Set.mem_singleton w)⟩

/-- The point-hitting formulation, with an explicitly positive iterate. -/
theorem exists_iterate_eq_nonzero {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {w : ℂ} (hw : w ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ z ∈ U, expIterate n z = w := by
  obtain ⟨N, hN⟩ := eventually_hits_nonzero hU hUne hw
  exact ⟨N + 1, by omega, hN (N + 1) (by omega)⟩

/-- **Lemma 6, negative-axis form.** This now follows from the Section 5 theorem
by taking the nonzero target to be `-1`. The connectedness hypothesis is retained
for compatibility with the original statement. -/
theorem lemma6_every_domain_eventually_meets_negative_real_axis
    {V : Set ℂ} (hVopen : IsOpen V) (_hVconn : IsConnected V) (hVne : V.Nonempty) :
    EventuallyMeetsNegativeRealAxis V := by
  obtain ⟨n, _, z, hz, heq⟩ := exists_iterate_eq_nonzero hVopen hVne
    (w := -1) (by norm_num)
  refine ⟨n, z, hz, ?_⟩
  rw [heq]
  norm_num

/-- The full iterated preimage of every nonzero point is dense in the plane. -/
theorem dense_iterated_preimages_nonzero {w : ℂ} (hw : w ≠ 0) :
    Dense {z : ℂ | ∃ n : ℕ, expIterate n z = w} := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨n, _, z, hz, hzw⟩ := exists_iterate_eq_nonzero hU hUne hw
  exact ⟨z, hz, n, hzw⟩

/-- The backward orbit of the real axis is dense. -/
theorem dense_iterated_preimages_real_axis :
    Dense {z : ℂ | ∃ n : ℕ, OnRealAxis (expIterate n z)} := by
  apply (dense_iterated_preimages_nonzero (w := 1) one_ne_zero).mono
  rintro z ⟨n, hn⟩
  exact ⟨n, by simp [hn, OnRealAxis]⟩

end

end ExponentialJuliaSetMisiurewicz
