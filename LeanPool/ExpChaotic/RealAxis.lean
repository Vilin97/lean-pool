/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

import LeanPool.ExpChaotic.HalfPlane
import LeanPool.ExpChaotic.StripGeometry

/-!
# Every domain eventually meets the real axis

Lemma 6: bounded transforms and compactness contradict the strip lemmas.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-! ### Towards Lemma 6 -/

/-- Harrison's auxiliary step inside `LEMMA_6`: if no forward image of `V` meets the real
axis, then all but finitely many images meet the disc of radius `exp 4`.

Contrapositive of Lemma 5: only finitely many images can sit inside the right half-plane, and
if the image at time `n` misses the disc then the image at time `n - 1` lay in the half-plane,
since `‖exp z‖ = exp (Re z)`. -/
theorem lemma6_eventually_meets_disc
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      (expIterate n '' V ∩ closedBall (0 : ℂ) (Real.exp 4)).Nonempty := by
  have hfin : {n : ℕ | MapsTo (expIterate n) V rightHalfPlane}.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨n, z, hz, hval⟩ :=
      lemma5_real_axis_of_frequently_in_rightHalfPlane hVopen hVconn hVne hinf
    exact hnoreal n z hz hval
  obtain ⟨M, hM⟩ := hfin.bddAbove
  refine ⟨M + 2, fun n hn => ?_⟩
  have hn1 : ¬ MapsTo (expIterate (n - 1)) V rightHalfPlane := by
    intro hmaps
    have hle : n - 1 ≤ M := hM hmaps
    omega
  rw [MapsTo] at hn1
  push Not at hn1
  obtain ⟨z, hz, hnot⟩ := hn1
  refine ⟨expIterate n z, ⟨z, hz, rfl⟩, ?_⟩
  have hre : (expIterate (n - 1) z).re ≤ 4 := by
    by_contra hgt
    push Not at hgt
    exact hnot hgt
  have hidx : n = (n - 1) + 1 := by omega
  rw [Metric.mem_closedBall, dist_zero_right]
  conv_lhs => rw [hidx]
  rw [expIterate_succ, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hre

/-- Two sequences in compact sets admit a *common* convergent subsequence. -/
theorem exists_double_subseq {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsCompact t)
    {a : ℕ → X} {b : ℕ → Y} (ha : ∀ n, a n ∈ s) (hb : ∀ n, b n ∈ t) :
    ∃ x ∈ s, ∃ y ∈ t, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x) ∧
      Filter.Tendsto (b ∘ φ) Filter.atTop (𝓝 y) := by
  obtain ⟨x, hxs, φ₁, hφ₁, hlim₁⟩ := hs.tendsto_subseq ha
  obtain ⟨y, hyt, φ₂, hφ₂, hlim₂⟩ := ht.tendsto_subseq (fun n => hb (φ₁ n))
  refine ⟨x, hxs, y, hyt, φ₁ ∘ φ₂, hφ₁.comp hφ₂, ?_, ?_⟩
  · exact hlim₁.comp hφ₂.tendsto_atTop
  · exact hlim₂

/-- Along all large times, the ball contains a point whose image stays in the disc of radius
`exp 4`. -/
theorem exists_disc_points
    {V : Set ℂ}
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {c : ℂ} {σ : ℝ} (hσ : 0 < σ) (hsub : ball c σ ⊆ V) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ y ∈ ball c σ, ‖expIterate n y‖ ≤ Real.exp 4 := by
  have hconn : IsConnected (ball c σ) :=
    ⟨⟨c, Metric.mem_ball_self hσ⟩, (convex_ball c σ).isPreconnected⟩
  have hnr : ∀ (n : ℕ), ∀ z ∈ ball c σ, (expIterate n z).im ≠ 0 :=
    fun n z hz => hnoreal n z (hsub hz)
  obtain ⟨N, hN⟩ := lemma6_eventually_meets_disc isOpen_ball hconn
    ⟨c, Metric.mem_ball_self hσ⟩ hnr
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := hN n hn
  refine ⟨y, hy, ?_⟩
  rwa [Metric.mem_closedBall, dist_zero_right] at hx

/-! ### Reduction of the lower half-plane case by conjugation -/

/-- Conjugation commutes with the iterates of `exp`. -/
theorem expIterate_conj (n : ℕ) (z : ℂ) :
    expIterate n ((starRingEnd ℂ) z) = (starRingEnd ℂ) (expIterate n z) := by
  induction n with
  | zero => simp [expIterate]
  | succ n ih =>
      rw [expIterate_succ, expIterate_succ, ih]
      exact Complex.exp_conj _

/-- Conjugation is an involution, so the image of a set is its preimage. -/
theorem conj_image_eq_preimage (V : Set ℂ) :
    (starRingEnd ℂ) '' V = (starRingEnd ℂ) ⁻¹' V := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨(starRingEnd ℂ) z, hz, by simp⟩

/-- Complex conjugation sends open sets to open sets. -/
theorem isOpen_conj_image {V : Set ℂ} (hV : IsOpen V) :
    IsOpen ((starRingEnd ℂ) '' V) := by
  rw [conj_image_eq_preimage]
  exact hV.preimage Complex.continuous_conj

/-- Complex conjugation sends connected sets to connected sets. -/
theorem isConnected_conj_image {V : Set ℂ} (hV : IsConnected V) :
    IsConnected ((starRingEnd ℂ) '' V) :=
  hV.image _ Complex.continuous_conj.continuousOn

/-- The conjugate image of a nonempty set is nonempty. -/
theorem nonempty_conj_image {V : Set ℂ} (hV : V.Nonempty) :
    ((starRingEnd ℂ) '' V).Nonempty := hV.image _

/-- No image of the conjugate meets the real axis if none of `V`'s images does. -/
theorem noreal_conj_image {V : Set ℂ}
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) :
    ∀ (n : ℕ), ∀ z ∈ (starRingEnd ℂ) '' V, (expIterate n z).im ≠ 0 := by
  rintro n z ⟨y, hy, rfl⟩ hval
  rw [expIterate_conj] at hval
  simp only [Complex.conj_im, neg_eq_zero] at hval
  exact hnoreal n y hy hval

/-- Times at which `V` lands in the lower half-plane are times at which the conjugate lands
in the upper one. -/
theorem conj_image_up_of_down {V : Set ℂ} {n : ℕ}
    (h : ∀ z ∈ V, (expIterate n z).im < 0) :
    ∀ z ∈ (starRingEnd ℂ) '' V, 0 < (expIterate n z).im := by
  rintro z ⟨y, hy, rfl⟩
  rw [expIterate_conj]
  simp only [Complex.conj_im, Left.neg_pos_iff]
  exact h y hy

/-- **The conjugation reduction.** If the conjugate set has an image meeting the real axis,
so does the original. -/
theorem eventuallyMeetsRealAxis_of_conj {V : Set ℂ}
    (h : EventuallyMeetsRealAxis ((starRingEnd ℂ) '' V)) :
    EventuallyMeetsRealAxis V := by
  obtain ⟨n, z, hz, hval⟩ := h
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨n, y, hy, ?_⟩
  rw [expIterate_conj] at hval
  change (expIterate n y).im = 0
  have : -(expIterate n y).im = 0 := hval
  linarith

/-- The orbit of a real point stays real and its real part grows by at least `1` each step. -/
theorem expIterate_real_orbit {p : ℂ} (hp : p.im = 0) (m : ℕ) :
    (expIterate m p).im = 0 ∧ p.re + m ≤ (expIterate m p).re := by
  induction m with
  | zero => simpa [expIterate] using hp
  | succ m ih =>
      obtain ⟨him, hre⟩ := ih
      constructor
      · rw [expIterate_succ, Complex.exp_im, him, Real.sin_zero, mul_zero]
      · rw [expIterate_succ, Complex.exp_re, him, Real.cos_zero, mul_one]
        have hexp := Real.add_one_le_exp (expIterate m p).re
        push_cast
        linarith

/-- A real point's orbit escapes to the right: some iterate has real part exceeding `4`. -/
theorem exists_re_gt_four_of_real {p : ℂ} (hp : p.im = 0) :
    ∃ m : ℕ, 4 < (expIterate m p).re := by
  obtain ⟨m, hm⟩ := exists_nat_gt (4 - p.re)
  refine ⟨m, ?_⟩
  have := (expIterate_real_orbit hp m).2
  linarith

/-- **Accumulation.** If infinitely many images of `V` lie in the upper half-plane and none
meets the real axis, there is a finite point `p` and a centre `y` such that arbitrarily small
balls about `y` are carried, at arbitrarily late times, into arbitrarily small neighbourhoods
of `p`. This is weak Montel in the form Lemma 6 consumes. -/
theorem lemma6_accumulation_up
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {T : Set ℕ} (hTinf : T.Infinite)
    (hTup : ∀ n ∈ T, ∀ z ∈ V, 0 < (expIterate n z).im) :
    ∃ p y : ℂ, 0 ≤ p.im ∧
      ∀ η > 0, ∃ δ > 0, ball y δ ⊆ V ∧
        ∀ K : ℕ, ∃ n, K ≤ n ∧ ∀ z ∈ ball y δ, ‖expIterate n z - p‖ < η := by
  classical
  obtain ⟨w, hw⟩ := hVne
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hVopen w hw
  set ρ : ℝ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hball2 : ball w (2 * ρ) ⊆ V := by
    have h2 : 2 * ρ = r := by rw [hρdef]; ring
    rw [h2]; exact hrsub
  have hballρ : ball w ρ ⊆ V := fun z hz => hball2 (by
    rw [Metric.mem_ball] at hz ⊢; linarith)
  have hballσ : ball w (ρ / 2) ⊆ V := fun z hz => hballρ (by
    rw [Metric.mem_ball] at hz ⊢; linarith)
  obtain ⟨N0, hN0⟩ := exists_disc_points hnoreal (by positivity : (0 : ℝ) < ρ / 2) hballσ
  -- enumerate the useful times
  set P : ℕ → Prop := fun n => n ∈ T ∧ N0 ≤ n with hPdef
  have hPinf : (Set.ofPred P).Infinite := by
    have hdiff : (T \ {n : ℕ | n < N0}).Infinite := hTinf.sdiff (Set.finite_Iio N0)
    refine Set.Infinite.mono ?_ hdiff
    intro n hn
    obtain ⟨hnT, hnlt⟩ := hn
    simp only [Set.mem_ofPred_eq] at hnlt
    exact ⟨hnT, by omega⟩
  set rr : ℕ → ℕ := fun k => Nat.nth P k with hrrdef
  have hrrP : ∀ k, P (rr k) := fun k => Nat.nth_mem_of_infinite hPinf k
  have hrrmono : StrictMono rr := fun a b hab => (Nat.nth_lt_nth hPinf).mpr hab
  have hchoice : ∀ k, ∃ y ∈ ball w (ρ / 2), ‖expIterate (rr k) y‖ ≤ Real.exp 4 :=
    fun k => hN0 (rr k) (hrrP k).2
  choose Y hYmem hYnorm using hchoice
  -- extract a common subsequence
  obtain ⟨ystar, hystar, p, hp, φ, hφ, hlimY, hlimB⟩ :=
    exists_double_subseq (isCompact_closedBall w (ρ / 2))
      (isCompact_closedBall (0 : ℂ) (Real.exp 4))
      (fun k => ball_subset_closedBall (hYmem k))
      (fun k => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hYnorm k)
  have hpim : 0 ≤ p.im := by
    refine ge_of_tendsto ((Complex.continuous_im.tendsto p).comp hlimB) ?_
    refine Filter.Eventually.of_forall (fun k => le_of_lt ?_)
    exact hTup _ (hrrP (φ k)).1 _ (hballσ (hYmem (φ k)))
  have hpI : p + Complex.I ≠ 0 := by
    intro hc
    have him : (p + Complex.I).im = 0 := by rw [hc, Complex.zero_im]
    simp only [Complex.add_im, Complex.I_im] at him
    linarith
  have hystarball : ystar ∈ closedBall w (ρ / 2) := hystar
  refine ⟨p, ystar, hpim, ?_⟩
  intro η hη
  -- Invert the Cayley transform near the finite accumulation point.
  obtain ⟨ε, hε, hpush⟩ := norm_sub_lt_of_cayley_close hpI hη
  obtain ⟨δ0, hδ0, hequi⟩ :=
    equicontinuous_cayleyUp (c := w) (ρ := ρ) hρ (T := T)
      (fun n hn z hz => hTup n hn z (hball2 hz)) (half_pos hε)
  -- One fixed source disk works for arbitrarily late times along the selected subsequence.
  set δ : ℝ := min (δ0 / 2) (ρ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδsub : ball ystar δ ⊆ ball w ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have h1 : dist ystar w ≤ ρ / 2 := by
      rwa [Metric.mem_closedBall] at hystarball
    have h2 : δ ≤ ρ / 2 := min_le_right _ _
    calc dist z w ≤ dist z ystar + dist ystar w := dist_triangle _ _ _
      _ < ρ := by linarith
  refine ⟨δ, hδpos, fun z hz => hballρ (hδsub hz), ?_⟩
  -- the two "eventually" facts
  have hMcont : ContinuousAt (fun u : ℂ => (u - Complex.I) / (u + Complex.I)) p := by
    refine ContinuousAt.div ?_ ?_ hpI
    · exact (continuous_id.sub continuous_const).continuousAt
    · exact (continuous_id.add continuous_const).continuousAt
  have hev1 : ∀ᶠ k in Filter.atTop, ‖Y (φ k) - ystar‖ < δ0 / 2 := by
    rw [Metric.tendsto_atTop] at hlimY
    obtain ⟨K1, hK1⟩ := hlimY (δ0 / 2) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop K1] with k hk
    have := hK1 k hk
    rwa [dist_eq_norm] at this
  have hev2 : ∀ᶠ k in Filter.atTop,
      ‖(expIterate (rr (φ k)) (Y (φ k)) - Complex.I)
          / (expIterate (rr (φ k)) (Y (φ k)) + Complex.I)
        - (p - Complex.I) / (p + Complex.I)‖ < ε / 2 := by
    have hcomp := hMcont.tendsto.comp hlimB
    rw [Metric.tendsto_atTop] at hcomp
    obtain ⟨K2, hK2⟩ := hcomp (ε / 2) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop K2] with k hk
    have := hK2 k hk
    rwa [dist_eq_norm] at this
  intro K
  obtain ⟨k, ⟨hk1, hk2⟩, hkK⟩ := ((hev1.and hev2).and (Filter.eventually_ge_atTop K)).exists
  refine ⟨rr (φ k), ?_, ?_⟩
  · calc K ≤ k := hkK
      _ ≤ φ k := hφ.le_apply
      _ ≤ rr (φ k) := hrrmono.le_apply
  · intro z hz
    have hzρ : z ∈ ball w ρ := hδsub hz
    have hYρ : Y (φ k) ∈ ball w ρ := by
      have := hYmem (φ k)
      rw [Metric.mem_ball] at this ⊢
      linarith
    have hclose : ‖z - Y (φ k)‖ < δ0 := by
      have hz1 : ‖z - ystar‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hz2 : δ ≤ δ0 / 2 := min_le_left _ _
      calc ‖z - Y (φ k)‖ ≤ ‖z - ystar‖ + ‖ystar - Y (φ k)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖z - ystar‖ + ‖Y (φ k) - ystar‖ := by rw [norm_sub_rev ystar]
        _ < δ0 := by linarith only [hz1, hz2, hk1]
    have hstep1 := hequi ⟨rr (φ k), (hrrP (φ k)).1⟩ z hzρ (Y (φ k)) hYρ hclose
    have hzI : expIterate (rr (φ k)) z + Complex.I ≠ 0 :=
      add_I_ne_zero (hTup _ (hrrP (φ k)).1 _ (hballρ hzρ))
    refine hpush _ hzI ?_
    calc ‖(expIterate (rr (φ k)) z - Complex.I) / (expIterate (rr (φ k)) z + Complex.I)
            - (p - Complex.I) / (p + Complex.I)‖
        ≤ ‖(expIterate (rr (φ k)) z - Complex.I) / (expIterate (rr (φ k)) z + Complex.I)
              - (expIterate (rr (φ k)) (Y (φ k)) - Complex.I)
                / (expIterate (rr (φ k)) (Y (φ k)) + Complex.I)‖
          + ‖(expIterate (rr (φ k)) (Y (φ k)) - Complex.I)
                / (expIterate (rr (φ k)) (Y (φ k)) + Complex.I)
              - (p - Complex.I) / (p + Complex.I)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε := by linarith

/-- The central strip is closed, since the absolute imaginary-part function is continuous. -/
theorem isClosed_centralStrip : IsClosed centralStrip :=
  isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const

/-- The half-plane `Re z > 4` is open. -/
theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The upper half-plane case of Lemma 6 is contradictory. -/
theorem lemma6_contradiction_up
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {T : Set ℕ} (hTinf : T.Infinite)
    (hTup : ∀ n ∈ T, ∀ z ∈ V, 0 < (expIterate n z).im) :
    False := by
  obtain ⟨p, y, hpim, haccum⟩ := lemma6_accumulation_up hVopen hVne hnoreal hTinf hTup
  by_cases hpreal : p.im = 0
  · -- `p` is real: its orbit escapes to the right, so Lemma 5 applies
    obtain ⟨m, hm⟩ := exists_re_gt_four_of_real hpreal
    obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.mp
      (isOpen_rightHalfPlane.preimage (continuous_expIterate m)) p hm
    obtain ⟨δ, hδ, hsubV, hinf⟩ := haccum η hη
    have hballconn : IsConnected (ball y δ) :=
      ⟨⟨y, Metric.mem_ball_self hδ⟩, (convex_ball y δ).isPreconnected⟩
    have hmaps : {N : ℕ | MapsTo (expIterate N) (ball y δ) rightHalfPlane}.Infinite := by
      apply Set.infinite_of_not_bddAbove
      rintro ⟨M, hM⟩
      obtain ⟨n, hn, hz⟩ := hinf (M + 1)
      have hmem : (m + n) ∈ {N : ℕ | MapsTo (expIterate N) (ball y δ) rightHalfPlane} := by
        intro z hzmem
        have h2 : expIterate n z ∈ ball p η := by
          rw [Metric.mem_ball, dist_eq_norm]; exact hz z hzmem
        have heq : expIterate (m + n) z = expIterate m (expIterate n z) :=
          Function.iterate_add_apply _ _ _ _
        rw [heq]
        exact hηball h2
      have hle := hM hmem
      omega
    obtain ⟨N, z, hz, hval⟩ := lemma5_real_axis_of_frequently_in_rightHalfPlane
      isOpen_ball hballconn ⟨y, Metric.mem_ball_self hδ⟩ hmaps
    exact hnoreal N z (hsubV hz) hval
  · -- `p` is not real: its orbit leaves the strip, contradicting Lemma 4
    obtain ⟨m, hm⟩ := lemma2b_eventually_leaves_strip (show ¬ OnRealAxis p from hpreal)
    obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.mp
      (isClosed_centralStrip.isOpen_compl.preimage (continuous_expIterate m)) p hm
    obtain ⟨δ, hδ, hsubV, hinf⟩ := haccum η hη
    have hballconn : IsConnected (ball y δ) :=
      ⟨⟨y, Metric.mem_ball_self hδ⟩, (convex_ball y δ).isPreconnected⟩
    obtain ⟨N4, hN4⟩ := lemma4_eventually_meets_centralStrip isOpen_ball hballconn
      ⟨y, Metric.mem_ball_self hδ⟩
    obtain ⟨n, hn, hz⟩ := hinf N4
    obtain ⟨x, ⟨u, hu, rfl⟩, hxs⟩ := hN4 (m + n) (by omega)
    have h2 : expIterate n u ∈ ball p η := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hz u hu
    have heq : expIterate (m + n) u = expIterate m (expIterate n u) :=
      Function.iterate_add_apply _ _ _ _
    rw [heq] at hxs
    exact hηball h2 hxs

/-- **Lemma 6.** Every non-empty open connected set has a forward image meeting the real
axis. HOL Light: `LEMMA_6`.

Harrison uses Montel's fundamental normality test for families omitting two values. Since the
images here omit the whole real axis and are connected, each lies in one open half-plane, so a
Cayley transform makes the family bounded and the Cauchy estimate suffices: see
`equicontinuous_cayleyUp` and `lemma6_accumulation_up`. The lower half-plane case reduces to
the upper one by conjugation. -/
theorem lemma6_every_domain_eventually_meets_real_axis
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty) :
    EventuallyMeetsRealAxis V := by
  by_contra hcon
  have hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0 := by
    intro n z hz hval
    exact hcon ⟨n, z, hz, hval⟩
  by_cases hup : {n : ℕ | ∀ z ∈ V, 0 < (expIterate n z).im}.Infinite
  · exact lemma6_contradiction_up hVopen hVne hnoreal hup (fun n hn z hz => hn z hz)
  · rw [Set.not_infinite] at hup
    have hdowninf : {n : ℕ | ∀ z ∈ V, (expIterate n z).im < 0}.Infinite := by
      refine Set.Infinite.mono ?_ (Set.infinite_univ.sdiff hup)
      intro n hn
      rcases image_in_half_plane hVconn hnoreal n with h | h
      · exact absurd h hn.2
      · exact h
    exact lemma6_contradiction_up (isOpen_conj_image hVopen) (nonempty_conj_image hVne)
      (noreal_conj_image hnoreal) hdowninf
      (fun n hn z hz => conj_image_up_of_down (fun u hu => hn u hu) z hz)

/- The negative-axis form of Lemma 6 is proved below as a consequence of compact covering. -/

end

end ExponentialJuliaSetMisiurewicz
