/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Topology.Semicontinuity.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Integral.Circle
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.SeparateAnalytic.Submean
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Topology.UpperSemicontinuous

/-!
# Subharmonic functions of one complex variable

A real-valued function on an open subset of `ℂ` is subharmonic if it is upper semicontinuous and
satisfies the local submean inequality: at every point, for all sufficiently small radii the
function is integrable on the circle and its value at the center is at most its circle average.
This is the definition of [Ransford][Ransford1995], *Potential Theory in the Complex Plane*,
Definition 2.2.1, and of [Fritzsche–Grauert][FritzscheGrauert2002], Chapter II, Section 2, with
the harmonic-majorant condition replaced by the submean inequality. Locality is then immediate.
The submean inequality on every closed disc in the domain and the plurisubharmonic theory are
developed in later files.

Only real-valued functions are considered; the value `-∞` is not admitted.

This file proves closure under sums, nonnegative multiples and maxima, gives the holomorphic
examples (real parts, positive powers of norms, logarithms of nonvanishing moduli), and proves
the maximum principle: a subharmonic function on a preconnected open set that attains its
supremum is constant. On a disc, if it is upper semicontinuous on the closed disc, it is
bounded by its supremum on the boundary circle.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 2;
[Range][Range1986] (1986), Chapter II, Section 5; [Ransford][Ransford1995] (1995), Chapter 2.

## Main definitions

* `HasSubmeanAt`: The local submean property at a point: for every sufficiently small radius, the
  function is integrable on the circle and its value at the center is bounded by its circle average.
* `SubharmonicOn`: A real function is subharmonic on a set if it is upper semicontinuous there and
  has the local submean property at each of its points.

## Main results

* `SubharmonicOn.eqOn_const_of_isMaxOn`: **Maximum principle.** A subharmonic function on a
  preconnected open set that attains its supremum at a point is constant.
* `SubharmonicOn.le_of_le_sphere`: **Maximum principle on a disc.** A function subharmonic on an
  open disc and upper semicontinuous on the closed disc is bounded by any bound valid on the
  boundary circle.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [T. Ransford, *Potential Theory in the Complex Plane*][Ransford1995]
-/

public section

open Filter MeasureTheory Metric Set Real
open scoped Interval Topology

namespace SeveralComplexVariables

/-- The local submean property at a point: for every sufficiently small radius, the function is
integrable on the circle and its value at the center is bounded by its circle average. -/
@[expose] def HasSubmeanAt (u : ℂ → ℝ) (a : ℂ) : Prop :=
  ∀ᶠ r in 𝓝[>] (0 : ℝ), CircleIntegrable u a r ∧ u a ≤ circleAverage u a r

/-- A real function is subharmonic on a set if it is upper semicontinuous there and has the local
submean property at each of its points. The set is intended to be open. -/
@[expose] def SubharmonicOn (u : ℂ → ℝ) (U : Set ℂ) : Prop :=
  UpperSemicontinuousOn u U ∧ ∀ a ∈ U, HasSubmeanAt u a

variable {u v : ℂ → ℝ} {U V : Set ℂ} {a : ℂ}

/-- A subharmonic function is upper semicontinuous. -/
theorem SubharmonicOn.upperSemicontinuousOn (h : SubharmonicOn u U) :
    UpperSemicontinuousOn u U := h.1

/-- A subharmonic function has the local submean property at each point of its domain. -/
theorem SubharmonicOn.hasSubmeanAt (h : SubharmonicOn u U) (ha : a ∈ U) : HasSubmeanAt u a :=
  h.2 a ha

/-- Subharmonicity restricts to subsets. -/
theorem SubharmonicOn.mono (h : SubharmonicOn u U) (hV : V ⊆ U) : SubharmonicOn u V :=
  ⟨h.1.mono hV, fun a ha => h.2 a (hV ha)⟩

/-- The local submean property provides a radius below which the inequality holds. -/
theorem HasSubmeanAt.exists_forall_lt (h : HasSubmeanAt u a) :
    ∃ ρ > 0, ∀ r, 0 < r → r < ρ → CircleIntegrable u a r ∧ u a ≤ circleAverage u a r := by
  obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  exact ⟨ρ, hρ, fun r h0 hr => hsub ⟨h0, hr⟩⟩

/-- Conversely, a radius bound gives the local submean property. -/
theorem hasSubmeanAt_of_forall_lt {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ r, 0 < r → r < ρ → CircleIntegrable u a r ∧ u a ≤ circleAverage u a r) :
    HasSubmeanAt u a :=
  mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨ρ, hρ, fun r hr => h r hr.1 hr.2⟩

/-- Subharmonicity is a local property. -/
theorem subharmonicOn_of_locally (h : ∀ a ∈ U, ∃ V ∈ 𝓝 a, SubharmonicOn u (V ∩ U)) :
    SubharmonicOn u U := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨V, hV, hu⟩ := h a ha
    intro y hy
    have := hu.1 a ⟨mem_of_mem_nhds hV, ha⟩ y hy
    rwa [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hV)] at this
  · obtain ⟨V, hV, hu⟩ := h a ha
    exact hu.2 a ⟨mem_of_mem_nhds hV, ha⟩

section Algebra

/-- Constants have the local submean property. -/
theorem hasSubmeanAt_const (c : ℝ) (a : ℂ) : HasSubmeanAt (fun _ => c) a :=
  Filter.Eventually.of_forall fun _ => ⟨circleIntegrable_const c a _, by rw [circleAverage_const]⟩

/-- Constants are subharmonic. -/
theorem subharmonicOn_const (c : ℝ) (U : Set ℂ) : SubharmonicOn (fun _ => c) U :=
  ⟨continuousOn_const.upperSemicontinuousOn, fun a _ => hasSubmeanAt_const c a⟩

/-- The local submean property is additive. -/
theorem HasSubmeanAt.add (hu : HasSubmeanAt u a) (hv : HasSubmeanAt v a) :
    HasSubmeanAt (fun z => u z + v z) a := by
  filter_upwards [hu, hv] with r ⟨hui, hu'⟩ ⟨hvi, hv'⟩
  refine ⟨hui.add hvi, ?_⟩
  rw [circleAverage_fun_add hui hvi]
  exact add_le_add hu' hv'

/-- Sums of subharmonic functions are subharmonic. -/
theorem SubharmonicOn.add (hu : SubharmonicOn u U) (hv : SubharmonicOn v U) :
    SubharmonicOn (fun z => u z + v z) U :=
  ⟨hu.1.add hv.1, fun a ha => (hu.2 a ha).add (hv.2 a ha)⟩

/-- Nonnegative multiples preserve the local submean property. -/
theorem HasSubmeanAt.const_mul {c : ℝ} (hc : 0 ≤ c) (hu : HasSubmeanAt u a) :
    HasSubmeanAt (fun z => c * u z) a := by
  filter_upwards [hu] with r ⟨hui, hu'⟩
  refine ⟨(circleIntegrable_def _ a r).mpr (((circleIntegrable_def u a r).mp hui).const_mul c), ?_⟩
  simp only [← smul_eq_mul, circleAverage_fun_smul]
  exact smul_le_smul_of_nonneg_left hu' hc

/-- Nonnegative multiples of subharmonic functions are subharmonic. -/
theorem SubharmonicOn.const_mul {c : ℝ} (hc : 0 ≤ c) (hu : SubharmonicOn u U) :
    SubharmonicOn (fun z => c * u z) U :=
  ⟨hu.1.const_mul hc, fun a ha => (hu.2 a ha).const_mul hc⟩

/-- The pointwise maximum preserves the local submean property. -/
theorem HasSubmeanAt.sup (hu : HasSubmeanAt u a) (hv : HasSubmeanAt v a) :
    HasSubmeanAt (fun z => max (u z) (v z)) a := by
  filter_upwards [hu, hv] with r ⟨hui, hu'⟩ ⟨hvi, hv'⟩
  have hm := CircleIntegrable.max hui hvi
  refine ⟨hm, max_le ?_ ?_⟩
  · exact hu'.trans (circleAverage_mono hui hm fun z _ => le_max_left _ _)
  · exact hv'.trans (circleAverage_mono hvi hm fun z _ => le_max_right _ _)

/-- The pointwise maximum of two subharmonic functions is subharmonic. -/
theorem SubharmonicOn.sup (hu : SubharmonicOn u U) (hv : SubharmonicOn v U) :
    SubharmonicOn (fun z => max (u z) (v z)) U :=
  ⟨hu.1.sup hv.1, fun a ha => (hu.2 a ha).sup (hv.2 a ha)⟩

end Algebra

section Holomorphic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A continuous function whose circle averages over all small circles equal its value at the center
has the local submean property; this applies to harmonic functions. -/
theorem hasSubmeanAt_of_circleAverage_eq {ρ : ℝ} (hρ : 0 < ρ) (hc : ContinuousOn u (ball a ρ))
    (h : ∀ r, 0 < r → r < ρ → circleAverage u a r = u a) : HasSubmeanAt u a :=
  hasSubmeanAt_of_forall_lt hρ fun r hr hrρ =>
    ⟨(hc.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hrρ))).circleIntegrable
      hr.le, (h r hr hrρ).ge⟩

/-- Real parts of holomorphic functions have the local submean property, with equality. -/
theorem circleAverage_re_eq_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f a) :
    ∃ ρ > 0, ∀ r, 0 < r → r < ρ → circleAverage (fun z => (f z).re) a r = (f a).re := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  have han : AnalyticOnNhd ℂ f (ball a ρ) := fun z hz => hball hz
  refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
  have hd : DiffContOnCl ℂ f (ball a |r|) := by
    rw [abs_of_pos hr]
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball a hr.ne']
    exact fun z hz => (han z (closedBall_subset_ball hrρ
      hz)).differentiableAt.differentiableWithinAt
  have hint : CircleIntegrable f a r :=
    ((han.mono (sphere_subset_closedBall.trans (closedBall_subset_ball
      hrρ))).continuousOn).circleIntegrable hr.le
  have := Complex.reCLM.circleAverage_comp_comm (f := f) (c := a) (R := r)
  simp only [Function.comp_def, Complex.reCLM_apply] at this
  rw [this hint, hd.circleAverage]

/-- The real part of a holomorphic function is subharmonic. -/
theorem _root_.AnalyticOnNhd.subharmonicOn_re {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    SubharmonicOn (fun z => (f z).re) U := by
  refine ⟨(Complex.continuous_re.comp_continuousOn hf.continuousOn).upperSemicontinuousOn,
    fun a ha => ?_⟩
  obtain ⟨ρ, hρ, h⟩ := circleAverage_re_eq_of_analyticAt (hf a ha)
  obtain ⟨ρ', hρ', hball⟩ := Metric.mem_nhds_iff.mp (hf a ha).eventually_analyticAt
  refine hasSubmeanAt_of_circleAverage_eq (lt_min hρ hρ') ?_ fun r hr hrρ => h r hr (hrρ.trans_le
    (min_le_left _ _))
  exact Complex.continuous_re.comp_continuousOn
    ((AnalyticOnNhd.continuousOn fun z hz => hball (ball_subset_ball (min_le_right _ _) hz)))

/-- Minus the real part of a holomorphic function is subharmonic. -/
theorem _root_.AnalyticOnNhd.subharmonicOn_neg_re {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    SubharmonicOn (fun z => -(f z).re) U := by
  have := AnalyticOnNhd.subharmonicOn_re (U := U) (f := fun z => -f z) (hf.neg)
  simpa using this

/-- Positive powers of the norm of a holomorphic function are subharmonic. -/
theorem _root_.AnalyticOnNhd.subharmonicOn_norm_rpow (hU : IsOpen U) {f : ℂ → F} {p : ℝ}
    (hp : 0 < p)
    (hf : AnalyticOnNhd ℂ f U) : SubharmonicOn (fun z => ‖f z‖ ^ p) U := by
  refine ⟨(hf.continuousOn.norm.rpow_const fun _ _ => Or.inr hp.le).upperSemicontinuousOn,
    fun a ha => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  refine hasSubmeanAt_of_forall_lt hρ fun r hr hrρ => ?_
  have hsub : closedBall a r ⊆ U := (closedBall_subset_ball hrρ).trans hball
  refine ⟨((hf.mono hsub).continuousOn.norm.rpow_const fun _ _ => Or.inr hp.le).mono
    sphere_subset_closedBall |>.circleIntegrable hr.le, ?_⟩
  exact norm_rpow_le_circleAverage hr hp (hf.mono hsub)

/-- The logarithm of the modulus of a nonvanishing holomorphic function is subharmonic. -/
theorem _root_.AnalyticOnNhd.subharmonicOn_log_norm (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0) :
    SubharmonicOn (fun z => Real.log ‖f z‖) U := by
  have hcont : ContinuousOn (fun z => Real.log ‖f z‖) U := by
    refine ContinuousOn.log hf.continuousOn.norm fun z hz => norm_ne_zero_iff.mpr (hne z hz)
  refine ⟨hcont.upperSemicontinuousOn, fun a ha => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  refine hasSubmeanAt_of_forall_lt hρ fun r hr hrρ => ?_
  have hsub : closedBall a r ⊆ U := (closedBall_subset_ball hrρ).trans hball
  refine ⟨(hcont.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le, ?_⟩
  exact log_norm_le_circleAverage hr (hf.mono hsub) (hne a ha)

end Holomorphic

section MaximumPrinciple

/-- A circle-integrable function bounded by `M` on a circle, upper semicontinuous there and strictly
below `M` at one point, has circle average strictly below `M`. -/
theorem circleAverage_lt_of_lt {r M : ℝ} (hr : 0 < r) (hint : CircleIntegrable u a r)
    (hle : ∀ z ∈ sphere a r, u z ≤ M) (husc : UpperSemicontinuousOn u (sphere a r))
    {z : ℂ} (hz : z ∈ sphere a r) (hlt : u z < M) : circleAverage u a r < M := by
  -- a parameter in `[0, 2π)` for the point `z`
  obtain ⟨θ, hθ⟩ : ∃ θ, circleMap a r θ = z := by
    have : z ∈ range (circleMap a r) := by rw [range_circleMap, abs_of_pos hr]; exact hz
    exact this
  set θ₀ := toIcoMod two_pi_pos 0 θ with hθ₀
  have hθ₀mem : θ₀ ∈ Ico 0 (2 * π) := by simpa using toIcoMod_mem_Ico two_pi_pos 0 θ
  have hθ₀z : circleMap a r θ₀ = z := by
    rw [hθ₀, ← self_sub_toIcoDiv_zsmul two_pi_pos 0 θ, (periodic_circleMap a r).sub_zsmul_eq, hθ]
  -- upper semicontinuity gives a small arc on which `u < M - ε`
  set ε := (M - u z) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have husc' := husc z hz (u z + ε) (by linarith)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp husc'
  have hballnhds : ball z δ ∈ 𝓝 (circleMap a r θ₀) := by
    rw [hθ₀z]
    exact ball_mem_nhds z hδ
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp
    ((continuous_circleMap a r).continuousAt.preimage_mem_nhds hballnhds)
  set θ₁ := min (θ₀ + η / 2) (2 * π) with hθ₁
  have hθ₀₁ : θ₀ < θ₁ := lt_min (by linarith) hθ₀mem.2
  have hθ₁le : θ₁ ≤ 2 * π := min_le_right _ _
  have harc : ∀ x ∈ Icc θ₀ θ₁, u (circleMap a r x) ≤ M - ε := by
    intro x hx
    have hxη : x ∈ ball θ₀ η := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2, min_le_left (θ₀ + η / 2) (2 * π)]
    have hmem : circleMap a r x ∈ ball z δ := hηsub hxη
    have : u (circleMap a r x) < u z + ε :=
      hδsub ⟨hmem, circleMap_mem_sphere a hr.le x⟩
    linarith
  -- compare integrals of the nonnegative function `M - u`
  set g : ℝ → ℝ := fun x => M - u (circleMap a r x) with hg
  have hgint : IntervalIntegrable g volume 0 (2 * π) :=
    (intervalIntegrable_const).sub ((circleIntegrable_def u a r).mp hint)
  have hgnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))] g := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x _ => ?_)
    exact sub_nonneg.mpr (hle _ (circleMap_mem_sphere a hr.le x))
  have hsmall : (θ₁ - θ₀) * ε ≤ ∫ x in θ₀..θ₁, g x := by
    have hsub : [[θ₀, θ₁]] ⊆ [[0, 2 * π]] := by
      rw [uIcc_of_le hθ₀₁.le, uIcc_of_le Real.two_pi_pos.le]
      exact Icc_subset_Icc hθ₀mem.1 hθ₁le
    have := intervalIntegral.integral_mono_on hθ₀₁.le intervalIntegrable_const
      (hgint.mono_set hsub) fun x hx => (by linarith [harc x hx] : ε ≤ g x)
    simpa using this
  have hbig : ∫ x in θ₀..θ₁, g x ≤ ∫ x in (0:ℝ)..2 * π, g x :=
    intervalIntegral.integral_mono_interval hθ₀mem.1 hθ₀₁.le hθ₁le hgnn hgint
  have hpos : 0 < ∫ x in (0:ℝ)..2 * π, g x :=
    (mul_pos (sub_pos.mpr hθ₀₁) hε0).trans_le (hsmall.trans hbig)
  have hcalc : ∫ x in (0:ℝ)..2 * π, g x = 2 * π * (M - circleAverage u a r) := by
    rw [hg, intervalIntegral.integral_sub intervalIntegrable_const
      ((circleIntegrable_def u a r).mp hint), intervalIntegral.integral_const,
      circleAverage_def, smul_eq_mul, smul_eq_mul, sub_zero]
    field_simp
  rw [hcalc] at hpos
  nlinarith [Real.two_pi_pos]

/-- A subharmonic function attaining its supremum at a point is constant near that point. -/
theorem SubharmonicOn.eventually_eq_of_isMaxOn (hU : IsOpen U) (hu : SubharmonicOn u U)
    (ha : a ∈ U) (hmax : ∀ z ∈ U, u z ≤ u a) : ∀ᶠ z in 𝓝 a, u z = u a := by
  obtain ⟨ρ₁, hρ₁, hsub⟩ := (hu.hasSubmeanAt ha).exists_forall_lt
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  filter_upwards [ball_mem_nhds a (lt_min hρ₁ hρ₂)] with z hz
  by_cases hza : z = a
  · rw [hza]
  · have hr0 : 0 < dist z a := dist_pos.mpr hza
    have hrρ₁ : dist z a < ρ₁ := (mem_ball.mp hz).trans_le (min_le_left _ _)
    have hsph : sphere a (dist z a) ⊆ U := fun w hw => hball (by
      rw [mem_ball, mem_sphere.mp hw]
      exact (mem_ball.mp hz).trans_le (min_le_right _ _))
    obtain ⟨hint, havg⟩ := hsub _ hr0 hrρ₁
    by_contra hne
    have hzs : z ∈ sphere a (dist z a) := mem_sphere.mpr rfl
    have hlt : u z < u a := lt_of_le_of_ne (hmax z (hsph hzs)) hne
    have := circleAverage_lt_of_lt hr0 hint (fun w hw => hmax w (hsph hw)) (hu.1.mono hsph) hzs hlt
    linarith

/-- **Maximum principle.** A subharmonic function on a preconnected open set that attains
its supremum at a point is constant. -/
theorem SubharmonicOn.eqOn_const_of_isMaxOn (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : SubharmonicOn u U) (ha : a ∈ U) (hmax : ∀ z ∈ U, u z ≤ u a) :
    ∀ z ∈ U, u z = u a := by
  let W := U ∩ {z | ∀ᶠ w in 𝓝 z, u w = u a}
  have hWo : IsOpen W := hU.inter isOpen_setOfPred_eventually_nhds
  have hWne : (U ∩ W).Nonempty := ⟨a, ha, ha, hu.eventually_eq_of_isMaxOn hU ha hmax⟩
  have hWval : ∀ w ∈ W, u w = u a := fun w hw => (mem_ofPred.mp hw.2).self_of_nhds
  have hcl : closure W ∩ U ⊆ W := by
    rintro z ⟨hz, hzU⟩
    have hle : u a ≤ u z := by
      by_contra hlt
      push Not at hlt
      have hne : NeBot (𝓝[W] z) := mem_closure_iff_nhdsWithin_neBot.mp hz
      have h1 : ∀ᶠ w in 𝓝[W] z, u w < u a :=
        nhdsWithin_mono z inter_subset_left (hu.1 z hzU (u a) hlt)
      have h2 : ∀ᶠ w in 𝓝[W] z, u w = u a := eventually_nhdsWithin_of_forall hWval
      obtain ⟨w, hw1, hw2⟩ := (h1.and h2).exists
      linarith
    have heq : u z = u a := le_antisymm (hmax z hzU) hle
    refine ⟨hzU, ?_⟩
    have := hu.eventually_eq_of_isMaxOn hU hzU (fun w hw => (hmax w hw).trans heq.ge)
    show ∀ᶠ w in 𝓝 z, u w = u a
    simpa only [heq] using this
  intro z hz
  exact hWval z (hc.subset_of_closure_inter_subset hWo hWne hcl hz)

/-- **Maximum principle on a disc.** A function subharmonic on an open disc and upper
semicontinuous on the closed disc is bounded by any bound valid on the boundary circle. -/
theorem SubharmonicOn.le_of_le_sphere {r M : ℝ} (hr : 0 < r) (hu : SubharmonicOn u (ball a r))
    (husc : UpperSemicontinuousOn u (closedBall a r)) (hM : ∀ z ∈ sphere a r, u z ≤ M) :
    ∀ z ∈ closedBall a r, u z ≤ M := by
  obtain ⟨z₀, hz₀, hmax⟩ :=
    husc.exists_isMaxOn (nonempty_closedBall.mpr hr.le) (isCompact_closedBall a r)
  suffices h : u z₀ ≤ M from fun z hz => (hmax hz).trans h
  by_cases hs : z₀ ∈ sphere a r
  · exact hM z₀ hs
  · have hz₀b : z₀ ∈ ball a r := by
      rw [mem_closedBall] at hz₀
      exact mem_ball.mpr (lt_of_le_of_ne hz₀ fun h => hs (mem_sphere.mpr h))
    have hconst := hu.eqOn_const_of_isMaxOn isOpen_ball isPreconnected_ball hz₀b
      fun z hz => hmax (ball_subset_closedBall hz)
    obtain ⟨p, hp⟩ : (sphere a r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have hpcl : p ∈ closedBall a r := sphere_subset_closedBall hp
    have hle : u z₀ ≤ u p := by
      by_contra hlt
      push Not at hlt
      have hne : NeBot (𝓝[ball a r] p) := mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_ball a hr.ne']
        exact hpcl)
      have h1 : ∀ᶠ w in 𝓝[ball a r] p, u w < u z₀ :=
        nhdsWithin_mono p ball_subset_closedBall (husc p hpcl (u z₀) hlt)
      have h2 : ∀ᶠ w in 𝓝[ball a r] p, u w = u z₀ := eventually_nhdsWithin_of_forall hconst
      obtain ⟨w, hw1, hw2⟩ := (h1.and h2).exists
      linarith
    exact hle.trans (hM p hp)

end MaximumPrinciple

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
