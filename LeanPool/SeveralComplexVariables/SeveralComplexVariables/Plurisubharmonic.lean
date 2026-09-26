/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Subharmonic

/-!
# Plurisubharmonic functions

A real function on an open subset of a complex normed space is plurisubharmonic if it is upper
semicontinuous and its restriction to every complex line is subharmonic, in the local submean
sense of `Subharmonic`. This file proves closure under sums, nonnegative multiples, maxima and
complex affine substitutions, shows that continuous convex functions are plurisubharmonic, and
gives the holomorphic examples: real parts, positive powers of norms, and logarithms of
nonvanishing moduli of holomorphic functions.

Only real-valued functions are considered. The characterization of `C²` plurisubharmonic
functions through the Levi form is proved in `LeviForm`.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 2;
[Hörmander][Hormander1973] (1973), Definition 2.6.1; [Range][Range1986] (1986), Chapter II,
Section 5.

## Main definitions

* `PlurisubharmonicOn`: A real function is plurisubharmonic on a set if it is upper semicontinuous
  there and its restriction to every complex line is subharmonic on the corresponding parameter set.

## Main results

* `PlurisubharmonicOn.add`: Sums of plurisubharmonic functions are plurisubharmonic.
* `PlurisubharmonicOn.sup`: The pointwise maximum of two plurisubharmonic functions is
  plurisubharmonic.
* `PlurisubharmonicOn.comp_affine`: Plurisubharmonicity is preserved by complex affine
  substitutions.
* `ConvexOn.plurisubharmonicOn`: A continuous convex function on an open set is plurisubharmonic.
* `plurisubharmonicOn_norm`: The norm is plurisubharmonic.
* `AnalyticOnNhd.plurisubharmonicOn_re`: Real parts of holomorphic functions are plurisubharmonic.
* `AnalyticOnNhd.plurisubharmonicOn_norm_rpow`: Positive powers of the norm of a holomorphic map are
  plurisubharmonic.
* `AnalyticOnNhd.plurisubharmonicOn_log_norm`: The logarithm of the modulus of a nonvanishing
  holomorphic function is plurisubharmonic.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public section

open Filter Metric Set Real
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A real function is plurisubharmonic on a set if it is upper semicontinuous there and its
restriction to every complex line is subharmonic on the corresponding parameter set. -/
@[expose] def PlurisubharmonicOn (f : E → ℝ) (U : Set E) : Prop :=
  UpperSemicontinuousOn f U ∧
    ∀ a ∈ U, ∀ w : E, SubharmonicOn (fun t : ℂ => f (a + t • w)) {t | a + t • w ∈ U}

variable {f g : E → ℝ} {U V : Set E}

/-- A plurisubharmonic function is upper semicontinuous. -/
theorem PlurisubharmonicOn.upperSemicontinuousOn (h : PlurisubharmonicOn f U) :
    UpperSemicontinuousOn f U := h.1

/-- Complex-line slices of a plurisubharmonic function are subharmonic. -/
theorem PlurisubharmonicOn.slice (h : PlurisubharmonicOn f U) {a : E} (ha : a ∈ U) (w : E) :
    SubharmonicOn (fun t : ℂ => f (a + t • w)) {t | a + t • w ∈ U} := h.2 a ha w

/-- The local submean property of the slice through a point of the domain. -/
theorem PlurisubharmonicOn.hasSubmeanAt_slice (h : PlurisubharmonicOn f U) {a : E} (ha : a ∈ U)
    (w : E) : HasSubmeanAt (fun t : ℂ => f (a + t • w)) 0 :=
  (h.slice ha w).hasSubmeanAt (by simpa using ha)

/-- Plurisubharmonicity restricts to subsets. -/
theorem PlurisubharmonicOn.mono (h : PlurisubharmonicOn f U) (hV : V ⊆ U) :
    PlurisubharmonicOn f V :=
  ⟨h.1.mono hV, fun a ha w => (h.2 a (hV ha) w).mono fun _ ht => hV ht⟩

/-- The slice of an upper semicontinuous function is upper semicontinuous. -/
theorem upperSemicontinuousOn_slice (h : UpperSemicontinuousOn f U) (a w : E) :
    UpperSemicontinuousOn (fun t : ℂ => f (a + t • w)) {t | a + t • w ∈ U} :=
  h.comp (by fun_prop : Continuous fun t : ℂ => a + t • w).continuousOn fun _ ht => ht

/-- Translating the parameter of a function with the local submean property. -/
theorem HasSubmeanAt.comp_add_right {u : ℂ → ℝ} {t₀ : ℂ}
    (h : HasSubmeanAt (fun t => u (t + t₀)) 0) : HasSubmeanAt u t₀ := by
  filter_upwards [h] with r ⟨hint, hle⟩
  have hmap : ∀ θ : ℝ, circleMap 0 r θ + t₀ = circleMap t₀ r θ := fun θ => by
    simp [circleMap, add_comm]
  refine ⟨?_, ?_⟩
  · rw [circleIntegrable_def] at hint ⊢
    simpa only [hmap] using hint
  · simpa only [zero_add, circleAverage_map_add_const] using hle

/-- Plurisubharmonicity follows from upper semicontinuity and the local submean property of the
slices through each point of the domain. -/
theorem plurisubharmonicOn_of_hasSubmeanAt (husc : UpperSemicontinuousOn f U)
    (h : ∀ a ∈ U, ∀ w : E, HasSubmeanAt (fun t : ℂ => f (a + t • w)) 0) :
    PlurisubharmonicOn f U := by
  refine ⟨husc, fun a ha w => ⟨upperSemicontinuousOn_slice husc a w, fun t₀ ht₀ => ?_⟩⟩
  apply HasSubmeanAt.comp_add_right
  have := h (a + t₀ • w) ht₀ w
  convert this using 2 with t
  simp only [add_smul, add_assoc, add_comm (t • w) (t₀ • w)]

section Algebra

/-- Constants are plurisubharmonic. -/
theorem plurisubharmonicOn_const (c : ℝ) (U : Set E) : PlurisubharmonicOn (fun _ => c) U :=
  ⟨continuousOn_const.upperSemicontinuousOn, fun _ _ _ => subharmonicOn_const c _⟩

/-- Sums of plurisubharmonic functions are plurisubharmonic. -/
theorem PlurisubharmonicOn.add (hf : PlurisubharmonicOn f U) (hg : PlurisubharmonicOn g U) :
    PlurisubharmonicOn (fun z => f z + g z) U :=
  ⟨hf.1.add hg.1, fun a ha w => (hf.2 a ha w).add (hg.2 a ha w)⟩

/-- Nonnegative multiples of plurisubharmonic functions are plurisubharmonic. -/
theorem PlurisubharmonicOn.const_mul {c : ℝ} (hc : 0 ≤ c) (hf : PlurisubharmonicOn f U) :
    PlurisubharmonicOn (fun z => c * f z) U :=
  ⟨(hf.1.const_mul hc), fun a ha w => (hf.2 a ha w).const_mul hc⟩

/-- The pointwise maximum of two plurisubharmonic functions is plurisubharmonic. -/
theorem PlurisubharmonicOn.sup (hf : PlurisubharmonicOn f U) (hg : PlurisubharmonicOn g U) :
    PlurisubharmonicOn (fun z => max (f z) (g z)) U :=
  ⟨hf.1.sup hg.1, fun a ha w => (hf.2 a ha w).sup (hg.2 a ha w)⟩

/-- Plurisubharmonicity is preserved by complex affine substitutions. -/
theorem PlurisubharmonicOn.comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hf : PlurisubharmonicOn f U) (L : F →L[ℂ] E) (b : E) :
    PlurisubharmonicOn (fun z => f (b + L z)) {z | b + L z ∈ U} := by
  refine ⟨hf.1.comp (by fun_prop) fun _ hz => hz, fun a ha w => ?_⟩
  have := hf.2 (b + L a) ha (L w)
  convert this using 2 with t <;> simp [map_add, map_smul, add_assoc]

end Algebra

section Convex

/-- A continuous function that is convex on an open set of `ℂ` is subharmonic there. -/
theorem _root_.ConvexOn.subharmonicOn {u : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hu : ConvexOn ℝ W u) (hc : ContinuousOn u W) : SubharmonicOn u W := by
  refine ⟨hc.upperSemicontinuousOn, fun a ha => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds ha)
  refine hasSubmeanAt_of_forall_lt hρ fun r hr hrρ => ?_
  have hsub : closedBall a r ⊆ W := (closedBall_subset_ball hrρ).trans hball
  have hint : CircleIntegrable u a r :=
    (hc.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le
  have hrefl : ∀ t ∈ sphere a r, 2 * a - t ∈ sphere a r := by
    intro t ht
    rw [mem_sphere, dist_eq_norm] at ht ⊢
    rw [← ht, ← norm_neg]
    congr 1
    ring
  have hint' : CircleIntegrable (fun t => u (2 * a - t)) a r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    exact (hc.mono (sphere_subset_closedBall.trans hsub)).comp (by fun_prop) fun t ht =>
      hrefl t (by simpa [abs_of_pos hr] using ht)
  refine ⟨hint, ?_⟩
  have hmid : ∀ t ∈ sphere a r, u a ≤ (1 / 2 : ℝ) • u t + (1 / 2 : ℝ) • u (2 * a - t) := by
    intro t ht
    have h1 : t ∈ W := hsub (sphere_subset_closedBall ht)
    have h2 : 2 * a - t ∈ W := hsub (sphere_subset_closedBall (hrefl t ht))
    have := hu.2 h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert this using 2
    simp only [Complex.real_smul]
    push_cast
    ring
  have hi₁ : CircleIntegrable (fun t => (1 / 2 : ℝ) • u t) a r := hint.const_smul
  have hi₂ : CircleIntegrable (fun t => (1 / 2 : ℝ) • u (2 * a - t)) a r := hint'.const_smul
  have hle := circleAverage_mono (circleIntegrable_const (u a) a r) (hi₁.add hi₂)
    (fun t ht => hmid t (by simpa [abs_of_pos hr] using ht))
  rw [circleAverage_const, circleAverage_add hi₁ hi₂, circleAverage_fun_smul,
    circleAverage_fun_smul, Real.circleAverage_reflect] at hle
  simp only [smul_eq_mul] at hle
  linarith

/-- A real convex combination of two points of a complex line, in line coordinates. -/
private theorem line_combo (a w : E) (s t : ℂ) {α β : ℝ} (hαβ : α + β = 1) :
    a + (α • s + β • t) • w = α • (a + s • w) + β • (a + t • w) := by
  have ha : a = α • a + β • a := by rw [← add_smul, hαβ, one_smul]
  conv_lhs => rw [ha]
  simp only [smul_add, add_smul, Complex.real_smul, mul_smul, Complex.coe_smul]
  abel

/-- A continuous convex function on an open set is plurisubharmonic. -/
theorem _root_.ConvexOn.plurisubharmonicOn (hU : IsOpen U) (hf : ConvexOn ℝ U f)
    (hc : ContinuousOn f U) : PlurisubharmonicOn f U := by
  refine ⟨hc.upperSemicontinuousOn, fun a ha w => ?_⟩
  apply ConvexOn.subharmonicOn (hU.preimage (by fun_prop : Continuous fun t : ℂ => a + t • w))
  · refine ⟨fun s hs t ht α β hα hβ hαβ => ?_, fun s hs t ht α β hα hβ hαβ => ?_⟩
    · change a + (α • s + β • t) • w ∈ U
      rw [line_combo a w s t hαβ]
      exact hf.1 hs ht hα hβ hαβ
    · have := hf.2 hs ht hα hβ hαβ
      simpa only [line_combo a w s t hαβ] using this
  · exact hc.comp (by fun_prop : Continuous fun t : ℂ => a + t • w).continuousOn fun _ ht => ht

/-- The norm is plurisubharmonic. -/
theorem plurisubharmonicOn_norm : PlurisubharmonicOn (fun z : E => ‖z‖) univ :=
  ConvexOn.plurisubharmonicOn isOpen_univ (convexOn_norm convex_univ)
    continuous_norm.continuousOn

end Convex

section Holomorphic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The slice of a holomorphic map along a complex line is holomorphic. -/
theorem analyticOnNhd_slice {h : E → F} (hh : AnalyticOnNhd ℂ h U) (a w : E) :
    AnalyticOnNhd ℂ (fun t : ℂ => h (a + t • w)) {t | a + t • w ∈ U} := fun _ ht =>
  (hh _ ht).comp_of_eq (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) rfl

/-- Real parts of holomorphic functions are plurisubharmonic. -/
theorem _root_.AnalyticOnNhd.plurisubharmonicOn_re {h : E → ℂ} (hh : AnalyticOnNhd ℂ h U) :
    PlurisubharmonicOn (fun z => (h z).re) U :=
  ⟨(Complex.continuous_re.comp_continuousOn hh.continuousOn).upperSemicontinuousOn,
    fun a _ w => AnalyticOnNhd.subharmonicOn_re (analyticOnNhd_slice hh a w)⟩

/-- Positive powers of the norm of a holomorphic map are plurisubharmonic. -/
theorem _root_.AnalyticOnNhd.plurisubharmonicOn_norm_rpow (hU : IsOpen U) {h : E → F} {p : ℝ}
    (hp : 0 < p) (hh : AnalyticOnNhd ℂ h U) : PlurisubharmonicOn (fun z => ‖h z‖ ^ p) U :=
  ⟨(hh.continuousOn.norm.rpow_const fun _ _ => Or.inr hp.le).upperSemicontinuousOn,
    fun a _ w => AnalyticOnNhd.subharmonicOn_norm_rpow
      (hU.preimage (by fun_prop : Continuous fun t : ℂ => a + t • w)) hp
      (analyticOnNhd_slice hh a w)⟩

/-- The logarithm of the modulus of a nonvanishing holomorphic function is plurisubharmonic. -/
theorem _root_.AnalyticOnNhd.plurisubharmonicOn_log_norm (hU : IsOpen U) {h : E → ℂ}
    (hh : AnalyticOnNhd ℂ h U) (hne : ∀ z ∈ U, h z ≠ 0) :
    PlurisubharmonicOn (fun z => Real.log ‖h z‖) U :=
  ⟨(ContinuousOn.log hh.continuousOn.norm fun z hz =>
      norm_ne_zero_iff.mpr (hne z hz)).upperSemicontinuousOn,
    fun a _ w => AnalyticOnNhd.subharmonicOn_log_norm
      (hU.preimage (by fun_prop : Continuous fun t : ℂ => a + t • w))
      (analyticOnNhd_slice hh a w) fun _ ht => hne _ ht⟩

end Holomorphic

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
