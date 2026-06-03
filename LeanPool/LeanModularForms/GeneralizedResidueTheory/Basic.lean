/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Homotopy.Basic

/-!
# Basic Definitions for Complex Analysis with Principal Values

Core definitions for piecewise C¹ curves, Cauchy principal value integrals,
and generalized winding numbers following Hungerbühler–Wasem.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- A piecewise continuously differentiable curve γ : [a,b] → ℂ.
The curve is C¹ on each subinterval between partition points. -/
structure PiecewiseC1Curve where
  /-- The underlying parametrization of the curve. -/
  toFun : ℝ → ℂ
  /-- The left endpoint of the parameter interval. -/
  a : ℝ
  /-- The right endpoint of the parameter interval. -/
  b : ℝ
  hab : a < b
  /-- The finite set of partition points subdividing `[a, b]`. -/
  partition : Finset ℝ
  partition_subset : ↑partition ⊆ Icc a b
  endpoints_in_partition : a ∈ partition ∧ b ∈ partition
  continuous_toFun : ContinuousOn toFun (Icc a b)
  smooth_off_partition : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ toFun t
  deriv_continuous_off_partition : ∀ t ∈ Ioo a b, t ∉ partition →
    ContinuousAt (deriv toFun) t

instance : CoeFun PiecewiseC1Curve fun _ => ℝ → ℂ where
  coe := PiecewiseC1Curve.toFun

/-- A closed curve has γ(a) = γ(b). -/
def PiecewiseC1Curve.IsClosed (γ : PiecewiseC1Curve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- A piecewise C¹ immersion: a piecewise C¹ curve with nonzero derivative. -/
structure PiecewiseC1Immersion extends PiecewiseC1Curve where
  deriv_ne_zero : ∀ t ∈ Icc a b, t ∉ partition → deriv toFun t ≠ 0
  left_deriv_limit : ∀ p ∈ partition, a < p →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toFun) (𝓝[<] p) (𝓝 L)
  right_deriv_limit : ∀ p ∈ partition, p < b →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toFun) (𝓝[>] p) (𝓝 L)

/-- The Cauchy principal value integrand at cutoff ε. -/
def cauchyPrincipalValueIntegrand' (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

@[simp]
theorem cauchyPrincipalValueIntegrand'_of_gt {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ}
    (h : ε < ‖γ t - z₀‖) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε t = f (γ t) * deriv γ t := by
  simp only [cauchyPrincipalValueIntegrand', show ‖γ t - z₀‖ > ε from h, ite_true]

@[simp]
theorem cauchyPrincipalValueIntegrand'_of_le {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ}
    (h : ‖γ t - z₀‖ ≤ ε) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε t = 0 := by
  simp only [cauchyPrincipalValueIntegrand', show ¬(‖γ t - z₀‖ > ε) from not_lt.mpr h, ite_false]

/-- The Cauchy principal value of ∮_γ f(z) dz, excluding ε-neighborhoods of z₀. -/
def cauchyPrincipalValue' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value exists if the limit exists. -/
def CauchyPrincipalValueExists' (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun ε =>
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
    (𝓝[>] 0) (𝓝 L)

/-- The generalized winding number of γ around z₀, defined via principal value.
`n_{z₀}(γ) = (1/2πi) · PV ∮_γ dz/(z - z₀)`. -/
def generalizedWindingNumber' (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0

/-- Two curves are homotopic relative to endpoints. -/
def CurvesHomotopic (Γ γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = Γ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = H (a, 0) ∧ H (b, s) = H (b, 0))

/-- Homotopy avoiding a point z₀. -/
def CurvesHomotopicAvoiding (Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = Γ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = z₀ ∧ H (b, s) = z₀) ∧
    (∀ t ∈ Ioo a b, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀)

private theorem aestronglyMeasurable_of_continuousOn_off_finite
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hf_cont : ContinuousOn f ((Icc a b) \ P)) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  have h_union : Icc a b =
      (Icc a b \ (P : Set ℝ)) ∪ ((P : Set ℝ) ∩ Icc a b) := by
    ext x; simp [and_comm]; tauto
  rw [h_union, aestronglyMeasurable_union_iff]
  constructor
  · exact hf_cont.aestronglyMeasurable
      (measurableSet_Icc.diff (Finset.measurableSet P))
  · rw [Measure.restrict_zero_set
      ((Finset.finite_toSet P |>.inter_of_left (Icc a b)).measure_zero _)]
    exact aestronglyMeasurable_zero_measure f

/-- A piecewise continuous bounded function is interval integrable. -/
theorem intervalIntegrable_of_piecewise_continuousOn_bounded
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (M : ℝ)
    (hab : a ≤ b)
    (hf_cont : ContinuousOn f ((Icc a b) \ P))
    (hf_bound : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) :
    IntervalIntegrable f volume a b := by
  have hf_int : IntegrableOn f (Icc a b) volume :=
    ⟨aestronglyMeasurable_of_continuousOn_off_finite hf_cont,
     MeasureTheory.HasFiniteIntegral.restrict_of_bounded M
       (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
       (by filter_upwards [ae_restrict_mem measurableSet_Icc]
           with t ht; exact hf_bound t ht)⟩
  rw [← uIcc_of_le hab] at hf_int
  exact hf_int.intervalIntegrable

/-- Given a finite set `{b} ∪ P` and `t < b`, find the minimum element above `t`
and show the open interval `(t, s_min)` avoids the set entirely. -/
private theorem exists_min_above_in_finite_union
    (P : Finset ℝ) (t b : ℝ) (ht_lt_b : t < b) :
    ∃ s_min : ℝ, t < s_min ∧ s_min ≤ b ∧
      (∀ x ∈ Ioo t s_min, x ∉ ({b} ∪ (P : Set ℝ))) := by
  let S : Set ℝ := {b} ∪ (P : Set ℝ)
  have hS_finite : S.Finite :=
    (Set.finite_singleton b).union (Finset.finite_toSet P)
  let S_above : Set ℝ := {s ∈ S | t < s}
  have hS_above_finite : S_above.Finite :=
    hS_finite.subset (fun s hs => hs.1)
  have hne : hS_above_finite.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact ⟨b, by simp [S_above, S, ht_lt_b]⟩
  set s_min := hS_above_finite.toFinset.min' hne
  have hs_min_in : s_min ∈ S_above := by
    have := Finset.min'_mem _ hne
    rwa [Set.Finite.mem_toFinset] at this
  have hs_min_le : ∀ s ∈ S_above, s_min ≤ s :=
    fun s hs => Finset.min'_le _ s
      ((Set.Finite.mem_toFinset hS_above_finite).mpr hs)
  exact ⟨s_min, hs_min_in.2,
    hs_min_le b ⟨Set.mem_union_left _ rfl, ht_lt_b⟩,
    fun x hx hxS => by linarith [hs_min_le x ⟨hxS, hx.1⟩, hx.2]⟩

-- FIXME: [STRUCTURE] 33 lines
private theorem eq_on_Ioo_of_deriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b t s_min : ℝ}
    (ht : t ∈ Ico a b) (ht_lt_s : t < s_min)
    (hf_cont : ContinuousOn f (Icc a b))
    (h_diff : DifferentiableOn ℝ f (Ioo t s_min))
    (h_dz : ∀ x ∈ Ioo t s_min, deriv f x = 0)
    (h_smin_le_b : s_min ≤ b) :
    ∀ x ∈ Ioo t s_min, f x = f t := by
  have h_const : ∀ x ∈ Ioo t s_min, ∀ y ∈ Ioo t s_min,
      f x = f y :=
    fun x hx y hy => IsOpen.is_const_of_deriv_eq_zero
      isOpen_Ioo isPreconnected_Ioo h_diff h_dz hx hy
  have h_mid : (t + s_min) / 2 ∈ Ioo t s_min := by
    constructor <;> linarith
  have h_eq_mid : ∀ x ∈ Ioo t s_min, f x = f ((t + s_min) / 2) :=
    fun x hx => h_const x hx _ h_mid
  have h_cont_Ioo : ContinuousWithinAt f (Ioo t s_min) t :=
    (hf_cont.continuousWithinAt (Ico_subset_Icc_self ht)).mono
      (fun x hx => ⟨le_of_lt (lt_of_le_of_lt ht.1 hx.1),
        le_of_lt (lt_of_lt_of_le hx.2 h_smin_le_b)⟩)
  haveI : (𝓝[Ioo t s_min] t).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot,
      closure_Ioo (ne_of_lt ht_lt_s)]
    exact ⟨le_refl t, le_of_lt ht_lt_s⟩
  have h_ft : f t = f ((t + s_min) / 2) := tendsto_nhds_unique
    (h_cont_Ioo.tendsto.congr' (by
      filter_upwards [self_mem_nhdsWithin]
        with y hy; exact h_eq_mid y hy))
    tendsto_const_nhds
  intro x hx; rw [h_ft]; exact h_eq_mid x hx

-- FIXME: [STRUCTURE] 34 lines
/-- If f is continuous on [a,b], differentiable on (a,b)\P with f'=0 there,
then f has zero right derivative at every point of [a,b). -/
theorem hasDerivWithinAt_zero_of_deriv_zero_off_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (P : Finset ℝ) (_hab : a < b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, t ∉ P →
      DifferentiableAt ℝ f t)
    (hf_deriv_zero : ∀ t ∈ Ioo a b, t ∉ P →
      deriv f t = 0) :
    ∀ t ∈ Ico a b, HasDerivWithinAt f 0 (Ici t) t := by
  intro t ht
  obtain ⟨s_min, ht_lt_s, h_smin_le_b, h_avoid⟩ :=
    exists_min_above_in_finite_union P t b ht.2
  have h_Ioo_sub : Ioo t s_min ⊆ Ioo a b := fun x hx =>
    ⟨lt_of_le_of_lt ht.1 hx.1, lt_of_lt_of_le hx.2 h_smin_le_b⟩
  have h_not_P : ∀ x ∈ Ioo t s_min, x ∉ (P : Set ℝ) :=
    fun x hx hxP => h_avoid x hx (Set.mem_union_right _ hxP)
  have h_eq : ∀ x ∈ Ioo t s_min, f x = f t :=
    eq_on_Ioo_of_deriv_zero ht ht_lt_s hf_cont
      (fun x hx => (hf_diff x (h_Ioo_sub hx)
        (h_not_P x hx)).differentiableWithinAt)
      (fun x hx => hf_deriv_zero x (h_Ioo_sub hx) (h_not_P x hx))
      h_smin_le_b
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact tendsto_nhds_of_eventually_eq (by
    filter_upwards [show Ioo t s_min ∈ 𝓝[Ici t \ {t}] t from by
      rw [mem_nhdsWithin]
      exact ⟨Iio s_min, isOpen_Iio, ht_lt_s,
        fun x ⟨hx_Iio, hx_Ici_diff⟩ =>
          ⟨lt_of_le_of_ne hx_Ici_diff.1
            (Ne.symm hx_Ici_diff.2), hx_Iio⟩⟩]
      with x hx
    simp only [slope, h_eq x hx, vsub_self, smul_zero])

theorem continuousWithinAt_integral_of_dominated_piecewise
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {F : X → ℝ → ℂ} {x₀ : X} {a b : ℝ} {S : Set X} {M : ℝ}
    (hab : a ≤ b)
    (hF_meas : ∀ x ∈ S, AEStronglyMeasurable (F x) (volume.restrict (Icc a b)))
    (hF_bound : ∀ x ∈ S, ∀ t ∈ Icc a b, ‖F x t‖ ≤ M)
    (hF_cont : ∀ᵐ t ∂volume.restrict (Icc a b), ContinuousWithinAt (fun x => F x t) S x₀) :
    ContinuousWithinAt (fun x => ∫ t in a..b, F x t) S x₀ := by
  let bound : ℝ → ℝ := fun _ => M
  have h_uIoc_sub : Set.uIoc a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := bound)
  · filter_upwards [self_mem_nhdsWithin (s := S)] with x hx
    exact (hF_meas x hx).mono_set h_uIoc_sub
  · filter_upwards [self_mem_nhdsWithin (s := S)] with x hx
    exact .of_forall fun t ht => hF_bound x hx t (h_uIoc_sub ht)
  · exact intervalIntegrable_const
  · exact MeasureTheory.ae_imp_of_ae_restrict
      (MeasureTheory.ae_restrict_of_ae_restrict_of_subset h_uIoc_sub hF_cont)

end
