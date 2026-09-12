/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Time derivatives of integrals with uniform compact spatial support

The public statements use the ordinary volume integral over all of R³.
Uniform compact support supplies integrability and a local dominating function.
-/

@[expose] public section



noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.CompactTimeIntegral

open ProblemStatement

variable {E : Type*} [NormedAddCommGroup E]

/-- Joint continuity on a time set gives continuity of each spatial slice. -/
theorem continuous_slice {F : ℝ × Space → E} {s : Set ℝ}
    (hF : ContinuousOn F (s ×ˢ univ)) {t : ℝ} (ht : t ∈ s) :
    Continuous (fun x : Space => F (t, x)) := by
  exact hF.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨ht, mem_univ _⟩)

/-- A continuous spatial slice supported in a fixed compact set is integrable. -/
theorem integrable_slice {F : ℝ × Space → E} {s : Set ℝ} {K : Set Space}
    (hK : IsCompact K) (hF : ContinuousOn F (s ×ˢ univ))
    (hsupp : ∀ t ∈ s, ∀ x ∉ K, F (t, x) = 0) {t : ℝ} (ht : t ∈ s) :
    Integrable (fun x : Space => F (t, x)) := by
  have hsupport : Function.support (fun x : Space => F (t, x)) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (hsupp t ht x hxK)
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp
    ((continuous_slice hF ht).continuousOn.integrableOn_compact hK)

variable [NormedSpace ℝ E]

/-- Ordinary spatial integration preserves continuity on the time set under
uniform compact support. In particular the time set may be a closed interval. -/
theorem continuousOn_integral {F : ℝ × Space → E} {s : Set ℝ} {K : Set Space}
    (hK : IsCompact K) (hF : ContinuousOn F (s ×ˢ univ))
    (hsupp : ∀ t ∈ s, ∀ x ∉ K, F (t, x) = 0) :
    ContinuousOn (fun t => ∫ x : Space, F (t, x)) s := by
  exact continuousOn_integral_of_compact_support hK hF
    (fun t x ht hx => hsupp t ht x hx)

/-- A time derivative vanishes outside the uniform spatial support at every
interior time. -/
theorem derivative_eq_zero_outside {F G : ℝ × Space → E} {a b : ℝ} {K : Set Space}
    (hsupp : ∀ t ∈ Ioo a b, ∀ x ∉ K, F (t, x) = 0)
    (hderiv : ∀ t ∈ Ioo a b, ∀ x : Space,
      HasDerivAt (fun r => F (r, x)) (G (t, x)) t)
    {t : ℝ} (ht : t ∈ Ioo a b) {x : Space} (hx : x ∉ K) :
    G (t, x) = 0 := by
  apply (hderiv t ht x).unique
  apply (hasDerivAt_const t (0 : E)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact hsupp r hr x hx

/-- Differentiation under the ordinary spatial integral. Joint continuity of
the field and its time derivative is needed only at interior times. -/
theorem hasDerivAt_integral {F G : ℝ × Space → E} {a b t : ℝ} {K : Set Space}
    (hK : IsCompact K) (hF : ContinuousOn F (Ioo a b ×ˢ univ))
    (hG : ContinuousOn G (Ioo a b ×ˢ univ))
    (hsupp : ∀ r ∈ Ioo a b, ∀ x ∉ K, F (r, x) = 0)
    (hderiv : ∀ r ∈ Ioo a b, ∀ x : Space,
      HasDerivAt (fun q => F (q, x)) (G (r, x)) r)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ x : Space, F (r, x))
      (∫ x : Space, G (t, x)) t := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Ioo_mem_nhds ht.1 ht.2)
  have hhalf : 0 < ε / 2 := half_pos hε
  have hclosed : Metric.closedBall t (ε / 2) ⊆ Ioo a b :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hsmall : Metric.ball t (ε / 2) ⊆ Ioo a b :=
    Metric.ball_subset_closedBall.trans hclosed
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t (ε / 2)).prod hK).exists_bound_of_continuousOn
    (hG.mono (Set.prod_mono hclosed (subset_univ K)))
  have hbound : ∀ᵐ x ∂(volume.restrict K),
      ∀ r ∈ Metric.ball t (ε / 2), ‖G (r, x)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro r hr
    exact hC (r, x) ⟨Metric.ball_subset_closedBall hr, hx⟩
  have hrestricted := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r (x : Space) => F (r, x)) (F' := fun r x => G (r, x))
    (μ := volume.restrict K) (bound := fun _ => C) (Metric.ball_mem_nhds t hhalf)
    (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      exact (continuous_slice hF hr).aestronglyMeasurable)
    ((continuous_slice hF ht).continuousOn.integrableOn_compact hK)
    ((continuous_slice hG ht).aestronglyMeasurable)
    hbound (integrableOn_const (C := C) hK.measure_ne_top)
    (Filter.Eventually.of_forall (fun x r hr => hderiv r (hsmall hr) x))).2
  have hGintegral : (∫ x in K, G (t, x)) = ∫ x : Space, G (t, x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => derivative_eq_zero_outside hsupp hderiv ht hx)
  rw [hGintegral] at hrestricted
  apply hrestricted.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hsupp r hr x hx)).symm

/-- The time derivative of a jointly C¹ field at an interior time is the
full derivative evaluated on the time direction. -/
theorem hasDerivAt_time_of_contDiffOn {F : ℝ × Space → E} {a b t : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ univ))
    (ht : t ∈ Ioo a b) (x : Space) :
    HasDerivAt (fun r => F (r, x)) (fderiv ℝ F (t, x) (1, 0)) t := by
  have hmem : (t, x) ∈ Ioo a b ×ˢ (univ : Set Space) := ⟨ht, mem_univ _⟩
  have hopen : IsOpen (Ioo a b ×ˢ (univ : Set Space)) := isOpen_Ioo.prod isOpen_univ
  have hF' : ContDiffOn ℝ 1 F (Ioo a b ×ˢ univ) :=
    hF.mono (Set.prod_mono Ioo_subset_Icc_self (Subset.refl _))
  have hdiff : DifferentiableAt ℝ F (t, x) :=
    (hF'.differentiableOn (by norm_num) _ hmem).differentiableAt (hopen.mem_nhds hmem)
  simpa only [Function.comp_def, id_eq] using hdiff.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

/-- The time component of the full derivative is jointly continuous in the
interior of the time slab. -/
theorem continuousOn_timeFDeriv_of_contDiffOn {F : ℝ × Space → E} {a b : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Space => fderiv ℝ F p (1, 0))
      (Ioo a b ×ˢ univ) := by
  have hopen : IsOpen (Ioo a b ×ˢ (univ : Set Space)) := isOpen_Ioo.prod isOpen_univ
  have hF' : ContDiffOn ℝ 1 F (Ioo a b ×ˢ univ) :=
    hF.mono (Set.prod_mono Ioo_subset_Icc_self (Subset.refl _))
  exact (hF'.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply continuousOn_const

/-- The ordinary one-dimensional time derivative of a jointly C¹ field is
jointly continuous at interior times. -/
theorem continuousOn_timeDeriv_of_contDiffOn {F : ℝ × Space → E} {a b : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Space => deriv (fun r => F (r, p.2)) p.1)
      (Ioo a b ×ˢ univ) := by
  apply (continuousOn_timeFDeriv_of_contDiffOn hF).congr
  intro p hp
  exact (hasDerivAt_time_of_contDiffOn hF hp.1 p.2).deriv

/-- A jointly C¹ field with uniform compact spatial support has a continuous
ordinary spatial integral throughout the closed time slab. -/
theorem continuousOn_integral_of_contDiffOn {F : ℝ × Space → E}
    {a b : ℝ} {K : Set Space} (hK : IsCompact K)
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ univ))
    (hsupp : ∀ t ∈ Icc a b, ∀ x ∉ K, F (t, x) = 0) :
    ContinuousOn (fun t => ∫ x : Space, F (t, x)) (Icc a b) :=
  continuousOn_integral hK hF.continuousOn hsupp

/-- At interior times, the derivative of the ordinary spatial integral is
the integral of the ordinary time derivative. -/
theorem hasDerivAt_integral_of_contDiffOn {F : ℝ × Space → E}
    {a b t : ℝ} {K : Set Space} (hK : IsCompact K)
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ univ))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, F (r, x) = 0)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ x : Space, F (r, x))
      (∫ x : Space, deriv (fun r => F (r, x)) t) t := by
  apply hasDerivAt_integral hK
    (hF.continuousOn.mono (Set.prod_mono Ioo_subset_Icc_self (Subset.refl _)))
    (continuousOn_timeDeriv_of_contDiffOn hF)
    (fun r hr x hx => hsupp r (Ioo_subset_Icc_self hr) x hx) _ ht
  intro r hr x
  exact (hasDerivAt_time_of_contDiffOn hF hr x).differentiableAt.hasDerivAt

/-- A convenient form of differentiation under the spatial integral in which
the derivative is supplied pointwise only at the time being considered. -/
theorem hasDerivAt_integral_of_contDiffOn_of_hasDerivAt
    {F : ℝ × Space → E} {G : Space → E} {a b t : ℝ} {K : Set Space}
    (hK : IsCompact K) (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ univ))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, F (r, x) = 0)
    (ht : t ∈ Ioo a b)
    (hderiv : ∀ x : Space, HasDerivAt (fun r => F (r, x)) (G x) t) :
    HasDerivAt (fun r => ∫ x : Space, F (r, x)) (∫ x : Space, G x) t := by
  have h := hasDerivAt_integral_of_contDiffOn hK hF hsupp ht
  have heq : (∫ x : Space, deriv (fun r => F (r, x)) t) = ∫ x : Space, G x :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => (hderiv x).deriv))
  rwa [heq] at h

end NavierStokesR3.CompactTimeIntegral
