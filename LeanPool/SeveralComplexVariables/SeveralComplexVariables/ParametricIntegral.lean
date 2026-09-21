/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity

/-!
# Analytic dependence of integrals on several complex parameters

This file combines Mathlib's dominated differentiation-under-the-integral API with
finite-dimensional complex analyticity from `SeveralComplexVariables.Analyticity`. A
compact-domain criterion derives the required domination from joint continuity of the pointwise
derivative.

The parameter space in the analyticity criterion is an arbitrary finite-dimensional complex
normed space: the statement uses Fréchet derivatives and requires no coordinates. The compact
integral criteria below concern a single complex parameter and arbitrary compact integration
sets, not a particular integration geometry. This material is ultimately intended near
`Mathlib.Analysis.Calculus.ParametricIntegral`.

## Main results

`analyticOnNhd_integral_of_dominated_of_fderiv_le` packages the existing local dominated
Fréchet-derivative criterion at every point of an open finite-dimensional parameter domain.

`hasDerivAt_integral_of_continuousOn_compact` identifies the derivative of a compact set
integral with the integral of its pointwise complex derivative.
`hasDerivAt_integral_smul_of_continuousOn_compact` allows a fixed scalar weight with Banach-valued
kernels; `hasDerivAt_integral_mul_of_continuousOn_compact` is its scalar specialization, including a
weight singular on the boundary. The general dominated Fréchet derivative identification is
already Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`. The integral theorem names
remain in the root namespace, consistently with that API.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An integral on a finite-dimensional complex parameter space is analytic if, locally at every
parameter, its pointwise Fréchet derivatives have an integrable uniform bound. The hypotheses
are grouped pointwise so that the dominating function and neighborhood may depend on the base
parameter. -/
theorem analyticOnNhd_integral_of_dominated_of_fderiv_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {μ : Measure α} {U : Set P} {F : P → α → E}
    (hU : IsOpen U)
    (hdom : ∀ x ∈ U, ∃ (s : Set P) (bound : α → ℝ)
        (F' : P → α → P →L[ℂ] E),
      s ∈ nhds x ∧
      (∀ᶠ y in nhds x, AEStronglyMeasurable (F y) μ) ∧
      Integrable (F x) μ ∧ AEStronglyMeasurable (F' x) μ ∧
      (∀ᵐ a ∂μ, ∀ y ∈ s, ‖F' y a‖ ≤ bound a) ∧ Integrable bound μ ∧
      (∀ᵐ a ∂μ, ∀ y ∈ s, HasFDerivAt (F · a) (F' y a) y)) :
    AnalyticOnNhd ℂ (fun x ↦ ∫ a, F x a ∂μ) U := by
  apply DifferentiableOn.analyticOnNhd_of_finiteDimensional _ hU
  intro x hx
  obtain ⟨s, bound, F', hs, hmeas, hint, hF'meas, hbound, hboundInt, hdiff⟩ := hdom x hx
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hmeas hint hF'meas
    hbound hboundInt hdiff).differentiableAt.differentiableWithinAt

omit [CompleteSpace E] in
/-- Differentiation under an integral over a compact set when the integrand and its pointwise
complex derivative are jointly continuous. Compactness supplies domination. -/
theorem hasDerivAt_integral_of_continuousOn_compact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {K : Set α} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {F F' : ℂ → α → E}
    (hF : ContinuousOn (fun p : ℂ × α => F p.1 p.2) (U ×ˢ K))
    (hF' : ContinuousOn (fun p : ℂ × α => F' p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ a ∈ K, HasDerivAt (fun w => F w a) (F' z a) z) :
    HasDerivAt (fun z => ∫ a in K, F z a ∂μ) (∫ a in K, F' x a ∂μ) x := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hc : IsCompact (Metric.closedBall x r ×ˢ K) := (isCompact_closedBall _ _).prod hK
  have hcont := hF'.mono (Set.prod_mono hball Subset.rfl)
  obtain ⟨M, hM⟩ := hc.bddAbove_image hcont.norm
  have hslice {z : ℂ} (hz : z ∈ U) : ContinuousOn (F z) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => ⟨hz, ha⟩)
  have hslice' {z : ℂ} (hz : z ∈ U) : ContinuousOn (F' z) K :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => ⟨hz, ha⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := F) (F' := F') (bound := fun _ => M)
    (Metric.closedBall_mem_nhds x hr) ?_ ((hslice hx).integrableOn_compact hK)
    ((hslice' hx).integrableOn_compact hK).aestronglyMeasurable ?_
    (integrableOn_const hK.measure_ne_top) ?_).2
  · filter_upwards [hU.eventually_mem hx] with z hz
    exact ((hslice hz).integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    exact hM (mem_image_of_mem (fun p : ℂ × α => ‖F' p.1 p.2‖)
      (show (z, a) ∈ Metric.closedBall x r ×ˢ K from ⟨hz, ha⟩))
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    exact hd z (hball hz) a ha

omit [CompleteSpace E] in
/-- An integrable scalar weight times a continuous Banach-valued function on a compact set is
integrable. Compactness gives both boundedness and a separable image, so no countability
assumption on either ambient space is required. -/
theorem MeasureTheory.IntegrableOn.smul_continuousOn_of_isCompact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} {K : Set α} {g : α → ℂ} {H : α → E}
    (hg : IntegrableOn g K μ) (hH : ContinuousOn H K) (hK : IsCompact K) :
    IntegrableOn (fun t => g t • H t) K μ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image hH.norm
  apply (hg.norm.mul_const M).mono'
    (hg.aestronglyMeasurable.smul (hH.aestronglyMeasurable_of_isCompact hK hK.measurableSet))
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  change ‖g t • H t‖ ≤ ‖g t‖ * M
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hM ⟨t, ht, rfl⟩) (norm_nonneg _)

omit [CompleteSpace E] in
/-- A fixed integrable scalar weight can be included in compact-domain differentiation. Only the
kernel and its derivative must be jointly continuous; the weight may be singular on the boundary
of the integration domain. -/
theorem hasDerivAt_integral_smul_of_continuousOn_compact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → ℂ} (hg : IntegrableOn g K μ)
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {F F' : ℂ → α → E}
    (hF : ContinuousOn (fun p : ℂ × α => F p.1 p.2) (U ×ˢ K))
    (hF' : ContinuousOn (fun p : ℂ × α => F' p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ a ∈ K, HasDerivAt (fun w => F w a) (F' z a) z) :
    HasDerivAt (fun z => ∫ a in K, g a • F z a ∂μ)
      (∫ a in K, g a • F' x a ∂μ) x := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hc : IsCompact (Metric.closedBall x r ×ˢ K) := (isCompact_closedBall _ _).prod hK
  obtain ⟨M, hM⟩ := hc.bddAbove_image
    (hF'.mono (Set.prod_mono hball Subset.rfl)).norm
  have hslice {z : ℂ} (hz : z ∈ U) : ContinuousOn (F z) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => ⟨hz, ha⟩)
  have hslice' {z : ℂ} (hz : z ∈ U) : ContinuousOn (F' z) K :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => ⟨hz, ha⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := fun z a => g a • F z a)
    (F' := fun z a => g a • F' z a) (bound := fun a => ‖g a‖ * M)
    (Metric.closedBall_mem_nhds x hr) ?_ (hg.smul_continuousOn_of_isCompact (hslice hx) hK)
    (hg.smul_continuousOn_of_isCompact (hslice' hx) hK).aestronglyMeasurable ?_
    (hg.norm.mul_const M) ?_).2
  · filter_upwards [hU.eventually_mem hx] with z hz
    exact (hg.smul_continuousOn_of_isCompact (hslice hz) hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hM (mem_image_of_mem (fun p : ℂ × α => ‖F' p.1 p.2‖)
        (show (z, a) ∈ Metric.closedBall x r ×ˢ K from ⟨hz, ha⟩))) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro z hz
    exact (hd z (hball hz) a ha).const_smul (g a)

/-- A fixed integrable scalar weight can be included in compact-domain differentiation. Only the
kernel and its derivative must be jointly continuous; the weight may be singular on the boundary
of the integration domain. -/
theorem hasDerivAt_integral_mul_of_continuousOn_compact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} {K : Set α} (hK : IsCompact K)
    {g : α → ℂ} (hg : IntegrableOn g K μ)
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    {F F' : ℂ → α → ℂ}
    (hF : ContinuousOn (fun p : ℂ × α => F p.1 p.2) (U ×ˢ K))
    (hF' : ContinuousOn (fun p : ℂ × α => F' p.1 p.2) (U ×ˢ K))
    (hd : ∀ z ∈ U, ∀ a ∈ K, HasDerivAt (fun w => F w a) (F' z a) z) :
    HasDerivAt (fun z => ∫ a in K, g a * F z a ∂μ)
      (∫ a in K, g a * F' x a ∂μ) x := by
  simpa only [smul_eq_mul] using
    hasDerivAt_integral_smul_of_continuousOn_compact hK hg hU hx hF hF' hd

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
