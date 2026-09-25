/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.BennettKernel

/-! # Truncation -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The centered finite sum `∑ (Xᵢ - E[Xᵢ])` attached to a family `X`. -/
def centeredFinsetSum (X : ι → Ω → ℝ) (μ : Measure Ω) (s : Finset ι) : Ω → ℝ :=
  fun ω => ∑ i ∈ s, (X i ω - μ[X i])

/-- The symmetrized finite sum `∑ (Xᵢ(ω₁) - Xᵢ(ω₂))` on the product space. -/
def symmetrizedFinsetSum (X : ι → Ω → ℝ) (s : Finset ι) : Ω × Ω → ℝ :=
  fun ω => ∑ i ∈ s, (X i ω.1 - X i ω.2)

/-- The signed absolute-tail piece `X 1_{|X| > r}` used in the Rosenthal
truncation argument. -/
def absTailIndicator (X : Ω → ℝ) (r : ℝ) : Ω → ℝ :=
  fun ω => if r < |X ω| then X ω else 0

/-- The bounded truncation `X - X 1_{|X| > r}`. -/
def absTruncation (X : Ω → ℝ) (r : ℝ) : Ω → ℝ :=
  fun ω => X ω - absTailIndicator X r ω

section

omit [MeasurableSpace Ω]

@[simp] theorem absTailIndicator_apply (X : Ω → ℝ) (r : ℝ) (ω : Ω) :
    absTailIndicator X r ω = if r < |X ω| then X ω else 0 :=
  rfl

@[simp] theorem absTruncation_apply (X : Ω → ℝ) (r : ℝ) (ω : Ω) :
    absTruncation X r ω = X ω - absTailIndicator X r ω :=
  rfl

@[simp] theorem absTailIndicator_of_lt_abs {X : Ω → ℝ} {r : ℝ} {ω : Ω}
    (h : r < |X ω|) :
    absTailIndicator X r ω = X ω := by
  simp [absTailIndicator, h]

@[simp] theorem absTailIndicator_of_not_lt_abs {X : Ω → ℝ} {r : ℝ} {ω : Ω}
    (h : ¬ r < |X ω|) :
    absTailIndicator X r ω = 0 := by
  simp [absTailIndicator, h]

theorem absTruncation_add_absTailIndicator (X : Ω → ℝ) (r : ℝ) :
    absTruncation X r + absTailIndicator X r = X := by
  funext ω
  simp [absTruncation]

theorem abs_absTailIndicator_le {X : Ω → ℝ} {r : ℝ} (ω : Ω) :
    |absTailIndicator X r ω| ≤ |X ω| := by
  by_cases h : r < |X ω|
  · simp [absTailIndicator, h]
  · simp [absTailIndicator, h]

@[simp] theorem absTruncation_of_abs_le {X : Ω → ℝ} {r : ℝ} {ω : Ω}
    (h : |X ω| ≤ r) :
    absTruncation X r ω = X ω := by
  have h' : ¬ r < |X ω| := not_lt_of_ge h
  simp [absTruncation, absTailIndicator, h']

@[simp] theorem absTruncation_of_lt_abs {X : Ω → ℝ} {r : ℝ} {ω : Ω}
    (h : r < |X ω|) :
    absTruncation X r ω = 0 := by
  simp [absTruncation, absTailIndicator, h]

theorem abs_absTruncation_le {X : Ω → ℝ} {r : ℝ} (hr : 0 ≤ r) (ω : Ω) :
    |absTruncation X r ω| ≤ r := by
  by_cases h : r < |X ω|
  · simp [absTruncation, absTailIndicator, h, hr]
  · have hle : |X ω| ≤ r := le_of_not_gt h
    rw [absTruncation_of_abs_le hle]
    exact hle

end

theorem absTailIndicator_measurable {X : Ω → ℝ} {r : ℝ}
    (hX : Measurable X) :
    Measurable (absTailIndicator X r) := by
  refine hX.piecewise ?_ measurable_const
  exact measurableSet_lt measurable_const (continuous_abs.measurable.comp hX)

theorem absTruncation_measurable {X : Ω → ℝ} {r : ℝ}
    (hX : Measurable X) :
    Measurable (absTruncation X r) := by
  exact hX.sub (absTailIndicator_measurable hX)

theorem integrable_absTailIndicator_of_integrable
    {X : Ω → ℝ} {r : ℝ}
    (hX_meas : Measurable X) (hX_int : Integrable X μ) :
    Integrable (absTailIndicator X r) μ := by
  refine Integrable.mono' hX_int.norm
    (absTailIndicator_measurable hX_meas).aemeasurable.aestronglyMeasurable ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using abs_absTailIndicator_le (X := X)
    (r := r) ω

theorem integrable_absTruncation_of_integrable
    {X : Ω → ℝ} {r : ℝ}
    (hX_meas : Measurable X) (hX_int : Integrable X μ) :
    Integrable (absTruncation X r) μ := by
  exact hX_int.sub (integrable_absTailIndicator_of_integrable hX_meas hX_int)

/-- The finite sum of signed absolute-tail pieces. -/
def absTailIndicatorFinsetSum (X : ι → Ω → ℝ) (r : ι → ℝ) (s : Finset ι) : Ω → ℝ :=
  fun ω => ∑ i ∈ s, absTailIndicator (X i) (r i) ω

/-- The finite sum of bounded absolute-truncation pieces. -/
def absTruncationFinsetSum (X : ι → Ω → ℝ) (r : ι → ℝ) (s : Finset ι) : Ω → ℝ :=
  fun ω => ∑ i ∈ s, absTruncation (X i) (r i) ω

section

omit [MeasurableSpace Ω]

theorem absTruncationFinsetSum_add_absTailIndicatorFinsetSum
    (X : ι → Ω → ℝ) (r : ι → ℝ) (s : Finset ι) :
    absTruncationFinsetSum X r s + absTailIndicatorFinsetSum X r s =
      fun ω => ∑ i ∈ s, X i ω := by
  funext ω
  simp [absTruncationFinsetSum, absTailIndicatorFinsetSum]

theorem abs_absTruncationFinsetSum_le_sum
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι}
    (hr : ∀ i ∈ s, 0 ≤ r i) (ω : Ω) :
    |absTruncationFinsetSum X r s ω| ≤ ∑ i ∈ s, r i := by
  change |∑ i ∈ s, absTruncation (X i) (r i) ω| ≤ ∑ i ∈ s, r i
  calc
    |∑ i ∈ s, absTruncation (X i) (r i) ω|
        ≤ ∑ i ∈ s, |absTruncation (X i) (r i) ω| := by
            exact Finset.abs_sum_le_sum_abs (f := fun i => absTruncation (X i) (r i) ω) (s := s)
    _ ≤ ∑ i ∈ s, r i := by
          exact Finset.sum_le_sum fun i hi =>
            abs_absTruncation_le (X := X i) (r := r i) (hr i hi) ω

end

theorem absTailIndicatorFinsetSum_measurable
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι}
    (hX : ∀ i ∈ s, Measurable (X i)) :
    Measurable (absTailIndicatorFinsetSum X r s) := by
  refine Finset.measurable_sum s ?_
  intro i hi
  exact absTailIndicator_measurable (hX i hi)

theorem absTruncationFinsetSum_measurable
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι}
    (hX : ∀ i ∈ s, Measurable (X i)) :
    Measurable (absTruncationFinsetSum X r s) := by
  refine Finset.measurable_sum s ?_
  intro i hi
  exact absTruncation_measurable (hX i hi)

/-- The centered bounded-truncation family used in the Rosenthal proof. -/
def centeredAbsTruncationFamily
    (X : ι → Ω → ℝ) (r : ι → ℝ) (μ : Measure Ω) : ι → Ω → ℝ :=
  fun i ω => absTruncation (X i) (r i) ω - μ[absTruncation (X i) (r i)]

@[simp] theorem centeredAbsTruncationFamily_apply
    (X : ι → Ω → ℝ) (r : ι → ℝ) (μ : Measure Ω) (i : ι) (ω : Ω) :
    centeredAbsTruncationFamily X r μ i ω =
      absTruncation (X i) (r i) ω - μ[absTruncation (X i) (r i)] :=
  rfl

theorem centeredAbsTruncationFamily_measurable
    {X : ι → Ω → ℝ} {r : ι → ℝ}
    (hX : ∀ i, Measurable (X i)) :
    ∀ i, Measurable (centeredAbsTruncationFamily X r μ i) := by
  intro i
  exact (absTruncation_measurable (X := X i) (r := r i) (hX i)).sub measurable_const

theorem centeredAbsTruncationFamily_iIndepFun
    {X : ι → Ω → ℝ} {r : ι → ℝ}
    (h_indep : iIndepFun X μ) :
    iIndepFun (centeredAbsTruncationFamily X r μ) μ := by
  let g : ι → ℝ → ℝ :=
    fun i x => absTruncation (fun t : ℝ => t) (r i) x - μ[absTruncation (X i) (r i)]
  have hg : ∀ i, Measurable (g i) := by
    intro i
    exact
      (absTruncation_measurable (X := fun t : ℝ => t) (r := r i) measurable_id).sub
        measurable_const
  simpa [centeredAbsTruncationFamily, g, Function.comp, absTruncation] using! h_indep.comp g hg

theorem centeredAbsTruncationFamily_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {i : ι}
    (hXi_meas : Measurable (X i)) (hXi_int : Integrable (X i) μ) :
    μ[centeredAbsTruncationFamily X r μ i] = 0 := by
  have hTrunc_int : Integrable (absTruncation (X i) (r i)) μ :=
    integrable_absTruncation_of_integrable (μ := μ) hXi_meas hXi_int
  have hconst_int : Integrable (fun _ : Ω => μ[absTruncation (X i) (r i)]) μ :=
    integrable_const _
  change ∫ ω, (absTruncation (X i) (r i) ω - μ[absTruncation (X i) (r i)]) ∂μ = 0
  rw [integral_sub hTrunc_int hconst_int, integral_const]
  simp

theorem sum_centeredAbsTruncationFamily_eq_centeredFinsetSum_absTruncation
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} :
    (fun ω => ∑ i ∈ s, centeredAbsTruncationFamily X r μ i ω) =
      centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s := by
  funext ω
  simp [centeredAbsTruncationFamily, centeredFinsetSum]

theorem centeredFinsetSum_eq_absTruncationFinsetSum_add_absTailIndicatorFinsetSum
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι}
    (hTrunc_int : ∀ i ∈ s, Integrable (absTruncation (X i) (r i)) μ)
    (hTail_int : ∀ i ∈ s, Integrable (absTailIndicator (X i) (r i)) μ) :
    centeredFinsetSum X μ s =
      fun ω =>
        centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s ω +
          centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s ω := by
  have hIntegral :
      ∀ i ∈ s,
        μ[X i] =
          μ[absTruncation (X i) (r i)] + μ[absTailIndicator (X i) (r i)] := by
    intro i hi
    calc
      μ[X i] = ∫ ω, absTruncation (X i) (r i) ω + absTailIndicator (X i) (r i) ω ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω =>
          (congr_fun (absTruncation_add_absTailIndicator (X i) (r i)) ω).symm
      _ = μ[absTruncation (X i) (r i)] + μ[absTailIndicator (X i) (r i)] := by
        simpa using
          (integral_add' (f := absTruncation (X i) (r i))
            (g := absTailIndicator (X i) (r i)) (hTrunc_int i hi) (hTail_int i hi))
  funext ω
  rw [centeredFinsetSum, centeredFinsetSum, centeredFinsetSum]
  calc
    ∑ i ∈ s, (X i ω - μ[X i])
      = ∑ i ∈ s,
          ((absTruncation (X i) (r i) ω + absTailIndicator (X i) (r i) ω) -
            (μ[absTruncation (X i) (r i)] + μ[absTailIndicator (X i) (r i)])) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [← congr_fun (absTruncation_add_absTailIndicator (X i) (r i)) ω, hIntegral i hi]
            simp
    _ = ∑ i ∈ s,
          ((absTruncation (X i) (r i) ω - μ[absTruncation (X i) (r i)]) +
            (absTailIndicator (X i) (r i) ω - μ[absTailIndicator (X i) (r i)])) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = (∑ i ∈ s, (absTruncation (X i) (r i) ω - μ[absTruncation (X i) (r i)])) +
          ∑ i ∈ s, (absTailIndicator (X i) (r i) ω - μ[absTailIndicator (X i) (r i)]) := by
            rw [Finset.sum_add_distrib]

omit [MeasurableSpace Ω] in
theorem upperTailEvent_add_subset_union
    {X Y : Ω → ℝ} {a b : ℝ} :
    upperTailEvent (fun ω => X ω + Y ω) (a + b) ⊆
      upperTailEvent X a ∪ upperTailEvent Y b := by
  intro ω hω
  by_contra hUnion
  rw [Set.mem_union, mem_upperTailEvent, mem_upperTailEvent, not_or] at hUnion
  have hX_le : X ω ≤ a := le_of_not_gt hUnion.1
  have hY_le : Y ω ≤ b := le_of_not_gt hUnion.2
  exact not_lt_of_ge (add_le_add hX_le hY_le) (by simpa [upperTailEvent] using hω)

omit [MeasurableSpace Ω] in
theorem absTailEvent_add_subset_union
    {X Y : Ω → ℝ} {a b : ℝ} :
    absTailEvent (fun ω => X ω + Y ω) (a + b) ⊆
      absTailEvent X a ∪ absTailEvent Y b := by
  intro ω hω
  by_contra hUnion
  rw [Set.mem_union, mem_absTailEvent, mem_absTailEvent, not_or] at hUnion
  have hX_le : |X ω| ≤ a := le_of_not_gt hUnion.1
  have hY_le : |Y ω| ≤ b := le_of_not_gt hUnion.2
  have hsum_le : |X ω + Y ω| ≤ a + b := by
    exact le_trans (abs_add_le (X ω) (Y ω)) (add_le_add hX_le hY_le)
  exact not_lt_of_ge hsum_le (by simpa [absTailEvent] using hω)

theorem absTailEvent_centeredFinsetSum_subset_union
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {a b : ℝ}
    (hTrunc_int : ∀ i ∈ s, Integrable (absTruncation (X i) (r i)) μ)
    (hTail_int : ∀ i ∈ s, Integrable (absTailIndicator (X i) (r i)) μ) :
    absTailEvent (centeredFinsetSum X μ s) (a + b) ⊆
      absTailEvent (centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s) a ∪
        absTailEvent (centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s) b := by
  let F : Ω → ℝ := centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s
  let G : Ω → ℝ := centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s
  have hdecomp :
      centeredFinsetSum X μ s = fun ω => F ω + G ω := by
    simpa [F, G] using
      (centeredFinsetSum_eq_absTruncationFinsetSum_add_absTailIndicatorFinsetSum
        (μ := μ) (X := X) (r := r) (s := s) hTrunc_int hTail_int)
  intro ω hω
  have hω' : ω ∈ absTailEvent (fun ω => F ω + G ω) (a + b) := by
    simpa [hdecomp] using hω
  exact absTailEvent_add_subset_union (X := F) (Y := G) hω'

theorem measureReal_absTailEvent_centeredFinsetSum_le_truncation_add_tail
    [IsFiniteMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {s : Finset ι} {a b : ℝ}
    (hTrunc_int : ∀ i ∈ s, Integrable (absTruncation (X i) (r i)) μ)
    (hTail_int : ∀ i ∈ s, Integrable (absTailIndicator (X i) (r i)) μ) :
    μ.real (absTailEvent (centeredFinsetSum X μ s) (a + b)) ≤
      μ.real (absTailEvent (centeredFinsetSum (fun i => absTruncation (X i) (r i)) μ s) a) +
        μ.real (absTailEvent (centeredFinsetSum (fun i => absTailIndicator (X i) (r i)) μ s) b) := by
  refine le_trans ?_ (measureReal_union_le _ _)
  exact measureReal_mono
    (absTailEvent_centeredFinsetSum_subset_union
      (μ := μ) (X := X) (r := r) (s := s) hTrunc_int hTail_int)

theorem integral_abs_sub_integral_le_two_mul
    [IsProbabilityMeasure μ]
    {Y : Ω → ℝ}
    (hY_int : Integrable Y μ) :
    ∫ ω, |Y ω - μ[Y]| ∂μ ≤ 2 * ∫ ω, |Y ω| ∂μ := by
  have hcentered_int : Integrable (fun ω => Y ω - μ[Y]) μ :=
    hY_int.sub (integrable_const _)
  have hpoint :
      ∀ᵐ ω ∂μ, |Y ω - μ[Y]| ≤ |Y ω| + |μ[Y]| := by
    exact Filter.Eventually.of_forall fun ω =>
      by simpa [sub_eq_add_neg] using abs_add_le (Y ω) (-μ[Y])
  calc
    ∫ ω, |Y ω - μ[Y]| ∂μ ≤ ∫ ω, (|Y ω| + |μ[Y]|) ∂μ := by
      refine integral_mono_ae hcentered_int.norm ?_ hpoint
      exact hY_int.norm.add (integrable_const _)
    _ = ∫ ω, |Y ω| ∂μ + ∫ ω, |μ[Y]| ∂μ := by
      rw [integral_add (f := fun ω => |Y ω|) (g := fun _ : Ω => |μ[Y]|)
        (hY_int.norm) (integrable_const _)]
    _ = ∫ ω, |Y ω| ∂μ + |μ[Y]| := by simp
    _ ≤ ∫ ω, |Y ω| ∂μ + ∫ ω, |Y ω| ∂μ := by
      gcongr
      exact abs_integral_le_integral_abs
    _ = 2 * ∫ ω, |Y ω| ∂μ := by ring

theorem abs_integral_absTruncation_le
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {r : ℝ}
    (hX_meas : Measurable X) (hX_int : Integrable X μ) (hr : 0 ≤ r) :
    |μ[absTruncation X r]| ≤ r := by
  have hTrunc_int : Integrable (absTruncation X r) μ :=
    integrable_absTruncation_of_integrable hX_meas hX_int
  have hpoint : ∀ᵐ ω ∂μ, |absTruncation X r ω| ≤ r := by
    exact Filter.Eventually.of_forall (abs_absTruncation_le (X := X) (r := r) hr)
  calc
    |μ[absTruncation X r]| = ‖∫ ω, absTruncation X r ω ∂μ‖ := by
      simp [Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖absTruncation X r ω‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ ω, |absTruncation X r ω| ∂μ := by simp [Real.norm_eq_abs]
    _ ≤ ∫ ω, r ∂μ := by
          exact integral_mono_ae hTrunc_int.norm (integrable_const r) hpoint
    _ = r := by simp

theorem abs_sub_integral_absTruncation_le_two_mul
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {r : ℝ}
    (hX_meas : Measurable X) (hX_int : Integrable X μ) (hr : 0 ≤ r) (ω : Ω) :
    |absTruncation X r ω - μ[absTruncation X r]| ≤ 2 * r := by
  calc
    |absTruncation X r ω - μ[absTruncation X r]|
      ≤ |absTruncation X r ω| + |μ[absTruncation X r]| := by
          simpa [sub_eq_add_neg] using abs_add_le (absTruncation X r ω) (-μ[absTruncation X r])
    _ ≤ r + r := add_le_add (abs_absTruncation_le (X := X) (r := r) hr ω)
          (abs_integral_absTruncation_le hX_meas hX_int hr)
    _ = 2 * r := by ring

theorem abs_centeredAbsTruncationFamily_le_two_mul
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {r : ι → ℝ} {i : ι}
    (hXi_meas : Measurable (X i)) (hXi_int : Integrable (X i) μ) (hri : 0 ≤ r i) (ω : Ω) :
    |centeredAbsTruncationFamily X r μ i ω| ≤ 2 * r i := by
  simpa [centeredAbsTruncationFamily] using
    abs_sub_integral_absTruncation_le_two_mul
      (μ := μ) (X := X i) (r := r i) hXi_meas hXi_int hri ω


end
end IndependentSums
end Homogenization
