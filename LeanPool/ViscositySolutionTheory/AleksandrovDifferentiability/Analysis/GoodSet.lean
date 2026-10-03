/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Foundation.SecondOrder
public import Mathlib.MeasureTheory.Integral.Prod

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Good and bad sets for second-order differentiability

This file gives names to the full-measure and exceptional-set formulations of the final
second-order differentiability conclusion.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Product-measure Fubini bookkeeping for a.e. restricted vertical sections.

If almost every vertical section of `s` is almost everywhere contained in `G`, measured with
respect to the restriction of `ν` to that section, then the product-measure complement `s \ G` is
null. This is the set-level shape needed later when a one-dimensional line theorem is integrated
over transverse coordinates. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_restrict_section
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν.restrict {y : β | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 := by
  rw [Measure.measure_prod_null hbad]
  refine hsection.mono fun x hxsection => ?_
  change ν (Prod.mk x ⁻¹' (s \ G)) = 0
  have hsx : MeasurableSet {y : β | (x, y) ∈ s} :=
    measurable_prodMk_left hs
  rw [ae_iff] at hxsection
  rw [Measure.restrict_apply_eq_zero' hsx] at hxsection
  have hset :
      {y : β | ¬(x, y) ∈ G} ∩ {y : β | (x, y) ∈ s} =
        Prod.mk x ⁻¹' (s \ G) := by
    ext y
    simp [and_comm]
  rwa [hset] at hxsection

/-- Null-measurable version of
`prod_measure_diff_eq_zero_of_ae_ae_restrict_section`.

This weakens the side condition on the product bad set from measurable to null-measurable, which is
often the natural output when the one-dimensional good set is only known modulo null sets. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_restrict_section₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν.restrict {y : β | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 := by
  rcases hbad.exists_measurable_subset_ae_eq with ⟨t, htsub, htmeas, htae⟩
  have ht0 : μ.prod ν t = 0 := by
    rw [Measure.measure_prod_null htmeas]
    refine hsection.mono fun x hxsection => ?_
    change ν (Prod.mk x ⁻¹' t) = 0
    have hsx : MeasurableSet {y : β | (x, y) ∈ s} :=
      measurable_prodMk_left hs
    rw [ae_iff] at hxsection
    rw [Measure.restrict_apply_eq_zero' hsx] at hxsection
    have hset :
        {y : β | ¬(x, y) ∈ G} ∩ {y : β | (x, y) ∈ s} =
          Prod.mk x ⁻¹' (s \ G) := by
      ext y
      simp [and_comm]
    rw [hset] at hxsection
    have hpre : Prod.mk x ⁻¹' t ⊆ Prod.mk x ⁻¹' (s \ G) := fun y hy => htsub hy
    exact le_antisymm ((measure_mono hpre).trans_eq hxsection) bot_le
  exact (measure_congr htae.symm).trans ht0

/-- Product-measure Fubini bookkeeping for restricted vertical sections.

If every vertical section of `s` is almost everywhere contained in `G`, measured with respect to
the restriction of `ν` to that section, then the product-measure complement `s \ G` is null. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_restrict_section
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ x : α, ∀ᵐ y ∂ν.restrict {y : β | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_section hs hbad
    (Filter.Eventually.of_forall hsection)

/-- Null-measurable version of
`prod_measure_diff_eq_zero_of_forall_ae_restrict_section`. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ x : α, ∀ᵐ y ∂ν.restrict {y : β | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_section₀ hs hbad
    (Filter.Eventually.of_forall hsection)

/-- Product-measure Fubini bookkeeping for restricted vertical sections in implication form. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_imp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_section hs hbad <|
    hsection.mono fun x hx => by
      have hsx : MeasurableSet {y : β | (x, y) ∈ s} :=
        measurable_prodMk_left hs
      filter_upwards [ae_restrict_mem hsx, ae_restrict_of_ae hx] with y hys hy
      exact hy hys

/-- Null-measurable version of `prod_measure_diff_eq_zero_of_ae_ae_imp`. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_imp₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_section₀ hs hbad <|
    hsection.mono fun x hx => by
      have hsx : MeasurableSet {y : β | (x, y) ∈ s} :=
        measurable_prodMk_left hs
      filter_upwards [ae_restrict_mem hsx, ae_restrict_of_ae hx] with y hys hy
      exact hy hys

/-- Product-measure Fubini bookkeeping for restricted vertical sections in pointwise implication
form. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_imp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ x : α, ∀ᵐ y ∂ν, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_imp hs hbad (Filter.Eventually.of_forall hsection)

/-- Null-measurable version of `prod_measure_diff_eq_zero_of_forall_ae_imp`. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_imp₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ x : α, ∀ᵐ y ∂ν, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_imp₀ hs hbad (Filter.Eventually.of_forall hsection)

/-- Product-measure Fubini bookkeeping for a.e. restricted horizontal sections.

This is the coordinate-swapped version of
`prod_measure_diff_eq_zero_of_ae_ae_restrict_section`: if almost every horizontal section of `s`
is almost everywhere contained in `G`, measured with respect to the restriction of `μ` to that
section, then the product-measure complement `s \ G` is null. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_restrict_horizontal_section
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ.restrict {x : α | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 := by
  rw [Measure.prod_apply_symm hbad]
  rw [lintegral_eq_zero_iff (measurable_measure_prodMk_right hbad)]
  refine hsection.mono fun y hysection => ?_
  change μ ((fun x : α => (x, y)) ⁻¹' (s \ G)) = 0
  have hsy : MeasurableSet {x : α | (x, y) ∈ s} :=
    measurable_prodMk_right hs
  rw [ae_iff] at hysection
  rw [Measure.restrict_apply_eq_zero' hsy] at hysection
  have hset :
      {x : α | ¬(x, y) ∈ G} ∩ {x : α | (x, y) ∈ s} =
        (fun x : α => (x, y)) ⁻¹' (s \ G) := by
    ext x
    simp [and_comm]
  rwa [hset] at hysection

/-- Null-measurable version of
`prod_measure_diff_eq_zero_of_ae_ae_restrict_horizontal_section`. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_restrict_horizontal_section₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ.restrict {x : α | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 := by
  rcases hbad.exists_measurable_subset_ae_eq with ⟨t, htsub, htmeas, htae⟩
  have ht0 : μ.prod ν t = 0 := by
    rw [Measure.prod_apply_symm htmeas]
    rw [lintegral_eq_zero_iff (measurable_measure_prodMk_right htmeas)]
    refine hsection.mono fun y hysection => ?_
    change μ ((fun x : α => (x, y)) ⁻¹' t) = 0
    have hsy : MeasurableSet {x : α | (x, y) ∈ s} :=
      measurable_prodMk_right hs
    rw [ae_iff] at hysection
    rw [Measure.restrict_apply_eq_zero' hsy] at hysection
    have hset :
        {x : α | ¬(x, y) ∈ G} ∩ {x : α | (x, y) ∈ s} =
          (fun x : α => (x, y)) ⁻¹' (s \ G) := by
      ext x
      simp [and_comm]
    rw [hset] at hysection
    have hpre : (fun x : α => (x, y)) ⁻¹' t ⊆
        (fun x : α => (x, y)) ⁻¹' (s \ G) := fun x hx => htsub hx
    exact le_antisymm ((measure_mono hpre).trans_eq hysection) bot_le
  exact (measure_congr htae.symm).trans ht0

/-- Product-measure Fubini bookkeeping for restricted horizontal sections.

If every horizontal section of `s` is almost everywhere contained in `G`, measured with respect to
the restriction of `μ` to that section, then the product-measure complement `s \ G` is null. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_restrict_horizontal_section
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ y : β, ∀ᵐ x ∂μ.restrict {x : α | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_horizontal_section hs hbad
    (Filter.Eventually.of_forall hsection)

/-- Null-measurable version of
`prod_measure_diff_eq_zero_of_forall_ae_restrict_horizontal_section`. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_restrict_horizontal_section₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ y : β, ∀ᵐ x ∂μ.restrict {x : α | (x, y) ∈ s}, (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_horizontal_section₀ hs hbad
    (Filter.Eventually.of_forall hsection)

/-- Product-measure Fubini bookkeeping for restricted horizontal sections in implication form. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_horizontal_imp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_horizontal_section hs hbad <|
    hsection.mono fun y hy => by
      have hsy : MeasurableSet {x : α | (x, y) ∈ s} :=
        measurable_prodMk_right hs
      filter_upwards [ae_restrict_mem hsy, ae_restrict_of_ae hy] with x hxs hx
      exact hx hxs

/-- Null-measurable version of `prod_measure_diff_eq_zero_of_ae_ae_horizontal_imp`. -/
theorem prod_measure_diff_eq_zero_of_ae_ae_horizontal_imp₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_restrict_horizontal_section₀ hs hbad <|
    hsection.mono fun y hy => by
      have hsy : MeasurableSet {x : α | (x, y) ∈ s} :=
        measurable_prodMk_right hs
      filter_upwards [ae_restrict_mem hsy, ae_restrict_of_ae hy] with x hxs hx
      exact hx hxs

/-- Product-measure Fubini bookkeeping for restricted horizontal sections in pointwise implication
form. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_horizontal_imp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : MeasurableSet (s \ G))
    (hsection : ∀ y : β, ∀ᵐ x ∂μ, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_horizontal_imp hs hbad
    (Filter.Eventually.of_forall hsection)

/-- Null-measurable version of `prod_measure_diff_eq_zero_of_forall_ae_horizontal_imp`. -/
theorem prod_measure_diff_eq_zero_of_forall_ae_horizontal_imp₀
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s G : Set (α × β)}
    (hs : MeasurableSet s) (hbad : NullMeasurableSet (s \ G) (μ.prod ν))
    (hsection : ∀ y : β, ∀ᵐ x ∂μ, (x, y) ∈ s → (x, y) ∈ G) :
    μ.prod ν (s \ G) = 0 :=
  prod_measure_diff_eq_zero_of_ae_ae_horizontal_imp₀ hs hbad
    (Filter.Eventually.of_forall hsection)

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exceptional set where `u` is not second-order differentiable. -/
def secondOrderBadSet (u : E → ℝ) : Set E :=
  (secondOrderDifferentiabilitySet u)ᶜ

/-- The exceptional set inside a prescribed domain. -/
def secondOrderBadSetOn (s : Set E) (u : E → ℝ) : Set E :=
  s \ secondOrderDifferentiabilitySet u

@[simp]
theorem mem_secondOrderBadSet {u : E → ℝ} {x : E} :
    x ∈ secondOrderBadSet u ↔ ¬ SecondOrderDifferentiableAt u x := by
  rfl

@[simp]
theorem mem_secondOrderBadSetOn {s : Set E} {u : E → ℝ} {x : E} :
    x ∈ secondOrderBadSetOn s u ↔ x ∈ s ∧ ¬ SecondOrderDifferentiableAt u x := by
  rfl

variable [MeasurableSpace E]

/-- `u` is second-order differentiable almost everywhere with respect to `μ`. -/
def SecondOrderDifferentiableAE (μ : Measure E) (u : E → ℝ) : Prop :=
  ∀ᵐ x ∂μ, SecondOrderDifferentiableAt u x

/-- `u` is second-order differentiable almost everywhere on `s`, with respect to `μ`. -/
def SecondOrderDifferentiableAEOn (μ : Measure E) (s : Set E) (u : E → ℝ) : Prop :=
  ∀ᵐ x ∂(μ.restrict s), SecondOrderDifferentiableAt u x

theorem secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero
    {μ : Measure E} {u : E → ℝ} :
    SecondOrderDifferentiableAE μ u ↔ μ (secondOrderBadSet u) = 0 := by
  rw [SecondOrderDifferentiableAE, ae_iff]
  have hset : {x | ¬ SecondOrderDifferentiableAt u x} = secondOrderBadSet u := by
    ext x
    rfl
  rw [hset]

theorem secondOrderDifferentiableAEOn_iff_restrict_measure_secondOrderBadSet_eq_zero
    {μ : Measure E} {s : Set E} {u : E → ℝ} :
    SecondOrderDifferentiableAEOn μ s u ↔ μ.restrict s (secondOrderBadSet u) = 0 := by
  rw [SecondOrderDifferentiableAEOn]
  exact secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero

/-- Restricted-measure null-bad-set form of an a.e.-on statement. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    {μ : Measure E} {s : Set E} {u : E → ℝ}
    (h : SecondOrderDifferentiableAEOn μ s u) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  secondOrderDifferentiableAEOn_iff_restrict_measure_secondOrderBadSet_eq_zero.mp h

/-- A restricted-measure null bad set gives second-order differentiability a.e. on the domain. -/
theorem secondOrderDifferentiableAEOn_of_restrict_measure_secondOrderBadSet_eq_zero
    {μ : Measure E} {s : Set E} {u : E → ℝ}
    (h : μ.restrict s (secondOrderBadSet u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_iff_restrict_measure_secondOrderBadSet_eq_zero.mpr h

omit [MeasurableSpace E] in
theorem secondOrderBadSet_inter_eq_secondOrderBadSetOn
    {s : Set E} {u : E → ℝ} :
    secondOrderBadSet u ∩ s = secondOrderBadSetOn s u := by
  ext x
  simp [and_comm]

theorem secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s) :
    SecondOrderDifferentiableAEOn μ s u ↔ μ (secondOrderBadSetOn s u) = 0 := by
  rw [secondOrderDifferentiableAEOn_iff_restrict_measure_secondOrderBadSet_eq_zero]
  rw [Measure.restrict_apply_eq_zero' hs]
  rw [secondOrderBadSet_inter_eq_secondOrderBadSetOn]

omit [MeasurableSpace E] in
theorem secondOrderBadSetOn_subset_domain {s : Set E} {u : E → ℝ} :
    secondOrderBadSetOn s u ⊆ s := by
  intro x hx
  exact hx.1

theorem measure_secondOrderBadSetOn_eq_zero_of_measure_eq_zero
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs0 : μ s = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  le_antisymm ((measure_mono (secondOrderBadSetOn_subset_domain (s := s) (u := u))).trans_eq
    hs0) bot_le

theorem secondOrderDifferentiableAEOn_of_measure_eq_zero
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s) (hs0 : μ s = 0) :
    SecondOrderDifferentiableAEOn μ s u := by
  rw [secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs]
  exact measure_secondOrderBadSetOn_eq_zero_of_measure_eq_zero hs0

omit [MeasurableSpace E] in
@[simp]
theorem secondOrderBadSetOn_empty {u : E → ℝ} :
    secondOrderBadSetOn (∅ : Set E) u = ∅ := by
  ext x
  simp

theorem secondOrderDifferentiableAEOn_empty
    {μ : Measure E} {u : E → ℝ} :
    SecondOrderDifferentiableAEOn μ (∅ : Set E) u :=
  secondOrderDifferentiableAEOn_of_measure_eq_zero MeasurableSet.empty (by simp)

theorem secondOrderDifferentiableAEOn_of_secondOrderBadSetOn_subset_null
    {μ : Measure E} {s : Set E} {u : E → ℝ} {N : Set E} (hs : MeasurableSet s)
    (hsubset : secondOrderBadSetOn s u ⊆ N) (hN : μ N = 0) :
    SecondOrderDifferentiableAEOn μ s u := by
  rw [secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs]
  exact le_antisymm ((measure_mono hsubset).trans_eq hN) bot_le

omit [MeasurableSpace E] in
theorem secondOrderBadSetOn_subset_domain_diff_of_inter_subset_differentiabilitySet
    {s G : Set E} {u : E → ℝ}
    (hG : s ∩ G ⊆ secondOrderDifferentiabilitySet u) :
    secondOrderBadSetOn s u ⊆ s \ G := by
  intro x hx
  rcases (mem_secondOrderBadSetOn.mp hx) with ⟨hxs, hxbad⟩
  refine ⟨hxs, ?_⟩
  intro hxG
  exact hxbad (by simpa using hG ⟨hxs, hxG⟩)

theorem secondOrderDifferentiableAEOn_of_fullMeasure_goodSet
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : s ∩ G ⊆ secondOrderDifferentiabilitySet u) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_secondOrderBadSetOn_subset_null hs
    (secondOrderBadSetOn_subset_domain_diff_of_inter_subset_differentiabilitySet hG) hnull

theorem secondOrderDifferentiableAEOn_of_fullMeasure_goodSet'
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G → SecondOrderDifferentiableAt u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact hG hx.1 hx.2)

/-- If every point of `s` is second-order differentiable, then `u` is second-order
differentiable almost everywhere on `s`. This is the degenerate good-set case `G = s`. -/
theorem secondOrderDifferentiableAEOn_of_forall_mem
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s → SecondOrderDifferentiableAt u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet' (G := s) hs (by simp) (by
    intro x hx _hx
    exact h hx)

/-- Null-bad-set version of `secondOrderDifferentiableAEOn_of_forall_mem`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_forall_mem
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s → SecondOrderDifferentiableAt u x) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_forall_mem hs h)

/-- Restricted-measure null-bad-set version of `secondOrderDifferentiableAEOn_of_forall_mem`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_forall_mem
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s → SecondOrderDifferentiableAt u x) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_forall_mem hs h)

/-- If every point of `s` carries explicit symmetric second-order expansion data, then `u` is
second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_forall_expansionData
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_forall_mem hs (by
    intro x hx
    rcases h hx with ⟨p, B, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB hquad)

/-- Null-bad-set version of `secondOrderDifferentiableAEOn_of_forall_expansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_forall_expansionData
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_forall_expansionData hs h)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_forall_expansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_forall_expansionData
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_forall_expansionData hs h)

/-- If every point of `s` carries explicit symmetric second-order expansion data with the
first-order term given as a represented continuous linear functional, then `u` is second-order
differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_forall_clmExpansionData
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_forall_mem hs (by
    intro x hx
    rcases h hx with ⟨p, ℓ, B, hℓ, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM_eq_inner hℓ hB hquad)

/-- Null-bad-set version of `secondOrderDifferentiableAEOn_of_forall_clmExpansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_forall_clmExpansionData
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_forall_clmExpansionData hs h)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_forall_clmExpansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_forall_clmExpansionData
    {μ : Measure E} {s : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : E⦄, x ∈ s →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_forall_clmExpansionData hs h)

omit [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- If `G` has full measure inside `s`, then almost every point of `s`, for the restricted
measure, belongs to `G`. This version does not require measurability of `G`. -/
theorem ae_restrict_mem_of_measure_diff_eq_zero
    {μ : Measure E} {s G : Set E} (hs : MeasurableSet s) (hnull : μ (s \ G) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ G := by
  rw [ae_iff]
  rw [Measure.restrict_apply_eq_zero' hs]
  have hset : {x : E | ¬x ∈ G} ∩ s = s \ G := by
    ext x
    simp [and_comm]
  rwa [hset]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A.e. membership in `G` for the restricted measure is the same as `G` having null complement
inside `s`. This version does not require measurability of `G`. -/
theorem measure_diff_eq_zero_of_ae_restrict_mem
    {μ : Measure E} {s G : Set E} (hs : MeasurableSet s)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ G) :
    μ (s \ G) = 0 := by
  rw [ae_iff] at hmem
  rw [Measure.restrict_apply_eq_zero' hs] at hmem
  have hset : {x : E | ¬x ∈ G} ∩ s = s \ G := by
    ext x
    simp [and_comm]
  rwa [hset] at hmem

/-- A.e. membership version of `secondOrderDifferentiableAEOn_of_fullMeasure_goodSet'`.
This is convenient for Fubini arguments that naturally produce restricted-a.e. membership
rather than a null-complement statement. -/
theorem secondOrderDifferentiableAEOn_of_ae_goodSet
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hmem : ∀ᵐ x ∂μ.restrict s, x ∈ G)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G → SecondOrderDifferentiableAt u x) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet' hs
    (measure_diff_eq_zero_of_ae_restrict_mem hs hmem) hG

omit [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Full-measure-in-`s` is monotone when the good set is enlarged. -/
theorem measure_diff_eq_zero_of_subset_of_measure_diff_eq_zero
    {μ : Measure E} {s G H : Set E} (hGH : G ⊆ H) (hG : μ (s \ G) = 0) :
    μ (s \ H) = 0 := by
  have hsubset : s \ H ⊆ s \ G := by
    intro x hx
    exact ⟨hx.1, fun hxG => hx.2 (hGH hxG)⟩
  exact le_antisymm ((measure_mono hsubset).trans_eq hG) bot_le

omit [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Countably many full-measure subsets of `s` hold simultaneously almost everywhere on `s`.
This is the main bookkeeping lemma for intersections of line/density good sets. -/
theorem ae_restrict_mem_iInter_of_forall_measure_diff_eq_zero
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∈ ⋂ n : ℕ, G n := by
  simpa [Set.mem_iInter] using
    (ae_all_iff.mpr fun n : ℕ =>
      ae_restrict_mem_of_measure_diff_eq_zero (μ := μ) (s := s) (G := G n) hs (hnull n))

/-- If countably many full-measure good sets jointly imply second-order differentiability on `s`,
then `u` is second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_countable_fullMeasure_goodSets
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) → SecondOrderDifferentiableAt u x) :
    SecondOrderDifferentiableAEOn μ s u := by
  rw [SecondOrderDifferentiableAEOn]
  filter_upwards [ae_restrict_mem hs,
    ae_restrict_mem_iInter_of_forall_measure_diff_eq_zero (μ := μ) hs hnull] with x hxs hxG
  exact hG hxs (by simpa [Set.mem_iInter] using hxG)

/-- Countable full-measure good sets whose simultaneous validity gives explicit symmetric
second-order expansion data imply second-order differentiability almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_countable_fullMeasure_expansionData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_goodSets hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, B, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB hquad)

/-- Countable full-measure good sets whose simultaneous validity gives represented
continuous-linear first-order expansion data imply second-order differentiability almost
everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_countable_fullMeasure_clmExpansionData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_goodSets hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, ℓ, B, hℓ, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM_eq_inner hℓ hB hquad)

omit [MeasurableSpace E] in
/-- The differentiability locus is exactly the set of points carrying some symmetric
second-order expansion data. This is mostly a named unfolding for final assembly arguments. -/
theorem secondOrderDifferentiabilitySet_eq_setOf_exists_expansionData
    {u : E → ℝ} :
    secondOrderDifferentiabilitySet u =
      {x | ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B} := by
  ext x
  rfl

/-- If a fixed symmetric expansion locus has full measure in `s`, then `u` is second-order
differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_expansionSet
    {μ : Measure E} {s : Set E} {u : E → ℝ} {p : E} {B : E →L[ℝ] E}
    (hs : MeasurableSet s) (hB : IsSymmetricOperator B)
    (hnull : μ (s \ secondOrderExpansionSet u p B) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact secondOrderExpansionSet_subset_secondOrderDifferentiabilitySet hB hx.2)

/-- If a full-measure set in `s` carries explicit symmetric second-order expansion data at every
point, then `u` is second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_expansionData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet' hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, B, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt hB hquad)

/-- If a full-measure set in `s` carries represented continuous-linear first-order expansion data
at every point, then `u` is second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_clmExpansionData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet' hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨p, ℓ, B, hℓ, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM_eq_inner hℓ hB hquad)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_expansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_expansionData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_expansionData hs hnull hG)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_expansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_expansionData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ B : E →L[ℝ] E,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAt u x p B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_fullMeasure_expansionData hs hnull hG)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_clmExpansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_clmExpansionData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_clmExpansionData hs hnull hG)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_clmExpansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_clmExpansionData
    {μ : Measure E} {s G : Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → x ∈ G →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_fullMeasure_clmExpansionData hs hnull hG)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_countable_fullMeasure_clmExpansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_countable_fullMeasure_clmExpansionData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_countable_fullMeasure_clmExpansionData hs hnull hG)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_countable_fullMeasure_clmExpansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_countable_fullMeasure_clmExpansionData
    {μ : Measure E} {s : Set E} {G : ℕ → Set E} {u : E → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : E⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ p : E, ∃ ℓ : E →L[ℝ] ℝ, ∃ B : E →L[ℝ] E,
        (∀ z : E, ℓ z = inner ℝ p z) ∧
          IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_countable_fullMeasure_clmExpansionData hs hnull hG)

section HilbertCLM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H]

/-- In a real Hilbert space, pointwise CLM-gradient expansion data implies second-order
differentiability almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_forall_hilbertClmExpansionData
    {μ : Measure H} {s : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : H⦄, x ∈ s →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_forall_mem hs (by
    intro x hx
    rcases h hx with ⟨ℓ, B, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM hB hquad)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_forall_hilbertClmExpansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_forall_hilbertClmExpansionData
    {μ : Measure H} {s : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : H⦄, x ∈ s →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_forall_hilbertClmExpansionData hs h)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_forall_hilbertClmExpansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_forall_hilbertClmExpansionData
    {μ : Measure H} {s : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (h : ∀ ⦃x : H⦄, x ∈ s →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_forall_hilbertClmExpansionData hs h)

/-- In a real Hilbert space, full-measure CLM-gradient expansion data implies second-order
differentiability almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionData
    {μ : Measure H} {s G : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : H⦄, x ∈ s → x ∈ G →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet' hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨ℓ, B, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM hB hquad)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_hilbertClmExpansionData
    {μ : Measure H} {s G : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : H⦄, x ∈ s → x ∈ G →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionData hs hnull hG)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_hilbertClmExpansionData
    {μ : Measure H} {s G : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ G) = 0)
    (hG : ∀ ⦃x : H⦄, x ∈ s → x ∈ G →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionData hs hnull hG)

/-- In a real Hilbert space, countably many full-measure good sets whose simultaneous validity
gives CLM-gradient expansion data imply second-order differentiability almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_countable_fullMeasure_hilbertClmExpansionData
    {μ : Measure H} {s : Set H} {G : ℕ → Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : H⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_countable_fullMeasure_goodSets hs hnull (by
    intro x hxs hxG
    rcases hG hxs hxG with ⟨ℓ, B, hB, hquad⟩
    exact secondOrderDifferentiableAt_of_hasSecondOrderExpansionAtCLM hB hquad)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_countable_fullMeasure_hilbertClmExpansionData`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_countable_fullMeasure_hilbertClmExpansionData
    {μ : Measure H} {s : Set H} {G : ℕ → Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : H⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_countable_fullMeasure_hilbertClmExpansionData hs hnull hG)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_countable_fullMeasure_hilbertClmExpansionData`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_countable_fullMeasure_hilbertClmExpansionData
    {μ : Measure H} {s : Set H} {G : ℕ → Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : ∀ n : ℕ, μ (s \ G n) = 0)
    (hG : ∀ ⦃x : H⦄, x ∈ s → (∀ n : ℕ, x ∈ G n) →
      ∃ ℓ : H →L[ℝ] ℝ, ∃ B : H →L[ℝ] H,
        IsSymmetricOperator B ∧ HasSecondOrderExpansionAtCLM u x ℓ B) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_countable_fullMeasure_hilbertClmExpansionData hs hnull hG)

/-- If a fixed CLM expansion locus has full measure in `s` and the Hessian candidate is
symmetric, then `u` is second-order differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionSet
    {μ : Measure H} {s : Set H} {u : H → ℝ} {ℓ : H →L[ℝ] ℝ} {B : H →L[ℝ] H}
    (hs : MeasurableSet s) (hB : IsSymmetricOperator B)
    (hnull : μ (s \ secondOrderExpansionSetCLM u ℓ B) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact secondOrderExpansionSetCLM_subset_secondOrderDifferentiabilitySet hB hx.2)

/-- If the CLM expansion-data locus has full measure in `s`, then `u` is second-order
differentiable almost everywhere on `s`. -/
theorem secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionDataSet
    {μ : Measure H} {s : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ secondOrderCLMExpansionDataSet u) = 0) :
    SecondOrderDifferentiableAEOn μ s u :=
  secondOrderDifferentiableAEOn_of_fullMeasure_goodSet hs hnull (by
    intro x hx
    exact secondOrderCLMExpansionDataSet_subset_secondOrderDifferentiabilitySet hx.2)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_hilbertClmExpansionSet
    {μ : Measure H} {s : Set H} {u : H → ℝ} {ℓ : H →L[ℝ] ℝ} {B : H →L[ℝ] H}
    (hs : MeasurableSet s) (hB : IsSymmetricOperator B)
    (hnull : μ (s \ secondOrderExpansionSetCLM u ℓ B) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionSet hs hB hnull)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionSet`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_hilbertClmExpansionSet
    {μ : Measure H} {s : Set H} {u : H → ℝ} {ℓ : H →L[ℝ] ℝ} {B : H →L[ℝ] H}
    (hs : MeasurableSet s) (hB : IsSymmetricOperator B)
    (hnull : μ (s \ secondOrderExpansionSetCLM u ℓ B) = 0) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionSet hs hB hnull)

/-- Null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionDataSet`. -/
theorem measure_secondOrderBadSetOn_eq_zero_of_fullMeasure_hilbertClmExpansionDataSet
    {μ : Measure H} {s : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ secondOrderCLMExpansionDataSet u) = 0) :
    μ (secondOrderBadSetOn s u) = 0 :=
  (secondOrderDifferentiableAEOn_iff_measure_secondOrderBadSetOn_eq_zero hs).mp
    (secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionDataSet hs hnull)

/-- Restricted-measure null-bad-set version of
`secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionDataSet`. -/
theorem restrict_measure_secondOrderBadSet_eq_zero_of_fullMeasure_hilbertClmExpansionDataSet
    {μ : Measure H} {s : Set H} {u : H → ℝ} (hs : MeasurableSet s)
    (hnull : μ (s \ secondOrderCLMExpansionDataSet u) = 0) :
    μ.restrict s (secondOrderBadSet u) = 0 :=
  restrict_measure_secondOrderBadSet_eq_zero_of_secondOrderDifferentiableAEOn
    (secondOrderDifferentiableAEOn_of_fullMeasure_hilbertClmExpansionDataSet hs hnull)

end HilbertCLM

end AleksandrovDifferentiability
