/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LocalizedMaximal.Covering

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Localized maximal estimates
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

theorem SourceLocalizedMaximalBadPredicateMeasurable.of_measurable_parts
    {α : Type*} [MeasurableSpace α] {μparam : α → Measure ℝ} {t : ℝ}
    (hunbdd :
      MeasurableSet
        {p : α × ℝ |
          ¬ BddAbove (localizedIntervalAverageSet (μparam p.1) sourceMaximalDomain p.2)})
    (hsuper :
      MeasurableSet
        {p : α × ℝ |
          t < localizedMaximalFunction (μparam p.1) sourceMaximalDomain p.2}) :
    SourceLocalizedMaximalBadPredicateMeasurable μparam t := by
  simpa [SourceLocalizedMaximalBadPredicateMeasurable, sourceLocalizedMaximalBadPredicate,
    localizedMaximalBadPredicate, Set.ofPred_or] using hunbdd.union hsuper

/-- The source-window maximal bad predicate is measurable as soon as the equivalent
interval-average-exceeds set is measurable. -/
theorem SourceLocalizedMaximalBadPredicateMeasurableOnWindow.of_averageExceeds
    {α : Type*} [MeasurableSpace α] {μparam : α → Measure ℝ} {t : ℝ}
    (havg : SourceLocalizedMaximalAverageExceedsMeasurable μparam t) :
    SourceLocalizedMaximalBadPredicateMeasurableOnWindow μparam t := by
  rw [SourceLocalizedMaximalAverageExceedsMeasurable] at havg
  rw [SourceLocalizedMaximalBadPredicateMeasurableOnWindow]
  convert havg using 1
  ext p
  constructor
  · rintro ⟨hs, hbad⟩
    exact ⟨hs,
      (sourceLocalizedMaximalBadPredicate_iff_exists_average_gt_of_mem_window
        (μ := μparam p.1) hs).mp hbad⟩
  · rintro ⟨hs, havg⟩
    exact ⟨hs,
      (sourceLocalizedMaximalBadPredicate_iff_exists_average_gt_of_mem_window
        (μ := μparam p.1) hs).mpr havg⟩

theorem bddAbove_of_not_localizedMaximalBadPredicate
    {μ : Measure ℝ} {domain : Set ℝ} {s t : ℝ}
    (hnot : ¬ localizedMaximalBadPredicate μ domain s t) :
    BddAbove (localizedIntervalAverageSet μ domain s) := by
  exact not_not.mp fun hbdd => hnot (Or.inl hbdd)

theorem not_lt_localizedMaximalFunction_of_not_localizedMaximalBadPredicate
    {μ : Measure ℝ} {domain : Set ℝ} {s t : ℝ}
    (hnot : ¬ localizedMaximalBadPredicate μ domain s t) :
    ¬ t < localizedMaximalFunction μ domain s := by
  exact fun hlt => hnot (Or.inr hlt)

theorem bddAbove_of_not_sourceLocalizedMaximalBadPredicate
    {μ : Measure ℝ} {s t : ℝ}
    (hnot : ¬ sourceLocalizedMaximalBadPredicate μ s t) :
    BddAbove (localizedIntervalAverageSet μ sourceMaximalDomain s) :=
  bddAbove_of_not_localizedMaximalBadPredicate hnot

theorem not_lt_localizedMaximalFunction_of_not_sourceLocalizedMaximalBadPredicate
    {μ : Measure ℝ} {s t : ℝ}
    (hnot : ¬ sourceLocalizedMaximalBadPredicate μ s t) :
    ¬ t < localizedMaximalFunction μ sourceMaximalDomain s :=
  not_lt_localizedMaximalFunction_of_not_localizedMaximalBadPredicate hnot

/-- Every admissible interval average is bounded by the localized maximal function, provided the
defining set of averages is bounded above. The boundedness hypothesis is intentionally explicit:
for measures with atoms these averages need not be bounded a priori. -/
theorem openIntervalMeasureAverage_le_localizedMaximalFunction
    {μ : Measure ℝ} {domain : Set ℝ} {s a b : ℝ}
    (hbdd : BddAbove (localizedIntervalAverageSet μ domain s))
    (hab : a < b) (hsub : Set.Ioo a b ⊆ domain) (hs : s ∈ Set.Ioo a b) :
    openIntervalMeasureAverage μ a b ≤ localizedMaximalFunction μ domain s := by
  rw [localizedMaximalFunction_eq_sSup_intervalAverageSet]
  exact le_csSup hbdd ⟨a, b, hab, hsub, hs, rfl⟩

/-- A point outside the localized maximal bad predicate controls every admissible interval
average through that point. -/
theorem openIntervalMeasureAverage_le_of_not_localizedMaximalBadPredicate
    {μ : Measure ℝ} {domain : Set ℝ} {s t a b : ℝ}
    (hnot : ¬ localizedMaximalBadPredicate μ domain s t)
    (hab : a < b) (hsub : Set.Ioo a b ⊆ domain) (hs : s ∈ Set.Ioo a b) :
    openIntervalMeasureAverage μ a b ≤ t :=
  (openIntervalMeasureAverage_le_localizedMaximalFunction
    (bddAbove_of_not_localizedMaximalBadPredicate hnot) hab hsub hs).trans
    (le_of_not_gt (not_lt_localizedMaximalFunction_of_not_localizedMaximalBadPredicate hnot))

/-- Source-local version of
`openIntervalMeasureAverage_le_of_not_localizedMaximalBadPredicate`. -/
theorem openIntervalMeasureAverage_le_of_not_sourceLocalizedMaximalBadPredicate
    {μ : Measure ℝ} {s t a b : ℝ}
    (hnot : ¬ sourceLocalizedMaximalBadPredicate μ s t)
    (hab : a < b) (hsub : Set.Ioo a b ⊆ sourceMaximalDomain) (hs : s ∈ Set.Ioo a b) :
    openIntervalMeasureAverage μ a b ≤ t :=
  openIntervalMeasureAverage_le_of_not_localizedMaximalBadPredicate
    hnot hab hsub hs

/-- A source non-bad point controls the real measure of every admissible interval through it.
This is the interval-mass estimate used in the one-dimensional endpoint-control proof. -/
theorem measureReal_Ioo_le_mul_of_not_sourceLocalizedMaximalBadPredicate
    {μ : Measure ℝ} {s t a b : ℝ}
    (hnot : ¬ sourceLocalizedMaximalBadPredicate μ s t)
    (hab : a < b) (hsub : Set.Ioo a b ⊆ sourceMaximalDomain) (hs : s ∈ Set.Ioo a b) :
    μ.real (Set.Ioo a b) ≤ t * (b - a) := by
  have havg :
      openIntervalMeasureAverage μ a b ≤ t :=
    openIntervalMeasureAverage_le_of_not_sourceLocalizedMaximalBadPredicate
      hnot hab hsub hs
  have hlen_pos : 0 < b - a := sub_pos.mpr hab
  rw [openIntervalMeasureAverage] at havg
  exact (div_le_iff₀ hlen_pos).mp havg

/-- A short symmetric interval around a source-window point stays inside the source maximal
domain. -/
theorem sourceMaximalWindow_Ioo_symm_subset_sourceMaximalDomain
    {x h : ℝ} (hx : x ∈ sourceMaximalWindow) (hh : h < 1) :
    Set.Ioo (x - h) (x + h) ⊆ sourceMaximalDomain := by
  intro y hy
  rcases hx with ⟨hx_left, hx_right⟩
  rcases hy with ⟨hy_left, hy_right⟩
  constructor <;> linarith

/-- Symmetric interval-mass bound at a source non-bad point. -/
theorem measureReal_Ioo_symm_le_two_mul_of_not_sourceLocalizedMaximalBadPredicate
    {μ : Measure ℝ} {x t h : ℝ}
    (hnot : ¬ sourceLocalizedMaximalBadPredicate μ x t)
    (hx : x ∈ sourceMaximalWindow) (hh_pos : 0 < h) (hh : h < 1) :
    μ.real (Set.Ioo (x - h) (x + h)) ≤ t * (2 * h) := by
  have hmass :=
    measureReal_Ioo_le_mul_of_not_sourceLocalizedMaximalBadPredicate
      (μ := μ) (s := x) (t := t) (a := x - h) (b := x + h)
      hnot (by linarith)
      (sourceMaximalWindow_Ioo_symm_subset_sourceMaximalDomain hx hh)
      ⟨by linarith, by linarith⟩
  convert hmass using 1
  ring

/-- Source weak-type localized maximal estimate, packaged as a theorem boundary.

The source proves this with the one-dimensional Vitali covering lemma. The hypothesis
`μ sourceMaximalDomain < ⊤` records that the localized measure has finite mass on `(-2,2)`. -/
def LocalizedMaximalEstimateStatement (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (μ : Measure ℝ) (t : ℝ),
      0 < t →
        μ sourceMaximalDomain < ⊤ →
          volume (sourceLocalizedMaximalBadSet μ t) ≤
            ENNReal.ofReal (C * μ.real sourceMaximalDomain / t)

/-- Existential form of the source weak-type localized maximal estimate. This is the theorem
boundary corresponding to the one-dimensional Vitali covering argument in the source proof. -/
def ExistsLocalizedMaximalEstimateStatement : Prop :=
  ∃ C : ℝ, LocalizedMaximalEstimateStatement C

/-- The source localized maximal weak-type estimate, proved by the one-dimensional Vitali
covering argument above. The explicit constant `4` comes from taking enlargement factor
`τ = 4 > 3`. -/
theorem localizedMaximalEstimateStatement_four :
    LocalizedMaximalEstimateStatement 4 := by
  constructor
  · norm_num
  · intro μ t ht hfinite
    rcases exists_disjoint_witnessBall_covering_enlargement
        (μ := μ) (t := t) (τ := (4 : ℝ)) (by norm_num) with
      ⟨u, hdisj, hcover⟩
    have hcount :
        u.Countable :=
      SourceMaximalWitnessInterval.countable_of_pairwiseDisjoint_witnessBall hdisj
    have hτ_nonneg : 0 ≤ (4 : ℝ) := by norm_num
    have hscale_nonneg : 0 ≤ (4 : ℝ) / t := div_nonneg hτ_nonneg ht.le
    have hballs :
        volume
            (⋃ I ∈ u,
              Metric.ball (SourceMaximalWitnessInterval.center I)
                ((4 : ℝ) * SourceMaximalWitnessInterval.radius I)) ≤
          ENNReal.ofReal ((4 : ℝ) / t) *
            ∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1) :=
      volume_biUnion_enlarged_witnessBall_le_mul_tsum_measure
        (μ := μ) (t := t) (τ := (4 : ℝ)) hcount ht hτ_nonneg hfinite
    have hmass :
        (∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1)) ≤
          μ sourceMaximalDomain :=
      tsum_measure_witnessInterval_le_sourceMaximalDomain hcount hdisj
    calc
      volume (sourceLocalizedMaximalBadSet μ t) ≤
          volume
            (⋃ I ∈ u,
              Metric.ball (SourceMaximalWitnessInterval.center I)
                ((4 : ℝ) * SourceMaximalWitnessInterval.radius I)) :=
        measure_mono hcover
      _ ≤
          ENNReal.ofReal ((4 : ℝ) / t) *
            ∑' I : u, μ (SourceMaximalWitnessInterval.interval I.1) :=
        hballs
      _ ≤ ENNReal.ofReal ((4 : ℝ) / t) * μ sourceMaximalDomain :=
        mul_le_mul_right hmass (ENNReal.ofReal ((4 : ℝ) / t))
      _ = ENNReal.ofReal (4 * μ.real sourceMaximalDomain / t) := by
        rw [← ENNReal.ofReal_toReal hfinite.ne]
        rw [← ENNReal.ofReal_mul hscale_nonneg]
        congr 1
        change ((4 : ℝ) / t) * (μ sourceMaximalDomain).toReal =
          4 * (μ sourceMaximalDomain).toReal / t
        ring

/-- Existential source localized maximal weak-type estimate. -/
theorem existsLocalizedMaximalEstimateStatement :
    ExistsLocalizedMaximalEstimateStatement :=
  ⟨4, localizedMaximalEstimateStatement_four⟩

/-- Consequence of the localized maximal estimate after replacing the source interval mass by an
external mass bound. This is the algebraic step used after the one-dimensional convex
second-derivative mass estimate. -/
theorem LocalizedMaximalEstimateStatement.sourceBadSet_measure_le_of_mass_bound
    {C M osc : ℝ} (hmax : LocalizedMaximalEstimateStatement C)
    {μ : Measure ℝ} {t : ℝ} (ht : 0 < t)
    (hfinite : μ sourceMaximalDomain < ⊤)
    (hmass : μ.real sourceMaximalDomain ≤ M * osc) :
    volume (sourceLocalizedMaximalBadSet μ t) ≤
      ENNReal.ofReal (C * M * osc / t) := by
  rcases hmax with ⟨hC, hestimate⟩
  refine (hestimate μ t ht hfinite).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hscale_nonneg : 0 ≤ C / t := div_nonneg hC ht.le
  have hscaled := mul_le_mul_of_nonneg_left hmass hscale_nonneg
  calc
    C * μ.real sourceMaximalDomain / t =
        (C / t) * μ.real sourceMaximalDomain := by ring
    _ ≤ (C / t) * (M * osc) := hscaled
    _ = C * M * osc / t := by ring

/-- Source-form consequence with the one-dimensional convex mass bound
`μ((-2,2)) <= 2 * osc`. -/
theorem LocalizedMaximalEstimateStatement.sourceBadSet_measure_le_of_two_mul_osc
    {C osc : ℝ} (hmax : LocalizedMaximalEstimateStatement C)
    {μ : Measure ℝ} {t : ℝ} (ht : 0 < t)
    (hfinite : μ sourceMaximalDomain < ⊤)
    (hmass : μ.real sourceMaximalDomain ≤ 2 * osc) :
    volume (sourceLocalizedMaximalBadSet μ t) ≤
      ENNReal.ofReal (2 * C * osc / t) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    hmax.sourceBadSet_measure_le_of_mass_bound (M := 2) (osc := osc) ht hfinite hmass

end AleksandrovDifferentiability
