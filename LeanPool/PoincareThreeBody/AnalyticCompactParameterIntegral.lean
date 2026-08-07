/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.JointSlabIntegral

/-!
# Analyticity under integration over a compact time set

A finite subcover of the compact time set reduces the result to the one-slab theorem.  We use
inclusion-exclusion for the finite cover, so no explicit partition or ordering of its members is
needed.
-/

namespace LeanPool.PoincareThreeBody

open Filter MeasureTheory Set Topology

/-- A jointly analytic scalar function remains analytic in its first variable after integration
of the second variable over a compact set.  The eventual integrability assumption is exactly what
is needed to identify the inclusion-exclusion sum near the center parameter. -/
theorem analyticAt_setIntegral_of_joint_analytic
    {function : ℝ × ℝ → ℝ} {centerParameter : ℝ} {timeSet : Set ℝ}
    (hcompact : IsCompact timeSet)
    (hjoint : ∀ time ∈ timeSet, AnalyticAt ℝ function (centerParameter, time))
    (hintegrable : ∀ᶠ parameter in 𝓝 centerParameter,
      IntegrableOn (fun time ↦ function (parameter, time)) timeSet) :
    AnalyticAt ℝ (fun parameter ↦ ∫ time in timeSet, function (parameter, time))
      centerParameter := by
  by_cases hnonempty : timeSet.Nonempty
  swap
  · have hempty : timeSet = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    simpa [hempty] using (analyticAt_const :
      AnalyticAt ℝ (fun _ : ℝ ↦ (0 : ℝ)) centerParameter)
  let Index := {time : ℝ // time ∈ timeSet}
  have hindexAnalytic : ∀ index : Index,
      AnalyticAt ℝ function (centerParameter, index.1) :=
    fun index ↦ hjoint index.1 index.2
  choose jointSeries hseriesAt using hindexAnalytic
  choose rawRadius hjointBall using hseriesAt
  have hrawRadiusPositive : ∀ index, 0 < rawRadius index :=
    fun index ↦ (hjointBall index).r_pos
  choose localRadius hlocalRadius using fun index ↦
    ENNReal.lt_iff_exists_nnreal_btwn.mp (hrawRadiusPositive index)
  let slabRadius : Index → NNReal := fun index ↦ localRadius index / 3
  have hslabRadiusPositive : ∀ index, 0 < slabRadius index := by
    intro index
    apply div_pos
    · exact_mod_cast (hlocalRadius index).1
    · norm_num
  have hlocalBall : ∀ index,
      HasFPowerSeriesOnBall function (jointSeries index)
        (centerParameter, index.1) (localRadius index) := by
    intro index
    exact (hjointBall index).mono
      (by exact_mod_cast (hlocalRadius index).1)
      (le_of_lt (hlocalRadius index).2)
  have hslabRadii : ∀ index,
      slabRadius index + slabRadius index < localRadius index := by
    intro index
    dsimp [slabRadius]
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat]
    nlinarith [show (0 : ℝ) < localRadius index by exact_mod_cast (hlocalRadius index).1]
  let neighborhood : Index → Set ℝ := fun index ↦
    Metric.ball index.1 (slabRadius index : ℝ)
  have hopen : ∀ index, IsOpen (neighborhood index) := fun _ ↦ Metric.isOpen_ball
  have hcovered : timeSet ⊆ ⋃ index, neighborhood index := by
    intro time htime
    apply mem_iUnion.mpr
    refine ⟨⟨time, htime⟩, ?_⟩
    exact Metric.mem_ball_self (by exact_mod_cast hslabRadiusPositive ⟨time, htime⟩)
  obtain ⟨cover, hcover⟩ :=
    hcompact.elim_finite_subcover neighborhood hopen hcovered
  let coverSet : Index → Set ℝ := fun index ↦ timeSet ∩ neighborhood index
  have hcoverSetMeasurable : ∀ index, MeasurableSet (coverSet index) := by
    intro index
    exact hcompact.measurableSet.inter (hopen index).measurableSet
  have hcoverSetSubset : ∀ index, coverSet index ⊆ timeSet :=
    fun _ ↦ inter_subset_left
  have hcoverUnion : (⋃ index ∈ cover, coverSet index) = timeSet := by
    apply Set.Subset.antisymm
    · exact iUnion₂_subset fun index _ ↦ hcoverSetSubset index
    · intro time htime
      rcases mem_iUnion₂.mp (hcover htime) with ⟨index, hindex, htimeNeighborhood⟩
      exact mem_iUnion₂.mpr ⟨index, hindex, htime, htimeNeighborhood⟩
  have hintersectionAnalytic : ∀ subset ∈ cover.powerset, subset.Nonempty →
      AnalyticAt ℝ (fun parameter ↦
        ∫ time in ⋂ index ∈ subset, coverSet index, function (parameter, time))
        centerParameter := by
    intro subset hsubset hsubsetNonempty
    obtain ⟨index, hindex⟩ := hsubsetNonempty
    have hindexCover : index ∈ cover := Finset.mem_powerset.mp hsubset hindex
    have hintersectionMeasurable : MeasurableSet (⋂ member ∈ subset, coverSet member) :=
      subset.measurableSet_biInter fun member _ ↦ hcoverSetMeasurable member
    have hintersectionSubset : (⋂ member ∈ subset, coverSet member) ⊆ timeSet :=
      (biInter_subset_of_mem hindex).trans (hcoverSetSubset index)
    have hintersectionFinite : volume (⋂ member ∈ subset, coverSet member) < ⊤ :=
      (measure_mono hintersectionSubset).trans_lt hcompact.measure_lt_top
    have hintersectionSlab : ∀ time ∈ ⋂ member ∈ subset, coverSet member,
        |time - index.1| ≤ (slabRadius index : ℝ) := by
      intro time htime
      have htimeCover : time ∈ coverSet index :=
        Set.mem_iInter.mp (Set.mem_iInter.mp htime index) hindex
      have htimeBall : time ∈ neighborhood index := htimeCover.2
      exact le_of_lt (by simpa [neighborhood, Real.dist_eq] using htimeBall)
    exact (hasFPowerSeriesOnBall_setIntegral_of_joint_ball_of_measurableSet
      (hlocalBall index) (hslabRadiusPositive index) (hslabRadii index)
      hintersectionMeasurable hintersectionFinite hintersectionSlab).analyticAt
  have hsumAnalytic : AnalyticAt ℝ
      (∑ subset ∈ cover.powerset.filter (·.Nonempty), fun parameter : ℝ ↦
        (-1 : ℝ) ^ (subset.card + 1) *
          ∫ time in ⋂ index ∈ subset, coverSet index,
            function (parameter, time)) centerParameter := by
    apply Finset.analyticAt_sum
    intro subset hsubset
    simp only [Finset.mem_filter] at hsubset
    exact analyticAt_const.mul
      (hintersectionAnalytic subset hsubset.1 hsubset.2)
  apply hsumAnalytic.congr
  filter_upwards [hintegrable] with parameter hparameter
  simp only [Finset.sum_apply, Finset.sum_filter]
  symm
  rw [← hcoverUnion]
  simpa only [Finset.sum_filter, smul_eq_mul] using
    (integral_biUnion_eq_sum_powerset
      (t := cover) (s := coverSet) (f := fun time ↦ function (parameter, time))
      (fun index _ ↦ hcoverSetMeasurable index)
      (fun index _ ↦ hparameter.mono (hcoverSetSubset index) le_rfl))

end LeanPool.PoincareThreeBody
