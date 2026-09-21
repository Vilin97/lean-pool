/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyGenerationLayers
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximalProof
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyBadScaleInputs

/-!
# Smallest-selected-interval partition for the direct quadratic proof

This is the finite set-theoretic partition used in the author's direct
Fourier proof of the quadratic localized one-node estimate.  For every
selected interval `J`, its region is what remains of `J` after removing all
strictly smaller selected intervals contained in `J`.  Laminarity makes these
regions pairwise disjoint, and they partition the carrier of every selected
root using only selected subintervals of that root.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectPartition

open KrauseLaceyStoppingExtraction


noncomputable section

local instance : DecidableEq RealInterval := Classical.decEq _

/-- Strict selected descendants of `J`. -/
def strictSelectedDescendants
    (S : Finset RealInterval) (J : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun H ↦ H ≠ J ∧ H.carrier ⊆ J.carrier

/-- The part of `J` assigned to `J` by the smallest-selected-interval
partition. -/
def smallestSelectedRegion
    (S : Finset RealInterval) (J : RealInterval) : Set ℝ :=
  J.carrier \ ⋃ H ∈ strictSelectedDescendants S J, H.carrier

theorem measurableSet_smallestSelectedRegion
    (S : Finset RealInterval) (J : RealInterval) :
    MeasurableSet (smallestSelectedRegion S J) := by
  unfold smallestSelectedRegion
  exact J.measurableSet_carrier.diff
    (Finset.measurableSet_biUnion (strictSelectedDescendants S J)
      fun H _ ↦ H.measurableSet_carrier)

theorem smallestSelectedRegion_subset_carrier
    (S : Finset RealInterval) (J : RealInterval) :
    smallestSelectedRegion S J ⊆ J.carrier :=
  sdiff_subset

/-- Selected intervals contained in a fixed selected root. -/
def selectedSubintervals
    (S : Finset RealInterval) (I : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun J ↦ J.carrier ⊆ I.carrier

theorem mem_selectedSubintervals_iff
    {S : Finset RealInterval} {I J : RealInterval} :
    J ∈ selectedSubintervals S I ↔ J ∈ S ∧ J.carrier ⊆ I.carrier := by
  classical
  simp [selectedSubintervals]

theorem mem_smallestSelectedRegion_iff
    {S : Finset RealInterval} {J : RealInterval} {x : ℝ} :
    x ∈ smallestSelectedRegion S J ↔
      x ∈ J.carrier ∧
        ∀ H ∈ S, H ≠ J → H.carrier ⊆ J.carrier → x ∉ H.carrier := by
  classical
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro H hHS hHJ hsub hxH
    exact hx.2 (Set.mem_iUnion_of_mem H
      (Set.mem_iUnion_of_mem
        (Finset.mem_filter.mpr ⟨hHS, hHJ, hsub⟩) hxH))
  · rintro ⟨hxJ, hmin⟩
    refine ⟨hxJ, ?_⟩
    intro hx
    obtain ⟨H, hH⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hHdesc, hxH⟩ := Set.mem_iUnion.mp hH
    have hd := Finset.mem_filter.mp hHdesc
    exact hmin H hd.1 hd.2.1 hd.2.2 hxH

private theorem length_le_of_carrier_subset {I J : RealInterval}
    (h : I.carrier ⊆ J.carrier) : I.length ≤ J.length := by
  have he := (Ioc_subset_Ioc_iff I.left_lt_right).mp h
  dsimp [RealInterval.length]
  linarith [he.1, he.2]

private theorem length_lt_of_strict_carrier_subset {I J : RealInterval}
    (hne : I ≠ J) (h : I.carrier ⊆ J.carrier) : I.length < J.length := by
  have hle := length_le_of_carrier_subset h
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hne
  exact interval_eq_of_carrier_subset_of_length_le h heq.ge

/-- Distinct smallest-selected regions are disjoint in a laminar selected
family. -/
theorem smallestSelectedRegion_disjoint
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    {I J : RealInterval} (hI : I ∈ S) (hJ : J ∈ S) (hne : I ≠ J) :
    Disjoint (smallestSelectedRegion S I) (smallestSelectedRegion S J) := by
  apply Set.disjoint_left.mpr
  intro x hxI hxJ
  rcases hlam hI hJ hne with hsub | hsub | hdis
  · exact (mem_smallestSelectedRegion_iff.mp hxJ).2 I hI hne
      hsub (mem_smallestSelectedRegion_iff.mp hxI).1
  · exact (mem_smallestSelectedRegion_iff.mp hxI).2 J hJ hne.symm
      hsub (mem_smallestSelectedRegion_iff.mp hxJ).1
  · exact Set.disjoint_left.mp hdis
      (mem_smallestSelectedRegion_iff.mp hxI).1
      (mem_smallestSelectedRegion_iff.mp hxJ).1

/-- Every point of a selected root belongs to the region of some selected
subinterval of that root. -/
theorem exists_mem_smallestSelectedRegion_of_mem_carrier
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    {I : RealInterval} (hI : I ∈ S) {x : ℝ} (hxI : x ∈ I.carrier) :
    ∃ J ∈ S, J.carrier ⊆ I.carrier ∧ x ∈ smallestSelectedRegion S J := by
  classical
  let A := S.filter fun J ↦ x ∈ J.carrier
  have hA : A.Nonempty := ⟨I, Finset.mem_filter.mpr ⟨hI, hxI⟩⟩
  obtain ⟨J, hJA, hJmin⟩ := A.exists_min_image RealInterval.length hA
  have hJS : J ∈ S := (Finset.mem_filter.mp hJA).1
  have hxJ : x ∈ J.carrier := (Finset.mem_filter.mp hJA).2
  have hregion : x ∈ smallestSelectedRegion S J := by
    apply mem_smallestSelectedRegion_iff.mpr
    refine ⟨hxJ, ?_⟩
    intro H hHS hHJ hsub hxH
    have hHA : H ∈ A := Finset.mem_filter.mpr ⟨hHS, hxH⟩
    exact (not_le_of_gt (length_lt_of_strict_carrier_subset hHJ hsub))
      (hJmin H hHA)
  have hJI : J.carrier ⊆ I.carrier := by
    by_cases hJIeq : J = I
    · subst J
      exact Subset.rfl
    rcases hlam hJS hI hJIeq with hsub | hsub | hdis
    · exact hsub
    · have hlen : J.length ≤ I.length := hJmin I
          (Finset.mem_filter.mpr ⟨hI, hxI⟩)
      have heq : I = J :=
        interval_eq_of_carrier_subset_of_length_le hsub hlen
      exact (hJIeq heq.symm).elim
    · exact (Set.disjoint_left.mp hdis hxJ hxI).elim
  exact ⟨J, hJS, hJI, hregion⟩

/-- The smallest-selected regions below a selected root give an exact
pointwise partition of an input restricted to that root. -/
theorem sum_indicator_smallestSelectedRegion_eq
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    {I : RealInterval} (hI : I ∈ S) (f : ℝ → ℂ) (x : ℝ) :
    ∑ J ∈ selectedSubintervals S I,
        (smallestSelectedRegion S J).indicator f x =
      I.carrier.indicator f x := by
  classical
  by_cases hxI : x ∈ I.carrier
  · obtain ⟨J, hJS, hJI, hxJ⟩ :=
      exists_mem_smallestSelectedRegion_of_mem_carrier hlam hI hxI
    have hJmem : J ∈ selectedSubintervals S I :=
      mem_selectedSubintervals_iff.mpr ⟨hJS, hJI⟩
    rw [Finset.sum_eq_single J]
    · simp only [Set.indicator_of_mem hxJ, Set.indicator_of_mem hxI]
    · intro K hK hKJ
      rw [Set.indicator_of_notMem]
      intro hxK
      exact Set.disjoint_left.mp
        (smallestSelectedRegion_disjoint hlam
          (mem_selectedSubintervals_iff.mp hK).1 hJS hKJ)
        hxK hxJ
    · intro hJnot
      exact (hJnot hJmem).elim
  · have hzero : ∀ J ∈ selectedSubintervals S I,
        (smallestSelectedRegion S J).indicator f x = 0 := by
      intro J hJ
      rw [Set.indicator_of_notMem]
      intro hxJ
      exact hxI ((mem_selectedSubintervals_iff.mp hJ).2
        (smallestSelectedRegion_subset_carrier S J hxJ))
    rw [Finset.sum_eq_zero hzero, Set.indicator_of_notMem hxI]

/-- The exact reconstruction remains true after the output interval's
central-third restriction.  This is the paper's identity
`f 1_{I'} = ∑ b_m 1_{I'}` before grouping by scale. -/
theorem sum_indicator_smallestSelectedRegion_centralThird_eq
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    {I : RealInterval} (hI : I ∈ S) (f : ℝ → ℂ) (x : ℝ) :
    ∑ J ∈ selectedSubintervals S I,
        I.centralThird.indicator
          ((smallestSelectedRegion S J).indicator f) x =
      I.centralThird.indicator f x := by
  classical
  by_cases hx : x ∈ I.centralThird
  · simp_rw [Set.indicator_of_mem hx]
    simpa only [Set.indicator_of_mem (I.centralThird_subset_carrier hx)] using
      sum_indicator_smallestSelectedRegion_eq hlam hI f x
  · simp_rw [Set.indicator_of_notMem hx]
    exact Finset.sum_const_zero

/-- The central-third reconstruction grouped by the selected intervals'
scales.  This is the finite, exact form of the sum over `m ≤ j`. -/
theorem sum_grouped_selectedRegions_centralThird_eq
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) {I : RealInterval} (hI : I ∈ S)
    (f : ℝ → ℂ) (x : ℝ) :
    ∑ m ∈ (selectedSubintervals S I).image scale,
        ∑ J ∈ (selectedSubintervals S I).filter (fun J ↦ scale J = m),
          I.centralThird.indicator
            ((smallestSelectedRegion S J).indicator f) x =
      I.centralThird.indicator f x := by
  classical
  rw [Finset.sum_fiberwise_of_maps_to
    (fun J hJ ↦ Finset.mem_image.mpr ⟨J, hJ, rfl⟩)]
  exact sum_indicator_smallestSelectedRegion_centralThird_eq hlam hI f x

/-- The direct proof's input piece at one interval-length scale. -/
def smallestScaleInput (S : Finset RealInterval)
    (scale : RealInterval → ℤ) (f : ℝ → ℂ) (m : ℤ) (x : ℝ) : ℂ :=
  ∑ J ∈ S.filter (fun J ↦ scale J = m),
    (smallestSelectedRegion S J).indicator f x

theorem integrable_smallestScaleInput
    (S : Finset RealInterval) (scale : RealInterval → ℤ)
    (f : L0Infinity) (m : ℤ) : Integrable (smallestScaleInput S scale f m) := by
  classical
  unfold smallestScaleInput
  apply integrable_finsetSum
  intro J hJ
  exact f.integrable_finiteSparseProof.indicator
    (measurableSet_smallestSelectedRegion S J)

/-- At a fixed scale, the selected regions are disjoint, so the norm of the
scale input is exactly the sum of the norms of its regional pieces. -/
theorem norm_smallestScaleInput_eq_sum
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) (f : ℝ → ℂ) (m : ℤ) (x : ℝ) :
    ‖smallestScaleInput S scale f m x‖ =
      ∑ J ∈ S.filter (fun J ↦ scale J = m),
        ‖(smallestSelectedRegion S J).indicator f x‖ := by
  classical
  let C := S.filter fun J ↦ scale J = m
  by_cases hex : ∃ J ∈ C, x ∈ smallestSelectedRegion S J
  · obtain ⟨J, hJC, hxJ⟩ := hex
    have hJS : J ∈ S := (Finset.mem_filter.mp hJC).1
    have hsum : smallestScaleInput S scale f m x =
        (smallestSelectedRegion S J).indicator f x := by
      unfold smallestScaleInput
      apply Finset.sum_eq_single J
      · intro K hKC hKJ
        apply Set.indicator_of_notMem
        intro hxK
        exact Set.disjoint_left.mp
          (smallestSelectedRegion_disjoint hlam
            (Finset.mem_filter.mp hKC).1 hJS hKJ)
          hxK hxJ
      · intro hJnot
        exact (hJnot hJC).elim
    rw [hsum]
    symm
    apply Finset.sum_eq_single J
    · intro K hKC hKJ
      have hxK : x ∉ smallestSelectedRegion S K := by
        intro hxK
        exact Set.disjoint_left.mp
          (smallestSelectedRegion_disjoint hlam
            (Finset.mem_filter.mp hKC).1 hJS hKJ)
          hxK hxJ
      rw [Set.indicator_of_notMem hxK, norm_zero]
    · intro hJnot
      exact (hJnot hJC).elim
  · have hzero : ∀ J ∈ S.filter (fun J ↦ scale J = m),
        (smallestSelectedRegion S J).indicator f x = 0 := by
      intro J hJ
      rw [Set.indicator_of_notMem]
      exact fun hxJ ↦ hex ⟨J, hJ, hxJ⟩
    unfold smallestScaleInput
    rw [Finset.sum_eq_zero hzero, norm_zero]
    apply (Finset.sum_eq_zero fun J hJ ↦ ?_).symm
    rw [hzero J hJ, norm_zero]

/-- Every scale input is pointwise dominated by the original input. -/
theorem norm_smallestScaleInput_le_norm
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) (f : ℝ → ℂ) (m : ℤ) (x : ℝ) :
    ‖smallestScaleInput S scale f m x‖ ≤ ‖f x‖ := by
  classical
  let C := S.filter fun J ↦ scale J = m
  by_cases hex : ∃ J ∈ C, x ∈ smallestSelectedRegion S J
  · obtain ⟨J, hJC, hxJ⟩ := hex
    have hJS : J ∈ S := (Finset.mem_filter.mp hJC).1
    have hsum : smallestScaleInput S scale f m x =
        (smallestSelectedRegion S J).indicator f x := by
      unfold smallestScaleInput
      apply Finset.sum_eq_single J
      · intro K hKC hKJ
        apply Set.indicator_of_notMem
        intro hxK
        exact Set.disjoint_left.mp
          (smallestSelectedRegion_disjoint hlam
            (Finset.mem_filter.mp hKC).1 hJS hKJ)
          hxK hxJ
      · intro hJnot
        exact (hJnot hJC).elim
    rw [hsum, Set.indicator_of_mem hxJ]
  · have hzero : smallestScaleInput S scale f m x = 0 := by
      unfold smallestScaleInput
      apply Finset.sum_eq_zero
      intro J hJ
      apply Set.indicator_of_notMem
      exact fun hxJ ↦ hex ⟨J, hJ, hxJ⟩
    rw [hzero, norm_zero]
    exact norm_nonneg _

/-- The regional masses are bounded by the mass of the root containing the
selected family.  This is the formal finite version of
`∑ₘ ‖bₘ‖₁ ≤ ‖f 1_{I₀}‖₁`. -/
theorem sum_integral_norm_smallestSelectedRegion_le
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    {I₀ : RealInterval} (hsub : ∀ J ∈ S, J.carrier ⊆ I₀.carrier)
    (f : L0Infinity) :
    ∑ J ∈ S, ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ ≤
      ∫ x in I₀.carrier, ‖f x‖ := by
  classical
  have hint (J : RealInterval) :
      Integrable (fun x ↦ ‖(smallestSelectedRegion S J).indicator f x‖) :=
    (f.integrable_finiteSparseProof.indicator
      (measurableSet_smallestSelectedRegion S J)).norm
  rw [← integral_finsetSum S (fun J _ ↦ hint J)]
  rw [← integral_indicator I₀.measurableSet_carrier]
  apply integral_mono
  · exact integrable_finsetSum S fun J _ ↦ hint J
  · exact f.integrable_finiteSparseProof.norm.indicator I₀.measurableSet_carrier
  intro x
  change (∑ J ∈ S,
      ‖(smallestSelectedRegion S J).indicator f x‖) ≤
    I₀.carrier.indicator (fun y ↦ ‖f y‖) x
  by_cases hex : ∃ J ∈ S, x ∈ smallestSelectedRegion S J
  · obtain ⟨J, hJS, hxJ⟩ := hex
    have hxI : x ∈ I₀.carrier :=
      hsub J hJS (smallestSelectedRegion_subset_carrier S J hxJ)
    have hsum : (∑ K ∈ S,
        ‖(smallestSelectedRegion S K).indicator f x‖) =
        ‖(smallestSelectedRegion S J).indicator f x‖ := by
      apply Finset.sum_eq_single J
      · intro K hKS hKJ
        have hxK : x ∉ smallestSelectedRegion S K := by
          intro hxK
          exact Set.disjoint_left.mp
            (smallestSelectedRegion_disjoint hlam hKS hJS hKJ)
            hxK hxJ
        rw [Set.indicator_of_notMem hxK, norm_zero]
      · intro hJnot
        exact (hJnot hJS).elim
    rw [hsum, Set.indicator_of_mem hxJ, Set.indicator_of_mem hxI]
  · have hzero : ∀ J ∈ S,
        ‖(smallestSelectedRegion S J).indicator f x‖ = 0 := by
      intro J hJ
      have hxJ : x ∉ smallestSelectedRegion S J :=
        fun hxJ ↦ hex ⟨J, hJ, hxJ⟩
      rw [Set.indicator_of_notMem hxJ, norm_zero]
    rw [Finset.sum_eq_zero hzero]
    by_cases hxI : x ∈ I₀.carrier
    · rw [Set.indicator_of_mem hxI]
      exact norm_nonneg _
    · rw [Set.indicator_of_notMem hxI]

/- The scale classes are a genuine finite partition of the regional masses. -/
theorem sum_integral_norm_smallestScaleInput_le
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) {I₀ : RealInterval}
    (hsub : ∀ J ∈ S, J.carrier ⊆ I₀.carrier) (f : L0Infinity) :
    ∑ m ∈ S.image scale, ∫ x, ‖smallestScaleInput S scale f m x‖ ≤
      ∫ x in I₀.carrier, ‖f x‖ := by
  classical
  have hpiece (m : ℤ) :
      ∫ x, ‖smallestScaleInput S scale f m x‖ =
        ∑ J ∈ S.filter (fun J ↦ scale J = m),
          ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ := by
    calc
      ∫ x, ‖smallestScaleInput S scale f m x‖ =
          ∫ x, ∑ J ∈ S.filter (fun J ↦ scale J = m),
            ‖(smallestSelectedRegion S J).indicator f x‖ := by
              apply integral_congr_ae
              filter_upwards [] with x
              exact norm_smallestScaleInput_eq_sum hlam scale f m x
      _ = ∑ J ∈ S.filter (fun J ↦ scale J = m),
            ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ := by
              apply integral_finsetSum
              intro J hJ
              exact (f.integrable_finiteSparseProof.indicator
                (measurableSet_smallestSelectedRegion S J)).norm
  calc
    ∑ m ∈ S.image scale, ∫ x, ‖smallestScaleInput S scale f m x‖ =
        ∑ m ∈ S.image scale, ∑ J ∈ S.filter (fun J ↦ scale J = m),
          ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hpiece m
    _ = ∑ J ∈ S, ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun J hJ ↦ Finset.mem_image.mpr ⟨J, hJ, rfl⟩) _
    _ ≤ ∫ x in I₀.carrier, ‖f x‖ :=
      sum_integral_norm_smallestSelectedRegion_le hlam hsub f

/- A scale class has the same local-window estimate as a disjoint carrier
   sum: replacing carriers by their smallest regions only removes mass. -/
theorem integral_window_norm_smallestScaleInput_le
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) (f : L0Infinity) (m : ℤ)
    (hdisj : Set.Pairwise
      (↑(S.filter (fun J ↦ scale J = m)) : Set RealInterval)
      (Disjoint on RealInterval.carrier))
    {L M a b : ℝ} (hL : 0 < L) (hM : 0 ≤ M) (hab : a ≤ b)
    (hlen : ∀ J ∈ S.filter (fun J ↦ scale J = m), J.length ≤ L)
    (hmass : ∀ J ∈ S.filter (fun J ↦ scale J = m),
      (∫ x in J.carrier, ‖f x‖) ≤ M * J.length) :
    (∫ x in Icc a b, ‖smallestScaleInput S scale f m x‖) ≤
      M * (b - a + 2 * L) := by
  classical
  let T := S.filter (fun J ↦ scale J = m)
  have hpoint (x : ℝ) :
      ‖smallestScaleInput S scale f m x‖ ≤
        ‖∑ J ∈ T, J.carrier.indicator f x‖ := by
    by_cases hex : ∃ J ∈ T, x ∈ smallestSelectedRegion S J
    · obtain ⟨J, hJT, hxJ⟩ := hex
      have hsumR' : smallestScaleInput S scale f m x =
          (smallestSelectedRegion S J).indicator f x := by
        unfold smallestScaleInput
        apply Finset.sum_eq_single J
        · intro K hKT hKJ
          apply Set.indicator_of_notMem
          intro hxK
          exact Set.disjoint_left.mp
            (smallestSelectedRegion_disjoint hlam
              (Finset.mem_filter.mp hKT).1 (Finset.mem_filter.mp hJT).1 hKJ)
            hxK hxJ
        · intro hJnot
          exact (hJnot hJT).elim
      have hsumC : (∑ K ∈ T, K.carrier.indicator f x) =
          J.carrier.indicator f x := by
        apply Finset.sum_eq_single J
        · intro K hKT hKJ
          apply Set.indicator_of_notMem
          intro hxK
          exact Set.disjoint_left.mp (hdisj hJT hKT hKJ.symm)
            (smallestSelectedRegion_subset_carrier S J hxJ) hxK
        · intro hJnot
          exact (hJnot hJT).elim
      rw [hsumR', hsumC, Set.indicator_of_mem hxJ,
        Set.indicator_of_mem (smallestSelectedRegion_subset_carrier S J hxJ)]
    · rw [norm_smallestScaleInput_eq_sum hlam scale f m x]
      have hzero : ∀ J ∈ T,
          ‖(smallestSelectedRegion S J).indicator f x‖ = 0 := by
        intro J hJT
        have hxnot : x ∉ smallestSelectedRegion S J :=
          fun hxJ ↦ hex ⟨J, hJT, hxJ⟩
        rw [Set.indicator_of_notMem hxnot, norm_zero]
      rw [Finset.sum_eq_zero hzero]
      exact norm_nonneg _
  have hcarrier : Integrable (fun x ↦ ∑ J ∈ T, J.carrier.indicator f x) :=
    integrable_finsetSum T (fun J hJ ↦
      f.integrable_finiteSparseProof.indicator J.measurableSet_carrier)
  calc
    (∫ x in Icc a b, ‖smallestScaleInput S scale f m x‖) ≤
        ∫ x in Icc a b, ‖∑ J ∈ T, J.carrier.indicator f x‖ := by
      apply integral_mono
      · exact (integrable_smallestScaleInput S scale f m).norm.integrableOn
      · exact hcarrier.norm.integrableOn
      · intro x
        exact hpoint x
    _ ≤ M * (b - a + 2 * L) := by
      apply KrauseLaceyBadScale.integral_window_sum_indicators_le T
        f.integrable_finiteSparseProof hdisj hL hM hab
      · intro J hJ
        exact hlen J hJ
      · intro J hJ
        exact hmass J hJ


end
end KrauseLaceyQuadraticDirectPartition
end QuadraticCarleson
