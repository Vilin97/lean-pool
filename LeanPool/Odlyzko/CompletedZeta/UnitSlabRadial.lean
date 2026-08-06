/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.UnitSlabTranslation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units Set
  dirichletUnitTheorem

namespace NumberField.Odlyzko

open mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- A nonnegative radial half space used in the Odlyzko-bound argument. -/
def nonnegativeRadialHalfSpace :
    Set (mixedEmbedding.realSpace K) :=
  {y | 0 ≤ y w₀}

open Classical in
/-- A negative radial half space used in the Odlyzko-bound argument. -/
def negativeRadialHalfSpace :
    Set (mixedEmbedding.realSpace K) :=
  {y | y w₀ < 0}

open Classical in
/-- A positive radial half space used in the Odlyzko-bound argument. -/
def positiveRadialHalfSpace :
    Set (mixedEmbedding.realSpace K) :=
  {y | 0 < y w₀}

open Classical in
/-- A nonnegative unit fundamental param set used in the Odlyzko-bound argument. -/
def nonnegativeUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  unitFundamentalParamSet K ∩ nonnegativeRadialHalfSpace (K := K)

open Classical in
/-- A negative unit fundamental param set used in the Odlyzko-bound argument. -/
def negativeUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  unitFundamentalParamSet K ∩ negativeRadialHalfSpace (K := K)

open Classical in
/-- A positive unit fundamental param set used in the Odlyzko-bound argument. -/
def positiveUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  unitFundamentalParamSet K ∩ positiveRadialHalfSpace (K := K)

open Classical in
theorem measurableSet_negativeRadialHalfSpace :
    MeasurableSet (negativeRadialHalfSpace (K := K)) :=
  measurableSet_lt (measurable_pi_apply w₀) measurable_const

open Classical in
theorem measurableSet_positiveRadialHalfSpace :
    MeasurableSet (positiveRadialHalfSpace (K := K)) :=
  measurableSet_lt measurable_const (measurable_pi_apply w₀)

open Classical in
theorem measurableSet_negativeUnitFundamentalParamSet :
    MeasurableSet (negativeUnitFundamentalParamSet (K := K)) :=
  measurableSet_unitFundamentalParamSet.inter
    measurableSet_negativeRadialHalfSpace

open Classical in
theorem measurableSet_positiveUnitFundamentalParamSet :
    MeasurableSet (positiveUnitFundamentalParamSet (K := K)) :=
  measurableSet_unitFundamentalParamSet.inter
    measurableSet_positiveRadialHalfSpace

open Classical in
theorem nonnegativeRadialHalfSpace_ae_eq_positive :
    nonnegativeRadialHalfSpace (K := K) =ᵐ[
      (volume : Measure (mixedEmbedding.realSpace K))]
        positiveRadialHalfSpace (K := K) := by
  rw [MeasureTheory.volume_pi]
  filter_upwards [Measure.ae_eval_ne (fun _ ↦ volume) w₀ 0] with y hy
  simp only [nonnegativeRadialHalfSpace, positiveRadialHalfSpace]
  apply propext
  constructor
  · intro h
    exact lt_of_le_of_ne h hy.symm
  · exact le_of_lt

open Classical in
theorem nonnegativeUnitFundamentalParamSet_ae_eq_positive :
    nonnegativeUnitFundamentalParamSet (K := K) =ᵐ[
      (volume : Measure (mixedEmbedding.realSpace K))]
        positiveUnitFundamentalParamSet (K := K) :=
  (ae_eq_refl (unitFundamentalParamSet K)).inter
    nonnegativeRadialHalfSpace_ae_eq_positive

open Classical in
theorem setIntegral_nonnegativeUnitFundamentalParamSet_eq_positive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E) :
    (∫ y in nonnegativeUnitFundamentalParamSet (K := K), f y) =
      ∫ y in positiveUnitFundamentalParamSet (K := K), f y :=
  setIntegral_congr_set nonnegativeUnitFundamentalParamSet_ae_eq_positive

open Classical in
theorem disjoint_nonnegative_negativeUnitFundamentalParamSet :
    Disjoint (nonnegativeUnitFundamentalParamSet (K := K))
      (negativeUnitFundamentalParamSet (K := K)) := by
  rw [Set.disjoint_left]
  intro y hy hny
  exact (not_lt_of_ge
    (show 0 ≤ y w₀ from hy.2))
    (show y w₀ < 0 from hny.2)

open Classical in
theorem union_nonnegative_negativeUnitFundamentalParamSet :
    nonnegativeUnitFundamentalParamSet (K := K) ∪
        negativeUnitFundamentalParamSet (K := K) =
      unitFundamentalParamSet K := by
  ext y
  simp only [nonnegativeUnitFundamentalParamSet,
    negativeUnitFundamentalParamSet, nonnegativeRadialHalfSpace,
    negativeRadialHalfSpace, Set.mem_union, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  grind

open Classical in
theorem setIntegral_unitFundamentalParamSet_eq_add_radialHalves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : IntegrableOn f (unitFundamentalParamSet K)) :
    (∫ y in unitFundamentalParamSet K, f y) =
      (∫ y in nonnegativeUnitFundamentalParamSet (K := K), f y) +
        ∫ y in negativeUnitFundamentalParamSet (K := K), f y := by
  rw [← union_nonnegative_negativeUnitFundamentalParamSet (K := K)]
  exact setIntegral_union
    disjoint_nonnegative_negativeUnitFundamentalParamSet
    measurableSet_negativeUnitFundamentalParamSet
    (hf.mono_set Set.inter_subset_left)
    (hf.mono_set Set.inter_subset_left)

open Classical in
theorem setIntegral_unitFundamentalParamSet_eq_add_openRadialHalves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : IntegrableOn f (unitFundamentalParamSet K)) :
    (∫ y in unitFundamentalParamSet K, f y) =
      (∫ y in positiveUnitFundamentalParamSet (K := K), f y) +
        ∫ y in negativeUnitFundamentalParamSet (K := K), f y := by
  rw [setIntegral_unitFundamentalParamSet_eq_add_radialHalves f hf,
    setIntegral_nonnegativeUnitFundamentalParamSet_eq_positive]

open Classical in
/-- A neg unit fundamental param set used in the Odlyzko-bound argument. -/
def negUnitFundamentalParamSet :
    Set (mixedEmbedding.realSpace K) :=
  (fun y ↦ -y) ⁻¹' unitFundamentalParamSet K

open Classical in
theorem measurableSet_negUnitFundamentalParamSet :
    MeasurableSet (negUnitFundamentalParamSet (K := K)) :=
  measurable_neg measurableSet_unitFundamentalParamSet

open Classical in
theorem isAddFundamentalDomain_negUnitFundamentalParamSet :
    IsAddFundamentalDomain (unitCoordinateLattice (K := K))
      (negUnitFundamentalParamSet (K := K)) volume := by
  apply IsAddFundamentalDomain.mk'
    measurableSet_negUnitFundamentalParamSet.nullMeasurableSet
  intro x
  obtain ⟨h, hh, huniq⟩ :=
    existsUnique_vadd_mem_unitFundamentalParamSet (K := K) (-x)
  let g : unitCoordinateLattice (K := K) := -h
  refine ⟨g, ?_, ?_⟩
  · change -((g : mixedEmbedding.realSpace K) + x) ∈
      unitFundamentalParamSet K
    simpa [g, add_comm] using hh
  · intro g' hg'
    have hneg :
        ((-g' : unitCoordinateLattice (K := K)) :
            mixedEmbedding.realSpace K) + -x ∈
          unitFundamentalParamSet K := by
      change -((g' : mixedEmbedding.realSpace K) + x) ∈
        unitFundamentalParamSet K at hg'
      simpa only [AddSubgroup.coe_neg, neg_add_rev, add_comm] using hg'
    have heq := huniq (-g') hneg
    simpa [g] using congrArg Neg.neg heq

open Classical in
theorem setIntegral_negUnitFundamentalParamSet_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x) :
    (∫ y in negUnitFundamentalParamSet (K := K), f y) =
      ∫ y in unitFundamentalParamSet K, f y :=
  (isAddFundamentalDomain_negUnitFundamentalParamSet (K := K)).setIntegral_eq
    isAddFundamentalDomain_unitFundamentalParamSet hf

open Classical in
theorem setIntegral_positive_comp_neg_eq_negSlab_negative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E) :
    (∫ y in positiveUnitFundamentalParamSet (K := K), f (-y)) =
      ∫ y in negUnitFundamentalParamSet (K := K) ∩
        negativeRadialHalfSpace (K := K), f y := by
  have h := measurableEmbedding_neg.setIntegral_map
    (μ := (volume : Measure (mixedEmbedding.realSpace K))) f
    (negUnitFundamentalParamSet (K := K) ∩
      negativeRadialHalfSpace (K := K))
  rw [Measure.map_neg_eq_self] at h
  have hpreimage :
      (fun y : mixedEmbedding.realSpace K ↦ -y) ⁻¹'
          (negUnitFundamentalParamSet (K := K) ∩
            negativeRadialHalfSpace (K := K)) =
        positiveUnitFundamentalParamSet (K := K) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff,
      negUnitFundamentalParamSet, negativeRadialHalfSpace,
      positiveUnitFundamentalParamSet, positiveRadialHalfSpace,
      Set.mem_ofPred_eq, Pi.neg_apply, neg_neg, neg_lt_zero]
  simp_all

open Classical in
theorem setIntegral_negative_eq_positive_comp_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x) :
    (∫ y in negativeUnitFundamentalParamSet (K := K), f y) =
      ∫ y in positiveUnitFundamentalParamSet (K := K), f (-y) := by
  let F := (negativeRadialHalfSpace (K := K)).indicator f
  have hF : ∀ (g : unitCoordinateLattice (K := K)) x,
      F ((g : mixedEmbedding.realSpace K) + x) = F x := by
    intro g x
    by_cases hx : x ∈ negativeRadialHalfSpace (K := K)
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∈
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx, hf]
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∉
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx]
  have hfund :=
    setIntegral_negUnitFundamentalParamSet_eq F hF
  rw [setIntegral_indicator measurableSet_negativeRadialHalfSpace,
    setIntegral_indicator measurableSet_negativeRadialHalfSpace] at hfund
  change (∫ y in unitFundamentalParamSet K ∩
      negativeRadialHalfSpace (K := K), f y) =
    ∫ y in positiveUnitFundamentalParamSet (K := K), f (-y)
  rw [setIntegral_positive_comp_neg_eq_negSlab_negative]
  simp_all

open Classical in
theorem integrableOn_negative_iff_positive_comp_neg
    {E : Type*} [NormedAddCommGroup E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x) :
    IntegrableOn f (negativeUnitFundamentalParamSet (K := K)) ↔
      IntegrableOn (fun y ↦ f (-y))
        (positiveUnitFundamentalParamSet (K := K)) := by
  let F := (negativeRadialHalfSpace (K := K)).indicator f
  have hF : ∀ (g : unitCoordinateLattice (K := K)) x,
      F ((g : mixedEmbedding.realSpace K) + x) = F x := by
    intro g x
    by_cases hx : x ∈ negativeRadialHalfSpace (K := K)
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∈
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx, hf]
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∉
            negativeRadialHalfSpace (K := K) := by
        simpa [negativeRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [F, hx, hgx]
  have hpreimage :
      (fun y : mixedEmbedding.realSpace K ↦ -y) ⁻¹'
          (negUnitFundamentalParamSet (K := K) ∩
            negativeRadialHalfSpace (K := K)) =
        positiveUnitFundamentalParamSet (K := K) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff,
      negUnitFundamentalParamSet, negativeRadialHalfSpace,
      positiveUnitFundamentalParamSet, positiveRadialHalfSpace,
      Set.mem_ofPred_eq, Pi.neg_apply, neg_neg, neg_lt_zero]
  constructor
  · intro hneg
    have hFstandard : IntegrableOn F (unitFundamentalParamSet K) := by
      apply IntegrableOn.congr_fun
        (hneg.integrable_indicator
          measurableSet_negativeUnitFundamentalParamSet).integrableOn
        _ measurableSet_unitFundamentalParamSet
      intro y hy
      by_cases hrad : y ∈ negativeRadialHalfSpace (K := K)
      · simp [F, negativeUnitFundamentalParamSet, hy, hrad]
      · simp [F, negativeUnitFundamentalParamSet, hrad]
    have hFneg :
        IntegrableOn F (negUnitFundamentalParamSet (K := K)) :=
      ((isAddFundamentalDomain_unitFundamentalParamSet).integrableOn_iff
        (isAddFundamentalDomain_negUnitFundamentalParamSet (K := K)) hF).mp
        hFstandard
    have hfneg :
        IntegrableOn f
          (negUnitFundamentalParamSet (K := K) ∩
            negativeRadialHalfSpace (K := K)) := by
      apply IntegrableOn.congr_fun
        (hFneg.mono_set Set.inter_subset_left)
        _ (measurableSet_negUnitFundamentalParamSet.inter
          measurableSet_negativeRadialHalfSpace)
      intro y hy
      simp [F, hy.2]
    have hmap :=
      (Measure.measurePreserving_neg
        (volume : Measure (mixedEmbedding.realSpace K))).integrableOn_comp_preimage
        measurableEmbedding_neg
        (f := f)
        (s := negUnitFundamentalParamSet (K := K) ∩
          negativeRadialHalfSpace (K := K))
    rw [hpreimage] at hmap
    exact hmap.mpr hfneg
  · intro hreflect
    have hmap :=
      (Measure.measurePreserving_neg
        (volume : Measure (mixedEmbedding.realSpace K))).integrableOn_comp_preimage
        measurableEmbedding_neg
        (f := f)
        (s := negUnitFundamentalParamSet (K := K) ∩
          negativeRadialHalfSpace (K := K))
    rw [hpreimage] at hmap
    have hfneg := hmap.mp hreflect
    have hFneg :
        IntegrableOn F (negUnitFundamentalParamSet (K := K)) := by
      have hindicator :
          Integrable
            ((negUnitFundamentalParamSet (K := K) ∩
              negativeRadialHalfSpace (K := K)).indicator f) :=
        hfneg.integrable_indicator
          (measurableSet_negUnitFundamentalParamSet.inter
            measurableSet_negativeRadialHalfSpace)
      apply IntegrableOn.congr_fun hindicator.integrableOn
        _ measurableSet_negUnitFundamentalParamSet
      intro y hy
      by_cases hrad : y ∈ negativeRadialHalfSpace (K := K)
      · simp [F, hy, hrad]
      · simp [F, hrad]
    have hFstandard :
        IntegrableOn F (unitFundamentalParamSet K) :=
      ((isAddFundamentalDomain_negUnitFundamentalParamSet (K := K)).integrableOn_iff
        isAddFundamentalDomain_unitFundamentalParamSet hF).mp hFneg
    apply IntegrableOn.congr_fun
      (hFstandard.mono_set Set.inter_subset_left)
      _ measurableSet_negativeUnitFundamentalParamSet
    intro y hy
    simp [F, hy.2]

open Classical in
theorem setIntegral_positiveUnitFundamentalParamSet_add_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x)
    (a : mixedEmbedding.realSpace K) (ha : a w₀ = 0) :
    (∫ x in positiveUnitFundamentalParamSet (K := K), f (x + a)) =
      ∫ x in positiveUnitFundamentalParamSet (K := K), f x := by
  let P := (positiveRadialHalfSpace (K := K)).indicator f
  have hP : ∀ (g : unitCoordinateLattice (K := K)) x,
      P ((g : mixedEmbedding.realSpace K) + x) = P x := by
    intro g x
    by_cases hx : x ∈ positiveRadialHalfSpace (K := K)
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∈
            positiveRadialHalfSpace (K := K) := by
        simpa [positiveRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [P, hx, hgx, hf]
    · have hgx :
          (g : mixedEmbedding.realSpace K) + x ∉
            positiveRadialHalfSpace (K := K) := by
        simpa [positiveRadialHalfSpace,
          unitCoordinateLattice_apply_w₀] using hx
      simp [P, hx, hgx]
  have hPa (x : mixedEmbedding.realSpace K) :
      P (x + a) =
        (positiveRadialHalfSpace (K := K)).indicator
          (fun y ↦ f (y + a)) x := by
    have hmem :
        x + a ∈ positiveRadialHalfSpace (K := K) ↔
          x ∈ positiveRadialHalfSpace (K := K) := by
      simp [positiveRadialHalfSpace, ha]
    by_cases hx : x ∈ positiveRadialHalfSpace (K := K)
    · simp [P, hx, hmem.mpr hx]
    · have hxa : x + a ∉ positiveRadialHalfSpace (K := K) :=
        fun h ↦ hx (hmem.mp h)
      simp [P, hx, hxa]
  calc
    (∫ x in positiveUnitFundamentalParamSet (K := K), f (x + a)) =
        ∫ x in unitFundamentalParamSet K, P (x + a) := by
      rw [show positiveUnitFundamentalParamSet (K := K) =
          unitFundamentalParamSet K ∩
            positiveRadialHalfSpace (K := K) by rfl,
        ← setIntegral_indicator measurableSet_positiveRadialHalfSpace]
      simp_all
    _ = ∫ x in unitFundamentalParamSet K, P x :=
      setIntegral_unitFundamentalParamSet_add_eq P hP a
    _ = ∫ x in positiveUnitFundamentalParamSet (K := K), f x := by
      rw [show positiveUnitFundamentalParamSet (K := K) =
          unitFundamentalParamSet K ∩
            positiveRadialHalfSpace (K := K) by rfl,
        ← setIntegral_indicator measurableSet_positiveRadialHalfSpace]

end NumberField.Odlyzko
