/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundLevelRecombination
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# A one-dimensional Calderón--Zygmund covering at height one

This module constructs, rather than assumes, a countable pairwise-disjoint
family of positive-radius closed intervals on which the average of `‖f‖` is
strictly larger than one.  The family covers `{x | 1 < ‖f x‖}` almost
everywhere and its total length is controlled by the `L¹` mass of `f`.

The construction uses the Besicovitch Vitali family and the Lebesgue
differentiation theorem.  Selection of intervals with the additional upper
average bound needed for the sharp height-two good part is deliberately left
to a subsequent stopping-time refinement.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal BigOperators Function Topology

namespace QuadraticCarleson
namespace CalderonZygmundDecomposition

open CalderonZygmundLevelRecombination


noncomputable section

/-- The closed-ball Vitali family for Lebesgue measure on the line. -/
abbrev realBallVitali : VitaliFamily (volume : Measure ℝ) :=
  Besicovitch.vitaliFamily volume

/-- Lebesgue differentiation points of the scalar function `‖f‖`. -/
def normDifferentiationPoints (f : ℝ → ℂ) : Set ℝ :=
  {x | Tendsto (fun s ↦ ⨍ y in s, ‖f y‖) (realBallVitali.filterAt x) (nhds ‖f x‖)}

/-- High points at which differentiation is available. -/
def differentiatingHighPoints (f : ℝ → ℂ) : Set ℝ :=
  normDifferentiationPoints f ∩ {x | 1 < ‖f x‖}

/-- Sets from the Vitali family whose `‖f‖` average exceeds height one. -/
def badAverageSubfamily (f : ℝ → ℂ) (_x : ℝ) : Set (Set ℝ) :=
  {s | 1 < ⨍ y in s, ‖f y‖}

/-- At differentiating high points, bad-average balls form a fine Vitali
subfamily. -/
theorem fine_badAverageSubfamily {f : ℝ → ℂ} (_hf : Integrable f) :
    realBallVitali.FineSubfamilyOn (badAverageSubfamily f)
      (differentiatingHighPoints f) := by
  apply realBallVitali.fineSubfamilyOn_of_frequently
  intro x hx
  rcases hx with ⟨hlim, hxhigh⟩
  change Tendsto (fun s ↦ ⨍ y in s, ‖f y‖) (realBallVitali.filterAt x) (nhds ‖f x‖) at hlim
  have hevent : ∀ᶠ s in realBallVitali.filterAt x, 1 < ⨍ y in s, ‖f y‖ :=
    (tendsto_order.1 hlim).1 1 hxhigh
  exact hevent.frequently

/-- The selected index set produced by the Vitali covering theorem. -/
def czIndex {f : ℝ → ℂ} (hf : Integrable f) : Set (ℝ × Set ℝ) :=
  (fine_badAverageSubfamily hf).index

/-- A selected bad interval. -/
def czSet {f : ℝ → ℂ} (hf : Integrable f) (i : czIndex hf) : Set ℝ :=
  (fine_badAverageSubfamily hf).covering i

/-- The exceptional union selected by the decomposition. -/
def czBadUnion {f : ℝ → ℂ} (hf : Integrable f) : Set ℝ :=
  ⋃ i : czIndex hf, czSet hf i

theorem czIndex_countable {f : ℝ → ℂ} (hf : Integrable f) :
    (czIndex hf).Countable :=
  (fine_badAverageSubfamily hf).index_countable

theorem czSet_pairwiseDisjoint {f : ℝ → ℂ} (hf : Integrable f) :
    Pairwise (Disjoint on fun i : czIndex hf ↦ czSet hf i) :=
  (fine_badAverageSubfamily hf).covering_disjoint_subtype

theorem measurableSet_czSet {f : ℝ → ℂ} (hf : Integrable f) (i : czIndex hf) :
    MeasurableSet (czSet hf i) :=
  (fine_badAverageSubfamily hf).measurableSet_u i.2

theorem one_lt_setAverage_norm_czSet {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) :
    1 < ⨍ y in czSet hf i, ‖f y‖ :=
  (fine_badAverageSubfamily hf).covering_mem i.2

/-- Every selected set is a genuine positive-radius closed interval centered
at its first coordinate. -/
theorem exists_pos_radius_czSet {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) :
    ∃ r : ℝ, 0 < r ∧ czSet hf i = closedBall i.1.1 r := by
  have hmem := (fine_badAverageSubfamily hf).covering_mem_family i.2
  rcases hmem with ⟨r, hr, hset⟩
  exact ⟨r, hr, hset.symm⟩

/-- The positive radius of a selected bad interval. -/
def czRadius {f : ℝ → ℂ} (hf : Integrable f) (i : czIndex hf) : ℝ :=
  (exists_pos_radius_czSet hf i).choose

theorem czRadius_pos {f : ℝ → ℂ} (hf : Integrable f) (i : czIndex hf) :
    0 < czRadius hf i :=
  (exists_pos_radius_czSet hf i).choose_spec.1

theorem czSet_eq_closedBall {f : ℝ → ℂ} (hf : Integrable f) (i : czIndex hf) :
    czSet hf i = closedBall i.1.1 (czRadius hf i) :=
  (exists_pos_radius_czSet hf i).choose_spec.2

theorem volume_czSet_lt_top {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) : volume (czSet hf i) < ∞ := by
  rcases exists_pos_radius_czSet hf i with ⟨r, -, hr⟩
  rw [hr, Real.volume_closedBall]
  exact ENNReal.ofReal_lt_top

theorem volume_czSet_eq_length {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) :
    volume (czSet hf i) = ENNReal.ofReal (2 * czRadius hf i) := by
  rw [czSet_eq_closedBall, Real.volume_closedBall]

/-- The total length of the selected disjoint bad intervals is bounded by
the global `L¹` mass. -/
theorem tsum_volume_czSet_le_lintegral_norm {f : ℝ → ℂ} (hf : Integrable f) :
    (∑' i : czIndex hf, volume (czSet hf i)) ≤
      ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  let _ := (czIndex_countable hf).toEncodable
  have hlocal : ∀ i : czIndex hf,
      volume (czSet hf i) ≤ ∫⁻ x in czSet hf i, ENNReal.ofReal ‖f x‖ := by
    intro i
    have hfin : volume (czSet hf i) ≠ ∞ := (volume_czSet_lt_top hf i).ne
    have havg : 1 < ⨍ y in czSet hf i, ‖f y‖ := one_lt_setAverage_norm_czSet hf i
    have hmpos : 0 < volume.real (czSet hf i) := by
      by_contra hn
      have hmzero : volume.real (czSet hf i) = 0 :=
        le_antisymm (le_of_not_gt hn) measureReal_nonneg
      rw [setAverage_eq, hmzero, inv_zero, zero_smul] at havg
      linarith
    have hreal : volume.real (czSet hf i) < ∫ x in czSet hf i, ‖f x‖ := by
      calc
        volume.real (czSet hf i) = volume.real (czSet hf i) * 1 := by ring
        _ < volume.real (czSet hf i) * (⨍ y in czSet hf i, ‖f y‖) :=
          mul_lt_mul_of_pos_left havg hmpos
        _ = ∫ x in czSet hf i, ‖f x‖ := by
          simpa [smul_eq_mul] using
            (measure_smul_setAverage (f := fun x ↦ ‖f x‖) hfin)
    calc
      volume (czSet hf i) = ENNReal.ofReal (volume.real (czSet hf i)) := by
        rw [Measure.real, ENNReal.ofReal_toReal hfin]
      _ ≤ ENNReal.ofReal (∫ x in czSet hf i, ‖f x‖) :=
        ENNReal.ofReal_le_ofReal hreal.le
      _ = ∫⁻ x in czSet hf i, ENNReal.ofReal ‖f x‖ :=
        ofReal_integral_eq_lintegral_ofReal hf.norm.integrableOn
          (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  calc
    (∑' i : czIndex hf, volume (czSet hf i)) ≤
        ∑' i : czIndex hf, ∫⁻ x in czSet hf i, ENNReal.ofReal ‖f x‖ :=
      ENNReal.tsum_le_tsum hlocal
    _ = ∫⁻ x in czBadUnion hf, ENNReal.ofReal ‖f x‖ := by
      rw [czBadUnion, lintegral_iUnion (measurableSet_czSet hf) (czSet_pairwiseDisjoint hf)]
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := volume) (f := fun x ↦ ENNReal.ofReal ‖f x‖)
          (subset_univ (czBadUnion hf)))

theorem tsum_czLength_le_lintegral_norm {f : ℝ → ℂ} (hf : Integrable f) :
    (∑' i : czIndex hf, ENNReal.ofReal (2 * czRadius hf i)) ≤
      ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  simpa only [← volume_czSet_eq_length hf] using tsum_volume_czSet_le_lintegral_norm hf

theorem centeredInterval_subset_czSet {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) :
    centeredInterval i.1.1 (2 * czRadius hf i) ⊆ czSet hf i := by
  rw [czSet_eq_closedBall, Real.closedBall_eq_Icc]
  intro x hx
  simp only [centeredInterval, mem_Ico] at hx
  simp only [mem_Icc]
  constructor <;> linarith

/-- The ordinary bad atom on a selected interval. -/
def czBadAtom {f : ℝ → ℂ} (hf : Integrable f) (i : czIndex hf) : ℝ → ℂ :=
  centeredAtom f i.1.1 (2 * czRadius hf i)

theorem support_centeredAtom_subset (f : ℝ → ℂ) (z R : ℝ) :
    Function.support (centeredAtom f z R) ⊆ centeredInterval z R := by
  intro x hx
  by_contra hnot
  exact hx (by simp [centeredAtom, hnot])

theorem integral_centeredAtom_eq_zero (f : ℝ → ℂ) (z R : ℝ) :
    ∫ x, centeredAtom f z R x = 0 := by
  rw [centeredAtom, integral_indicator
    (show MeasurableSet (centeredInterval z R) by exact measurableSet_Ico)]
  exact setAverage_sub_setAverage
    (CalderonZygmundLevelAtoms.volume_centeredInterval_lt_top z R).ne f

theorem integrable_centeredAtom {f : ℝ → ℂ} (hf : Integrable f) (z R : ℝ) :
    Integrable (centeredAtom f z R) := by
  apply IntegrableOn.integrable_indicator
    (hf.integrableOn.sub (integrableOn_const
      (CalderonZygmundLevelAtoms.volume_centeredInterval_lt_top z R).ne))
    measurableSet_Ico

theorem support_czBadAtom_subset {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) : Function.support (czBadAtom hf i) ⊆ czSet hf i := by
  exact (support_centeredAtom_subset f i.1.1 (2 * czRadius hf i)).trans
    (centeredInterval_subset_czSet hf i)

theorem integral_czBadAtom_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) : ∫ x, czBadAtom hf i x = 0 :=
  integral_centeredAtom_eq_zero f i.1.1 (2 * czRadius hf i)

theorem integrable_czBadAtom {f : ℝ → ℂ} (hf : Integrable f)
    (i : czIndex hf) : Integrable (czBadAtom hf i) :=
  integrable_centeredAtom hf i.1.1 (2 * czRadius hf i)

theorem measurableSet_czBadUnion {f : ℝ → ℂ} (hf : Integrable f) :
    MeasurableSet (czBadUnion hf) := by
  let _ := (czIndex_countable hf).toEncodable
  exact MeasurableSet.iUnion (measurableSet_czSet hf)

private theorem ae_highPoint_mem_czBadUnion_aux {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, 1 < ‖f x‖ → x ∈ czBadUnion hf := by
  have hdiff : ∀ᵐ x ∂volume, x ∈ normDifferentiationPoints f :=
    by simpa [normDifferentiationPoints] using
      realBallVitali.ae_tendsto_average hf.norm.locallyIntegrable
  have hcover : ∀ᵐ x ∂volume,
      x ∉ differentiatingHighPoints f \ czBadUnion hf := by
    apply measure_eq_zero_iff_ae_notMem.mp
    simpa [czBadUnion, czSet, czIndex] using
      (fine_badAverageSubfamily hf).measure_sdiff_biUnion
  filter_upwards [hdiff, hcover] with x hxd hxcover
  intro hxhigh
  by_contra hxunion
  exact hxcover ⟨⟨hxd, hxhigh⟩, hxunion⟩

/-- The part of `f` outside the selected bad intervals. -/
def czOutsideGoodPart {f : ℝ → ℂ} (hf : Integrable f) : ℝ → ℂ :=
  (czBadUnion hf)ᶜ.indicator f

theorem integrable_czOutsideGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (czOutsideGoodPart hf) :=
  hf.indicator (measurableSet_czBadUnion hf).compl

/-- Outside the selected family, `f` is bounded by the decomposition height
almost everywhere. -/
theorem ae_norm_czOutsideGoodPart_le_one {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, ‖czOutsideGoodPart hf x‖ ≤ 1 := by
  filter_upwards [ae_highPoint_mem_czBadUnion_aux hf] with x hx
  by_cases hxu : x ∈ czBadUnion hf
  · simp [czOutsideGoodPart, hxu]
  · rw [czOutsideGoodPart, indicator_of_mem (mem_compl hxu)]
    exact le_of_not_gt (fun hhigh ↦ hxu (hx hhigh))

/-- The outside good part has the expected height-one squared-`L²` control.
This is the sharp good estimate off the selected intervals; controlling the
averages on the intervals requires the stopping-time upper bound. -/
theorem integral_sq_norm_czOutsideGoodPart_le_l1 {f : ℝ → ℂ}
    (hf : Integrable f) :
    (∫ x, ‖czOutsideGoodPart hf x‖ ^ 2) ≤ ∫ x, ‖f x‖ := by
  have hg : Integrable (czOutsideGoodPart hf) := integrable_czOutsideGoodPart hf
  have hsq : Integrable (fun x ↦ ‖czOutsideGoodPart hf x‖ ^ 2) := by
    apply Integrable.mono' hg.norm
      ((hg.1.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
    filter_upwards [ae_norm_czOutsideGoodPart_le_one hf] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    nlinarith [norm_nonneg (czOutsideGoodPart hf x)]
  calc
    (∫ x, ‖czOutsideGoodPart hf x‖ ^ 2) ≤ ∫ x, ‖czOutsideGoodPart hf x‖ := by
      apply integral_mono_ae hsq hg.norm
      filter_upwards [ae_norm_czOutsideGoodPart_le_one hf] with x hx
      rw [pow_two]
      nlinarith [norm_nonneg (czOutsideGoodPart hf x)]
    _ ≤ ∫ x, ‖f x‖ := by
      apply integral_mono_ae hg.norm hf.norm
      filter_upwards with x
      exact norm_indicator_le_norm_self f x

/-- Almost every point of the height-one superlevel set is covered by a
selected bad interval. -/
theorem ae_highPoint_mem_czBadUnion {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, 1 < ‖f x‖ → x ∈ czBadUnion hf :=
  ae_highPoint_mem_czBadUnion_aux hf

end
end CalderonZygmundDecomposition
end QuadraticCarleson
