/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectAction

/-!
# Positive structural reduction for one direct offset

This file contains the part of the direct argument which is genuinely
positive. It replaces the supremum of partial tails by the finite sum of
the absolute values of its localized pieces. Consequently every positive
pairing estimate for the individual pieces (for instance the elementary
kernel-size/Tonelli estimate) may be summed without any stopping-time or
orthogonality input.

The final theorem is deliberately formulated with the one-piece positive
estimate as an argument. This makes its use independent of which concrete
kernel-size implementation supplies that estimate.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectPositivePairing

open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectPartition


noncomputable
section

/-- Classical equality for the interval indices of the positive pairing. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- Finite grouped inputs are integrable. This is the input-side finiteness
needed to distribute the positive pairing over output intervals. -/
theorem integrable_offsetGroupedInput
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (I : RealInterval) (s : ℤ) :
    Integrable (offsetGroupedInput S scale f I s) := by
  classical
  let T := (selectedSubintervals S I).filter
    (fun J ↦ scale I - scale J = s)
  have hsum : Integrable (∑ J ∈ T,
      I.centralThird.indicator ((smallestSelectedRegion S J).indicator f)) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert J T hJ ih =>
        have hterm : Integrable
            (I.centralThird.indicator ((smallestSelectedRegion S J).indicator f)) :=
          (f.integrable_finiteSparseProof.indicator
            (measurableSet_smallestSelectedRegion S J)).indicator
              I.measurableSet_centralThird
        simpa [Finset.sum_insert, hJ] using hterm.add ih
  unfold offsetGroupedInput
  have hsum' : Integrable (fun x ↦ ∑ J ∈ T,
      I.centralThird.indicator ((smallestSelectedRegion S J).indicator f) x) := by
    convert hsum using 1
    funext x
    simp only [Finset.sum_apply]
  simpa only [T] using hsum'

/-- A tail at a fixed cutoff is bounded by the positive sum of *all* its
localized pieces. In particular, no cost is paid for the number of possible
cutoffs in the definition of `offsetTailMaximal`. -/
theorem enorm_offsetLocalizedActionOn_le_sum_enorm_piece
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (x : ℝ) :
    ‖offsetLocalizedActionOn S A scale f ell s x‖ₑ ≤
      ∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x‖ₑ := by
  classical
  unfold offsetLocalizedActionOn
  calc
    ‖∑ I ∈ A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
        krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x‖ₑ ≤
        ∑ I ∈ A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
          ‖krauseLaceyLocalizedPiece 1 (scale I) I
            (offsetGroupedInput S scale f I s) x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x‖ₑ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro I _ _
      exact bot_le

/-- Positive majorization of the genuine (possibly infinite-indexed)
maximal tail by a finite sum. -/
theorem offsetTailMaximalOn_le_sum_enorm_piece
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) (x : ℝ) :
    offsetTailMaximalOn S A scale f ell₀ s x ≤
      ∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x‖ₑ := by
  unfold offsetTailMaximalOn
  apply iSup_le
  rintro ⟨ell, hell⟩
  exact enorm_offsetLocalizedActionOn_le_sum_enorm_piece S A scale f ell s x

/-- The grouped input is identically zero outside the output central third. -/
theorem offsetGroupedInput_eq_zero_of_notMem_centralThird
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (I : RealInterval) (s : ℤ) {x : ℝ} (hx : x ∉ I.centralThird) :
    offsetGroupedInput S scale f I s x = 0 := by
  unfold offsetGroupedInput
  apply Finset.sum_eq_zero
  intro J hJ
  simp [Set.indicator_of_notMem hx]

/-- The elementary kernel-size estimate for one direct offset piece. The
factor `8` is exactly the ratio between the parent length and the positive
annular outer radius. -/
theorem norm_offsetLocalizedPiece_le_mass_of_scale
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (I : RealInterval) (s : ℤ)
    (hscale : I.length = (2 : ℝ) ^ (scale I + 2)) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (offsetGroupedInput S scale f I s) x‖ ≤
      (8 * positiveDyadicAmplitudeBound / I.length) *
        ∫ t, ‖offsetGroupedInput S scale f I s t‖ := by
  have hb := integrable_offsetGroupedInput S scale f I s
  have h := (krauseLaceyPositiveKernel (scale I)).norm_applyIntegral_le
    (hb.indicator I.measurableSet_centralThird) x
  simp only [FiniteRangeKernel.applyIntegral, krauseLaceyPositiveKernel_apply,
    ← krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution] at h
  have hcentral : (∫ t, ‖I.centralThird.indicator
      (offsetGroupedInput S scale f I s) t‖) =
      ∫ t, ‖offsetGroupedInput S scale f I s t‖ := by
    calc
      (∫ t, ‖I.centralThird.indicator
          (offsetGroupedInput S scale f I s) t‖) =
          ∫ t in I.centralThird, ‖offsetGroupedInput S scale f I s t‖ := by
        simp only [norm_indicator_eq_indicator_norm]
        exact integral_indicator I.measurableSet_centralThird
      _ = ∫ t, ‖offsetGroupedInput S scale f I s t‖ := by
        rw [← integral_indicator I.measurableSet_centralThird]
        apply integral_congr_ae
        filter_upwards [] with t
        by_cases ht : t ∈ I.centralThird
        · rw [Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht,
            offsetGroupedInput_eq_zero_of_notMem_centralThird S scale f I s ht,
            norm_zero]
  rw [hcentral] at h
  apply h.trans_eq
  change (positiveDyadicAmplitudeBound / (2 : ℝ) ^ (scale I - 1)) * _ = _
  rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
  ring

/-- A kernel-size/support majorant for the true offset maximal tail on an
arbitrary output subcollection. -/
theorem offsetTailMaximalOn_le_massMajorant_of_scale
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (ell₀ s : ℤ) (hscale : ∀ I ∈ A,
      I.length = (2 : ℝ) ^ (scale I + 2)) (x : ℝ) :
    offsetTailMaximalOn S A scale f ell₀ s x ≤
      ∑ I ∈ A, ENNReal.ofReal (I.carrier.indicator (fun _ ↦
        (8 * positiveDyadicAmplitudeBound / I.length) *
          ∫ t, ‖offsetGroupedInput S scale f I s t‖) x) := by
  apply iSup_le
  rintro ⟨ell, hell⟩
  unfold offsetLocalizedActionOn
  calc
    ‖∑ I ∈ A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
        krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x‖ₑ ≤
        ∑ I ∈ A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
          ‖krauseLaceyLocalizedPiece 1 (scale I) I
            (offsetGroupedInput S scale f I s) x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ I ∈ A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
        ENNReal.ofReal (I.carrier.indicator (fun _ ↦
          (8 * positiveDyadicAmplitudeBound / I.length) *
            ∫ t, ‖offsetGroupedInput S scale f I s t‖) x) := by
      apply Finset.sum_le_sum
      intro I hI
      by_cases hx : x ∈ I.carrier
      · rw [Set.indicator_of_mem hx]
        simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal
          (norm_offsetLocalizedPiece_le_mass_of_scale S scale f I s
            (hscale I (Finset.mem_filter.mp hI).1) x)
      · rw [Set.indicator_of_notMem hx,
          krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
            (hscale I (Finset.mem_filter.mp hI).1) hx]
        simp
    _ ≤ ∑ I ∈ A, ENNReal.ofReal (I.carrier.indicator (fun _ ↦
        (8 * positiveDyadicAmplitudeBound / I.length) *
          ∫ t, ‖offsetGroupedInput S scale f I s t‖) x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro I _ _
      exact bot_le

/-- The direct positive pairing estimate for one fixed offset and an
arbitrary output subcollection. The proof uses only the localized kernel
size bound, its support in `I`, and Tonelli for a finite sum. -/
theorem lintegral_offsetTailMaximalOn_pairing_le_sum_local_averages
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (h : ℝ → ℂ) (hh : Integrable h) (ell₀ s : ℤ)
    (hscale : ∀ I ∈ A, I.length = (2 : ℝ) ^ (scale I + 2)) :
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ s x * ‖h x‖ₑ) ≤
      ENNReal.ofReal (∑ I ∈ A, 8 * positiveDyadicAmplitudeBound *
        (∫ t, ‖offsetGroupedInput S scale f I s t‖) * intervalL1Average h I) := by
  let C : RealInterval → ℝ := fun I ↦
    (8 * positiveDyadicAmplitudeBound / I.length) *
      ∫ t, ‖offsetGroupedInput S scale f I s t‖
  have hC (I : RealInterval) : 0 ≤ C I := by
    dsimp [C]
    apply mul_nonneg
    · exact div_nonneg
        (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
        I.length_pos.le
    · exact integral_nonneg fun _ ↦ norm_nonneg _
  have hind (I : RealInterval) (x : ℝ) :
      ENNReal.ofReal (I.carrier.indicator (fun _ ↦ C I) x) * ‖h x‖ₑ =
        ENNReal.ofReal (C I) * I.carrier.indicator (fun y ↦ ‖h y‖ₑ) x := by
    by_cases hx : x ∈ I.carrier <;> simp [hx]
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ s x * ‖h x‖ₑ) ≤
        ∫⁻ x, ∑ I ∈ A, ENNReal.ofReal (C I) *
          I.carrier.indicator (fun y ↦ ‖h y‖ₑ) x := by
      apply lintegral_mono
      intro x
      calc
        offsetTailMaximalOn S A scale f ell₀ s x * ‖h x‖ₑ ≤
            (∑ I ∈ A, ENNReal.ofReal
              (I.carrier.indicator (fun _ ↦ C I) x)) * ‖h x‖ₑ :=
          mul_le_mul' (offsetTailMaximalOn_le_massMajorant_of_scale S A scale f
            ell₀ s hscale x) le_rfl
        _ = ∑ I ∈ A, ENNReal.ofReal (I.carrier.indicator (fun _ ↦ C I) x) *
            ‖h x‖ₑ := by rw [Finset.sum_mul]
        _ = ∑ I ∈ A, ENNReal.ofReal (C I) *
            I.carrier.indicator (fun y ↦ ‖h y‖ₑ) x := by
          apply Finset.sum_congr rfl
          intro I hI
          exact hind I x
    _ = ∑ I ∈ A, ENNReal.ofReal (C I) * ∫⁻ x in I.carrier, ‖h x‖ₑ := by
      have hm (I : RealInterval) : AEMeasurable (fun x ↦
          ENNReal.ofReal (C I) * I.carrier.indicator (fun y ↦ ‖h y‖ₑ) x)
          volume :=
        aemeasurable_const.mul
          (hh.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier)
      rw [lintegral_finsetSum' _ (fun I _ ↦ hm I)]
      apply Finset.sum_congr rfl
      intro I hI
      rw [lintegral_const_mul'' _
        (hh.aestronglyMeasurable.enorm.indicator I.measurableSet_carrier),
        lintegral_indicator I.measurableSet_carrier]
    _ = ∑ I ∈ A, ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        (∫ t, ‖offsetGroupedInput S scale f I s t‖) * intervalL1Average h I) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [← ofReal_integral_norm_eq_lintegral_enorm hh.integrableOn,
        ← ENNReal.ofReal_mul (hC I), ← intervalL1Average_mul_length h I]
      congr 1
      dsimp [C]
      field_simp [I.length_pos.ne']
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun I _ ↦ by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
          (integral_nonneg fun _ ↦ norm_nonneg _))
        (intervalL1Average_nonneg h I))).symm

/-- The nonnegative pairing form of the preceding structural reduction.
The right hand side is still an integral of a finite positive sum, which is
often the most convenient form before applying Tonelli to each summand. -/
theorem lintegral_offsetTailMaximalOn_mul_le_lintegral_sum_piece
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) (h : ℝ → ℝ≥0∞) :
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ s x * h x) ≤
      ∫⁻ x, (∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x‖ₑ) * h x := by
  apply lintegral_mono
  intro x
  exact mul_le_mul' (offsetTailMaximalOn_le_sum_enorm_piece S A scale f ell₀ s x) le_rfl

/-- A finite positive pairing can be distributed over its localized pieces
once their measurability is known. -/
theorem lintegral_sum_enorm_piece_mul
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (s : ℤ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x, (∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x‖ₑ) * h x =
      ∑ I ∈ A, ∫⁻ x, ‖krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x‖ₑ * h x := by
  classical
  calc
    ∫⁻ x, (∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x‖ₑ) * h x =
        ∫⁻ x, ∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x‖ₑ * h x := by
      apply lintegral_congr
      intro x
      rw [Finset.sum_mul]
    _ = _ := by
      apply lintegral_finsetSum'
      intro I hI
      exact (integrable_krauseLaceyLocalizedPiece (scale I) I
        (integrable_offsetGroupedInput S scale f I s)).aestronglyMeasurable.enorm.mul
          hh.enorm.aemeasurable

/-- The exact positive structural pairing inequality. The hypothesis is
the elementary per-piece kernel-size/Tonelli estimate; its conclusion has
the paper's mass times local-`L¹` average form and is valid for every finite
subcollection `T`. No decomposition, packing, or maximal-tail theorem is
used in this reduction. -/
theorem lintegral_offsetTailMaximalOn_mul_le_mass_average_sum
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (ell₀ s : ℤ) (h : ℝ → ℂ) (hh : Measurable fun x ↦ ‖h x‖ₑ)
    {C : ℝ≥0∞}
    (hpiece : ∀ I ∈ A,
      (∫⁻ x, ‖krauseLaceyLocalizedPiece 1 (scale I) I
        (offsetGroupedInput S scale f I s) x‖ₑ * ‖h x‖ₑ) ≤
        C * ENNReal.ofReal (∫ x, ‖offsetGroupedInput S scale f I s x‖) *
          ENNReal.ofReal (intervalL1Average h I)) :
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ s x * ‖h x‖ₑ) ≤
      ∑ I ∈ A, C * ENNReal.ofReal (∫ x, ‖offsetGroupedInput S scale f I s x‖) *
        ENNReal.ofReal (intervalL1Average h I) := by
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ s x * ‖h x‖ₑ) ≤
        ∫⁻ x, (∑ I ∈ A, ‖krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x‖ₑ) * ‖h x‖ₑ :=
      lintegral_offsetTailMaximalOn_mul_le_lintegral_sum_piece S A scale f ell₀ s _
    _ = ∑ I ∈ A, ∫⁻ x, ‖krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x‖ₑ * ‖h x‖ₑ :=
      lintegral_sum_enorm_piece_mul S A scale f s _ hh
    _ ≤ ∑ I ∈ A, C * ENNReal.ofReal (∫ x, ‖offsetGroupedInput S scale f I s x‖) *
          ENNReal.ofReal (intervalL1Average h I) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hpiece I hI

/-- The restricted mass statement needed when a fixed offset is tested on
an exceptional root: central-third restriction cannot increase the grouped
input's `L¹` mass. -/
theorem integral_norm_offsetGroupedInput_le_carrier
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (I : RealInterval) (s : ℤ) :
    (∫ x, ‖offsetGroupedInput S scale f I s x‖) ≤
      ∫ x in I.carrier, ‖offsetGroupedInput S scale f I s x‖ := by
  have hsupp : I.carrier.indicator
      (fun x ↦ ‖offsetGroupedInput S scale f I s x‖) =
      fun x ↦ ‖offsetGroupedInput S scale f I s x‖ := by
    funext x
    by_cases hx : x ∈ I.carrier
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,
        offsetGroupedInput_eq_zero_of_notMem_centralThird S scale f I s
          (fun hthird ↦ hx (I.centralThird_subset_carrier hthird)), norm_zero]
  rw [← integral_indicator I.measurableSet_carrier, hsupp]

/-- Fixed-offset mass is controlled by the disjoint-region masses which
generated it. This form is stable when the output family is replaced by an
arbitrary subcollection: the regions are still those of the ambient family
`S`, rather than a newly formed partition. -/
theorem integral_norm_offsetGroupedInput_le_sum_region_mass
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (I : RealInterval) (s : ℤ) :
    (∫ x, ‖offsetGroupedInput S scale f I s x‖) ≤
      ∑ J ∈ (selectedSubintervals S I).filter
          (fun J ↦ scale I - scale J = s),
        ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ := by
  classical
  let T := (selectedSubintervals S I).filter
    (fun J ↦ scale I - scale J = s)
  have hright (J : RealInterval) (hJ : J ∈ T) :
      Integrable (fun x ↦ ‖(smallestSelectedRegion S J).indicator f x‖) :=
    (f.integrable_finiteSparseProof.indicator
      (measurableSet_smallestSelectedRegion S J)).norm
  calc
    (∫ x, ‖offsetGroupedInput S scale f I s x‖) ≤
        ∫ x, ∑ J ∈ T, ‖(smallestSelectedRegion S J).indicator f x‖ := by
      apply integral_mono
      · exact (integrable_offsetGroupedInput S scale f I s).norm
      · exact integrable_finsetSum T fun J hJ ↦ hright J hJ
      · intro x
        unfold offsetGroupedInput
        change ‖∑ J ∈ T, I.centralThird.indicator
          ((smallestSelectedRegion S J).indicator f) x‖ ≤ _
        calc
          _ ≤ ∑ J ∈ T, ‖I.centralThird.indicator
              ((smallestSelectedRegion S J).indicator f) x‖ := norm_sum_le _ _
          _ ≤ ∑ J ∈ T, ‖(smallestSelectedRegion S J).indicator f x‖ := by
            apply Finset.sum_le_sum
            intro J hJ
            by_cases hx : x ∈ I.centralThird
            · rw [Set.indicator_of_mem hx]
            · rw [Set.indicator_of_notMem hx, norm_zero]
              exact norm_nonneg _
    _ = ∑ J ∈ T, ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ :=
      integral_finsetSum T fun J hJ ↦ hright J hJ
    _ = _ := by rfl

/-- The preceding fixed-offset mass estimate summed over any retained output
subcollection. It is the mass-sum form used for a maximal exceptional root;
the right side explicitly records every ambient smallest-region contribution,
so changing `A` never changes the partition. -/
theorem sum_integral_norm_offsetGroupedInput_le_sum_region_mass
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (s : ℤ) :
    ∑ I ∈ A, (∫ x, ‖offsetGroupedInput S scale f I s x‖) ≤
      ∑ I ∈ A, ∑ J ∈ (selectedSubintervals S I).filter
          (fun J ↦ scale I - scale J = s),
        ∫ x, ‖(smallestSelectedRegion S J).indicator f x‖ := by
  apply Finset.sum_le_sum
  intro I hI
  exact integral_norm_offsetGroupedInput_le_sum_region_mass S scale f I s


end
end KrauseLaceyQuadraticDirectPositivePairing
end QuadraticCarleson
