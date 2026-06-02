/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Analysis.SpecialFunctions.Sigmoid
import LeanPool.QuasiBorelSpaces.MeasureTheory.Cases
import LeanPool.QuasiBorelSpaces.MeasureTheory.Pack
import LeanPool.QuasiBorelSpaces.MeasureTheory.Quantile
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Restrict
import LeanPool.QuasiBorelSpaces.MeasureTheory.Measure
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.QuasiBorelSpaces.MeasureTheory.StandardBorelSpace

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Randomization

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Randomization`.
-/


open scoped unitInterval

namespace MeasureTheory.Measure

variable {A B} [MeasurableSpace A] [MeasurableSpace B]

/-- `normalize` is the canonical injection from `[0, r)` to `[0, 1]`. -/
noncomputable def normalize {r : ℝ} (x : Set.Ico 0 r) : I where
  val := x / r
  property := by rw [Set.mem_Icc, le_div_iff₀, div_le_iff₀] <;> grind

@[simp, fun_prop]
lemma measurable_normalize (r) : Measurable (normalize (r := r)) := by
  unfold normalize
  fun_prop

lemma injective_normalize (r) : Function.Injective (normalize (r := r)) := by
  intro i₁ i₂ hi
  simp only [normalize, Subtype.mk.injEq] at hi
  rw [div_left_inj'] at hi
  · ext
    exact hi
  · grind

noncomputable instance instMeasureSpaceElemRealIcoOfNatLeanPool (r : ℝ) :
    MeasureSpace (Set.Ico 0 r) where
  volume := ENNReal.ofReal r • volume.comap normalize

instance : IsEmpty (Set.Ico 0 (0 : ℝ)) := by simp

@[simp]
lemma volume_zero : (volume : Measure (Set.Ico 0 (0 : ℝ))) = 0 := by
  ext s
  have hs : s = ∅ := by
    ext a
    simpa using a.property
  simp only [hs, measure_empty]

@[simp]
lemma measurableEmbedding_normalize (r) : MeasurableEmbedding (normalize (r := r)) where
  injective := injective_normalize r
  measurable := measurable_normalize r
  measurableSet_image' := by
    intro s hs
    apply MeasurableSet.of_subtype_image
    simp only [normalize, ← Set.image_comp, Function.comp_apply]
    replace hs := MeasurableSet.subtype_image (by simp) hs
    have : ((fun a ↦ ↑a / r) '' s) = (· / r) '' (Subtype.val '' s) := by
      simp only [← Set.image_comp]
      rfl
    rw [this]
    generalize ht : Subtype.val '' s = t
    rw [ht] at hs
    clear ht this s
    wlog! hr : r ≠ 0
    · subst hr
      simp only [Set.image, div_zero, exists_and_right, measurableSet_setOf]
      fun_prop
    have : (fun x ↦ x / r) '' t = (· * r) ⁻¹' t := by grind
    rw [this]
    apply MeasurableMul.measurable_mul_const
    exact hs

@[simp]
lemma range_normalize {r} (hr : 0 < r) : Set.range (normalize (r := r)) = Set.Ico 0 1 := by
  ext x
  simp only [Set.mem_range, normalize, Subtype.exists, Set.mem_Ico, zero_le, true_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    rw [Subtype.mk_lt_mk, Set.Icc.coe_one, div_lt_one] <;> grind
  · intro h
    use x * r
    have : 0 ≤ x * r := by apply mul_nonneg <;> grind
    have : x * r < r := by rw [mul_lt_iff_lt_one_left] <;> grind
    simp only [and_self, exists_true_left, *]
    rw [Subtype.mk_eq_mk, MulDivCancelClass.mul_div_cancel]
    grind

@[simp]
lemma volume_restrict_normalize : volume.restrict (Set.Ico 0 (1 : I)) = volume := by
  ext s hs
  simp only [hs, restrict_apply]
  apply MeasureTheory.measure_inter_conull
  simp only [
    measurableSet_Ico, MeasurableSet.nullMeasurableSet, prob_compl_eq_zero_iff₀,
    unitInterval.volume_Ico, Set.Icc.coe_one, Set.Icc.coe_zero, sub_zero, ENNReal.ofReal_one]

private noncomputable def packI [StandardBorelSpace A] : A → I := unpack ∘ pack
private noncomputable def unpackI [StandardBorelSpace A] [Nonempty A] : I → A := unpack ∘ pack

@[local simp, local fun_prop]
private lemma measurable_packI [StandardBorelSpace A] : Measurable (packI (A := A)) := by
  unfold packI
  fun_prop

@[local simp, local fun_prop]
private lemma measurable_unpackI
    [StandardBorelSpace A] [Nonempty A]
    : Measurable (unpackI (A := A)) := by
  unfold unpackI
  fun_prop

@[local simp]
private lemma unpackI_packI
    [StandardBorelSpace A] [Nonempty A] {x : A}
    : unpackI (packI x) = x := by
  unfold unpackI packI
  simp only [
    Function.comp_apply, Set.countable_coe_iff,
    Cardinal.Real.Icc_countable_iff, not_le,
    zero_lt_one, pack_unpack, unpack_pack]

private instance [StandardBorelSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ]
    : IsProbabilityMeasure (μ.map packI) := by
  apply Measure.isProbabilityMeasure_map
  fun_prop

/-- The function `det μ` is a function such that `volume.map (det μ) = μ`. -/
noncomputable def det [StandardBorelSpace A] (μ : Measure A) [IsProbabilityMeasure μ] : I → A :=
  have := MeasureTheory.nonempty_of_isProbabilityMeasure μ
  unpackI ∘ quantile (μ.map packI)

@[fun_prop]
lemma measurable_det
    [StandardBorelSpace B]
    {μ : A → Measure B} [∀ x, IsProbabilityMeasure (μ x)] (hμ : Measurable μ)
    {i : A → I} (hi : Measurable i)
    : Measurable fun x ↦ det (μ x) (i x) := by
  wlog hA : Nonempty A
  · simp only [not_nonempty_iff] at hA
    apply measurable_of_empty
  have hB := MeasureTheory.nonempty_of_isProbabilityMeasure (μ hA.some)
  apply Measurable.comp (measurable_unpackI (A := B))
  fun_prop

@[simp]
lemma eq_det_volume
    [StandardBorelSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    : volume.map (det μ) = μ := by
  rw [det, ← Measure.map_map]
  · rw [eq_quantile_volume, Measure.map_map]
    · simp +unfoldPartialApp only [Function.comp, unpackI_packI, map_id']
    · fun_prop
    · fun_prop
  · fun_prop
  · apply measurable_quantile <;> fun_prop

/-- The function `detf μ` is a function such that `volume.map (detf μ) = μ`. -/
noncomputable def detf [StandardBorelSpace A]
    (μ : Measure A) [IsFiniteMeasure μ]
    (r : Set.Ico 0 (μ Set.univ).toReal) : A :=
  have : NeZero μ := by
    constructor
    rintro rfl
    simpa using r.property
  det ((μ Set.univ)⁻¹ • μ) (normalize r)

@[fun_prop]
lemma measurable_detf
    [StandardBorelSpace A]
    {μ : Measure A} [IsFiniteMeasure μ]
    : Measurable (detf μ) := by
  unfold detf
  simp only
  wlog! hμ : μ ≠ 0
  · subst hμ
    simp only [coe_zero, Pi.ofNat_apply, ENNReal.toReal_zero, ENNReal.inv_zero, smul_zero]
    apply measurable_of_empty
  have : NeZero μ := ⟨hμ⟩
  apply measurable_det <;> fun_prop

@[simp]
lemma eq_detf_volume
    [StandardBorelSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    : volume.map (detf μ) = μ := by
  wlog! hμ : μ ≠ 0
  · subst hμ
    have hIE : IsEmpty (Set.Ico (0 : ℝ) ((0 : Measure A) Set.univ).toReal) := by
      simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, Set.Ico_self]
      exact Set.isEmpty_coe_sort.mpr rfl
    have : (volume : Measure (Set.Ico (0 : ℝ) ((0 : Measure A) Set.univ).toReal)) = 0 := by
      ext s _
      simp only [Measure.coe_zero, Pi.zero_apply]
      rw [show s = ∅ from Set.eq_empty_of_isEmpty s]
      simp only [measure_empty]
    rw [this]
    simp only [Measure.map_zero]
  have : NeZero μ := ⟨hμ⟩
  change map (((μ Set.univ)⁻¹ • μ).det ∘ normalize) (_ • comap normalize volume) = μ
  simp only [ne_eq, measure_ne_top, not_false_eq_true, ENNReal.ofReal_toReal, Measure.map_smul]
  rw [← map_map, MeasurableEmbedding.map_comap]
  · have : 0 < (μ Set.univ).toReal := by
      rw [(by simp : 0 = ENNReal.toReal 0), ENNReal.toReal_lt_toReal]
      · simp only [measure_univ_pos, ne_eq, hμ, not_false_eq_true]
      · simp only [ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
      · simp only [ne_eq, measure_ne_top, not_false_eq_true]
    simp only [this, range_normalize, volume_restrict_normalize, eq_det_volume]
    rw [smul_smul, ENNReal.mul_inv_cancel]
    · simp only [one_smul]
    · simp only [ne_eq, measure_univ_eq_zero, hμ, not_false_eq_true]
    · simp only [ne_eq, measure_ne_top, not_false_eq_true]
  · apply measurableEmbedding_normalize
  · apply measurable_det <;> fun_prop
  · fun_prop

end MeasureTheory.Measure

namespace MeasureTheory

/-- Splits `I` into two independent copies of `I` via the determinizing map of the
product Lebesgue measure on `I × I`. -/
noncomputable def splitI : I → I × I := Measure.det volume

@[simp, fun_prop]
lemma measurable_splitI : Measurable splitI := by
  unfold splitI
  apply Measure.measurable_det <;> fun_prop

lemma measurePreserving_splitI : MeasurePreserving splitI where
  measurable := by fun_prop
  map_eq := by simp only [splitI, Measure.eq_det_volume]

end MeasureTheory
