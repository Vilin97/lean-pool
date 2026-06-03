/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Probability.CDF
import LeanPool.QuasiBorelSpaces.MeasureTheory.Measure
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Quantile

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Quantile`.
-/


namespace MeasureTheory

variable {A : Type*} [MeasurableSpace A]

open scoped unitInterval

/-- The set of rational elements of the unit interval. -/
private def unitIntervalRat : Set I := { r : I | ∃q : ℚ, r.val = q }

private instance : Countable unitIntervalRat := by
  constructor
  use fun x ↦ Encodable.encode x.property.choose
  apply Function.Injective.comp
  · apply Encodable.encode_injective
  · grind [Function.Injective]

private lemma exists_unitIntervalRat_btwn
    {i j : I} (h : i < j)
    : ∃k : unitIntervalRat, i < k ∧ k < j := by
  rcases i
  rcases j
  simp only [Subtype.mk_lt_mk] at h
  obtain ⟨k, hk₁, hk₂⟩ := exists_rat_btwn h
  exact ⟨⟨⟨k, by grind⟩, by use k⟩, hk₁, hk₂⟩

private noncomputable def cdf (μ : Measure I) [IsProbabilityMeasure μ] (i : I) : I where
  val := ProbabilityTheory.cdf (μ.map Subtype.val) i
  property := by
    simp only [
      Set.mem_Icc, ProbabilityTheory.cdf_nonneg,
      ProbabilityTheory.cdf_le_one, and_self]

@[simp]
private lemma cdf_apply_val (μ : Measure I) [IsProbabilityMeasure μ] (i : I)
    : (cdf μ i).val = (μ (Set.Iic i)).toReal := by
  have : IsProbabilityMeasure (μ.map Subtype.val) := by
    apply Measure.isProbabilityMeasure_map
    fun_prop
  simp only [cdf, ProbabilityTheory.cdf_eq_real, Measure.real]
  rw [Measure.map_apply]
  · rfl
  · fun_prop
  · simp only [measurableSet_Iic]

@[fun_prop]
private lemma measurable_cdf
    {μ : A → Measure I} [∀ x, IsProbabilityMeasure (μ x)] (hμ : Measurable μ)
    {i : A → I} (hi : Measurable i)
    : Measurable fun x ↦ cdf (μ x) (i x) := by
  have {x} : IsProbabilityMeasure  ((μ x).map Subtype.val) := by
    apply Measure.isProbabilityMeasure_map
    fun_prop
  have : ProbabilityTheory.IsFiniteKernel ⟨μ, hμ⟩ := by
    use 1
    simp only [ENNReal.one_lt_top, measure_univ, le_refl, implies_true, and_self]
  have : Measurable (Subtype.val : { x // x ∈ I } → ℝ) := by fun_prop
  simp only [
    cdf, ProbabilityTheory.cdf_eq_real, Measure.real_def, this,
    measurableSet_Iic, Measure.map_apply, Set.preimage_subtype_val_Iic]
  apply Measurable.subtype_mk
  apply Measurable.ennreal_toReal
  apply Measure.measurable_apply
  · infer_instance
  · simp only [Set.mem_Iic]
    fun_prop

@[simp]
private lemma cdf_top (μ : Measure I) [IsProbabilityMeasure μ] : cdf μ ⊤ = ⊤ := by
  ext
  simp only [cdf_apply_val, Set.Iic_top, measure_univ, ENNReal.toReal_one, Set.Icc.coe_top]

private lemma monotone_cdf (μ : Measure I) [IsProbabilityMeasure μ] : Monotone (cdf μ) := by
  intro r₁ r₂ hr
  apply ProbabilityTheory.monotone_cdf
  apply hr

private lemma cdf_continuous
    (μ : Measure I) [IsProbabilityMeasure μ] (i)
    : ContinuousWithinAt (cdf μ) (Set.Ici i) i := by
  unfold cdf
  have := (ProbabilityTheory.cdf (μ.map Subtype.val)).right_continuous i
  rw [Metric.continuousWithinAt_iff] at ⊢ this
  intro ε hε
  obtain ⟨δ, hδ₁, hδ₂⟩ := this ε hε
  use δ, hδ₁
  intro j hj hj'
  apply hδ₂ hj hj'

/-- The quantile distribution function (i.e., the inverse of `cdf`). -/
noncomputable def quantile (μ : Measure I) [IsProbabilityMeasure μ] (i : I) : I :=
  sInf {r : I | i ≤ cdf μ r}

@[fun_prop]
lemma measurable_quantile
    {μ : A → Measure I} [∀ x, IsProbabilityMeasure (μ x)] (hμ : Measurable μ)
    {f : A → I} (hf : Measurable f)
    : Measurable (fun x ↦ quantile (μ x) (f x)) := by
  unfold quantile
  simp only [sInf_eq_iInf, Set.mem_setOf_eq, iInf_eq_if]
  have {i x}
      : (⨅ j : I, if i ≤ cdf (μ x) j then j else ⊤)
      = (⨅ j : unitIntervalRat, if i ≤ cdf (μ x) j then ↑j else ⊤) := by
    apply le_antisymm
    · apply le_iInf fun j ↦ ?_
      apply iInf_le
    · apply le_iInf fun j ↦ ?_
      split_ifs with h
      · have := cdf_continuous (μ x) j
        rw [Metric.continuousWithinAt_iff] at this
        rw [iInf_le_iff]
        by_contra! ⟨k, hk, hkj⟩
        replace hkj : j.val < k.val := by simp only [Subtype.coe_lt_coe, hkj]
        obtain ⟨l, hl, _⟩ := exists_unitIntervalRat_btwn hkj
        have := monotone_cdf (μ x) (le_of_lt hl)
        grind
      · simp only [le_top]
  simp only [this]
  apply Measurable.iInf fun i ↦ ?_
  apply Measurable.ite
  · simp only [measurableSet_setOf]
    apply Measurable.le'
    · fun_prop
    · apply measurable_cdf <;> fun_prop
  · apply measurable_const
  · apply measurable_const

private lemma le_cdf_quantile (u μ) [IsProbabilityMeasure μ] : u ≤ cdf μ (quantile μ u) := by
  simp only [quantile]
  rw [MonotoneOn.map_sInf_of_continuousWithinAt (f := cdf μ)]
  · simp only [le_sInf_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro j k h rfl
    exact h
  · have := cdf_continuous μ (sInf {r | u ≤ cdf μ r})
    apply ContinuousWithinAt.mono this
    intro j hj
    simp only [Set.mem_setOf_eq, Set.mem_Ici] at ⊢ hj
    apply sInf_le
    simp only [Set.mem_setOf_eq, hj]
  · intro i₁ hi₁ i₂ hi₂
    apply monotone_cdf
  · simp only [cdf_top]

namespace Measure

@[simp]
lemma eq_quantile_volume
    (μ : Measure I) [IsProbabilityMeasure μ]
    : volume.map (quantile μ) = μ := by
  apply Measure.ext_of_Iic
  intro i
  rw [map_apply]
  · have lemma₁ {u} : quantile μ u ≤ i ↔ u ≤ cdf μ i := by
      apply Iff.intro
      · intro h
        have := monotone_cdf μ h
        have := le_cdf_quantile u μ
        grind
      · intro h
        apply sInf_le
        simp only [Set.mem_setOf_eq, h]
    simp only [Set.preimage, Set.mem_Iic, lemma₁]
    have lemma₂ : {r : I | r ≤ cdf μ i} = Set.Iic (cdf μ i) := by
      ext ⟨_, _⟩
      simp only [Set.mem_setOf_eq, Set.mem_Iic]
    simp only [
      lemma₂, unitInterval.volume_Iic, cdf_apply_val, ne_eq,
      measure_ne_top, not_false_eq_true, ENNReal.ofReal_toReal]
  · apply measurable_quantile
    · fun_prop
    · fun_prop
  · simp only [measurableSet_Iic]

end Measure

end MeasureTheory
