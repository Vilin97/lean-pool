/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.Domain
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Bounded measurable domains with normalized volume

This module packages the minimum geometric data needed to use volume-normalized
integrals on a bounded measurable domain of strictly positive Lebesgue volume.
The normalization is an `ENNReal` rescaling of restricted Lebesgue measure, so
it has no zero-volume fallback and does not use `ENNReal.toReal` to define a
measure.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

/-- A bounded measurable subset of `R^d` with strictly positive Lebesgue volume. -/
structure BoundedMeasurableDomain (d : ℕ) where
  /-- The underlying measurable subset of `R^d`. -/
  carrier : Set (Vec d)
  measurableSet : MeasurableSet carrier
  isBoundedDomain : IsBoundedDomain carrier
  volume_pos : 0 < MeasureTheory.volume carrier

namespace BoundedMeasurableDomain

instance {d : ℕ} : SetLike (BoundedMeasurableDomain d) (Vec d) where
  coe U := U.carrier
  coe_injective := by
    intro U V hUV
    cases U
    cases V
    cases hUV
    rfl

@[simp] theorem coe_mk {d : ℕ} (U : Set (Vec d)) (hU_meas : MeasurableSet U)
    (hU_bounded : IsBoundedDomain U) (hU_pos : 0 < MeasureTheory.volume U) :
    ((BoundedMeasurableDomain.mk U hU_meas hU_bounded hU_pos :
      BoundedMeasurableDomain d) : Set (Vec d)) = U :=
  rfl

/-- The bounded-domain witness gives a bounded set in the ambient norm. -/
theorem isBounded {d : ℕ} (U : BoundedMeasurableDomain d) :
    Bornology.IsBounded (U : Set (Vec d)) := by
  rcases U.isBoundedDomain with ⟨R, hR_pos, hR⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg hR_pos.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i

/-- Lebesgue measure of a bounded measurable domain is finite. -/
theorem volume_lt_top {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.volume (U : Set (Vec d)) < ∞ :=
  U.isBounded.measure_lt_top

theorem volume_ne_zero {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
  ne_of_gt U.volume_pos

theorem volume_ne_top {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.volume (U : Set (Vec d)) ≠ ∞ :=
  ne_of_lt U.volume_lt_top

/-- Restricted Lebesgue measure on a bounded measurable domain. -/
noncomputable def restrictedVolume {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.Measure (Vec d) :=
  MeasureTheory.volume.restrict U

@[simp] theorem restrictedVolume_apply_univ {d : ℕ} (U : BoundedMeasurableDomain d) :
    U.restrictedVolume Set.univ = MeasureTheory.volume (U : Set (Vec d)) := by
  simp [restrictedVolume]

/-- The probability measure obtained by normalizing restricted Lebesgue measure. -/
noncomputable def normalizedVolume {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.Measure (Vec d) :=
  (MeasureTheory.volume (U : Set (Vec d)))⁻¹ • U.restrictedVolume

@[simp] theorem normalizedVolume_apply_univ {d : ℕ} (U : BoundedMeasurableDomain d) :
    U.normalizedVolume Set.univ = 1 := by
  rw [normalizedVolume, MeasureTheory.Measure.smul_apply, U.restrictedVolume_apply_univ]
  exact ENNReal.inv_mul_cancel U.volume_ne_zero U.volume_ne_top

theorem normalizedVolume_ne_zero {d : ℕ} (U : BoundedMeasurableDomain d) :
    U.normalizedVolume ≠ 0 := by
  intro hU
  have hzero : U.normalizedVolume Set.univ = 0 := by
    rw [hU]
    simp
  simp at hzero

/-- Restricted volume is finite on a bounded measurable domain. -/
theorem restrictedVolume_isFiniteMeasure {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.IsFiniteMeasure U.restrictedVolume where
  measure_univ_lt_top := by
    rw [U.restrictedVolume_apply_univ]
    exact U.volume_lt_top

/-- Normalized volume is a finite measure, without registering a global instance. -/
theorem normalizedVolume_isFiniteMeasure {d : ℕ} (U : BoundedMeasurableDomain d) :
    MeasureTheory.IsFiniteMeasure U.normalizedVolume where
  measure_univ_lt_top := by
    rw [U.normalizedVolume_apply_univ]
    norm_num

/-- Integrability is unchanged by the strictly positive finite normalization factor. -/
theorem integrable_normalizedVolume_iff {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [NormedAddCommGroup E] (f : Vec d → E) :
    MeasureTheory.Integrable f U.normalizedVolume ↔
      MeasureTheory.Integrable f U.restrictedVolume := by
  rw [normalizedVolume]
  exact MeasureTheory.integrable_smul_measure
    (ENNReal.inv_ne_zero.2 U.volume_ne_top) (ENNReal.inv_ne_top.2 U.volume_ne_zero)

/-- The integrability witness required by `average` is valid for normalized volume. -/
theorem integrable_normalizedVolume {d : ℕ} (U : BoundedMeasurableDomain d)
    {E : Type*} [NormedAddCommGroup E] (f : Vec d → E)
    (hf : MeasureTheory.Integrable f U.restrictedVolume) :
    MeasureTheory.Integrable f U.normalizedVolume :=
  (U.integrable_normalizedVolume_iff f).2 hf

/-- The volume-normalized Bochner average of an integrable function.

The explicit proof is transported to `normalizedVolume` by
`integrable_normalizedVolume`; thus its integral body is integrable. -/
noncomputable def average {d : ℕ} (U : BoundedMeasurableDomain d) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec d → E)
    (_hf : MeasureTheory.Integrable f U.restrictedVolume) : E :=
  ∫ x, f x ∂U.normalizedVolume

/-- The normalized Bochner average is inverse volume times the set integral. -/
theorem average_eq_volume_toReal_inv_smul_setIntegral {d : ℕ}
    (U : BoundedMeasurableDomain d) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E) (hf : MeasureTheory.Integrable f U.restrictedVolume) :
    U.average f hf = (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ •
      ∫ x in (U : Set (Vec d)), f x ∂MeasureTheory.volume := by
  rw [average, normalizedVolume, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv]
  rfl

/-- The source-style scalar average formula. -/
theorem average_eq_volume_toReal_inv_mul_setIntegral {d : ℕ}
    (U : BoundedMeasurableDomain d) (f : Vec d → ℝ)
    (hf : MeasureTheory.Integrable f U.restrictedVolume) :
    U.average f hf = (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), f x ∂MeasureTheory.volume := by
  simpa [smul_eq_mul] using U.average_eq_volume_toReal_inv_smul_setIntegral f hf

/-- The volume-normalized scalar pairing of an integrable product. -/
noncomputable def pairing {d : ℕ} (U : BoundedMeasurableDomain d)
    (f g : Vec d → ℝ)
    (hfg : MeasureTheory.Integrable (fun x => f x * g x) U.restrictedVolume) : ℝ :=
  U.average (fun x => f x * g x) hfg

/-- The scalar pairing is the source-style normalized set integral. -/
theorem pairing_eq_volume_toReal_inv_mul_setIntegral {d : ℕ}
    (U : BoundedMeasurableDomain d) (f g : Vec d → ℝ)
    (hfg : MeasureTheory.Integrable (fun x => f x * g x) U.restrictedVolume) :
    U.pairing f g hfg = (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), f x * g x ∂MeasureTheory.volume := by
  simpa [pairing] using
    U.average_eq_volume_toReal_inv_mul_setIntegral (fun x => f x * g x) hfg

end BoundedMeasurableDomain

end Homogenization
