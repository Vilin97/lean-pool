/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Lifetime.Basic

/-!
# Deterministic time shifts of lifetime paths

This file shifts a lifetime path forward by a fixed finite time. A shift beyond the original
lifetime produces a path with zero lifetime, hence with cemetery state at every coordinate.
-/

noncomputable section PortComputability

open MeasureTheory
open scoped ENNReal

namespace MarkovProcess.LifetimePath

section

variable {α : Type*} [TopologicalSpace α]

/-- Shift a lifetime path forward by the deterministic time `S`. -/
def shift (S : NNReal) (ω : LifetimePath α) : LifetimePath α where
  lifetime := ω.lifetime - (S : ENNReal)
  livePath := fun t ↦ ω.livePath ⟨S + t, by
    rw [ENNReal.coe_add, add_comm]
    exact lt_tsub_iff_right.mp t.property⟩
  continuous_livePath := by
    apply ω.continuous_livePath.comp
    exact (continuous_const.add continuous_subtype_val).subtype_mk _

@[simp]
theorem lifetime_shift (S : NNReal) (ω : LifetimePath α) :
    (shift S ω).lifetime = ω.lifetime - (S : ENNReal) :=
  rfl

/-- A shifted coordinate before the shifted lifetime is the corresponding original coordinate. -/
theorem coordinate_shift_of_lt (S t : NNReal) (ω : LifetimePath α)
    (ht : (t : ENNReal) < (shift S ω).lifetime) :
    coordinate t (shift S ω) = coordinate (S + t) ω := by
  rw [coordinate_of_lt _ _ ht]
  have hst : ((S + t : NNReal) : ENNReal) < ω.lifetime := by
    rw [ENNReal.coe_add, add_comm]
    exact lt_tsub_iff_right.mp ht
  rw [coordinate_of_lt _ _ hst]
  rfl

/-- At and after the shifted lifetime, the shifted coordinate is the cemetery state. -/
theorem coordinate_shift_of_le (S t : NNReal) (ω : LifetimePath α)
    (ht : (shift S ω).lifetime ≤ (t : ENNReal)) :
    coordinate t (shift S ω) = Cemetery.delta :=
  coordinate_of_le _ _ ht

/-- Every shifted coordinate is the corresponding original coordinate, including at and after
the lifetime, where both sides are the cemetery state. -/
@[simp]
theorem coordinate_shift (S t : NNReal) (ω : LifetimePath α) :
    coordinate t (shift S ω) = coordinate (S + t) ω := by
  by_cases ht : (t : ENNReal) < (shift S ω).lifetime
  · exact coordinate_shift_of_lt S t ω ht
  · rw [coordinate_shift_of_le S t ω (not_lt.mp ht)]
    apply Eq.symm
    apply coordinate_of_le
    rw [lifetime_shift] at ht
    rw [ENNReal.coe_add, add_comm]
    exact not_lt.mp (lt_tsub_iff_right.not.mp ht)

/-- Shifting at or beyond the original lifetime leaves zero remaining lifetime. -/
theorem lifetime_shift_eq_zero_of_le (S : NNReal) (ω : LifetimePath α)
    (hω : ω.lifetime ≤ (S : ENNReal)) : (shift S ω).lifetime = 0 := by
  rw [lifetime_shift]
  exact tsub_eq_zero_iff_le.mpr hω

/-- A shift at or beyond the original lifetime is at the cemetery state at every time,
including time zero. -/
theorem coordinate_shift_eq_delta_of_lifetime_le (S t : NNReal) (ω : LifetimePath α)
    (hω : ω.lifetime ≤ (S : ENNReal)) :
    coordinate t (shift S ω) = Cemetery.delta := by
  apply coordinate_shift_of_le
  rw [lifetime_shift_eq_zero_of_le S ω hω]
  exact bot_le

/-- Shifting twice is shifting once by the sum of the two deterministic times. -/
theorem shift_shift (S T : NNReal) (ω : LifetimePath α) :
    shift T (shift S ω) = shift (S + T) ω := by
  have hlifetime :
      (shift T (shift S ω)).lifetime = (shift (S + T) ω).lifetime := by
    simp only [lifetime_shift, ENNReal.coe_add]
    exact tsub_tsub ω.lifetime (S : ENNReal) (T : ENNReal)
  apply ext_coordinate
  · exact hlifetime
  · intro t
    by_cases ht : (t : ENNReal) < (shift T (shift S ω)).lifetime
    · rw [coordinate_shift_of_lt T t (shift S ω) ht]
      have hTt : ((T + t : NNReal) : ENNReal) < (shift S ω).lifetime := by
        rw [lifetime_shift] at ht
        rw [ENNReal.coe_add, add_comm]
        exact lt_tsub_iff_right.mp ht
      rw [coordinate_shift_of_lt S (T + t) ω hTt]
      have hsum : (t : ENNReal) < (shift (S + T) ω).lifetime := by
        rwa [← hlifetime]
      rw [coordinate_shift_of_lt (S + T) t ω hsum]
      rw [add_assoc]
    · have htle : (shift T (shift S ω)).lifetime ≤ (t : ENNReal) := not_lt.mp ht
      rw [coordinate_shift_of_le T t (shift S ω) htle]
      rw [coordinate_shift_of_le]
      rwa [← hlifetime]

section Measurable

variable [MeasurableSpace α]

/-- Shifting by a fixed deterministic time is measurable for the coordinate-generated
measurable structure on lifetime paths. -/
theorem measurable_shift (S : NNReal) :
    Measurable (shift S : LifetimePath α → LifetimePath α) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpace, MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  apply sup_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_lifetime.sub measurable_const).comap_le
  · rw [iSup_le_iff]
    intro t
    rw [MeasurableSpace.comap_comp]
    have hfun : coordinate (α := α) t ∘ shift S = coordinate (S + t) := by
      funext ω
      exact coordinate_shift S t ω
    rw [hfun]
    exact (measurable_coordinate (S + t)).comap_le

end Measurable

end
end MarkovProcess.LifetimePath

end PortComputability
