/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
/-!
# The unit subgroup of a nonarchimedean local field

This module identifies the image of valuation-ring units in the field unit
group with the valuation-one sphere and records that this subgroup is open in
the native topology of a nonarchimedean local field.
-/

@[expose] public section

noncomputable section

universe u

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The image of valuation-ring units in the field unit group. -/
def localBaseUnitSubgroup
    (K : Type u) [Field K] [ValuativeRel K] : Subgroup Kˣ :=
  MonoidHom.range (integerUnitsToFieldUnits K)

/-- A field unit lies in the image of valuation-ring units exactly when its
valuation is one. -/
theorem mem_localBaseUnitSubgroup_iff_valuation_eq_one
    (K : Type u) [Field K] [ValuativeRel K] (x : Kˣ) :
    x ∈ localBaseUnitSubgroup K ↔ ValuativeRel.valuation K (x : K) = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) a)
  · intro hx
    let a : 𝒪[K]ˣ :=
      { val := ⟨(x : K), by
          rw [Valuation.mem_integer_iff]
          exact hx.le⟩
        inv := ⟨(x⁻¹ : K), by
          rw [Valuation.mem_integer_iff]
          simp [hx]⟩
        val_inv := by ext; simp
        inv_val := by ext; simp }
    exact ⟨a, by ext; rfl⟩

/-- The image of valuation-ring units is open in the native topology of a
nonarchimedean local field. -/
theorem localBaseUnitSubgroup_isOpen
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (localBaseUnitSubgroup K : Set Kˣ) := by
  have hsphere : IsOpen {x : K | ValuativeRel.valuation K x = 1} :=
    by
      simpa only [Valuation.restrict_eq_one_iff] using
        (ValuativeRel.valuation K).isOpen_sphere one_ne_zero
  have hpre := hsphere.preimage (Units.continuous_val :
    Continuous (fun x : Kˣ => (x : K)))
  rw [show (localBaseUnitSubgroup K : Set Kˣ) =
      {x : Kˣ | ValuativeRel.valuation K (x : K) = 1} by
    ext x
    exact mem_localBaseUnitSubgroup_iff_valuation_eq_one K x]
  exact hpre

end LocalFieldTheory
