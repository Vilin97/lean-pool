/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
/-!
# Uniqueness of logarithms on local-field units

This module isolates the torsion and unit-decomposition argument used to prove
that an extension of the principal-unit logarithm is determined by its value
on a uniformizer.
-/

@[expose] public section

noncomputable
section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- In a complete discretely valued field with finite residue field, `q - 1`
is nonzero. -/
theorem residueField_card_sub_one_ne_zero
    (F : CompleteDVF K) [Finite F.residueField] :
    Nat.card F.residueField - 1 ≠ 0 := by
  classical
  let := Fintype.ofFinite F.residueField
  have hunitpos : 0 < Fintype.card F.residueFieldˣ :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hpos : 0 < Nat.card F.residueField - 1 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_units] using hunitpos
  exact ne_of_gt hpos

/-- A Teichmüller factor in the field-unit decomposition has order dividing
the residue-field cardinality minus one. -/
theorem residueRootsOfUnity_fieldUnitHom_pow_card_sub_one_eq_one
    (F : CompleteDVF K) [Finite F.residueField]
    (ζ : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (ζ : F.valuationSubringˣ)) ^ (Nat.card F.residueField - 1) = 1 := by
  have hζ :
      (ζ : F.valuationSubringˣ) ^ (Nat.card F.residueField - 1) = 1 :=
    ζ.property
  let ι :=
    CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
  calc
    ι (ζ : F.valuationSubringˣ) ^ (Nat.card F.residueField - 1) =
        ι ((ζ : F.valuationSubringˣ) ^ (Nat.card F.residueField - 1)) :=
      (ι.map_pow (ζ : F.valuationSubringˣ)
        (Nat.card F.residueField - 1)).symm
    _ = ι 1 := by rw [hζ]
    _ = 1 := ι.map_one

/-- Every homomorphism from field units to a torsion-free additive group kills
the Teichmüller factor in the field-unit decomposition. -/
theorem monoidHom_toMultiplicative_residueRoot_eq_one
    {A : Type*} [AddCommGroup A] [IsAddTorsionFree A]
    (F : CompleteDVF K) [Finite F.residueField]
    (φ : Kˣ →* Multiplicative A)
    (ζ : CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    φ (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (ζ : F.valuationSubringˣ)) = 1 := by
  apply (pow_eq_one_iff_left
    (M := Multiplicative A)
    (a := φ
      (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (ζ : F.valuationSubringˣ)))
    (residueField_card_sub_one_ne_zero (K := K) F)).1
  calc
    φ (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ)) ^ (Nat.card F.residueField - 1) =
        φ ((CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ)) ^ (Nat.card F.residueField - 1)) :=
      (φ.map_pow _ _).symm
    _ = φ 1 := by
      rw [residueRootsOfUnity_fieldUnitHom_pow_card_sub_one_eq_one (K := K) F ζ]
    _ = 1 := φ.map_one

/-- A homomorphism on field units with torsion-free additive target is
determined by its values on principal units and on a chosen uniformizer. -/
theorem monoidHom_toMultiplicative_ext_of_agree_principalUnits_and_uniformizer
    {A : Type*} [AddCommGroup A] [IsAddTorsionFree A]
    (F : CompleteDVF K) [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ)
    (φ ψ : Kˣ →* Multiplicative A)
    (hprincipal :
      ∀ u : (CompleteDVF.higherPrincipalUnitGroup F) 1,
        φ (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (u : F.valuationSubringˣ)) =
          ψ (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (u : F.valuationSubringˣ)))
    (huniformizer : φ ϖ = ψ ϖ) :
    φ = ψ := by
  ext x
  rcases
      CompleteDVF.higherPrincipalUnitGroup.exists_roots_principalUnit_uniformizer_zpow
        (F := F) V hzero hϖ x with
    ⟨ζ, p, m, hx⟩
  rw [hx]
  have hζφ :
      φ (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ)) = 1 :=
    monoidHom_toMultiplicative_residueRoot_eq_one (K := K) F φ ζ
  have hζψ :
      ψ (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ)) = 1 :=
    monoidHom_toMultiplicative_residueRoot_eq_one (K := K) F ψ ζ
  have hϖm : φ (ϖ ^ m) = ψ (ϖ ^ m) := by
    rw [map_zpow, map_zpow, huniformizer]
  simp [hζφ, hζψ, hprincipal p, hϖm]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
