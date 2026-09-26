/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
/-!
# The zeroth lower group is the inertia group

Mathlib defines inertia through the action on the residue field.  The
valuation-subring definition of `G₀` uses the equivalent condition that
every difference `σ • x - x` belongs to the maximal ideal.
-/

@[expose] public section

namespace ClassFieldTheory

universe u v

/-- The zeroth lower ramification group agrees with Mathlib's inertia
subgroup of the decomposition group. -/
theorem lowerRamificationGroup_zero_eq_inertiaSubgroup
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    lowerRamificationGroup K A 0 = A.inertiaSubgroup K := by
  ext σ
  constructor
  · intro hσ
    change (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) σ) = 1
    apply RingEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    change σ • IsLocalRing.residue A x = IsLocalRing.residue A x
    have hx : σ • x - x ∈ IsLocalRing.maximalIdeal A := by
      simpa only [zero_add, pow_one] using hσ x
    have hz : IsLocalRing.residue A (σ • x - x) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 hx
    have heq : IsLocalRing.residue A (σ • x) = IsLocalRing.residue A x :=
      sub_eq_zero.mp (by simpa only [map_sub] using hz)
    simpa only [IsLocalRing.ResidueField.residue_smul] using heq
  · intro hσ x
    change (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) σ) = 1 at hσ
    have hfix : σ • IsLocalRing.residue A x = IsLocalRing.residue A x := by
      have h := congrArg
        (fun e : RingAut (IsLocalRing.ResidueField A) =>
          e (IsLocalRing.residue A x)) hσ
      simpa using h
    have hz : IsLocalRing.residue A (σ • x - x) = 0 := by
      rw [map_sub, IsLocalRing.ResidueField.residue_smul, hfix, sub_self]
    simpa only [zero_add, pow_one] using (IsLocalRing.residue_eq_zero_iff _).1 hz

end ClassFieldTheory
