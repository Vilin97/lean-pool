/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.RestrictedFinite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
/-!
# The maximal Kummer subgroup

The largest admissible Kummer subgroup is the full unit group.  Its
restricted radical quotient is canonically the ordinary power-class group.
-/

noncomputable section

namespace KummerTheory

variable (K : Type) [Field K]

/-- The largest admissible Kummer subgroup, corresponding to adjoining all
`n`-th roots of elements of `Kˣ`. -/
def maximalKummerSubgroup (n : ℕ+) : KummerSubgroup K n :=
  ⟨⊤, le_top⟩

/-- In the maximal Kummer subgroup, restricted ambient powers are the
ordinary `n`-th-power subgroup of the top subgroup. -/
theorem restrictedNthPowersSubgroup_maximal_eq (n : ℕ+) :
    restrictedNthPowersSubgroup n (maximalKummerSubgroup K n) =
      (powMonoidHom (n : ℕ) : (⊤ : Subgroup Kˣ) →* (⊤ : Subgroup Kˣ)).range := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ :=
      (mem_restrictedNthPowersSubgroup_iff n
        (maximalKummerSubgroup K n)).1 ha
    exact (MonoidHom.mem_range (G := (⊤ : Subgroup Kˣ))).2
      ⟨⟨b, Subgroup.mem_top b⟩, Subtype.ext hb⟩
  · intro ha
    obtain ⟨b, hb⟩ :=
      (MonoidHom.mem_range (G := (⊤ : Subgroup Kˣ))).1 ha
    exact
      (mem_restrictedNthPowersSubgroup_iff n
        (maximalKummerSubgroup K n)).2
        ⟨b.1, congrArg Subtype.val hb⟩

/-- The radical quotient for the maximal Kummer subgroup is canonically the
power-class group `Kˣ / Kˣⁿ`. -/
noncomputable def maximalRestrictedRadicalQuotientEquiv (n : ℕ+) :
    Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≃*
      RestrictedRadicalQuotient n (maximalKummerSubgroup K n) :=
  ((LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
        Kˣ (⊤ : Subgroup Kˣ) (n : ℕ) Subgroup.topEquiv.symm).trans
      (QuotientGroup.congr
        ((powMonoidHom (n : ℕ) : (⊤ : Subgroup Kˣ) →* (⊤ : Subgroup Kˣ)).range)
        (restrictedNthPowersSubgroup n (maximalKummerSubgroup K n))
        (MulEquiv.refl (⊤ : Subgroup Kˣ))
        ((Subgroup.map_id _).trans
          (restrictedNthPowersSubgroup_maximal_eq K n).symm))).trans
    (restrictedRadicalQuotientMulEquiv
      n (maximalKummerSubgroup K n)).symm

end KummerTheory

end
