/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
/-!
# Ramification inside the decomposition group

The principal-unit condition forces trivial residue action, so the
ramification group inside inertia has a canonical image in the
decomposition group.

-/

@[expose] public section

noncomputable section

universe u v

namespace RamificationTheory
namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The intrinsic principal-unit ramification condition already forces an
element of the decomposition group to lie in inertia. -/
theorem ramificationCondition_mem_inertiaGroup
    (A : _root_.ValuationSubring L) (sigma : decompositionGroup K A)
    (hsigma : ∀ x : Lˣ,
      automorphismUnitQuotient K A sigma x ∈ A.principalUnitGroup) :
    sigma ∈ inertiaGroup K A := by
  rw [← residueAction_ker (K := K) A, MonoidHom.mem_ker]
  ext z
  change sigma • z = z
  induction z using Quotient.inductionOn' with
  | h a =>
      change sigma • IsLocalRing.residue A a = IsLocalRing.residue A a
      rw [← IsLocalRing.ResidueField.residue_smul]
      by_cases ha : (a : L) = 0
      · have ha' : a = 0 := Subtype.ext ha
        subst a
        simp
      · let x : Lˣ := Units.mk0 (a : L) ha
        have hx : A.valuation
            ((automorphismUnitQuotient K A sigma x : L) - 1) < 1 :=
          (A.mem_principalUnitGroup_iff
            (automorphismUnitQuotient K A sigma x)).mp (hsigma x)
        rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
          A.valuation_lt_one_iff]
        have hfield :
            (((sigma • a - a : A) : A) : L) =
              (a : L) *
                ((automorphismUnitQuotient K A sigma x : L) - 1) := by
          simp [automorphismUnitQuotient, x, div_eq_mul_inv, mul_sub, ha,
            mul_comm]
          rfl
        rw [show ((sigma • a - a : A) : L) =
            (a : L) *
              ((automorphismUnitQuotient K A sigma x : L) - 1) by
          simpa using hfield,
          Valuation.map_mul]
        exact (mul_le_of_le_one_left zero_le
          (A.valuation_le_one a)).trans_lt hx

/-- The ramification group transported from inertia into the decomposition group. -/
abbrev ramificationGroupInDecomposition
    (A : _root_.ValuationSubring L) :
    Subgroup (decompositionGroup K A) :=
  Subgroup.map (inertiaGroup K A).subtype (ramificationGroup K A)
/-- Membership in the transported ramification group is the intrinsic principal-unit condition. -/
theorem mem_ramificationGroupInDecomposition_iff
    (A : _root_.ValuationSubring L) (sigma : decompositionGroup K A) :
    sigma ∈ ramificationGroupInDecomposition K A ↔
      ∀ x : Lˣ,
        automorphismUnitQuotient K A sigma x ∈ A.principalUnitGroup := by
  constructor
  · rintro ⟨iota, hiota, rfl⟩
    exact hiota
  · intro hsigma
    have hi : sigma ∈ inertiaGroup K A :=
      ramificationCondition_mem_inertiaGroup (K := K) A sigma hsigma
    exact ⟨⟨sigma, hi⟩, hsigma, rfl⟩

end ValuationSubring
end HilbertRamification
end RamificationTheory
end
