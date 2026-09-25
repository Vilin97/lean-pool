/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.UnramifiedRationals
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldUnramified
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields
/-!
# Global cyclotomic inertia argument: completion of the inertia-generation step

The preceding fixed-field lemma shows that a subgroup containing all inertia
groups has an everywhere-unramified fixed field.  Minkowski's discriminant
bound makes that fixed field equal to `ℚ`, and Galois correspondence then
makes the subgroup equal to the full Galois group.
-/

@[expose] public section

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField
open AlgebraicNumberTheory.Ramification

variable {G M : Type*}
variable [Group G]
variable [Field M] [NumberField M]
variable [MulSemiringAction G M]
variable [IsGaloisGroup G ℚ M]

/-- The global cyclotomic inertia argument, completed global inertia-generation step.

Every subgroup of `Gal(M / ℚ)` which contains the inertia group at every
finite prime of `M` is the whole Galois group. -/
theorem subgroup_eq_top_of_forall_inertiaGroup_le
    (H : Subgroup G)
    (hI : ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.IsMaximal],
      inertiaGroup Q G ≤ H) :
    H = ⊤ := by
  let : Finite G := IsGaloisGroup.finite G ℚ M
  have hunramified :
      ∀ (P : Ideal
          (𝓞 (fixedFieldOfSubgroup (K := ℚ) (L := M) G H)))
        [P.IsPrime],
        Algebra.IsUnramifiedAt ℤ P :=
    fixedFieldOfSubgroup_forall_isUnramifiedAt_of_inertiaGroup_le H hI
  have hdegree :
      Module.finrank ℚ
        (fixedFieldOfSubgroup (K := ℚ) (L := M) G H) = 1 :=
    numberField_finrank_eq_one_of_forall_isUnramifiedAt
      (fixedFieldOfSubgroup (K := ℚ) (L := M) G H)
      hunramified
  have hfixed :
      fixedFieldOfSubgroup (K := ℚ) (L := M) G H = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp hdegree
  exact
    (fixedFieldOfSubgroup_eq_bot_iff_subgroup_eq_top
      (K := ℚ) (L := M) (G := G) (H := H)).mp hfixed

end HilbertRamification.Dedekind

end
