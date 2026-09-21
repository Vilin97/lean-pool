/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

/-! # Residue Datum -/
namespace LocalClassFieldTheory
open RamificationTheory

open ClassFormation

/-!
# Finite local reciprocity: the residue datum and its finite indices

The arithmetic-Frobenius degree on an algebraic closure of a finite field is
packaged as the initial datum of the abstract class-formation framework.  For every finite residue
subextension, the image of its fixing subgroup is proved to be exactly
`n ℤ̂`; consequently the abstract residue degree is the ordinary field
degree.  This is the finite-coordinate comparison needed in the local-field
specialization.
-/

noncomputable section

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- The abstract class-formation datum supplied by arithmetic Frobenius on the actual
residue algebraic closure. -/
noncomputable def residueDatumIn : DegreeData (Omega ≃ₐ[k] Omega) where
  degree := residueAbsoluteDegreeIn k Omega
  degree_surjective := (residueAbsoluteFrobeniusEquivIn k Omega).symm.surjective

omit [Fintype k] [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega] in
private theorem mem_fixingSubgroup_iff_restrictNormalHom_eq_one
    (E : FiniteGaloisIntermediateField k Omega)
    (sigma : Omega ≃ₐ[k] Omega) :
    sigma ∈ E.toIntermediateField.fixingSubgroup ↔
      AlgEquiv.restrictNormalHom E sigma = 1 := by
  constructor
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff] at hsigma
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom E sigma x : E) : Omega) = (x : Omega)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact hsigma x x.property
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : E := ⟨x, hx⟩
    have hy := congrArg (fun tau : E ≃ₐ[k] E => tau y) hsigma
    have hyval := congrArg Subtype.val hy
    rw [AlgEquiv.restrictNormalHom_apply] at hyval
    simpa [y] using hyval

/-- The degree image of the subgroup fixing a finite residue extension of
degree `n` is exactly `n ℤ̂`. -/
theorem residueDatumIn_fieldImage_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    (residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E) =
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup := by
  ext z
  let : Finite E := Module.finite_of_finite k
  constructor
  · rintro ⟨sigma, rfl⟩
    change (residueAbsoluteDegreeIn k Omega sigma.1).toAdd ∈
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range
    rw [zHatMulNat_range_eq_ker_reduction
      (Module.finrank k E) Module.finrank_pos]
    change zHatReduction (Module.finrank k E) Module.finrank_pos
      (residueAbsoluteDegreeIn k Omega sigma.1).toAdd = 0
    have hrestrict : AlgEquiv.restrictNormalHom E sigma.1 = 1 :=
      (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E sigma.1).1 sigma.2
    have hcoordinate :=
      finiteResidueFrobeniusExponentEquiv_symm_restrict_in
        k Omega sigma.1 E
    rw [hrestrict, map_one] at hcoordinate
    exact congrArg Multiplicative.toAdd hcoordinate |>.symm
  · intro hz
    change z.toAdd ∈
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range at hz
    rw [zHatMulNat_range_eq_ker_reduction
      (Module.finrank k E) Module.finrank_pos] at hz
    refine ⟨⟨residueAbsoluteFrobenius k Omega z, ?_⟩, ?_⟩
    · apply (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E (residueAbsoluteFrobenius k Omega z)).2
      rw [restrictNormalHom_residueAbsoluteFrobenius]
      change finiteResidueFrobeniusFromZHat k E z = 1
      rw [finiteResidueFrobeniusFromZHat_apply]
      change finiteResidueFrobeniusExponentHom k E
        (Multiplicative.ofAdd
          (zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd)) = 1
      rw [show zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd = 0
        from hz]
      simp
    · exact (residueAbsoluteFrobeniusEquivIn k Omega).symm_apply_apply z

/-- Internal finite-coordinate calculation: the degree image of the fixing
subgroup has natural index equal to the ordinary residue-field degree.  Public
residue-degree APIs use `Cardinal` or a finite residue-field bundle. -/
theorem Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    ((residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E)).index = Module.finrank k E := by
  rw [residueDatumIn_fieldImage_closedFixingSubgroup k Omega E,
    AddSubgroup.index_toSubgroup]
  exact zHatMulNat_range_index (Module.finrank k E) Module.finrank_pos

end
end LocalClassFieldTheory
