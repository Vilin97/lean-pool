/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueDatum
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence

/-! # Residue Action Index -/
namespace LocalClassFieldTheory

open RamificationTheory

open ClassFormation

/-!
# Finite local reciprocity: residue-action image indices

This file separates the two group-theoretic comparisons used by the local
degree map.  The residue-action exact-sequence theorem supplies the actual action of an absolute
decomposition group on the selected residue algebraic closure.  Once the
decomposition group is all of the absolute Galois group, that action is
surjective.  If a finite-index subgroup has residue-action image equal to the
fixing group of a finite residue subextension, its degree image has the
ordinary residue-field index.
-/

noncomputable section

universe u v

open HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

/-- View every ambient Galois automorphism as a decomposition-group element
when the chosen extension valuation has full decomposition group.  This is
kept generic in the Galois ambient field: the ambient field is the
separable closure, not the algebraic closure (the latter need not be Galois
over an imperfect local field). -/
noncomputable def toDecompositionGroupOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →* decompositionGroup K A where
  toFun sigma := ⟨sigma, by rw [hA]; exact Subgroup.mem_top sigma⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

omit [IsGalois K L] in
/-- States the theorem `toDecompositionGroupOfEqTop_coe`. -/
@[simp] theorem toDecompositionGroupOfEqTop_coe
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤)
    (sigma : L ≃ₐ[K] L) :
    (toDecompositionGroupOfEqTop K A hA sigma : L ≃ₐ[K] L) = sigma :=
  rfl

/-- The residue action from the exact sequence, viewed on the whole Galois group
when the chosen extension valuation has full decomposition group. -/
noncomputable def residueAlgActionOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (decompositionGroupResidueAction (K := K) A).comp
    (toDecompositionGroupOfEqTop K A hA)

/-- States the theorem `residueAlgActionOfEqTop_surjective`. -/
theorem residueAlgActionOfEqTop_surjective
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    Function.Surjective (residueAlgActionOfEqTop K A hA) := by
  intro tau
  obtain ⟨sigma, hsigma⟩ :=
    decompositionGroupResidueAction_surjective (K := K) A tau
  refine ⟨(sigma : L ≃ₐ[K] L), ?_⟩
  have heq :
      toDecompositionGroupOfEqTop K A hA (sigma : L ≃ₐ[K] L) = sigma := by
    ext
    rfl
  simpa [residueAlgActionOfEqTop, heq] using hsigma

section FiniteImageIndex

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- Finite-subgroup coordinate/index comparison.  If the residue action of a
subgroup is precisely the subgroup fixing a finite residue field `E`, then
the image of the composite degree map has index `[E:k]`. -/
theorem residueDegreeImage_index_eq_finrank_of_map_eq_fixingSubgroup
    {G : Type*} [Group G]
    (rho : G →* (Omega ≃ₐ[k] Omega))
    (H : Subgroup G)
    (E : FiniteGaloisIntermediateField k Omega)
    (himage : H.map rho = E.toIntermediateField.fixingSubgroup) :
    (H.map ((residueAbsoluteDegreeIn k Omega).toMonoidHom.comp rho)).index =
      Module.finrank k E := by
  rw [← Subgroup.map_map, himage]
  have h :=
    Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup k Omega E
  rw [(residueDatumIn k Omega).fieldImage_eq_map] at h
  simpa [residueDatumIn, closedFixingSubgroup] using h

end FiniteImageIndex

end
end LocalClassFieldTheory
