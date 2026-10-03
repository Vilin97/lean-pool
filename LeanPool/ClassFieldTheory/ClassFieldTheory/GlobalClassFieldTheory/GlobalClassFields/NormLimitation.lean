/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianSubextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IntermediateNormAbelianization
/-!
# The norm limitation theorem

For an arbitrary finite extension `L / K`, let `N` be its chosen finite
normal closure, let `E` be the distinguished copy of `L` in `N`, and let
`A` be the largest abelian Galois intermediate field contained in `E`.
This file proves

`N_{L/K} C_L = N_{A/K} C_A`.

The proof applies finite reciprocity over `N / K` to `E` and `A`.  Their
Artin preimages agree because the fixing subgroup of `A` is obtained from
the fixing subgroup of `E` by adjoining the commutator subgroup, which is
killed by abelianization.  The final step transports the norm range from
the distinguished copy `E` back to the original field `L`.
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable
    (K : Type) (L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The fixing subgroup of the maximal abelian subfield and the fixing
subgroup of the original field copy have the same image in the
abelianization of the normal-closure Galois group. -/
theorem
    maximalAbelianSubfield_fixingSubgroup_image_eq_original_image :
    (finiteNormalClosureMaximalAbelianSubfield K L).fixingSubgroup.map
        (Abelianization.of :
          Gal(finiteNormalClosure K L/K) →*
            Abelianization Gal(finiteNormalClosure K L/K)) =
      (finiteNormalClosureOriginalFixingSubgroup K L).map
        (Abelianization.of :
          Gal(finiteNormalClosure K L/K) →*
            Abelianization Gal(finiteNormalClosure K L/K)) := by
  let N := finiteNormalClosure K L
  let G := Gal(N/K)
  let H : Subgroup G := finiteNormalClosureOriginalFixingSubgroup K L
  change
    (IntermediateField.fixedField
        (H ⊔ _root_.commutator G)).fixingSubgroup.map
        (Abelianization.of : G →* Abelianization G) =
      H.map (Abelianization.of : G →* Abelianization G)
  rw [IntermediateField.fixingSubgroup_fixedField]
  apply le_antisymm
  · rintro z ⟨sigma, hsigma, rfl⟩
    change sigma ∈
      (H.map (Abelianization.of : G →* Abelianization G)).comap
        (Abelianization.of : G →* Abelianization G)
    rw [H.comap_map_abelianization_eq_sup_commutator]
    exact hsigma
  · exact Subgroup.map_mono le_sup_left

/-- The distinguished original field copy and its maximal abelian
subfield have the same idèle-class norm subgroup. -/
theorem
    finiteNormalClosureOriginalField_ideleClassNorm_range_eq_maximalAbelianSubfield :
    (_root_.ideleClassNorm K
        (finiteNormalClosureOriginalField K L)).range =
      (_root_.ideleClassNorm K
        (finiteNormalClosureMaximalAbelianSubfield K L)).range := by
  calc
    (_root_.ideleClassNorm K
        (finiteNormalClosureOriginalField K L)).range =
      ((finiteNormalClosureOriginalField K L).fixingSubgroup.map
          (Abelianization.of :
            Gal(finiteNormalClosure K L/K) →*
              Abelianization Gal(finiteNormalClosure K L/K))).comap
        (Reciprocity.globalNormResidueAbelianizationMonoidHom K
          (finiteNormalClosure K L)) :=
      Reciprocity.ideleClassNorm_range_eq_artin_preimage_abelianizedFixingSubgroup
        (K := K) (N := finiteNormalClosure K L)
        (finiteNormalClosureOriginalField K L)
    _ =
      ((finiteNormalClosureMaximalAbelianSubfield K L).fixingSubgroup.map
          (Abelianization.of :
            Gal(finiteNormalClosure K L/K) →*
              Abelianization Gal(finiteNormalClosure K L/K))).comap
        (Reciprocity.globalNormResidueAbelianizationMonoidHom K
          (finiteNormalClosure K L)) := by
      change
        ((finiteNormalClosureOriginalFixingSubgroup K L).map
            (Abelianization.of :
              Gal(finiteNormalClosure K L/K) →*
                Abelianization Gal(finiteNormalClosure K L/K))).comap
          (Reciprocity.globalNormResidueAbelianizationMonoidHom K
            (finiteNormalClosure K L)) = _
      rw [
        maximalAbelianSubfield_fixingSubgroup_image_eq_original_image]
    _ =
      (_root_.ideleClassNorm K
        (finiteNormalClosureMaximalAbelianSubfield K L)).range :=
      (Reciprocity.ideleClassNorm_range_eq_artin_preimage_abelianizedFixingSubgroup
        (K := K) (N := finiteNormalClosure K L)
        (finiteNormalClosureMaximalAbelianSubfield K L)).symm

/-- Norm limitation: an arbitrary finite extension and its maximal abelian
Galois subextension inside the chosen normal closure have the same actual
idèle-class norm subgroup in the base field. -/
theorem ideleClassNorm_range_eq_maximalAbelianSubfield :
    (_root_.ideleClassNorm K L).range =
      (_root_.ideleClassNorm K
        (finiteNormalClosureMaximalAbelianSubfield K L)).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        (_root_.ideleClassNorm K
          (finiteNormalClosureOriginalField K L)).range := by
      simpa only [ordinaryIdeleClassNorm_range_eq_relative] using
        (ideleClassNorm_range_algEquiv
          (K := K) (finiteNormalClosureOriginalFieldEquiv K L)).symm
    _ =
        (_root_.ideleClassNorm K
          (finiteNormalClosureMaximalAbelianSubfield K L)).range :=
      finiteNormalClosureOriginalField_ideleClassNorm_range_eq_maximalAbelianSubfield
        K L

/-- Membership form of the norm limitation theorem. -/
theorem normLimitation (c : IdeleClassGroup K) :
    c ∈ (_root_.ideleClassNorm K L).range ↔
      c ∈ (_root_.ideleClassNorm K
        (finiteNormalClosureMaximalAbelianSubfield K L)).range := by
  rw [ideleClassNorm_range_eq_maximalAbelianSubfield K L]

omit [FiniteDimensional K L] in
/-- If the original extension is already abelian Galois, its distinguished
copy is the maximal abelian subfield selected by norm limitation. -/
theorem
    finiteNormalClosureMaximalAbelianSubfield_eq_originalField_of_isAbelianGalois
    [IsAbelianGalois K L] :
    finiteNormalClosureMaximalAbelianSubfield K L =
      finiteNormalClosureOriginalField K L := by
  let : IsAbelianGalois K (finiteNormalClosureOriginalField K L) :=
    IsAbelianGalois.of_algHom
      (finiteNormalClosureOriginalFieldEquiv K L).symm.toAlgHom
  apply le_antisymm
  · exact finiteNormalClosureMaximalAbelianSubfield_le_originalField K L
  · exact
      finiteNormalClosureMaximalAbelianSubfield_greatest K L
        (finiteNormalClosureOriginalField K L) le_rfl

end GlobalClassFields
end GlobalClassFieldTheory
