/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallActual
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldOverOriginalBase
/-!
# Small Hilbert reciprocity over the original number field

The original-base specialization is compiled separately from the realized-base
specialization and reuses the shared reciprocity transport provider.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

local instance
    smallHilbertClassFieldReciprocityOverOriginalIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

/-- Over the original number field scalar structure, the actual norm
range of the selected small Hilbert class field is exactly the
intrinsic small-Hilbert norm subgroup. -/
theorem smallHilbertClassField_ideleClassNorm_range_over_original :
    (_root_.ideleClassNorm K (smallHilbertClassField K)).range =
      smallHilbertClassFieldNormSubgroup (K := K) := by
  let e :=
    smallHilbertClassFieldBaseEquiv (K := K)
  let g :=
    (ideleClassCongr e).toMonoidHom
  apply
    Subgroup.map_injective
      (f := g)
      (ideleClassCongr e).injective
  calc
    ((_root_.ideleClassNorm K
          (smallHilbertClassField K)).range).map g =
        (_root_.ideleClassNorm
          (smallHilbertClassFieldBase K)
          (smallHilbertClassField K)).range := by
      exact
        ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
          e
          (AlgEquiv.refl
            (R := ℚ) (A₁ := smallHilbertClassField K))
          (fun x => by
            exact smallHilbertClassField_algebraMap_original K x)
    _ =
        smallHilbertClassFieldNormSubgroup
          (K := smallHilbertClassFieldBase K) :=
      smallHilbertClassField_ideleClassNorm_range_eq_intrinsic
        (K := K)
    _ =
        (smallHilbertClassFieldNormSubgroup (K := K)).map g :=
      (smallHilbertClassFieldNormSubgroup_map_ideleClassCongr e).symm

/-- Global reciprocity for the selected small Hilbert class field over
the original number field gives the ordinary ideal class group
directly. -/
private noncomputable def
    smallHilbertClassFieldReciprocityOverOriginalData :
    {e : Gal((smallHilbertClassField K) / K) ≃*
        ClassGroup (𝓞 K) //
      ∀ c : IdeleClassGroup K,
        e (globalNormResidueMonoidHom K
            (smallHilbertClassField K) c) =
          smallHilbertClassFieldQuotientEquivClassGroup
            (K := K)
            (QuotientGroup.mk'
              (smallHilbertClassFieldNormSubgroup (K := K)) c)} := by
  let d := hilbertClassFieldGlobalReciprocityTransportData
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassField_ideleClassNorm_range_over_original
      (K := K))
    (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K))
  refine ⟨d.1, ?_⟩
  intro c
  exact d.2 c

/-- The direct reciprocity equivalence for the small Hilbert class field,
using the original number field as the scalar base. -/
noncomputable def smallHilbertClassFieldGaloisEquivClassGroupOverOriginal :
    Gal((smallHilbertClassField K) / K) ≃*
      ClassGroup (𝓞 K) :=
  (smallHilbertClassFieldReciprocityOverOriginalData (K := K)).1

/-- The direct small-Hilbert reciprocity equivalence sends the genuine
global norm-residue symbol to its ordinary ideal class. -/
@[simp]
theorem
    smallHilbertClassFieldGaloisEquivClassGroupOverOriginal_globalNormResidue
    (c : IdeleClassGroup K) :
    smallHilbertClassFieldGaloisEquivClassGroupOverOriginal
        (K := K)
        (globalNormResidueMonoidHom K
          (smallHilbertClassField K) c) =
      smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) c) := by
  exact
    (smallHilbertClassFieldReciprocityOverOriginalData (K := K)).2 c

/-- On an actual idèle, direct small-Hilbert reciprocity is its
ordinary ideal class. -/
@[simp]
theorem smallHilbertClassFieldGaloisEquivClassGroupOverOriginal_idele
    (a : IdeleGroup K) :
    smallHilbertClassFieldGaloisEquivClassGroupOverOriginal
        (K := K)
        (globalNormResidueMonoidHom K
          (smallHilbertClassField K)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      IdeleGroup.idealClass a := by
  exact
    ((smallHilbertClassFieldReciprocityOverOriginalData (K := K)).2
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a)).trans
      (smallHilbertClassFieldQuotientEquivClassGroup_mk
        (K := K) a)

end GlobalClassFields
end GlobalClassFieldTheory
