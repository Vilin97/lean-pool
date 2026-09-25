/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigActual
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassFieldOverOriginalBase
/-!
# Big Hilbert reciprocity over the original number field

The original-base specialization is compiled separately from the realized-base
specialization and reuses the shared reciprocity transport provider.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
local instance
    bigHilbertClassFieldReciprocityOverOriginalIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

attribute [local instance] bigHilbertClassFieldReciprocityOverOriginalIsMulCommutative

open scoped Classical in
/-- Over the original number field scalar structure, the actual norm
range of the selected big Hilbert class field is exactly the intrinsic
big-Hilbert norm subgroup. -/
theorem bigHilbertClassField_ideleClassNorm_range_over_original :
    (_root_.ideleClassNorm K (bigHilbertClassField K)).range =
      bigHilbertClassFieldNormSubgroup (K := K) := by
  let e :=
    bigHilbertClassFieldBaseEquiv (K := K)
  let g :=
    (ideleClassCongr e).toMonoidHom
  apply
    Subgroup.map_injective
      (f := g)
      (ideleClassCongr e).injective
  calc
    ((_root_.ideleClassNorm K
          (bigHilbertClassField K)).range).map g =
        (_root_.ideleClassNorm
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K)).range := by
      exact
        ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv
          e
          (AlgEquiv.refl
            (R := ℚ) (A₁ := bigHilbertClassField K))
          (fun x => by
            exact bigHilbertClassField_algebraMap_original K x)
    _ =
        bigHilbertClassFieldNormSubgroup
          (K := bigHilbertClassFieldBase K) :=
      bigHilbertClassField_ideleClassNorm_range_eq_intrinsic
        (K := K)
    _ =
        (bigHilbertClassFieldNormSubgroup (K := K)).map g :=
      (bigHilbertClassFieldNormSubgroup_map_ideleClassCongr e).symm

open scoped Classical in
/-- Global reciprocity for the selected big Hilbert class field over
the original number field gives the narrow ideal class group directly,
without a residual fixed-field transport. -/
private noncomputable def
    bigHilbertClassFieldReciprocityOverOriginalData :
    {e : Gal((bigHilbertClassField K)/K) ≃*
        RayClass.NarrowClassGroup K //
      ∀ c : IdeleClassGroup K,
        e (globalNormResidueMonoidHom K
            (bigHilbertClassField K) c) =
          bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := K)
            (QuotientGroup.mk'
              (bigHilbertClassFieldNormSubgroup (K := K)) c)} := by
  let d := hilbertClassFieldGlobalReciprocityTransportData
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassField_ideleClassNorm_range_over_original
      (K := K))
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K))
  refine ⟨d.1, ?_⟩
  intro c
  exact d.2 c

open scoped Classical in
/-- The direct reciprocity equivalence for the big Hilbert class field,
using the original number field as the scalar base. -/
noncomputable def
    bigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal :
    Gal((bigHilbertClassField K)/K) ≃*
      RayClass.NarrowClassGroup K :=
  (bigHilbertClassFieldReciprocityOverOriginalData (K := K)).1

open scoped Classical in
/-- The direct big-Hilbert reciprocity equivalence sends the genuine
global norm-residue symbol to its narrow ideal class. -/
theorem
    bigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal_globalNormResidue
    (c : IdeleClassGroup K) :
    bigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal
        (K := K)
        (globalNormResidueMonoidHom K
          (bigHilbertClassField K) c) =
      bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) c) := by
  exact
    (bigHilbertClassFieldReciprocityOverOriginalData (K := K)).2 c

open scoped Classical in
/-- On an actual idèle, direct big-Hilbert reciprocity is its narrow
ideal class. -/
theorem bigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal_idele
    (a : IdeleGroup K) :
    bigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal
        (K := K)
        (globalNormResidueMonoidHom K
          (bigHilbertClassField K)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K)) a := by
  exact
    ((bigHilbertClassFieldReciprocityOverOriginalData (K := K)).2
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a)).trans
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk
        (K := K) a)

end GlobalClassFields
end GlobalClassFieldTheory
