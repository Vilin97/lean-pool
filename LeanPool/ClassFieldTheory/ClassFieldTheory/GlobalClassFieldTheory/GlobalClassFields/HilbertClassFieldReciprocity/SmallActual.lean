/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.Transport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldNaturality
/-!
# Small Hilbert reciprocity over the realized base field

This leaf specializes the shared reciprocity transport to the actual base
field of the selected small Hilbert class field.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
local instance
    smallHilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

attribute [local instance] smallHilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

open scoped Classical in
/-- The actual norm range of the selected small Hilbert class field is
the intrinsic small-Hilbert norm subgroup of its actual base field. -/
theorem smallHilbertClassField_ideleClassNorm_range_eq_intrinsic :
    (_root_.ideleClassNorm
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K)).range =
      smallHilbertClassFieldNormSubgroup
        (K := smallHilbertClassFieldBase K) := by
  rw [smallHilbertClassField_ideleClassNorm_range]
  exact
    smallHilbertClassFieldNormSubgroup_map_ideleClassCongr
      (smallHilbertClassFieldBaseEquiv (K := K))

open scoped Classical in
/-- Global reciprocity identifies the genuine Galois group of the
selected small Hilbert class field with the ordinary ideal class group
of the original number field. -/
private noncomputable def smallHilbertClassFieldReciprocityData :
    {e : Gal((smallHilbertClassField K)/(smallHilbertClassFieldBase K)) ≃*
        ClassGroup (𝓞 K) //
      ∀ c : IdeleClassGroup (smallHilbertClassFieldBase K),
        e (globalNormResidueMonoidHom
            (smallHilbertClassFieldBase K)
            (smallHilbertClassField K) c) =
          smallHilbertClassGroupCongr
            (smallHilbertClassFieldBaseEquiv (K := K)).symm
            (smallHilbertClassFieldQuotientEquivClassGroup
              (K := smallHilbertClassFieldBase K)
              (QuotientGroup.mk'
                (smallHilbertClassFieldNormSubgroup
                  (K := smallHilbertClassFieldBase K)) c))} := by
  let d := hilbertClassFieldGlobalReciprocityTransportData
    (smallHilbertClassFieldNormSubgroup
      (K := smallHilbertClassFieldBase K))
    (smallHilbertClassField_ideleClassNorm_range_eq_intrinsic
      (K := K))
    ((smallHilbertClassFieldQuotientEquivClassGroup
        (K := smallHilbertClassFieldBase K)).trans
      (smallHilbertClassGroupCongr
        (smallHilbertClassFieldBaseEquiv (K := K)).symm))
  refine ⟨d.1, ?_⟩
  intro c
  exact d.2 c

open scoped Classical in
/-- The reciprocity equivalence from the actual small Hilbert Galois group
to the ordinary ideal class group of the original number field. -/
noncomputable def smallHilbertClassFieldGaloisEquivClassGroup :
    Gal((smallHilbertClassField K)/(smallHilbertClassFieldBase K)) ≃*
      ClassGroup (𝓞 K) :=
  (smallHilbertClassFieldReciprocityData (K := K)).1

open scoped Classical in
/-- Under the small-Hilbert reciprocity equivalence, the actual global
norm-residue symbol of an idèle class is its ordinary ideal class,
transported back from the concrete base fixed field to the original
number field. -/
theorem smallHilbertClassFieldGaloisEquivClassGroup_globalNormResidue
    (c : IdeleClassGroup (smallHilbertClassFieldBase K)) :
    smallHilbertClassFieldGaloisEquivClassGroup (K := K)
        (globalNormResidueMonoidHom
          (smallHilbertClassFieldBase K)
          (smallHilbertClassField K) c) =
      smallHilbertClassGroupCongr
        (smallHilbertClassFieldBaseEquiv (K := K)).symm
        (smallHilbertClassFieldQuotientEquivClassGroup
          (K := smallHilbertClassFieldBase K)
          (QuotientGroup.mk'
            (smallHilbertClassFieldNormSubgroup
              (K := smallHilbertClassFieldBase K)) c)) := by
  exact (smallHilbertClassFieldReciprocityData (K := K)).2 c

open scoped Classical in
/-- Representative form of small-Hilbert reciprocity: the global
norm-residue symbol of an actual idèle maps to its ordinary ideal
class, with only the canonical base-field transport remaining. -/
theorem smallHilbertClassFieldGaloisEquivClassGroup_idele
    (a : IdeleGroup (smallHilbertClassFieldBase K)) :
    smallHilbertClassFieldGaloisEquivClassGroup (K := K)
        (globalNormResidueMonoidHom
          (smallHilbertClassFieldBase K)
          (smallHilbertClassField K)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup
              (smallHilbertClassFieldBase K)) a)) =
      smallHilbertClassGroupCongr
        (smallHilbertClassFieldBaseEquiv (K := K)).symm
        (IdeleGroup.idealClass a) := by
  calc
    _ = smallHilbertClassGroupCongr
          (smallHilbertClassFieldBaseEquiv (K := K)).symm
          (smallHilbertClassFieldQuotientEquivClassGroup
            (K := smallHilbertClassFieldBase K)
            (QuotientGroup.mk'
              (smallHilbertClassFieldNormSubgroup
                (K := smallHilbertClassFieldBase K))
              (QuotientGroup.mk'
                (IdeleGroup.principalSubgroup
                  (smallHilbertClassFieldBase K)) a))) :=
      (smallHilbertClassFieldReciprocityData (K := K)).2 _
    _ = _ :=
      congrArg
        (smallHilbertClassGroupCongr
          (smallHilbertClassFieldBaseEquiv (K := K)).symm)
        (smallHilbertClassFieldQuotientEquivClassGroup_mk
          (K := smallHilbertClassFieldBase K) a)

end GlobalClassFields
end GlobalClassFieldTheory
