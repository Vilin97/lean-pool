/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
/-!
# Naturality of the small Hilbert class field

An equivalence of number fields carries the small-Hilbert norm subgroup
exactly onto the small-Hilbert norm subgroup.  Consequently it induces the
canonical equivalence of the corresponding reciprocity quotients.  Transport
of ordinary ideal classes is obtained from this quotient equivalence and is
therefore compatible with the canonical quotient--class-group equivalences.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- Supply the canonical commutativity used by both small-Hilbert quotients. -/
private theorem smallHilbertNaturalityIdeleClassIsMulCommutative
    {F : Type*} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] smallHilbertNaturalityIdeleClassIsMulCommutative

variable
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M]

/-- Transport of ordinary idele classes along an equivalence of number
fields carries the small-Hilbert norm subgroup exactly onto the
small-Hilbert norm subgroup of the target. -/
theorem smallHilbertClassFieldNormSubgroup_map_ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    (smallHilbertClassFieldNormSubgroup (K := K)).map
        (ideleClassCongr e).toMonoidHom =
      smallHilbertClassFieldNormSubgroup (K := M) := by
  simpa only [smallHilbertClassFieldNormSubgroup,
    IdeleGroup.ordinaryIdealClassSubgroup] using
    ordinaryIdealClassSubgroup_image_map_ideleClassCongr e

/-- The canonical equivalence of small-Hilbert reciprocity quotients induced
by an equivalence of number fields. -/
noncomputable def smallHilbertClassFieldQuotientCongr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) ≃*
      (IdeleClassGroup M ⧸
        smallHilbertClassFieldNormSubgroup (K := M)) :=
  QuotientGroup.congr
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup (K := M))
    (ideleClassCongr e)
    (smallHilbertClassFieldNormSubgroup_map_ideleClassCongr e)

/-- On representatives, the small-Hilbert quotient transport is induced by
the existing transport of ordinary idele classes. -/
@[simp]
theorem smallHilbertClassFieldQuotientCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (c : IdeleClassGroup K) :
    smallHilbertClassFieldQuotientCongr e
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (smallHilbertClassFieldNormSubgroup (K := M))
        (ideleClassCongr e c) :=
  rfl

/-- The canonical transport of ordinary ideal classes determined by the
small-Hilbert reciprocity quotient. -/
noncomputable def smallHilbertClassGroupCongr
    (e : K ≃ₐ[ℚ] M) :
    ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 M) :=
  (smallHilbertClassFieldQuotientEquivClassGroup
      (K := K)).symm |>.trans
    ((smallHilbertClassFieldQuotientCongr e).trans
      (smallHilbertClassFieldQuotientEquivClassGroup
        (K := M)))

/-- Naturality of the canonical identification of the small-Hilbert
reciprocity quotient with the ordinary ideal class group. -/
@[simp]
theorem smallHilbertClassFieldQuotientEquivClassGroup_naturality
    (e : K ≃ₐ[ℚ] M)
    (q : IdeleClassGroup K ⧸
      smallHilbertClassFieldNormSubgroup (K := K)) :
    smallHilbertClassFieldQuotientEquivClassGroup
        (K := M)
        (smallHilbertClassFieldQuotientCongr e q) =
      smallHilbertClassGroupCongr e
        (smallHilbertClassFieldQuotientEquivClassGroup
          (K := K) q) := by
  simp [smallHilbertClassGroupCongr]

/-- Homomorphism form of naturality for the small-Hilbert
quotient--class-group identification. -/
theorem smallHilbertClassFieldQuotientEquivClassGroup_naturality_hom
    (e : K ≃ₐ[ℚ] M) :
    (smallHilbertClassFieldQuotientEquivClassGroup
        (K := M)).toMonoidHom.comp
        (smallHilbertClassFieldQuotientCongr
          (K := K) (M := M) e).toMonoidHom =
      (smallHilbertClassGroupCongr
        (K := K) (M := M) e).toMonoidHom.comp
        (smallHilbertClassFieldQuotientEquivClassGroup
          (K := K)).toMonoidHom := by
  ext q
  exact
    smallHilbertClassFieldQuotientEquivClassGroup_naturality
      (K := K) (M := M) e q

/-- On an idele representative, the induced transport of ordinary ideal
classes is the ideal class of the transported idele.  Thus the class-group
transport above is characterized by the actual idelic transport, rather than
by a choice of representatives in the quotient. -/
@[simp]
theorem smallHilbertClassGroupCongr_idealClass
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    smallHilbertClassGroupCongr e
        (IdeleGroup.idealClass a) =
      IdeleGroup.idealClass (ideleCongr e a) := by
  let q :
      IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K) :=
    QuotientGroup.mk'
      (smallHilbertClassFieldNormSubgroup (K := K))
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a)
  calc
    smallHilbertClassGroupCongr e
          (IdeleGroup.idealClass a) =
        smallHilbertClassGroupCongr e
          (smallHilbertClassFieldQuotientEquivClassGroup
            (K := K) q) := by
              simp only [q,
                smallHilbertClassFieldQuotientEquivClassGroup_mk]
    _ =
        smallHilbertClassFieldQuotientEquivClassGroup
          (K := M)
          (smallHilbertClassFieldQuotientCongr e q) :=
      (smallHilbertClassFieldQuotientEquivClassGroup_naturality
        e q).symm
    _ = IdeleGroup.idealClass (ideleCongr e a) := by
      simp only [q, smallHilbertClassFieldQuotientCongr_mk,
        ideleClassCongr_mk,
        smallHilbertClassFieldQuotientEquivClassGroup_mk]

/-- Homomorphism form of naturality for ordinary ideal classes under the
small-Hilbert class-group transport. -/
theorem smallHilbertClassGroupCongr_naturality
    (e : K ≃ₐ[ℚ] M) :
    (smallHilbertClassGroupCongr e).toMonoidHom.comp
        (IdeleGroup.idealClass (K := K)) =
      (IdeleGroup.idealClass (K := M)).comp
        (ideleCongr e).toMonoidHom := by
  ext a
  exact smallHilbertClassGroupCongr_idealClass e a

end GlobalClassFields
end GlobalClassFieldTheory
