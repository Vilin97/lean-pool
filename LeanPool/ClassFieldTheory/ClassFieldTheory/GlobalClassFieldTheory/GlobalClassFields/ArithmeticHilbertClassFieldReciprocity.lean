/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.Transport
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigActual
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallActual
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.BigOriginal
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldReciprocity.SmallOriginal
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
/-!
# Arithmetic reciprocity for the actual Hilbert class fields

The canonical ideal-theoretic Artin map uses arithmetic Frobenius.
Accordingly, these equivalences use arithmetic global reciprocity
before identifying the intrinsic Hilbert norm quotient with the narrow
or ordinary ideal class group.  The class groups in the current API
carry no native topological structure, so the mathematically correct
public bundle here is `MulEquiv`; the preceding Galois/norm-quotient
factor remains a `ContinuousMulEquiv`.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- Fix the commutative idèle-class instance path shared by the norm quotient
and its transported literal quotient throughout this module. -/
local instance
    arithmeticHilbertClassFieldIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- Arithmetic reciprocity followed by transport between equal norm
quotients sends a norm-residue symbol to its represented quotient class. -/
private theorem
    arithmeticReciprocity_quotientTransport_globalNormResidue
    {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (c : IdeleClassGroup F) :
    QuotientGroup.quotientMulEquivOfEq h
        (arithmeticGlobalReciprocityContinuousMulEquiv F E
          (arithmeticGlobalNormResidueMonoidHom F E c)) =
      QuotientGroup.mk' H c := by
  let e := arithmeticGlobalReciprocityContinuousMulEquiv F E
  let q :=
    QuotientGroup.mk'
      (_root_.ideleClassNorm F E).range c
  have hsymm :
      e.symm q = arithmeticGlobalNormResidueMonoidHom F E c :=
    arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk F E c
  have he :
      e (arithmeticGlobalNormResidueMonoidHom F E c) = q := by
    calc
      e (arithmeticGlobalNormResidueMonoidHom F E c) =
          e (e.symm q) :=
        congrArg (fun σ => e σ) hsymm.symm
      _ = q := e.apply_symm_apply q
  calc
    QuotientGroup.quotientMulEquivOfEq h
        (arithmeticGlobalReciprocityContinuousMulEquiv F E
          (arithmeticGlobalNormResidueMonoidHom F E c)) =
        QuotientGroup.quotientMulEquivOfEq h q :=
      congrArg
        (fun x => QuotientGroup.quotientMulEquivOfEq h x) he
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk h c

/-- Postcomposing transported arithmetic reciprocity with any quotient
equivalence preserves the represented quotient class formula. -/
private theorem
    arithmeticReciprocity_quotientTransport_trans_globalNormResidue
    {F E A : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [Group A]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (f : (IdeleClassGroup F ⧸ H) ≃* A)
    (c : IdeleClassGroup F) :
    ((arithmeticGlobalReciprocityContinuousMulEquiv F E).toMulEquiv.trans
        ((QuotientGroup.quotientMulEquivOfEq h).trans f))
        (arithmeticGlobalNormResidueMonoidHom F E c) =
      f (QuotientGroup.mk' H c) := by
  calc
    ((arithmeticGlobalReciprocityContinuousMulEquiv F E).toMulEquiv.trans
        ((QuotientGroup.quotientMulEquivOfEq h).trans f))
        (arithmeticGlobalNormResidueMonoidHom F E c) =
      f
        (QuotientGroup.quotientMulEquivOfEq h
          (arithmeticGlobalReciprocityContinuousMulEquiv F E
            (arithmeticGlobalNormResidueMonoidHom F E c))) := rfl
    _ = f (QuotientGroup.mk' H c) :=
      congrArg f
        (arithmeticReciprocity_quotientTransport_globalNormResidue
          H h c)

private noncomputable def arithmeticBigHilbertClassFieldReciprocityData
    (K : Type) [Field K] [NumberField K] :
    { e : Gal((bigHilbertClassField K) / K) ≃*
        RayClass.NarrowClassGroup K //
      ∀ c : IdeleClassGroup K,
        e (arithmeticGlobalNormResidueMonoidHom
            K (bigHilbertClassField K) c) =
          bigHilbertClassFieldQuotientEquivNarrowClassGroup
            (K := K)
            (QuotientGroup.mk'
              (bigHilbertClassFieldNormSubgroup (K := K)) c) } :=
  ⟨(arithmeticGlobalReciprocityContinuousMulEquiv
      K (bigHilbertClassField K)).toMulEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (bigHilbertClassField_ideleClassNorm_range_over_original
          (K := K))).trans
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K))),
    arithmeticReciprocity_quotientTransport_trans_globalNormResidue
      (bigHilbertClassFieldNormSubgroup (K := K))
      (bigHilbertClassField_ideleClassNorm_range_over_original
        (K := K))
      (bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K))⟩

private noncomputable def arithmeticSmallHilbertClassFieldReciprocityData
    (K : Type) [Field K] [NumberField K] :
    { e : Gal((smallHilbertClassField K) / K) ≃*
        ClassGroup (𝓞 K) //
      ∀ c : IdeleClassGroup K,
        e (arithmeticGlobalNormResidueMonoidHom
            K (smallHilbertClassField K) c) =
          smallHilbertClassFieldQuotientEquivClassGroup
            (K := K)
            (QuotientGroup.mk'
              (smallHilbertClassFieldNormSubgroup (K := K)) c) } :=
  ⟨(arithmeticGlobalReciprocityContinuousMulEquiv
      K (smallHilbertClassField K)).toMulEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (smallHilbertClassField_ideleClassNorm_range_over_original
          (K := K))).trans
        (smallHilbertClassFieldQuotientEquivClassGroup
          (K := K))),
    arithmeticReciprocity_quotientTransport_trans_globalNormResidue
      (smallHilbertClassFieldNormSubgroup (K := K))
      (smallHilbertClassField_ideleClassNorm_range_over_original
        (K := K))
      (smallHilbertClassFieldQuotientEquivClassGroup
        (K := K))⟩

/-- Arithmetic global reciprocity for the selected big Hilbert class
field over the original number field. -/
noncomputable def
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal :
    Gal((bigHilbertClassField K) / K) ≃*
      RayClass.NarrowClassGroup K :=
  (arithmeticBigHilbertClassFieldReciprocityData K).1

/-- The arithmetic global norm-residue symbol maps to its genuine
narrow ideal class. -/
@[simp]
theorem
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal_globalNormResidue
    (c : IdeleClassGroup K) :
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal
        (K := K)
        (arithmeticGlobalNormResidueMonoidHom
          K (bigHilbertClassField K) c) =
      bigHilbertClassFieldQuotientEquivNarrowClassGroup
        (K := K)
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) c) := by
  exact (arithmeticBigHilbertClassFieldReciprocityData K).2 c

/-- On an actual idèle, arithmetic big-Hilbert reciprocity is its
narrow ideal class. -/
@[simp]
theorem
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal_idele
    (a : IdeleGroup K) :
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal
        (K := K)
        (arithmeticGlobalNormResidueMonoidHom
          K (bigHilbertClassField K)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      QuotientGroup.mk'
        (RayClass.narrowDenominator (K := K)) a := by
  rw [
    arithmeticBigHilbertClassFieldGaloisEquivNarrowClassGroupOverOriginal_globalNormResidue,
    bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk]

/-- Arithmetic global reciprocity for the selected small Hilbert class
field over the original number field. -/
noncomputable def
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal :
    Gal((smallHilbertClassField K) / K) ≃*
      ClassGroup (𝓞 K) :=
  (arithmeticSmallHilbertClassFieldReciprocityData K).1

/-- The arithmetic global norm-residue symbol maps to its genuine
ordinary ideal class. -/
@[simp]
theorem
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal_globalNormResidue
    (c : IdeleClassGroup K) :
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal
        (K := K)
        (arithmeticGlobalNormResidueMonoidHom
          K (smallHilbertClassField K) c) =
      smallHilbertClassFieldQuotientEquivClassGroup
        (K := K)
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) c) := by
  exact (arithmeticSmallHilbertClassFieldReciprocityData K).2 c

/-- On an actual idèle, arithmetic small-Hilbert reciprocity is its
ordinary ideal class. -/
@[simp]
theorem
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal_idele
    (a : IdeleGroup K) :
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal
        (K := K)
        (arithmeticGlobalNormResidueMonoidHom
          K (smallHilbertClassField K)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      IdeleGroup.idealClass a := by
  rw [
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal_globalNormResidue,
    smallHilbertClassFieldQuotientEquivClassGroup_mk]

end GlobalClassFields
end GlobalClassFieldTheory
