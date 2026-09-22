/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.Factorization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicRayNorm
/-!
# The rational ray class field as an actual cyclotomic field

For a nonzero natural number `m`, the selected ray class field for the
rational modulus `(m)` is isomorphic over `ℚ` to the actual cyclotomic
field `CyclotomicField m ℚ`.

The field comparison is obtained from the exact idèle-class norm-range
equality.  We also retain the topological content of global reciprocity:

`Gal(ℚ(μ_m) / ℚ) ≃ₜ* C_ℚ / C_ℚ^m`.

Thus the result is an equality of actual class fields and not merely an
equality of degrees or an abstract comparison of finite groups.
-/

open scoped IsMulCommutative NumberField Cyclotomic

noncomputable section

namespace KroneckerWeber

open GlobalClassFieldTheory
open GlobalClassFieldTheory.GlobalClassFields
open GlobalClassFieldTheory.Reciprocity
open NumberField IsDedekindDomain

open scoped Classical in
noncomputable local instance rationalCyclotomicLevelIsAbelianGalois
    (n : ℕ+) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel n) :=
  IsCyclotomicExtension.isAbelianGalois {(n : ℕ)} ℚ
    (KummerTheory.rationalCyclotomicLevel n)

attribute [local instance] rationalCyclotomicLevelIsAbelianGalois

open scoped Classical in
private noncomputable def
    galoisContinuousMulEquivRayClassGroupOfNormRangeEq
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]
    (r : RayClass.Modulus ℚ)
    (h : (_root_.ideleClassNorm ℚ L).range =
      RayClass.Modulus.congruenceSubgroup r) :
    Gal(L / ℚ) ≃ₜ* RayClass.RayClassGroup r := by
  letI : (_root_.ideleClassNorm ℚ L).range.Normal :=
    h ▸ inferInstance
  letI : DiscreteTopology (RayClass.RayClassGroup r) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup r)
  let reciprocity :
      Gal(L / ℚ) ≃*
        (IdeleClassGroup ℚ ⧸
          (_root_.ideleClassNorm ℚ L).range) :=
    AddEquiv.toMultiplicative (globalReciprocityEquiv ℚ L)
  exact
    { reciprocity.trans
        (QuotientGroup.quotientMulEquivOfEq h) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

open scoped Classical in
private theorem quotientMulEquivOfNormRangeEq_globalNormResidue
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]
    (H : Subgroup (IdeleClassGroup ℚ))
    [(_root_.ideleClassNorm ℚ L).range.Normal] [H.Normal]
    (h : (_root_.ideleClassNorm ℚ L).range = H)
    (c : IdeleClassGroup ℚ) :
    QuotientGroup.quotientMulEquivOfEq h
        (Additive.toMul
          ((globalNormResidueEquiv ℚ L).symm
            (Additive.ofMul
              (globalNormResidueMonoidHom ℚ L c)))) =
      QuotientGroup.mk' H c := by
  have hNormResidue :
      Additive.ofMul (globalNormResidueMonoidHom ℚ L c) =
        globalNormResidueEquiv ℚ L
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm ℚ L).range c)) :=
    congrArg (fun σ => Additive.ofMul σ)
      (globalNormResidueMonoidHom_apply ℚ L c)
  calc
    _ = QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul
            ((globalNormResidueEquiv ℚ L).symm
              (globalNormResidueEquiv ℚ L
                (Additive.ofMul
                  (QuotientGroup.mk'
                    (_root_.ideleClassNorm ℚ L).range c))))) :=
      congrArg
        (fun τ =>
          QuotientGroup.quotientMulEquivOfEq h
            (Additive.toMul
              ((globalNormResidueEquiv ℚ L).symm τ)))
        hNormResidue
    _ = QuotientGroup.mk' H c := by
      rw [AddEquiv.symm_apply_apply]
      exact QuotientGroup.quotientMulEquivOfEq_mk h c

open scoped Classical in
private theorem
    galoisContinuousMulEquivRayClassGroupOfNormRangeEq_globalNormResidue
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]
    (r : RayClass.Modulus ℚ)
    (h : (_root_.ideleClassNorm ℚ L).range =
      RayClass.Modulus.congruenceSubgroup r)
    (c : IdeleClassGroup ℚ) :
    galoisContinuousMulEquivRayClassGroupOfNormRangeEq L r h
        (globalNormResidueMonoidHom ℚ L c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup r) c := by
  let : (_root_.ideleClassNorm ℚ L).range.Normal :=
    h ▸ inferInstance
  change
    QuotientGroup.quotientMulEquivOfEq h
        (Additive.toMul
          ((globalNormResidueEquiv ℚ L).symm
            (Additive.ofMul
              (globalNormResidueMonoidHom ℚ L c)))) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup r) c
  exact
    quotientMulEquivOfNormRangeEq_globalNormResidue
      L (RayClass.Modulus.congruenceSubgroup r) h c

open scoped Classical in
/-- Conjugating an automorphism between two actual singleton
cyclotomic extensions preserves its exponent on primitive roots. -/
theorem galEquivZMod_autCongr
    (m : ℕ) [NeZero m]
    (A B : Type*) [Field A] [NumberField A]
    [Field B] [NumberField B]
    [IsCyclotomicExtension {m} ℚ A]
    [IsCyclotomicExtension {m} ℚ B]
    (e : A ≃ₐ[ℚ] B)
    (σ : Gal(A/ℚ)) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m B (AlgEquiv.autCongr e σ) =
      IsCyclotomicExtension.Rat.galEquivZMod
        m A σ := by
  let ζ : A :=
    IsCyclotomicExtension.zeta m ℚ A
  have hζ : IsPrimitiveRoot ζ m :=
    IsCyclotomicExtension.zeta_spec m ℚ A
  have hζB : IsPrimitiveRoot (e ζ) m :=
    hζ.map_of_injective e.injective
  suffices
      (e ζ) ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            m B (AlgEquiv.autCongr e σ)).val.val =
        (e ζ) ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            m A σ).val.val by
    rw [
      (hζB.isOfFinOrder (NeZero.ne m)).pow_inj_mod,
      ← hζB.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff',
      ZMod.natCast_val,
      ZMod.natCast_val,
      ZMod.cast_id'] at this
    rwa [Units.ext_iff]
  calc
    (e ζ) ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            m B (AlgEquiv.autCongr e σ)).val.val =
        (AlgEquiv.autCongr e σ) (e ζ) := by
      symm
      exact
        IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
          m B (AlgEquiv.autCongr e σ) hζB.pow_eq_one
    _ = e (σ ζ) := by
      simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
        e.symm_apply_apply]
    _ =
        e
          (ζ ^
            (IsCyclotomicExtension.Rat.galEquivZMod
              m A σ).val.val) := by
      rw [
        IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
          m A σ hζ.pow_eq_one]
    _ =
        (e ζ) ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            m A σ).val.val := by
      rw [map_pow]

section NonzeroOrder

variable (m : ℕ) [NeZero m]

open scoped Classical in
local instance localNeZeroInstance1 : NeZero (m : ℚ) :=
  ⟨by exact_mod_cast (NeZero.ne m)⟩

attribute [local instance] localNeZeroInstance1

open scoped Classical in
noncomputable local instance localNumberFieldInstance1 :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨m, NeZero.pos m⟩

attribute [local instance] localNumberFieldInstance1

open scoped Classical in
noncomputable local instance localIsAbelianGaloisInstance1 :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨m, NeZero.pos m⟩

attribute [local instance] localIsAbelianGaloisInstance1

open scoped Classical in
noncomputable local instance rationalCyclotomicLevelIsCyclotomicExtensionAtOrder :
    IsCyclotomicExtension {m} ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩) := by
  change
    IsCyclotomicExtension
      {((⟨m, NeZero.pos m⟩ : ℕ+) : ℕ)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩)
  exact
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      ⟨m, NeZero.pos m⟩

attribute [local instance] rationalCyclotomicLevelIsCyclotomicExtensionAtOrder

open scoped Classical in
noncomputable local instance rationalCyclotomicFieldIsCyclotomicExtension :
    IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
  CyclotomicField.isCyclotomicExtension m ℚ

attribute [local instance] rationalCyclotomicFieldIsCyclotomicExtension

open scoped Classical in
noncomputable local instance rationalCyclotomicFieldIsAbelianGalois :
    IsAbelianGalois ℚ (CyclotomicField m ℚ) :=
  IsCyclotomicExtension.isAbelianGalois {m} ℚ
    (CyclotomicField m ℚ)

attribute [local instance] rationalCyclotomicFieldIsAbelianGalois

open scoped Classical in
noncomputable local instance rationalCyclotomicLevelIdeleClassNormRangeNormal :
    (_root_.ideleClassNorm ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩)).range.Normal := by
  rw [
    rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
      m (NeZero.ne m)]
  infer_instance

attribute [local instance] rationalCyclotomicLevelIdeleClassNormRangeNormal

open scoped Classical in
noncomputable local instance rationalCyclotomicFieldIdeleClassNormRangeNormal :
    (_root_.ideleClassNorm ℚ (CyclotomicField m ℚ)).range.Normal := by
  rw [
    rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
      m (NeZero.ne m)]
  infer_instance

attribute [local instance] rationalCyclotomicFieldIdeleClassNormRangeNormal

open scoped Classical in
/-- The internal finite level of the rational cyclotomic closure is
isomorphic over `ℚ` to mathlib's concrete cyclotomic field of the same
order. -/
noncomputable def rationalCyclotomicLevelAlgEquivCyclotomicField
    :
    KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩ ≃ₐ[ℚ]
      CyclotomicField m ℚ := by
  exact
    IsCyclotomicExtension.algEquiv {m} ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩)
      (CyclotomicField m ℚ)

open scoped Classical in
/-- A normalized local element of order one at the rational prime `q`.
It is the inverse of the rational uniformizer in the absolute-value
completion, transported to the adic-completion model used by idèles. -/
noncomputable def rationalPrimeArithmeticFrobeniusLocalInput
    (q : Nat.Primes) :
    ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ :=
  finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)
    ((rationalPrimeFinitePlaceFieldUnit q)⁻¹)

open scoped Classical in
/-- The normalized local input for prime-ideal Artin reciprocity has
inverse-standard valuation exponent one. -/
theorem rationalPrimeArithmeticFrobeniusLocalInput_valuationMap
    (q : Nat.Primes) :
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (rationalPrimeArithmeticFrobeniusLocalInput q))) =
      1 := by
  rw [
    rationalPrimeArithmeticFrobeniusLocalInput,
    (finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)).symm_apply_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_ofMul_inv,
    rationalPrimeFinitePlaceFieldUnit_valuationMap]
  norm_num

open scoped Classical in
private theorem
    rationalCyclotomicLevel_chosenFinitePlaceArtin_at_unramifiedPrime
    (m : ℕ) [NeZero m]
    (q : Nat.Primes) (hq : ¬ q.1 ∣ m) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩)
          (RayClass.rationalPrime q)
          (rationalPrimeArithmeticFrobeniusLocalInput q)) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  calc
    IsCyclotomicExtension.Rat.galEquivZMod
        m
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩)
          (RayClass.rationalPrime q)
          (rationalPrimeArithmeticFrobeniusLocalInput q)) =
        (ZMod.unitOfCoprime q.1
          (q.2.coprime_iff_not_dvd.mpr hq)) ^
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
            (HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion
            (Additive.ofMul
              ((finitePlaceCompletionUnitsContinuousMulEquiv
                (RayClass.rationalPrime q)).symm
                (rationalPrimeArithmeticFrobeniusLocalInput q))) := by
      apply
        galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
      change ¬ q.1 ∣ m
      exact hq
    _ = ZMod.unitOfCoprime q.1
          (q.2.coprime_iff_not_dvd.mpr hq) := by
      rw [
        rationalPrimeArithmeticFrobeniusLocalInput_valuationMap,
        zpow_one]

open scoped Classical in
/-- At an unramified rational prime `q ∤ m`, the actual global
norm-residue symbol on the normalized one-place prime idèle acts on the
internal `m`-th cyclotomic level by the direct exponent `q`. -/
theorem
    rationalCyclotomicLevel_globalNormResidue_at_unramifiedPrime
    (q : Nat.Primes) (hq : ¬ q.1 ∣ m) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        (globalNormResidueMonoidHom
          ℚ
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩)
          (IdeleGroup.finitePlaceIdeleClass
            (RayClass.rationalPrime q)
            (rationalPrimeArithmeticFrobeniusLocalInput q))) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  have hglobal :
      globalNormResidueMonoidHom ℚ
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩)
          (IdeleGroup.finitePlaceIdeleClass
            (RayClass.rationalPrime q)
            (rationalPrimeArithmeticFrobeniusLocalInput q)) =
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩)
          (RayClass.rationalPrime q)
          (rationalPrimeArithmeticFrobeniusLocalInput q) :=
    DFunLike.congr_fun
      (globalNormResidueMonoidHom_comp_finitePlaceIdeleClass
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        (RayClass.rationalPrime q))
      (rationalPrimeArithmeticFrobeniusLocalInput q)
  calc
    _ = IsCyclotomicExtension.Rat.galEquivZMod
          m
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩)
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L := KummerTheory.rationalCyclotomicLevel
              ⟨m, NeZero.pos m⟩)
            (RayClass.rationalPrime q)
            (rationalPrimeArithmeticFrobeniusLocalInput q)) :=
      congrArg
        (IsCyclotomicExtension.Rat.galEquivZMod
          m
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩))
        hglobal
    _ = ZMod.unitOfCoprime q.1
          (q.2.coprime_iff_not_dvd.mpr hq) :=
      rationalCyclotomicLevel_chosenFinitePlaceArtin_at_unramifiedPrime
        m q hq

open scoped Classical in
/-- Topological global reciprocity for the actual finite level inside the
rational cyclotomic closure.  The target is the idelic rational ray class
group modulo `(m)`, transported along the exact norm-range equality. -/
noncomputable def
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
    :
    Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩ / ℚ) ≃ₜ*
      RayClass.RayClassGroup (RayClass.rationalModulus m) :=
  galoisContinuousMulEquivRayClassGroupOfNormRangeEq
      (KummerTheory.rationalCyclotomicLevel
        ⟨m, NeZero.pos m⟩)
      (RayClass.rationalModulus m)
      (rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
        m (NeZero.ne m))

open scoped Classical in
/-- Evaluation of finite-level rational cyclotomic reciprocity is inverse
global norm-residue reciprocity followed by the exact ray norm-range
transport. -/
@[simp]
theorem
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_apply
    (σ :
      Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩/ℚ)) :
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
        m σ =
      QuotientGroup.quotientMulEquivOfEq
          (rationalCyclotomicLevel_ideleClassNorm_range_eq_rationalCongruenceSubgroup
            m (NeZero.ne m))
        (Additive.toMul
          ((globalNormResidueEquiv
              ℚ
              (KummerTheory.rationalCyclotomicLevel
                ⟨m, NeZero.pos m⟩)).symm
            (Additive.ofMul σ))) := by
  rfl

open scoped Classical in
/-- On an idèle-class representative, finite-level cyclotomic reciprocity
is the actual global norm-residue symbol followed by its rational ray
class modulo `(m)`. -/
theorem
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_globalNormResidue
    (c : IdeleClassGroup ℚ) :
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
        m
        (globalNormResidueMonoidHom
          ℚ
          (KummerTheory.rationalCyclotomicLevel
            ⟨m, NeZero.pos m⟩) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.rationalModulus m)) c := by
  rw [
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_apply]
  apply
    quotientMulEquivOfNormRangeEq_globalNormResidue

open scoped Classical in
/-- Inverse finite-level cyclotomic reciprocity sends the ray class of an
idèle class back to its genuine global norm-residue symbol. -/
theorem
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_symm_mk
    (c : IdeleClassGroup ℚ) :
    (rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
        m).symm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.rationalModulus m)) c) =
      globalNormResidueMonoidHom
        ℚ
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩) c := by
  apply
    (rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
      m).injective
  rw [
    (rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
      m).apply_symm_apply,
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_globalNormResidue]

open scoped Classical in
/-- The inverse ray reciprocity image of the normalized one-place class at
an unramified rational prime has direct cyclotomic exponent `q`.  This
places the actual global map, its ray quotient, and the Frobenius
normalization on one literal finite cyclotomic field. -/
theorem
    rationalCyclotomicLevel_rayReciprocity_at_unramifiedPrime
    (q : Nat.Primes) (hq : ¬ q.1 ∣ m) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
        ((rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup
            m).symm
          (QuotientGroup.mk'
            (RayClass.Modulus.congruenceSubgroup
              (RayClass.rationalModulus m))
            (IdeleGroup.finitePlaceIdeleClass
              (RayClass.rationalPrime q)
              (rationalPrimeArithmeticFrobeniusLocalInput q)))) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  rw [
    rationalCyclotomicLevelGaloisContinuousMulEquivRayClassGroup_symm_mk,
    rationalCyclotomicLevel_globalNormResidue_at_unramifiedPrime
      m q hq]

open scoped Classical in
/-- The actual arithmetic Frobenius at `q` on the concrete cyclotomic
field, obtained by transporting the genuine global one-place Artin
symbol from the internal cyclotomic level. -/
noncomputable def rationalCyclotomicPrimeArithmeticFrobenius
    (q : Nat.Primes) :
    Gal(CyclotomicField m ℚ / ℚ) := by
  let mp : ℕ+ := ⟨m, NeZero.pos m⟩
  let L : Type := KummerTheory.rationalCyclotomicLevel mp
  let : NumberField L :=
    KummerTheory.rationalCyclotomicLevel_numberField mp
  let : FiniteDimensional ℚ L :=
    rationalCyclotomicPrincipalPrimeLevelFiniteDimensional mp
  let : IsAbelianGalois ℚ L :=
    rationalCyclotomicLevelIsAbelianGalois mp
  exact
    AlgEquiv.autCongr
      (rationalCyclotomicLevelAlgEquivCyclotomicField m)
      (globalNormResidueMonoidHom
        ℚ L
        (IdeleGroup.finitePlaceIdeleClass
          (RayClass.rationalPrime q)
          (rationalPrimeArithmeticFrobeniusLocalInput q)))

open scoped Classical in
/-- For `q ∤ m`, the actual arithmetic Frobenius on
`CyclotomicField m ℚ` is the direct-`q` automorphism
`ζ ↦ ζ ^ q`; no inverse appears. -/
theorem rationalCyclotomicPrimeArithmeticFrobenius_galEquivZMod
    (q : Nat.Primes) (hq : ¬ q.1 ∣ m) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ)
        (rationalCyclotomicPrimeArithmeticFrobenius m q) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  let mp : ℕ+ := ⟨m, NeZero.pos m⟩
  let L : Type := KummerTheory.rationalCyclotomicLevel mp
  let : NumberField L :=
    KummerTheory.rationalCyclotomicLevel_numberField mp
  let : IsCyclotomicExtension {m} ℚ L := by
    change
      IsCyclotomicExtension {m} ℚ
        (KummerTheory.rationalCyclotomicLevel
          ⟨m, NeZero.pos m⟩)
    exact rationalCyclotomicLevelIsCyclotomicExtensionAtOrder m
  let : FiniteDimensional ℚ L :=
    rationalCyclotomicPrincipalPrimeLevelFiniteDimensional mp
  let : IsAbelianGalois ℚ L :=
    rationalCyclotomicLevelIsAbelianGalois mp
  change
    IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ)
        (AlgEquiv.autCongr
          (rationalCyclotomicLevelAlgEquivCyclotomicField m)
          (globalNormResidueMonoidHom
            ℚ L
            (IdeleGroup.finitePlaceIdeleClass
              (RayClass.rationalPrime q)
              (rationalPrimeArithmeticFrobeniusLocalInput q)))) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)
  rw [
    galEquivZMod_autCongr,
    rationalCyclotomicLevel_globalNormResidue_at_unramifiedPrime
      m q hq]

open scoped Classical in
/-- The selected rational ray class field is the actual cyclotomic field
of the same modulus, as an equivalence of fields over `ℚ`. -/
private noncomputable def rationalRayClassFieldCyclotomicRingEquiv
    :
    rayClassField ℚ (RayClass.rationalModulus m) ≃+*
      CyclotomicField m ℚ := by
  letI : Algebra ℚ
      (rayClassField ℚ (RayClass.rationalModulus m)) :=
    rayClassFieldAlgebraOverOriginal (RayClass.rationalModulus m)
  exact
    (Classical.choice
      ((nonempty_algEquiv_rayClassField_iff_ideleClassNorm_range_eq
          (K := ℚ)
          (CyclotomicField m ℚ)
          (RayClass.rationalModulus m)).2
        (rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
          m (NeZero.ne m)))).symm.toRingEquiv

open scoped Classical in
/-- A chosen `ℚ`-algebra equivalence from the selected rational ray class
field to the cyclotomic field of the same modulus. -/
noncomputable def rationalRayClassFieldCyclotomicAlgEquiv
    :
    rayClassField ℚ (RayClass.rationalModulus m) ≃ₐ[ℚ]
      CyclotomicField m ℚ := by
  let e := rationalRayClassFieldCyclotomicRingEquiv m
  refine { e with commutes' := ?_ }
  intro q
  exact map_ratCast e q

open scoped Classical in
noncomputable local instance rationalRayClassFieldIsCyclotomicExtension :
    IsCyclotomicExtension {m} ℚ
      (rayClassField ℚ (RayClass.rationalModulus m)) :=
  IsCyclotomicExtension.equiv {m} ℚ (CyclotomicField m ℚ)
    (rationalRayClassFieldCyclotomicAlgEquiv m).symm

attribute [local instance] rationalRayClassFieldIsCyclotomicExtension

open scoped Classical in
noncomputable local instance rationalRayClassFieldIsAbelianGalois :
    IsAbelianGalois ℚ
      (rayClassField ℚ (RayClass.rationalModulus m)) :=
  IsCyclotomicExtension.isAbelianGalois {m} ℚ
    (rayClassField ℚ (RayClass.rationalModulus m))

attribute [local instance] rationalRayClassFieldIsAbelianGalois

open scoped Classical in
/-- Transporting the actual norm-residue symbol of the selected rational
ray class field to the concrete cyclotomic realization preserves its
cyclotomic character.  The left side uses the literal conjugation map on
Galois automorphisms, not an abstract identification of finite groups. -/
theorem
    rationalRayClassFieldCyclotomicAlgEquiv_autCongr_globalNormResidue_character
    (c : IdeleClassGroup ℚ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ)
        (AlgEquiv.autCongr
          (rationalRayClassFieldCyclotomicAlgEquiv m)
          (globalNormResidueMonoidHom
            ℚ (rayClassField ℚ (RayClass.rationalModulus m)) c)) =
      IsCyclotomicExtension.Rat.galEquivZMod
        m (rayClassField ℚ (RayClass.rationalModulus m))
        (globalNormResidueMonoidHom
          ℚ (rayClassField ℚ (RayClass.rationalModulus m)) c) := by
  let e := rationalRayClassFieldCyclotomicAlgEquiv m
  exact galEquivZMod_autCongr m
    (rayClassField ℚ (RayClass.rationalModulus m))
    (CyclotomicField m ℚ) e
    (globalNormResidueMonoidHom
      ℚ (rayClassField ℚ (RayClass.rationalModulus m)) c)

open scoped Classical in
/-- Monoid-hom form of cyclotomic-character invariance under the selected
ray-class-field/cyclotomic-field realization. -/
theorem
    rationalRayClassFieldCyclotomicAlgEquiv_autCongr_globalNormResidue_character_hom
    :
    ((IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ)).toMonoidHom.comp
      ((AlgEquiv.autCongr
        (rationalRayClassFieldCyclotomicAlgEquiv m)).toMonoidHom.comp
        (globalNormResidueMonoidHom
          ℚ (rayClassField ℚ (RayClass.rationalModulus m))))) =
      ((IsCyclotomicExtension.Rat.galEquivZMod
        m (rayClassField ℚ (RayClass.rationalModulus m))).toMonoidHom.comp
        (globalNormResidueMonoidHom
          ℚ (rayClassField ℚ (RayClass.rationalModulus m)))) := by
  apply MonoidHom.ext
  intro c
  exact
    rationalRayClassFieldCyclotomicAlgEquiv_autCongr_globalNormResidue_character
      m c

open scoped Classical in
/-- Topological global reciprocity for the actual rational cyclotomic
field, with target the rational ray class group modulo `(m)`. -/
noncomputable def
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup
    :
    Gal(CyclotomicField m ℚ / ℚ) ≃ₜ*
      RayClass.RayClassGroup (RayClass.rationalModulus m) :=
  galoisContinuousMulEquivRayClassGroupOfNormRangeEq
      (CyclotomicField m ℚ) (RayClass.rationalModulus m)
      (rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
        m (NeZero.ne m))

open scoped Classical in
/-- The ordinary cyclotomic character, retaining the finite Krull
topology on the actual Galois group and the discrete topology on
`(ℤ/mℤ)ˣ`. -/
noncomputable def
    rationalCyclotomicGaloisContinuousMulEquivZModUnits
    :
    Gal(CyclotomicField m ℚ / ℚ) ≃ₜ*
      (ZMod m)ˣ := by
  exact
    { IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

open scoped Classical in
/-- Forgetting topology from the cyclotomic character recovers the
standard `galEquivZMod` map literally. -/
@[simp]
theorem
    rationalCyclotomicGaloisContinuousMulEquivZModUnits_apply
    (σ : Gal(CyclotomicField m ℚ/ℚ)) :
    rationalCyclotomicGaloisContinuousMulEquivZModUnits
        m σ =
      IsCyclotomicExtension.Rat.galEquivZMod
        m (CyclotomicField m ℚ) σ := by
  rfl

open scoped Classical in
/-- Evaluation of rational cyclotomic reciprocity is inverse global
norm-residue reciprocity followed by transport along the exact
cyclotomic norm-range equality. -/
@[simp]
theorem
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup_apply
    (σ : Gal(CyclotomicField m ℚ/ℚ)) :
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup
        m σ =
      QuotientGroup.quotientMulEquivOfEq
          (rationalCyclotomicField_ideleClassNorm_range_eq_rationalCongruenceSubgroup
            m (NeZero.ne m))
        (Additive.toMul
          ((globalNormResidueEquiv
              ℚ (CyclotomicField m ℚ)).symm
            (Additive.ofMul σ))) := by
  rfl

open scoped Classical in
/-- On an idèle-class representative, rational cyclotomic reciprocity
sends the actual global norm-residue symbol to its ray class modulo
`(m)`. -/
theorem
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup_globalNormResidue
    (c : IdeleClassGroup ℚ) :
    rationalCyclotomicGaloisContinuousMulEquivRayClassGroup
        m
        (globalNormResidueMonoidHom
          ℚ (CyclotomicField m ℚ) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.rationalModulus m)) c := by
  rw [rationalCyclotomicGaloisContinuousMulEquivRayClassGroup_apply]
  apply
    quotientMulEquivOfNormRangeEq_globalNormResidue

end NonzeroOrder

end KroneckerWeber
