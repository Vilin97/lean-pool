/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerExponentTower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
/-!
# Compatibility of local Hilbert symbols at divisible exponents

The source Hilbert symbol uses its first argument as the local Artin input
and its second as the Kummer radical. Artin restriction along the actual
simple Kummer tower makes its values compatible as the exponent varies.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory.Kummer

open RamificationTheory

/-- If `m ∣ n`, the exponent-`m` Hilbert value is the `(n/m)`-th power of
the exponent-`n` value, compared as units of the base field. -/
theorem localHilbertSymbol_exponentCompatibility
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (m n : ℕ+) (hmK : ((m : ℕ) : K) ≠ 0)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmuM : (primitiveRoots (m : ℕ) K).Nonempty)
    (hmuN : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmn : (m : ℕ) ∣ (n : ℕ)) (a b : Kˣ) :
    (localHilbertSymbol K m hmK hmuM a b).1 =
      (localHilbertSymbol K n hnK hmuN a b).1 ^ ((n : ℕ) / (m : ℕ)) := by
  obtain ⟨q, hq⟩ := hmn
  have hqm : q * (m : ℕ) = (n : ℕ) := by
    rw [mul_comm, ← hq]
  have hdiv : (n : ℕ) / (m : ℕ) = q := by
    rw [hq, Nat.mul_div_cancel_left _ m.pos]
  rw [hdiv]
  let Em := KummerTheory.chosenSimpleKummerExtension K m hmK b
  let En := KummerTheory.chosenSimpleKummerExtension K n hnK b
  let hEF : Em ≤ En :=
    chosenSimpleKummerExtension_le_of_dvd K m n hmK hnK hmuM ⟨q, hq⟩ b
  let : FiniteDimensional K Em :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K m hmK b
  let : FiniteDimensional K En :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K Em :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K m hmK hmuM b
  let : IsAbelianGalois K En :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmuN b
  let βm : Emˣ := KummerTheory.chosenSimpleKummerRootUnit K m hmK b
  let βn : Enˣ := KummerTheory.chosenSimpleKummerRootUnit K n hnK b
  let βmN : Enˣ := Units.map (IntermediateField.inclusion hEF).toMonoidHom βm
  let σm : Gal(Em/K) :=
    chosenSimpleKummerNormResidueAutomorphism K m hmK hmuM b a
  let σn : Gal(En/K) :=
    chosenSimpleKummerNormResidueAutomorphism K n hnK hmuN b a
  have hrestrict :
      intermediateFieldRestrictNormalHom Em En hEF σn = σm := by
    change intermediateFieldRestrictNormalHom Em En hEF
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom K En a) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom K Em a
    exact DFunLike.congr_fun
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom_restrict K Em En hEF) a
  have hβmN : βmN ^ (m : ℕ) =
      Units.map (algebraMap K En).toMonoidHom b := by
    change (Units.map (IntermediateField.inclusion hEF).toMonoidHom βm) ^
        (m : ℕ) = _
    rw [← map_pow, KummerTheory.chosenSimpleKummerRootUnit_pow]
    apply Units.ext
    rfl
  have hβnq : (βn ^ q) ^ (m : ℕ) =
      Units.map (algebraMap K En).toMonoidHom b := by
    rw [← pow_mul, hqm]
    exact KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK b
  have hratio : (βmN / βn ^ q) ^ (m : ℕ) = 1 := by
    rw [div_pow, hβmN, hβnq, div_self']
  obtain ⟨ζ, hζ⟩ :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := En) m hmuM (βmN / βn ^ q) hratio
  have hrootEq :
      KummerTheory.rootQuotient (K := K) (L := En) βmN σn =
        KummerTheory.rootQuotient (K := K) (L := En) (βn ^ q) σn := by
    apply div_eq_one.mp
    rw [KummerTheory.rootQuotient_changeRoot]
    rw [← hζ]
    exact KummerTheory.rootQuotient_algebraMap_unit ζ σn
  have hrootPow :
      KummerTheory.rootQuotient (K := K) (L := En) (βn ^ q) σn =
        (KummerTheory.rootQuotient (K := K) (L := En) βn σn) ^ q := by
    apply Units.ext
    simp only [KummerTheory.rootQuotient, AlgEquiv.smul_units_def,
      Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.coe_map]
    rw [map_pow, div_pow]
  have hmval :
      Units.map (algebraMap K Em).toMonoidHom
          (localHilbertSymbol K m hmK hmuM a b).1 =
        KummerTheory.rootQuotient (K := K) (L := Em) βm σm := by
    have h := congrArg Subtype.val
      (localHilbertSymbol_map_eq_rootQuotient K m hmK hmuM a b)
    change Units.map (algebraMap K Em).toMonoidHom
        (localHilbertSymbol K m hmK hmuM a b).1 =
      KummerTheory.rootQuotient (K := K) (L := Em) βm σm at h
    exact h
  have hnval :
      Units.map (algebraMap K En).toMonoidHom
          (localHilbertSymbol K n hnK hmuN a b).1 =
        KummerTheory.rootQuotient (K := K) (L := En) βn σn := by
    have h := congrArg Subtype.val
      (localHilbertSymbol_map_eq_rootQuotient K n hnK hmuN a b)
    change Units.map (algebraMap K En).toMonoidHom
        (localHilbertSymbol K n hnK hmuN a b).1 =
      KummerTheory.rootQuotient (K := K) (L := En) βn σn at h
    exact h
  apply Units.map_injective (algebraMap K En).injective
  calc
    Units.map (algebraMap K En).toMonoidHom
        (localHilbertSymbol K m hmK hmuM a b).1 =
      Units.map (IntermediateField.inclusion hEF).toMonoidHom
        (KummerTheory.rootQuotient (K := K) (L := Em) βm σm) := by
          rw [← hmval]
          apply Units.ext
          rfl
    _ = KummerTheory.rootQuotient (K := K) (L := En) βmN σn := by
      rw [← hrestrict]
      exact (KummerTheory.rootQuotient_map_intermediateFieldInclusion
        Em En hEF βm σn).symm
    _ = KummerTheory.rootQuotient (K := K) (L := En) (βn ^ q) σn := hrootEq
    _ = (KummerTheory.rootQuotient (K := K) (L := En) βn σn) ^ q := hrootPow
    _ = Units.map (algebraMap K En).toMonoidHom
          ((localHilbertSymbol K n hnK hmuN a b).1 ^ q) := by
      rw [← hnval, ← map_pow]

end LocalClassFieldTheory.Kummer
