/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation

/-! # Henselian Valuation Base -/
namespace LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: the value group of the local henselian valuation

The normalized valuation of the base local field is transported to the
actual fixed coefficient group in the separable closure and then embedded
in `ℤ̂`.  Its range is proved to be exactly the ordinary integers inside
`ℤ̂`, and the quotients by `nℤ` are identified with `ZMod n`.  These are the
source-producing parts of the Henselian valuation condition.
-/

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private abbrev G := Gal(SeparableClosure K / K)

private abbrev A : Rep ℤ (G K) :=
  galoisAmbientUnitsRep K (SeparableClosure K)

/-- `Kˣ` is the coefficient group fixed by the distinguished base subgroup
of the absolute separable Galois group. -/
def baseFieldUnitsEquiv :
    Additive Kˣ ≃+ ambientFixedAddSubgroup (A K) (baseField (G K)) :=
  (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).trans
    (AddEquiv.addSubgroupCongr
      (congrArg (ambientFixedAddSubgroup (A K))
        (closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K))))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- States the theorem `baseFieldUnitsEquiv_val`. -/
@[simp]
theorem baseFieldUnitsEquiv_val (x : Kˣ) :
    ((Additive.toMul
      ((baseFieldUnitsEquiv K (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K) := by
  change
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K)
  exact baseUnitsEquivGaloisAmbientFixed_val K (SeparableClosure K) x

/-- The normalized valuation `v_K : Kˣ → ℤ`, embedded in `ℤ̂` and written on
the actual fixed coefficient group. -/
def localBaseValuation :
    ambientFixedAddSubgroup (A K) (baseField (G K)) →+ ZHat :=
  (Int.castRingHom ZHat).toAddMonoidHom.comp
    ((LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K).comp
      (baseFieldUnitsEquiv K).symm.toAddMonoidHom)

/-- States the theorem `localBaseValuation_baseFieldUnitsEquiv`. -/
@[simp]
theorem localBaseValuation_baseFieldUnitsEquiv (x : Additive Kˣ) :
    localBaseValuation K (baseFieldUnitsEquiv K x) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x) := by
  simp [localBaseValuation]

/-- The value group is exactly the image of the ordinary integers in the
profinite integers. -/
theorem localBaseValuation_range :
    (localBaseValuation K).range =
      (Int.castRingHom ZHat).toAddMonoidHom.range := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨IsNonarchimedeanLocalField.valuationMap K
      ((baseFieldUnitsEquiv K).symm x), rfl⟩
  · rintro z ⟨m, rfl⟩
    obtain ⟨x, hx⟩ :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective K m
    refine ⟨baseFieldUnitsEquiv K x, ?_⟩
    rw [localBaseValuation_baseFieldUnitsEquiv, hx]
    rfl

/-- Every ordinary integer occurs as a value, as required in the Henselian valuation condition. -/
theorem intToProCInteger_mem_localBaseValuation_range (m : ℤ) :
    Int.castRingHom ZHat m ∈
      (localBaseValuation K).range := by
  rw [localBaseValuation_range]
  exact ⟨m, rfl⟩

/-- Reduction modulo `n` on the actual value group. -/
def localValueGroupReduction (n : ℕ) (hn : 0 < n) :
    (localBaseValuation K).range →+ ZMod n :=
  (zHatReduction n hn).toAddMonoidHom.comp
    (localBaseValuation K).range.subtype

/-- States the theorem `localValueGroupReduction_surjective`. -/
theorem localValueGroupReduction_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (localValueGroupReduction K n hn) := by
  intro a
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  let z : (localBaseValuation K).range :=
    ⟨Int.castRingHom ZHat m,
      intToProCInteger_mem_localBaseValuation_range K m⟩
  refine ⟨z, ?_⟩
  exact zHatReduction_int n hn m

/-- The kernel of reduction on the value group is precisely `nZ`. -/
theorem localValueGroupReduction_ker (n : ℕ) (hn : 0 < n) :
    (localValueGroupReduction K n hn).ker =
      nsmulWithin (localBaseValuation K).range n := by
  apply le_antisymm
  · intro z hz
    have hzInt : (z : ZHat) ∈
        (Int.castRingHom ZHat).toAddMonoidHom.range := by
      rw [← localBaseValuation_range K]
      exact z.property
    obtain ⟨m, hm⟩ := hzInt
    change Int.castRingHom ZHat m = (z : ZHat) at hm
    have hmod : (m : ZMod n) = 0 := by
      have hz0 : localValueGroupReduction K n hn z = 0 := hz
      change zHatReduction n hn (z : ZHat) = 0 at hz0
      rw [← hm, zHatReduction_int] at hz0
      exact hz0
    have hdiv : (n : ℤ) ∣ m := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hdiv
    let w : (localBaseValuation K).range :=
      ⟨Int.castRingHom ZHat k,
        intToProCInteger_mem_localBaseValuation_range K k⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change n • Int.castRingHom ZHat k = (z : ZHat)
    rw [← map_nsmul]
    have hnk : n • k = m := by
      simpa [nsmul_eq_mul] using hk.symm
    rw [hnk, hm]
  · rintro z ⟨w, rfl⟩
    change zHatReduction n hn (n • (w : ZHat)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul]

/-- The cyclic quotient condition in the Henselian valuation condition, for the actual local value
group. -/
def localValueGroupQuotientEquivZMod (n : ℕ) (hn : 0 < n) :
    ((localBaseValuation K).range ⧸
        nsmulWithin (localBaseValuation K).range n) ≃+ ZMod n :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (localValueGroupReduction_ker K n hn).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (localValueGroupReduction K n hn)
      (localValueGroupReduction_surjective K n hn))

/-- The inclusion-and-reduction quotient map of the Henselian valuation condition is
bijective for the actual local value group. -/
theorem localCanonicalValueQuotientMap_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      (canonicalValueQuotientMap (localBaseValuation K).range n hn) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [← localValueGroupReduction_ker K n hn]
    change localValueGroupReduction K n hn (z₁ - z₂) = 0
    rw [map_sub]
    change localValueGroupReduction K n hn z₁ =
      localValueGroupReduction K n hn z₂ at h
    rw [h, sub_self]
  · intro a
    obtain ⟨z, hz⟩ := localValueGroupReduction_surjective K n hn a
    refine ⟨QuotientAddGroup.mk'
      (nsmulWithin (localBaseValuation K).range n) z, ?_⟩
    exact hz

end
end LocalClassFieldTheory
