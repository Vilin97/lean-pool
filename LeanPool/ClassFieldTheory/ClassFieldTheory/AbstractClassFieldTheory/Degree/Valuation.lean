/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm

/-! # Valuation -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: henselian valuations

The multiplicative coefficient module is represented additively, as
in .  Accordingly a valuation and a norm are additive homomorphisms.  This
file formalizes the valuation-quotient axiom and constructs the normalized valuations of
normalized-valuation functoriality.
-/

noncomputable section

universe u

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm `N_{K|k}` on the actual fixed modules. -/
def normToBase (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))] :
    ambientFixedAddSubgroup A K →+
      ambientFixedAddSubgroup A (baseField G) :=
  relativeNorm A (baseField G) K (le_baseField K)

/-- Multiplication by `n` on an additive subgroup. -/
def nsmulOnAddSubgroup (Z : AddSubgroup ZHat) (n : ℕ) : Z →+ Z where
  toFun z := ⟨n • z.1, Z.nsmul_mem z.2 n⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The subgroup `nZ` inside a value group `Z`. -/
def nsmulWithin (Z : AddSubgroup ZHat) (n : ℕ) : AddSubgroup Z :=
  (nsmulOnAddSubgroup Z n).range

/-- The ambient subgroup `nZ ⊆ ℤ̂`. -/
def nsmulImage (Z : AddSubgroup ZHat) (n : ℕ) : AddSubgroup ZHat :=
  Z.map
    { toFun := fun z : ZHat => n • z
      map_zero' := nsmul_zero n
      map_add' := fun x y => nsmul_add x y n }

/-- An element belongs to the natural-multiple image exactly when it has a
preimage in the subgroup. -/
@[simp]
theorem mem_nsmulImage_iff (Z : AddSubgroup ZHat) (n : ℕ) (z : ZHat) :
    z ∈ nsmulImage Z n ↔ ∃ x ∈ Z, n • x = z := by
  rfl

/-- Multiples of the full value group are the range of multiplication
by the same natural number on `ZHat`. -/
@[simp]
theorem nsmulImage_top (n : ℕ) :
    nsmulImage (⊤ : AddSubgroup ZHat) n =
      (zHatMulNat n).toAddMonoidHom.range := by
  ext z
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, AddSubgroup.mem_top x, rfl⟩

/-- Restriction of reduction modulo `n` along the inclusion `Z ≤ ℤ̂`. -/
def valueGroupReduction (Z : AddSubgroup ZHat) (n : ℕ) (hn : 0 < n) :
    Z →+ ZMod n :=
  (zHatReduction n hn).toAddMonoidHom.comp Z.subtype

/-- The canonical map `Z/nZ → ℤ/nℤ` induced by the inclusion `Z ≤ ℤ̂`
and reduction modulo `n`.

This is the specific map required in the valuation-quotient axiom, rather than an
arbitrarily chosen abstract equivalence between the two quotients. -/
def canonicalValueQuotientMap (Z : AddSubgroup ZHat)
    (n : ℕ) (hn : 0 < n) : (Z ⧸ nsmulWithin Z n) →+ ZMod n :=
  QuotientAddGroup.lift (nsmulWithin Z n) (valueGroupReduction Z n hn) (by
    rintro _ ⟨z, rfl⟩
    change zHatReduction n hn (n • (z : ZHat)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul])

/-- The canonical value map evaluates on a quotient representative by reduction modulo `n`. -/
theorem canonicalValueQuotientMap_mk (Z : AddSubgroup ZHat)
    (n : ℕ) (hn : 0 < n) (z : Z) :
    canonicalValueQuotientMap Z n hn
        (QuotientAddGroup.mk' (nsmulWithin Z n) z) =
      zHatReduction n hn (z : ZHat) :=
  rfl

/-- For the full profinite-integer value group, the canonical
inclusion-and-reduction quotient map is bijective. -/
theorem canonicalValueQuotientMap_top_bijective
    (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      (canonicalValueQuotientMap
        (⊤ : AddSubgroup ZHat) n hn) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hz :
        zHatReduction n hn
            ((z₁ : ZHat) - (z₂ : ZHat)) =
          0 := by
      rw [map_sub]
      change
        zHatReduction n hn (z₁ : ZHat) =
          zHatReduction n hn (z₂ : ZHat) at h
      rw [h, sub_self]
    have hrange :
        (z₁ : ZHat) - (z₂ : ZHat) ∈
          (zHatMulNat n).toAddMonoidHom.range := by
      rw [zHatMulNat_range_eq_ker_reduction n hn]
      exact hz
    obtain ⟨w, hw⟩ := hrange
    refine ⟨⟨w, AddSubgroup.mem_top w⟩, ?_⟩
    apply Subtype.ext
    exact hw
  · intro a
    obtain ⟨z, hz⟩ :=
      zHatReduction_surjective n hn a
    exact
      ⟨QuotientAddGroup.mk'
          (nsmulWithin (⊤ : AddSubgroup ZHat) n)
          ⟨z, AddSubgroup.mem_top z⟩,
        hz⟩

/-- The quotient used by the norm has the positive degree carried by a
finite abstract field. -/
@[simp] theorem FiniteAbstractField.normToBase_index_eq_degree
    {G : Type*} [Group G] [TopologicalSpace G]
    (K : FiniteAbstractField G) :
    (extensionSubgroup (baseField G) K.field
      (le_baseField K.field)).index =
      (K.toFiniteAbstractExtension.degree : ℕ) :=
  K.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree

/-- **the valuation-quotient axiom.** A henselian valuation of `A_k` with respect to `d`.

`integers_mem` and `canonical_value_quotient_bijective` are precisely
condition (i), while `norm_range` is condition (ii). -/
structure ValuationData (D : DegreeData G) (A : Rep ℤ G) where
  /-- The additive valuation on the distinguished base-field fixed module. -/
  toAddMonoidHom : ambientFixedAddSubgroup A (baseField G) →+ ZHat
  /-- Every integral value occurs in the image of the valuation. -/
  integers_mem : ∀ m : ℤ,
    (Int.castRingHom ZHat) m ∈
      toAddMonoidHom.range
  /-- Reduction of the value group modulo every positive integer is bijective. -/
  canonical_value_quotient_bijective : ∀ (n : ℕ) (hn : 0 < n),
    Function.Bijective
      (canonicalValueQuotientMap toAddMonoidHom.range n hn)
  /-- Norms from a finite abstract field have the prescribed value-group image. -/
  norm_range : ∀ K : FiniteAbstractField G,
    (toAddMonoidHom.comp (normToBase A K.field)).range =
      nsmulImage toAddMonoidHom.range (K.residueDegree D : ℕ)

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The value group `Z = v(A_k)`. -/
def valueGroup (v : ValuationData D A) : AddSubgroup ZHat :=
  v.toAddMonoidHom.range

/-- The valuation-quotient axiom's canonical map for a henselian valuation. -/
def canonicalQuotientMap (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) →+ ZMod n :=
  canonicalValueQuotientMap v.valueGroup n hn

/-- The former equivalence API, now derived from the bijectivity of the
canonical inclusion-and-reduction map in the valuation-quotient axiom. -/
def cyclicValueQuotients (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) ≃+ ZMod n :=
  AddEquiv.ofBijective (v.canonicalQuotientMap n hn)
    (v.canonical_value_quotient_bijective n hn)

/-- Canonical reduction of the value group modulo `n`. -/
def valueModulo (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    v.valueGroup →+ ZMod n :=
  (v.cyclicValueQuotients n hn).toAddMonoidHom.comp
    (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n))

/-- Value modulo `n` is profinite-integer reduction of the underlying value. -/
@[simp]
theorem valueModulo_apply (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) (z : v.valueGroup) :
    v.valueModulo n hn z = zHatReduction n hn (z : ZHat) :=
  rfl

/-- Reduction of the value group modulo a positive integer is surjective. -/
theorem valueModulo_surjective (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    Function.Surjective (v.valueModulo n hn) := by
  intro z
  obtain ⟨q, rfl⟩ := (v.cyclicValueQuotients n hn).surjective z
  refine Quotient.inductionOn' q ?_
  intro a
  exact ⟨a, rfl⟩

/-- The norm composite `v ∘ N_{K|k}` before division by the residue degree. -/
def normCompositeAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ZHat :=
  v.toAddMonoidHom.comp (normToBase A K.field)

/-- The norm-valuation composite has range equal to the residue-degree multiple image. -/
theorem normCompositeAt_range (v : ValuationData D A) (K : FiniteAbstractField G) :
    (v.normCompositeAt K).range =
      nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
  v.norm_range K

/-- `v(N_{K|k}a)` regarded as an element of `f_K ℤ̂`. -/
def normCompositeAtInResidueImage (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+
      (zHatMulNat (K.residueDegree D : ℕ)).toAddMonoidHom.range where
  toFun a := ⟨v.normCompositeAt K a, by
    have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
    rw [v.normCompositeAt_range K] at ha
    obtain ⟨z, _hz, hz⟩ := ha
    exact ⟨z, hz⟩⟩
  map_zero' := by ext; simp [normCompositeAt]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (v.normCompositeAt K) x y

/-- Division by `f_K` before restricting the codomain back to `Z`. -/
def dividedAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ZHat :=
  (zHatDivide (K.residueDegree D : ℕ)
    (K.residueDegree D).property).toAddMonoidHom.comp
      (v.normCompositeAtInResidueImage K)

/-- The defining identity `f_K v_K = v ∘ N_{K|k}` before codomain
restriction. -/
theorem residueDegree_nsmul_dividedAt (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    (K.residueDegree D : ℕ) • v.dividedAt K a = v.normCompositeAt K a := by
  exact zHatMulNat_zHatDivide (K.residueDegree D : ℕ)
    (K.residueDegree D).property
    (v.normCompositeAtInResidueImage K a)

/-- The divided value lies in the original value group `Z`. -/
theorem dividedAt_mem_valueGroup (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    v.dividedAt K a ∈ v.valueGroup := by
  have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
  rw [v.normCompositeAt_range K] at ha
  obtain ⟨z, hzZ, hz⟩ := ha
  have hzSubtype : v.normCompositeAtInResidueImage K a =
      ⟨zHatMulNat (K.residueDegree D : ℕ) z, ⟨z, rfl⟩⟩ := by
    apply Subtype.ext
    change v.normCompositeAt K a =
      zHatMulNat (K.residueDegree D : ℕ) z
    exact hz.symm
  change zHatDivide (K.residueDegree D : ℕ)
      (K.residueDegree D).property
        (v.normCompositeAtInResidueImage K a) ∈ v.valueGroup
  rw [hzSubtype]
  exact (zHatDivide_zHatMulNat (K.residueDegree D : ℕ)
    (K.residueDegree D).property z).symm ▸ hzZ

/-- The normalized valuation `v_K = (1/f_K) v ∘ N_{K|k}`, with the exact
codomain `Z` from the valuation-quotient axiom. -/
def valuationAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ v.valueGroup :=
  (v.dividedAt K).codRestrict v.valueGroup (fun a => v.dividedAt_mem_valueGroup K a)

/-- The underlying profinite value of the positive valuation is the divided valuation. -/
@[simp]
theorem valuationAt_coe (v : ValuationData D A) (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    (v.valuationAt K a : ZHat) = v.dividedAt K a :=
  rfl

/-- **normalized-valuation functoriality (surjectivity).** The normalized valuation over every
finite abstract field maps onto `Z`. -/
theorem normalizedValuation_surjective (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    Function.Surjective (v.valuationAt K) := by
  intro z
  have hzImage : (K.residueDegree D : ℕ) • z.1 ∈
      nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
    ⟨z.1, z.2, rfl⟩
  rw [← v.normCompositeAt_range K] at hzImage
  obtain ⟨a, ha⟩ := hzImage
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change zHatDivide (K.residueDegree D : ℕ)
      (K.residueDegree D).property
        (v.normCompositeAtInResidueImage K a) = z.1
  have hsub : v.normCompositeAtInResidueImage K a =
      ⟨zHatMulNat (K.residueDegree D : ℕ) z.1, ⟨z.1, rfl⟩⟩ := by
    apply Subtype.ext
    change v.normCompositeAt K a =
      zHatMulNat (K.residueDegree D : ℕ) z.1
    exact ha
  rw [hsub]
  exact zHatDivide_zHatMulNat (K.residueDegree D : ℕ)
    (K.residueDegree D).property z.1

end ValuationData

end
end ClassFormation
