/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer
/-!
# Abstract reciprocity: the maximal-unramified symbol

This file constructs the source maps used in maximal-unramified reciprocity.  In
particular, the maximal unramified quotient is projected to every finite
unramified Galois quotient, and its Frobenius is sent to the finite
arithmetic Frobenius.  The valuation--Frobenius map below is kept as a
candidate until its compatibility with the finite norm-residue symbols has
been proved from the unramified norm-quotient equivalence.
-/

noncomputable section

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Restriction from the maximal unramified Galois group over `K` to the
actual quotient of an unramified Galois extension `L / K`.  This construction
does not require the quotient to be finite. -/
def maximalUnramifiedExtensionRestriction
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : GaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →*
      L.extensionQuotient :=
  L.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    (QuotientGroup.map (D.fieldInertiaWithin K.field)
      (extensionSubgroup K.field L.field L.below)
      (MonoidHom.id K.field.toSubgroup) (by
        intro k hk
        apply (mem_extensionSubgroup_iff K.field L.field L.below k).2
        exact (L.isUnramified_iff_inertia_le D).1 hUnramified ⟨k.2, hk⟩))

/--
Establishes the identity `maximalUnramifiedExtensionRestriction D K L hUnramified
(QuotientGroup.mk k) = L.extensionQuotientMk k`.
-/
@[simp]
theorem maximalUnramifiedExtensionRestriction_mk
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : GaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (k : K.field.toSubgroup) :
    maximalUnramifiedExtensionRestriction D K L hUnramified
        (QuotientGroup.mk k) =
      L.extensionQuotientMk k := by
  exact
    L.extensionQuotientMulEquiv.symm_apply_eq.mpr
      (L.extensionQuotientMk_apply k).symm

/-- Restriction sends the maximal-unramified Frobenius to the arithmetic
Frobenius of every finite unramified quotient. -/
@[simp]
theorem maximalUnramifiedRestriction_frobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : GaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    maximalUnramifiedExtensionRestriction D K L hUnramified
        (D.frobenius K) =
      L.extensionQuotientMulEquiv.symm
        (D.unramifiedFrobenius K L.field L.below) := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ZHat)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ZHat)))
  have hmk : (QuotientGroup.mk φ :
      K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) = D.frobenius K := by
    apply (D.maximalUnramifiedDegreeEquiv K).injective
    rw [D.maximalUnramifiedDegreeEquiv_mk, hφ,
      D.maximalUnramifiedDegreeEquiv_frobenius]
  rw [← hmk, maximalUnramifiedExtensionRestriction_mk D]
  symm
  exact
    L.extensionQuotientMulEquiv.symm_apply_eq.mpr
      (L.extensionQuotientMk_apply φ).symm

/-- Restriction to a bundled finite Galois extension.  The named comparison
between the finite and non-finite Galois quotient boundaries is applied here,
once, rather than left to definitional unfolding in every consumer. -/
def finiteUnramifiedRestriction
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →*
      L.extensionQuotient :=
  L.toGaloisExtensionQuotientMulEquiv.symm.toMonoidHom.comp
    (D.maximalUnramifiedExtensionRestriction K L.toGaloisSubextension
      (L.isUnramified_toGaloisSubextension D hUnramified))

/--
Establishes the identity `finiteUnramifiedRestriction D K L hUnramified (QuotientGroup.mk k) =
L.extensionQuotientMk k`.
-/
@[simp]
theorem finiteUnramifiedRestriction_mk
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) (k : K.field.toSubgroup) :
    finiteUnramifiedRestriction D K L hUnramified (QuotientGroup.mk k) =
      L.extensionQuotientMk k := by
  apply L.extensionQuotientMulEquiv.injective
  simp [finiteUnramifiedRestriction,
    maximalUnramifiedExtensionRestriction_mk,
    FiniteGaloisSubextension.toGaloisExtensionQuotientMulEquiv]
  exact L.toGaloisSubextension.extensionQuotientMk_apply k

/--
Establishes the identity `finiteUnramifiedRestriction D K L hUnramified (D.frobenius K) =
L.extensionQuotientMulEquiv.symm (D.unramifiedFrobenius K L.field L.below)`.
-/
@[simp]
theorem finiteUnramifiedRestriction_frobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    finiteUnramifiedRestriction D K L hUnramified (D.frobenius K) =
      L.extensionQuotientMulEquiv.symm
        (D.unramifiedFrobenius K L.field L.below) := by
  rw [finiteUnramifiedRestriction, MonoidHom.comp_apply,
    maximalUnramifiedRestriction_frobenius]
  apply L.extensionQuotientMulEquiv.injective
  simp [FiniteGaloisSubextension.toGaloisExtensionQuotientMulEquiv]
  exact
    L.toGaloisSubextension.extensionQuotientMulEquiv.apply_symm_apply
      (D.unramifiedFrobenius K L.field L.below)

private theorem finiteUnramifiedDegreeHom_killsExtension
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    extensionSubgroup K.field L.field L.below ≤
      (((zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property).comp
        (D.normalizedDegree K)).toMonoidHom).ker := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) :=
    L.finite
  intro k hk
  let E := L.toFiniteAbstractExtension
  let ER : FiniteResidueAbstractExtension D :=
    FiniteResidueAbstractExtension.ofInclusion D L.field K L.below
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  have hkL : k.1 ∈ L.field.toSubgroup :=
    (mem_extensionSubgroup_iff K.field L.field L.below k).1 hk
  let l : ER.field.field.toSubgroup :=
    ⟨k.1, by
      simpa [ER, FiniteResidueAbstractExtension.ofInclusion] using hkL⟩
  have hkl : Subgroup.inclusion ER.below l = k := Subtype.ext rfl
  have hd := D.frobeniusRestrictionNaturality_normalizedDegree ER l
  have hERUnramified : ER.toFiniteAbstractExtension.IsUnramified D := by
    simpa [ER, FiniteResidueAbstractExtension.ofInclusion,
      FiniteResidueAbstractExtension.toFiniteAbstractExtension,
      FiniteGaloisSubextension.IsUnramified,
      FiniteGaloisSubextension.toFiniteAbstractExtension] using hUnramified
  have hdegree :
      (ER.toFiniteAbstractExtension.degree : ℕ) = n := by
    change Nat.card ER.toFiniteAbstractExtension.quotient =
      Nat.card E.quotient
    apply Nat.card_congr
    change
      (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) ≃
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below)
    exact Equiv.refl _
  have hresidueDegree : (ER.residueDegree : ℕ) = n := by
    exact
      (ER.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified
        D hERUnramified).trans hdegree
  rw [hresidueDegree] at hd
  have hd' :
      (D.normalizedDegree K (Subgroup.inclusion ER.below l)).toAdd =
        n • (D.normalizedDegree ER.field l).toAdd := by
    change
      (D.normalizedDegree ER.base
        (Subgroup.inclusion ER.below l)).toAdd =
        n • (D.normalizedDegree ER.field l).toAdd
    exact hd
  change zHatReductionMul n hn (D.normalizedDegree K k) = 1
  apply Multiplicative.ext
  change zHatReduction n hn (D.normalizedDegree K k).toAdd = 0
  rw [← hkl, hd', map_nsmul]
  exact ZModModule.char_nsmul_eq_zero n _

/-- Normalized degree modulo `[L : K]` on a finite unramified Galois
quotient. -/
def finiteUnramifiedDegreeHom
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    L.extensionQuotient →*
      Multiplicative
        (ZMod (L.toFiniteAbstractExtension.degree : ℕ)) :=
  (QuotientGroup.lift (extensionSubgroup K.field L.field L.below)
      (((zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property).comp
        (D.normalizedDegree K)).toMonoidHom)
      (finiteUnramifiedDegreeHom_killsExtension D K L hUnramified)).comp
    L.extensionQuotientMulEquiv.toMonoidHom

/--
Establishes the identity `finiteUnramifiedDegreeHom D K L hUnramified (L.extensionQuotientMk k) =
zHatReductionMul (L.toFiniteAbstractExtension.degree : ℕ)
L.toFiniteAbstractExtension.degree.property (D.normalizedDegree K k)`.
-/
theorem finiteUnramifiedDegreeHom_mk
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (k : K.field.toSubgroup) :
    finiteUnramifiedDegreeHom D K L hUnramified
        (L.extensionQuotientMk k) =
      zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property
        (D.normalizedDegree K k) := by
  exact QuotientGroup.lift_mk' (extensionSubgroup K.field L.field L.below)
    (finiteUnramifiedDegreeHom_killsExtension D K L hUnramified) k

/--
The specified map is surjective: `Function.Surjective (finiteUnramifiedDegreeHom D K L
hUnramified)`.
-/
theorem finiteUnramifiedDegreeHom_surjective
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    Function.Surjective
      (finiteUnramifiedDegreeHom D K L hUnramified) := by
  intro z
  let E := L.toFiniteAbstractExtension
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  obtain ⟨w, hw⟩ := zHatReduction_surjective n hn z.toAdd
  obtain ⟨k, hk⟩ :=
    D.normalizedDegree_surjective K (Multiplicative.ofAdd w)
  refine ⟨L.extensionQuotientMk k, ?_⟩
  rw [finiteUnramifiedDegreeHom_mk D]
  apply Multiplicative.ext
  change zHatReduction n hn (D.normalizedDegree K k).toAdd = z.toAdd
  rw [hk]
  exact hw

/-- For an unramified finite extension, normalized degree modulo the
extension degree is an isomorphism. -/
def finiteUnramifiedDegreeEquiv
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    L.extensionQuotient ≃*
      Multiplicative (ZMod (L.toFiniteAbstractExtension.degree : ℕ)) := by
  let E := L.toFiniteAbstractExtension
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) :=
    L.finite
  apply MulEquiv.ofBijective
    (finiteUnramifiedDegreeHom D K L hUnramified)
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨finiteUnramifiedDegreeHom_surjective D
    K L hUnramified, ?_⟩
  calc
    Nat.card L.extensionQuotient =
        Nat.card
          (K.field.toSubgroup ⧸
            extensionSubgroup K.field L.field L.below) :=
      Nat.card_congr L.extensionQuotientMulEquiv.toEquiv
    _ =
        (extensionSubgroup K.field L.field L.below).index :=
      (Subgroup.index_eq_card _).symm
    _ = n := by
      change
        (extensionSubgroup E.base E.field E.below).index =
          (E.degree : ℕ)
      exact E.extensionSubgroup_index_eq_degree
    _ = Nat.card (ZMod n) := (Nat.card_zmod n).symm
    _ = Nat.card (Multiplicative (ZMod n)) :=
      (Nat.card_congr Multiplicative.toAdd).symm

/-- The maximal and finite normalized-degree isomorphisms commute with
restriction and reduction modulo `[L : K]`. -/
theorem finiteUnramifiedDegreeEquiv_restriction
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (x : K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :
    finiteUnramifiedDegreeEquiv D K L hUnramified
        (finiteUnramifiedRestriction D K L hUnramified x) =
      zHatReductionMul
        (L.toFiniteAbstractExtension.degree : ℕ)
        L.toFiniteAbstractExtension.degree.property
        (D.maximalUnramifiedDegreeEquiv K x) := by
  refine Quotient.inductionOn' x ?_
  intro k
  change finiteUnramifiedDegreeHom D K L hUnramified
      (L.extensionQuotientMk k) = _
  rw [finiteUnramifiedDegreeHom_mk D,
    D.maximalUnramifiedDegreeEquiv_mk]

/-- The arithmetic Frobenius has finite normalized degree one. -/
theorem finiteUnramifiedDegreeEquiv_unramifiedFrobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D) :
    finiteUnramifiedDegreeEquiv D K L hUnramified
        (L.extensionQuotientMulEquiv.symm
          (D.unramifiedFrobenius K L.field L.below)) =
      Multiplicative.ofAdd
        (1 : ZMod (L.toFiniteAbstractExtension.degree : ℕ)) := by
  rw [← finiteUnramifiedRestriction_frobenius D K L hUnramified,
    finiteUnramifiedDegreeEquiv_restriction D]
  rw [D.maximalUnramifiedDegreeEquiv_frobenius]
  apply Multiplicative.ext
  rfl

/-- Profinite exponentiation of the maximal-unramified Frobenius, expressed
through the canonical degree isomorphism with `ℤ̂`. -/
def maximalUnramifiedFrobeniusPower
    (D : DegreeData G) (K : FiniteResidueAbstractField D) (z : ZHat) :
    Additive (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :=
  (D.maximalUnramifiedDegreeEquiv K).toAdditive.symm z

/--
Establishes the identity `maximalUnramifiedFrobeniusPower D K 1 = Additive.ofMul (D.frobenius K)`.
-/
@[simp]
theorem maximalUnramifiedFrobeniusPower_one
    (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    maximalUnramifiedFrobeniusPower D K 1 =
      Additive.ofMul (D.frobenius K) := by
  rfl

end DegreeData

end DegreeOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

open DegreeData

namespace ValuationData

/-- A finite unramified reciprocity homomorphism which sends Frobenius to
the prime class intertwines the canonical valuation and normalized-degree
isomorphisms.  This is the generator calculation in the unramified norm-quotient equivalence,
expressed in the normalization needed. -/
theorem canonicalUnramifiedReciprocity_degree_of_generator
    (v : ValuationData D A)

    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ (hUnramified : L.IsUnramified D)
      (r : Additive L.extensionQuotient →+
        FiniteNormQuotient A K.field L.field L.below)
      (_hr : r (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L.field L.below)) =
        finiteNormClass A K.field L.field L.below (v.chosenPrimeElement K))
      (q : Additive L.extensionQuotient),
    v.canonicalUnramifiedNormQuotientValuation
        L.toFiniteAbstractFieldExtension hUnramified
        (r q) =
      (finiteUnramifiedDegreeEquiv D (K.toFiniteResidueAbstractField D)
        L hUnramified
        q.toMul).toAdd := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro hUnramified r hr q
  let KR := K.toFiniteResidueAbstractField D
  let g : Additive L.extensionQuotient :=
    Additive.ofMul (D.unramifiedFrobenius KR L.field L.below)
  let lhs : Additive L.extensionQuotient →+
      ZMod (L.toFiniteAbstractFieldExtension.degree : ℕ) :=
    (v.canonicalUnramifiedNormQuotientValuation
      L.toFiniteAbstractFieldExtension hUnramified).comp r
  let rhs : Additive L.extensionQuotient →+
      ZMod (L.toFiniteAbstractFieldExtension.degree : ℕ) :=
    (finiteUnramifiedDegreeEquiv D
      KR L hUnramified).toAdditive.toAddMonoidHom
  change lhs q = rhs q
  have hgen : lhs g = rhs g := by
    change v.canonicalUnramifiedNormQuotientValuation
        L.toFiniteAbstractFieldExtension hUnramified
        (r g) =
      (finiteUnramifiedDegreeEquiv D KR L hUnramified
        g.toMul).toAdd
    rw [show r g = finiteNormClass A K.field L.field L.below
        (v.chosenPrimeElement K) from hr]
    change v.canonicalUnramifiedValuationHom
      L.toFiniteAbstractFieldExtension
      (v.chosenPrimeElement K) = _
    change v.canonicalValueReduction
        (L.toFiniteAbstractFieldExtension.degree : ℕ)
        _ (v.valuationAt K (v.chosenPrimeElement K)) = _
    exact (congrArg
      (v.canonicalValueReduction (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property)
      (v.valuationAt_chosenPrimeElement K)).trans <|
      (v.canonicalValueReduction_one (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property).trans <|
        congrArg Multiplicative.toAdd
          (finiteUnramifiedDegreeEquiv_unramifiedFrobenius D
            KR L hUnramified).symm
  have hqmem : q ∈ AddSubgroup.zmultiples g := by
    rw [show AddSubgroup.zmultiples g = ⊤ from
      D.unramifiedFrobenius_zmultiples_eq_top
        KR L.field L.below hUnramified]
    trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hqmem
  rw [← hm, map_zsmul, map_zsmul, hgen]

/-- The maximal-unramified norm-residue symbol, given by the
valuation--Frobenius homomorphism. -/
def maximalUnramifiedNormResidueSymbol
    (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+
      Additive (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :=
  (D.maximalUnramifiedDegreeEquiv
    (K.toFiniteResidueAbstractField D)).toAdditive.symm.toAddMonoidHom.comp
    ((v.valueGroup).subtype.comp (v.valuationAt K))

/-- Applying normalized degree to the maximal-unramified symbol recovers the valuation. -/
@[simp]
theorem maximalUnramifiedNormResidue_degree
    (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    ((D.maximalUnramifiedDegreeEquiv (K.toFiniteResidueAbstractField D)
      (maximalUnramifiedNormResidueSymbol v K a).toMul).toAdd : ZHat) =
        (v.valuationAt K a : ZHat) := by
  change (D.maximalUnramifiedDegreeEquiv
      (K.toFiniteResidueAbstractField D)).toAdditive
      ((D.maximalUnramifiedDegreeEquiv
        (K.toFiniteResidueAbstractField D)).toAdditive.symm
        ((v.valueGroup).subtype (v.valuationAt K a))) =
    (v.valuationAt K a : ZHat)
  exact (D.maximalUnramifiedDegreeEquiv
    (K.toFiniteResidueAbstractField D)).toAdditive.apply_symm_apply
      ((v.valueGroup).subtype (v.valuationAt K a))

/-- The maximal-unramified symbol is literally the profinite power
`φ_K ^ v_K(a)`. -/
theorem maximalUnramifiedNormResidue_eq_frobeniusPower
    (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    maximalUnramifiedNormResidueSymbol v K a =
      maximalUnramifiedFrobeniusPower D (K.toFiniteResidueAbstractField D)
        (v.valuationAt K a : ZHat) := by
  rfl

/-- At every finite unramified quotient, normalized degree of the
maximal-unramified symbol is valuation reduced modulo the extension degree. -/
theorem maximalUnramifiedNormResidueSymbol_finiteDegree
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (hUnramified : L.IsUnramified D)
    (a : ambientFixedAddSubgroup A K.field) :
    (finiteUnramifiedDegreeEquiv D (K.toFiniteResidueAbstractField D)
      L hUnramified
      (finiteUnramifiedRestriction D
        (K.toFiniteResidueAbstractField D) L hUnramified
        (maximalUnramifiedNormResidueSymbol v K a).toMul)).toAdd =
      zHatReduction
        (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property
        (v.valuationAt K a : ZHat) := by
  let KR := K.toFiniteResidueAbstractField D
  have h := finiteUnramifiedDegreeEquiv_restriction D
    KR L hUnramified
      (maximalUnramifiedNormResidueSymbol v K a).toMul
  have hv := maximalUnramifiedNormResidue_degree v K a
  exact congrArg Multiplicative.toAdd h |>.trans (by
    change zHatReduction
        (L.toFiniteAbstractFieldExtension.degree : ℕ)
        L.toFiniteAbstractFieldExtension.degree.property
        ((D.maximalUnramifiedDegreeEquiv KR
          (maximalUnramifiedNormResidueSymbol v K a).toMul).toAdd) = _
    rw [hv])

/-- The maximal-unramified symbol extends every finite unramified reciprocity map: after
restriction to `G(L/K)`, applying finite reciprocity gives the class of the
original element.  This is the non-circular compatibility statement which
identifies the symbol with the inverse-limit norm-residue map. -/
theorem maximalUnramifiedNormResidueSymbol_finiteReciprocity_of_generator
    (v : ValuationData D A) (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ (hUnramified : L.IsUnramified D)
      (r : Additive L.extensionQuotient →+
        FiniteNormQuotient A K.field L.field L.below)
      (_hr : r (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L.field L.below)) =
        finiteNormClass A K.field L.field L.below (v.chosenPrimeElement K))
      (a : ambientFixedAddSubgroup A K.field),
    r (Additive.ofMul
        (finiteUnramifiedRestriction D
          (K.toFiniteResidueAbstractField D) L hUnramified
          (maximalUnramifiedNormResidueSymbol v K a).toMul)) =
      finiteNormClass A K.field L.field L.below a := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro hUnramified r hr a
  apply v.canonicalUnramifiedNormQuotientValuation_injective
    hAxiom L.toFiniteAbstractFieldExtension L.normal hUnramified
  rw [canonicalUnramifiedReciprocity_degree_of_generator v
    K L hUnramified r hr]
  change _ = v.canonicalUnramifiedValuationHom
    L.toFiniteAbstractFieldExtension a
  exact maximalUnramifiedNormResidueSymbol_finiteDegree v
    K L hUnramified a

/-- The finite restriction of the maximal-unramified symbol is the
inverse of finite unramified reciprocity.  The map `r` is kept explicit
here so this statement records the uniqueness argument of maximal-unramified reciprocity
without anticipating the final name of the finite reciprocity equivalence: the unramified
  norm-quotient equivalence
promotes any reciprocity map with the Frobenius--prime value to an
equivalence, and the preceding compatibility identifies its inverse. -/
theorem maximalUnramifiedNormResidueSymbol_finiteRestriction_of_generator
    (v : ValuationData D A) (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field L.field L.below) := L.finite
    ∀ (hUnramified : L.IsUnramified D)
      (r : Additive L.extensionQuotient →+
        FiniteNormQuotient A K.field L.field L.below)
      (hr : r (Additive.ofMul (D.unramifiedFrobenius
          (K.toFiniteResidueAbstractField D) L.field L.below)) =
        finiteNormClass A K.field L.field L.below (v.chosenPrimeElement K))
      (a : ambientFixedAddSubgroup A K.field),
    (v.unramifiedReciprocityEquivOfGenerator hAxiom K L.field L.below
        hUnramified r hr).symm
        (finiteNormClass A K.field L.field L.below a) =
      Additive.ofMul
        (finiteUnramifiedRestriction D
          (K.toFiniteResidueAbstractField D) L hUnramified
          (maximalUnramifiedNormResidueSymbol v K a).toMul) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) := L.finite
  intro hUnramified r hr a
  apply (v.unramifiedReciprocityEquivOfGenerator hAxiom K L.field L.below
    hUnramified r hr).injective
  rw [AddEquiv.apply_symm_apply]
  exact (maximalUnramifiedNormResidueSymbol_finiteReciprocity_of_generator v hAxiom
    K L hUnramified r hr a).symm

end ValuationData

end Representation

end ClassFormation
