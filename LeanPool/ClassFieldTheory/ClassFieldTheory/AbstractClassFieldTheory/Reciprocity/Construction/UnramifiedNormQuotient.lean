/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence

/-! # Unramified Norm Quotient -/

@[expose] public section
universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence: the
  unramified norm quotient

For a finite unramified Galois extension `L / K`, normalized valuation
identifies the actual norm quotient `A_K / N_{L/K} A_L` with
`ℤ / [L : K]ℤ`.  The only non-formal part of injectivity is the unit
correction: the unit-cohomology axiom (`H⁰ = 0`) makes every unit of `K` the norm
of a unit of `L`.
-/

noncomputable
section

section unramifiedFrobenius

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The degree-one lift `φ_K` used in the unramified norm-quotient equivalence. -/
def chosenUnramifiedFrobeniusLift
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.FrobeniusElements K L hLK := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ZHat)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ZHat)))
  refine ⟨QuotientGroup.mk φ, 1, Nat.zero_lt_one, ?_⟩
  rw [D.extensionNormalizedDegree_mk K L hLK φ, hφ, pow_one]

/--
Establishes the identity `D.frobeniusExponent K L hLK (D.chosenUnramifiedFrobeniusLift K L hLK) =
1`.
-/
@[simp]
theorem chosenUnramifiedFrobeniusLift_exponent
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.frobeniusExponent K L hLK
      (D.chosenUnramifiedFrobeniusLift K L hLK) = 1 := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK
          (D.chosenUnramifiedFrobeniusLift K L hLK) =
      D.extensionNormalizedDegree K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK)).symm
    _ = Multiplicative.ofAdd (1 : ZHat) := by
      change D.normalizedDegree K
          (Classical.choose
            (D.normalizedDegree_surjective K
              (Multiplicative.ofAdd (1 : ZHat)))) = _
      exact Classical.choose_spec
        (D.normalizedDegree_surjective K
          (Multiplicative.ofAdd (1 : ZHat)))
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^ 1 := (pow_one _).symm

/-- The arithmetic Frobenius `φ_{L/K}`, obtained by restricting `φ_K`. -/
def unramifiedFrobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK :=
  D.frobeniusRestriction K L hLK
    (D.chosenUnramifiedFrobeniusLift K L hLK)

/-- In an unramified extension, arithmetic Frobenius generates the actual
finite Galois quotient. -/
theorem unramifiedFrobenius_generates
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    ∀ x : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      x ∈ Subgroup.zpowers (D.unramifiedFrobenius K L hLK) := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ZHat)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ZHat)))
  simpa only [unramifiedFrobenius, chosenUnramifiedFrobeniusLift, φ,
    frobeniusRestriction, extensionRestriction_mk] using
    D.quotient_generator_of_unramified_degree_one
      K L hLK hUnramified φ hφ

/-- Additive form of the preceding generator statement, matching the
domain of the reciprocity homomorphism in the finite reciprocity equivalence. -/
theorem unramifiedFrobenius_zmultiples_eq_top
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    AddSubgroup.zmultiples
      (Additive.ofMul (D.unramifiedFrobenius K L hLK)) = ⊤ := by
  ext x
  constructor
  · intro _
    exact AddSubgroup.mem_top x
  · intro _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (D.unramifiedFrobenius_generates K L hLK hUnramified x.toMul)
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    change Additive.ofMul
      ((D.unramifiedFrobenius K L hLK) ^ m) = x
    exact congrArg Additive.ofMul hm

end DegreeData

end unramifiedFrobenius

section valuationQuotient

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

private theorem valueModulo_eq_zero_iff
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n)
    (z : v.valueGroup) :
    v.valueModulo n hn z = 0 ↔ ∃ w : v.valueGroup, z = n • w := by
  constructor
  · intro hz
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) z = 0 := by
      apply (v.cyclicValueQuotients n hn).injective
      change v.valueModulo n hn z = v.valueModulo n hn 0
      rw [hz, map_zero]
    obtain ⟨w, hw⟩ :=
      (QuotientAddGroup.eq_zero_iff z).1 hq
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, rfl⟩
    have hq :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w) = 0 := by
      apply (QuotientAddGroup.eq_zero_iff _).2
      exact ⟨w, rfl⟩
    change (v.cyclicValueQuotients n hn)
        ((QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)) (n • w)) = 0
    rw [hq, map_zero]

/-- The normalized valuation reduced modulo the finite extension degree. -/
def unramifiedValuationHom
    (v : ValuationData D A) (K : FiniteAbstractField G)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    ambientFixedAddSubgroup A K.field →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  (v.valueModulo
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)
      (FiniteAbstractFieldExtension.ofInclusion L K hLK).degree.property).comp
    (v.valuationAt K)

private theorem finiteNormSubgroup_le_unramifiedValuationHom_ker
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    finiteNormSubgroup A K.field L hLK ≤
      (v.unramifiedValuationHom K L hLK).ker := by
  rintro _ ⟨a, rfl⟩
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  have htower := v.normalizedValuation_tower E a
  change (E.residueDegree D : ℕ) • _ = _ at htower
  rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
  have hval : v.valuationAt K (relativeNorm A K.field L hLK a) =
      n • v.valuationAt E.field a := by
    apply Subtype.ext
    exact htower.symm
  change v.valueModulo n E.degree.property
      (v.valuationAt K (relativeNorm A K.field L hLK a)) = 0
  rw [hval]
  exact (v.valueModulo_eq_zero_iff n E.degree.property _).2
    ⟨v.valuationAt E.field a, rfl⟩

/-- The valuation map induced on the finite norm quotient. -/
def unramifiedNormQuotientValuation
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    FiniteNormQuotient A K.field L hLK →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  finiteNormQuotientLift A K.field L hLK
    (v.unramifiedValuationHom K L hLK)
    (by exact v.finiteNormSubgroup_le_unramifiedValuationHom_ker K L hLK hUnramified)

/--
Establishes the identity `v.unramifiedNormQuotientValuation K L hLK hUnramified (finiteNormClass A
K.field L hLK a) = v.unramifiedValuationHom K L hLK a`.
-/
@[simp]
theorem unramifiedNormQuotientValuation_finiteNormClass
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (a : ambientFixedAddSubgroup A K.field) :
    v.unramifiedNormQuotientValuation K L hLK hUnramified
        (finiteNormClass A K.field L hLK a) =
      v.unramifiedValuationHom K L hLK a :=
  rfl

/--
The specified map is surjective: `Function.Surjective (v.unramifiedNormQuotientValuation K L hLK
hUnramified)`.
-/
theorem unramifiedNormQuotientValuation_surjective
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Function.Surjective
      (v.unramifiedNormQuotientValuation K L hLK hUnramified) := by
  intro z
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  obtain ⟨c, hc⟩ :=
    v.valueModulo_surjective n E.degree.property z
  obtain ⟨a, ha⟩ := v.normalizedValuation_surjective K c
  refine ⟨finiteNormClass A K.field L hLK a, ?_⟩
  rw [v.unramifiedNormQuotientValuation_finiteNormClass]
  change v.valueModulo n E.degree.property
      (v.valuationAt K a) = z
  rw [ha]
  exact hc

/-- The unit argument: modulo valuation, the unit-cohomology axiom makes the
remaining unit an actual norm. -/
theorem unramifiedNormQuotientValuation_injective
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Function.Injective
      (v.unramifiedNormQuotientValuation K L hLK hUnramified) := by
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  have hkernel : ∀ q : FiniteNormQuotient A K.field L hLK,
      v.unramifiedNormQuotientValuation K L hLK hUnramified q = 0 → q = 0 := by
    intro q
    refine FiniteNormQuotient.induction_on A K.field L hLK q ?_
    intro a ha
    change v.unramifiedValuationHom K L hLK a = 0 at ha
    change v.valueModulo n E.degree.property
        (v.valuationAt K a) = 0 at ha
    obtain ⟨z, haz⟩ :=
      (v.valueModulo_eq_zero_iff n E.degree.property
        (v.valuationAt K a)).1 ha
    obtain ⟨b, hb⟩ := v.normalizedValuation_surjective E.field z
    let normb : ambientFixedAddSubgroup A K.field :=
      relativeNorm A K.field L hLK b
    have htower := v.normalizedValuation_tower E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
    have hnormb : v.valuationAt K normb = n • z := by
      apply Subtype.ext
      calc
        ((v.valuationAt K normb : v.valueGroup) : ZHat) =
            n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) := htower.symm
        _ = n • ((z : v.valueGroup) : ZHat) := by rw [hb]
        _ = (((n • z : v.valueGroup)) : ZHat) := rfl
    let u : v.unitAddSubgroup K :=
      ⟨a - normb, by
        rw [v.mem_unitAddSubgroup_iff, map_sub, haz, hnormb, sub_self]⟩
    let KR := K.toFiniteResidueAbstractField D
    let : (extensionSubgroup KR.field L hLK).Normal := by
      change (extensionSubgroup K.field L hLK).Normal
      exact hnormal
    let : Finite
        (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
      change Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)
      exact hfinite
    obtain ⟨g, hg⟩ :=
      D.exists_quotient_generator_of_unramified
        KR L hLK hUnramified
    let : Fintype
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
      Fintype.ofFinite _
    let Euc : FiniteUnramifiedCyclicExtension D K :=
      { field := L
        below := hLK
        normal := hnormal
        finite := hfinite
        generator := g
        generates := hg
        unramified := hUnramified }
    have hzero :
        CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) 0) ∧
          CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) (-1)) :=
      hAxiom K Euc
    obtain ⟨ε, hε⟩ :=
      v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
        Euc.toFiniteAbstractFieldExtension Euc.normal
          Euc.toFiniteAbstractFieldExtension_isUnramified
          g hg hzero.1 u
    change v.unitAddSubgroup E.field at ε
    change relativeNorm A K.field L hLK ε.1 = u.1 at hε
    apply (finiteNormClass_eq_zero_iff A K.field L hLK a).2
    refine ⟨b + ε.1, ?_⟩
    rw [map_add, hε]
    change normb + (a - normb) = a
    abel
  intro x y hxy
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hxy, sub_self]

/-- **the unramified norm-quotient equivalence (valuation part).**  For finite unramified `L / K`,
valuation induces `A_K / N_{L/K}A_L ≃ ℤ/[L:K]ℤ`. -/
def unramifiedReciprocityValuationEquiv
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    FiniteNormQuotient A K.field L hLK ≃+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  AddEquiv.ofBijective
    (v.unramifiedNormQuotientValuation K L hLK hUnramified)
    ⟨v.unramifiedNormQuotientValuation_injective hAxiom K L hLK
        hUnramified,
      v.unramifiedNormQuotientValuation_surjective K L hLK hUnramified⟩

/-- A prime class has exact additive order `[L : K]` in an unramified
norm quotient.  The lower bound is read after reduction in `ℤ̂/nℤ̂`; the
upper bound is the norm of the included prime. -/
theorem primeClass_addOrderOf
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    addOrderOf
      (finiteNormClass A K.field L hLK π) =
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) := by
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  let g : FiniteNormQuotient A K.field L hLK :=
    finiteNormClass A K.field L hLK π
  have hn : 0 < n := E.degree.property
  have hng : n • g = 0 := by
    change n • finiteNormClass A K.field L hLK π = 0
    rw [← finiteNormClass_nsmul]
    apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
    refine ⟨fixedFieldInclusion A K.field L hLK π, ?_⟩
    have hnorm :=
      relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension π
    change relativeNorm A K.field L hLK
        (fixedFieldInclusion A K.field L hLK π) = n • π at hnorm
    exact hnorm
  have hdiv : ∀ m : ℕ, m • g = 0 → n ∣ m := by
    intro m hm
    have hm' :
        finiteNormClass A K.field L hLK (m • π) = 0 := by
      simpa [g] using hm
    have hmNorm := (finiteNormClass_eq_zero_iff A K.field L hLK _).1 hm'
    obtain ⟨b, hb⟩ := hmNorm
    have htower := v.normalizedValuation_tower E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
    have hval :
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZHat) := by
      calc
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
            ((v.valuationAt K (relativeNorm A K.field L hLK b) :
              v.valueGroup) : ZHat) := htower
        _ = ((v.valuationAt K (m • π) : v.valueGroup) : ZHat) := by
          rw [hb]
        _ = m • ((v.valuationAt K π : v.valueGroup) : ZHat) := by
          exact congrArg Subtype.val (map_nsmul (v.valuationAt K) m π)
        _ = m • (1 : ZHat) := by rw [hπ, v.oneValue_coe]
    have hred := congrArg (fun z : ZHat => zHatReduction n hn z) hval
    have hredOne : zHatReduction n hn (1 : ZHat) = 1 := rfl
    have hred' :
        n • zHatReduction n hn
            ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZMod n) := by
      simpa only [map_nsmul, hredOne] using hred
    have hmzero : (m : ZMod n) = 0 := by
      have hmzero' : m • (1 : ZMod n) = 0 := by
        rw [← hred']
        simp [nsmul_eq_mul]
      simpa using hmzero'
    exact (ZMod.natCast_eq_zero_iff m n).1 hmzero
  apply Nat.dvd_antisymm
  · exact (addOrderOf_dvd_iff_nsmul_eq_zero).2 hng
  · exact hdiv (addOrderOf g) (addOrderOf_nsmul_eq_zero g)

/-- The prime class generates the full unramified norm quotient, as in the
last sentence of the proof of the unramified norm-quotient equivalence. -/
theorem primeClass_zmultiples_eq_top
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    AddSubgroup.zmultiples
      (finiteNormClass A K.field L hLK π) = ⊤ := by
  let e := v.unramifiedReciprocityValuationEquiv hAxiom K L hLK hUnramified
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let : NeZero (E.degree : ℕ) :=
    ⟨E.degree.property.ne'⟩
  let : Finite (FiniteNormQuotient A K.field L hLK) :=
    Finite.of_equiv (ZMod (E.degree : ℕ)) (by
      simpa [E] using e.symm.toEquiv)
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples,
    v.primeClass_addOrderOf K L hLK hUnramified π hπ]
  exact ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)).symm

end ValuationData

end valuationQuotient

end
end ClassFormation
