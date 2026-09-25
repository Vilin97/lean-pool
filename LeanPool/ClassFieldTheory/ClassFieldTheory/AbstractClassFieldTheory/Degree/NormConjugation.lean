/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse

/-! # Norm Conjugation -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Conjugation and relative norms

These are the field-conjugation and norm identities used in the abstract reciprocity
  construction and theorem.  They belong before the reciprocity construction: their proofs
use only the actual relative norm and the conjugation action.
-/

noncomputable section

open scoped BigOperators

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Conjugation preserves inclusions of abstract fields. -/
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup := by
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  rw [conjugateClosedSubgroup_mem] at hx ⊢
  exact hLK hx

/-- Conjugation by `s⁻¹` identifies a field subgroup with the subgroup
representing its right conjugate `K^s`. -/
def conjugateSubgroupEquiv [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) :
    K.toSubgroup ≃* (conjugateClosedSubgroup K s).toSubgroup where
  toFun k := ⟨s⁻¹ * k.1 * s, by
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
    rw [conjugateClosedSubgroup_mem]
    convert k.2 using 1
    simp [mul_assoc]⟩
  invFun x := ⟨s * x.1 * s⁻¹,
    (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Establishes the identity `(conjugateSubgroupEquiv K s k).1 = s⁻¹ * k.1 * s`. -/
@[simp]
theorem conjugateSubgroupEquiv_apply_coe [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) (k : K.toSubgroup) :
    (conjugateSubgroupEquiv K s k).1 = s⁻¹ * k.1 * s :=
  rfl

/-- Conjugation carries the subgroup for `L/K` exactly to the subgroup for
`L^s/K^s`. -/
theorem map_extensionSubgroup_conjugate [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (extensionSubgroup K L hLK).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup L s
    rw [conjugateClosedSubgroup_mem]
    simpa [mul_assoc] using hk
  · intro hx
    refine ⟨(conjugateSubgroupEquiv K s).symm x, ?_, ?_⟩
    · change s * x.1 * s⁻¹ ∈ L.toSubgroup
      exact (conjugateClosedSubgroup_mem L s x.1).mp hx
    · exact (conjugateSubgroupEquiv K s).apply_symm_apply x

/-- Conjugation identifies the relative coset spaces even when the
extension is not normal. -/
noncomputable def relativeConjugateCosetEquiv [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  Quotient.congr (conjugateSubgroupEquiv K s).toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    let e := conjugateSubgroupEquiv K s
    let H := extensionSubgroup K L hLK
    let Hs := extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
    have hmap : H.map e.toMonoidHom = Hs :=
      map_extensionSubgroup_conjugate K L hLK s
    change x⁻¹ * y ∈ H ↔ (e x)⁻¹ * e y ∈ Hs
    rw [← hmap]
    constructor
    · intro hxy
      refine ⟨x⁻¹ * y, hxy, ?_⟩
      simp
    · rintro ⟨z, hz, hez⟩
      have heq : z = x⁻¹ * y := by
        apply e.injective
        simpa using hez
      simpa [heq] using hz)

/--
Establishes the identity `relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
QuotientGroup.mk (conjugateSubgroupEquiv K s k)`.
-/
@[simp]
theorem relativeConjugateCosetEquiv_mk [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (k : K.toSubgroup) :
    relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) :=
  rfl

/-- A conjugate of a Galois extension is Galois. -/
instance conjugateExtension_normal [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).Normal := by
  rw [← map_extensionSubgroup_conjugate K L hLK s]
  exact Subgroup.Normal.map hLnormal
    (conjugateSubgroupEquiv K s).toMonoidHom
    (conjugateSubgroupEquiv K s).surjective

/-- The left vertical isomorphism in the conjugation diagram of
norm--conjugation naturality, `τ ↦ s⁻¹τs`. -/
noncomputable def finiteReciprocityNaturalityConjugation
    [ContinuousMul G] (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  QuotientGroup.congr
    (extensionSubgroup K L hLK)
    (extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s))
    (conjugateSubgroupEquiv K s)
    (map_extensionSubgroup_conjugate K L hLK s)

/--
Establishes the identity `finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k) =
QuotientGroup.mk (conjugateSubgroupEquiv K s k)`.
-/
@[simp]
theorem finiteReciprocityNaturalityConjugation_mk [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) := by
  exact QuotientGroup.congr_mk' _ _ _ _ k

/-- Conjugation preserves finiteness of the Galois quotient. -/
theorem finite_conjugateExtension [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
  Finite.of_equiv
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (relativeConjugateCosetEquiv K L hLK s)

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Conjugation intertwines the two relative coset actions. -/
private theorem relativeCosetAction_conjugate
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a)
        (relativeConjugateCosetEquiv K L hLK s q) =
      A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeConjugateCosetEquiv_mk, relativeCosetAction_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    A.ρ (s⁻¹ * k.1 * s) (A.ρ s⁻¹ a.1) =
        A.ρ ((s⁻¹ * k.1 * s) * s⁻¹) a.1 := by
      have hm := congrArg (fun φ => φ a.1)
        (map_mul A.ρ (s⁻¹ * k.1 * s) s⁻¹)
      exact hm.symm
    _ = A.ρ (s⁻¹ * k.1) a.1 := by
      congr 2
      simp [mul_assoc]
    _ = A.ρ s⁻¹ (A.ρ k.1 a.1) := by
      exact congrArg (fun φ => φ a.1) (map_mul A.ρ s⁻¹ k.1)

/-- Relative norms commute with the right conjugation used in the second
diagram of norm--conjugation naturality:
`N_{L^s/K^s}(a^s) = N_{L/K}(a)^s`. -/
theorem relativeNorm_conjugate_apply
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    relativeNorm A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a) =
      conjugateFixedElement A K s (relativeNorm A K L hLK a) := by
  let hConj := conjugateClosedSubgroup_mono hLK s
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e := relativeConjugateCosetEquiv K L hLK s
  let conjugateFintype : Fintype
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) :=
    Fintype.ofEquiv (K.toSubgroup ⧸ extensionSubgroup K L hLK) e
  have hconjugateFintype : Fintype.ofFinite
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) = conjugateFintype :=
    Subsingleton.elim _ _
  apply Subtype.ext
  simp only [relativeNorm_apply_coe, relativeNormValue,
    conjugateFixedElement_coe]
  rw [hconjugateFintype]
  calc
    ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) q =
      ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) (e q) := by
          exact (e.sum_comp fun q =>
            relativeCosetAction A (conjugateClosedSubgroup K s)
              (conjugateClosedSubgroup L s) hConj
              (conjugateFixedElement A L s a) q).symm
    _ = ∑ q, A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact relativeCosetAction_conjugate A K L hLK s a q
    _ = A.ρ s⁻¹ (∑ q, relativeCosetAction A K L hLK a q) := by
      rw [map_sum]

end Representation

end
end ClassFormation
