/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Relative Norm Double Coset -/
universe u

namespace ClassFormation

open KummerTheory

/-!
# The abstract reciprocity construction: the double-coset decomposition of a relative norm

The norm calculation in the proof of transfer--norm naturality partitions
the left cosets for an extension by the orbits of an intermediate subgroup.
This file constructs that partition from Mathlib's class-formula equivalence
and reindexes the actual relative norm along it.
-/

noncomputable section

open scoped BigOperators

open CyclicCohomology MulAction

section doubleCosetEquivalences

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Membership in the stabilizer of a left coset is the literal conjugate
intersection condition.  For the representative `t⁻¹` this reads
`k' ∈ K' ∩ t⁻¹ S t`, the subgroup occurring in the classical
double-coset norm calculation. -/
theorem mem_relativeNormDoubleCoset_stabilizer_iff
    (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (t : K.toSubgroup)
    (k' : extensionSubgroup K K' hK'K) :
    k' ∈ MulAction.stabilizer (extensionSubgroup K K' hK'K)
        (QuotientGroup.mk t :
          K.toSubgroup ⧸ extensionSubgroup K S hSK) ↔
      t.1⁻¹ * k'.1.1 * t.1 ∈ S.toSubgroup := by
  rw [mem_stabilizer_iff]
  change QuotientGroup.mk (k'.1 * t) = QuotientGroup.mk t ↔ _
  rw [QuotientGroup.eq]
  change (k'.1 * t).1⁻¹ * t.1 ∈ S.toSubgroup ↔ _
  constructor
  · intro h
    have hi := S.toSubgroup.inv_mem h
    simpa [mul_assoc] using hi
  · intro h
    have hi := S.toSubgroup.inv_mem h
    simpa [mul_assoc] using hi

/-- The class-formula decomposition of the left cosets for `S | K` into
orbits under the subgroup belonging to `K' | K` and the corresponding
stabilizer cosets.  These orbits are the double cosets used. -/
noncomputable def relativeNormDoubleCosetEquiv
    (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    (K.toSubgroup ⧸ extensionSubgroup K S hSK) ≃
      Σ q : Quotient (orbitRel (extensionSubgroup K K' hK'K)
        (K.toSubgroup ⧸ extensionSubgroup K S hSK)),
        (extensionSubgroup K K' hK'K) ⧸
          MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out :=
  MulAction.selfEquivSigmaOrbitsQuotientStabilizer
    (extensionSubgroup K K' hK'K)
    (K.toSubgroup ⧸ extensionSubgroup K S hSK)

/-- The inverse class-formula map is left multiplication of the selected
orbit representative by the selected stabilizer-coset representative. -/
@[simp]
theorem relativeNormDoubleCosetEquiv_symm_apply
    (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (q : Quotient (orbitRel (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK)))
    (r : (extensionSubgroup K K' hK'K) ⧸
      MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out) :
    (relativeNormDoubleCosetEquiv K K' S hSK hK'K).symm ⟨q, r⟩ =
      r.out • q.out := by
  change (((MulAction.orbitEquivQuotientStabilizer
    (extensionSubgroup K K' hK'K) q.out).symm r :
      MulAction.orbit (extensionSubgroup K K' hK'K) q.out) :
        K.toSubgroup ⧸ extensionSubgroup K S hSK) = _
  refine Quotient.inductionOn' r ?_
  intro s
  calc
    (((MulAction.orbitEquivQuotientStabilizer
        (extensionSubgroup K K' hK'K) q.out).symm
          (QuotientGroup.mk s) :
        MulAction.orbit (extensionSubgroup K K' hK'K) q.out) :
          K.toSubgroup ⧸ extensionSubgroup K S hSK) = s • q.out :=
      MulAction.orbitEquivQuotientStabilizer_symm_apply
        (extensionSubgroup K K' hK'K) q.out s
    _ = (QuotientGroup.mk s).out • q.out := by
      symm
      simpa only [MulAction.ofQuotientStabilizer_mk] using
        congrArg
          (MulAction.ofQuotientStabilizer
            (extensionSubgroup K K' hK'K) q.out)
          (QuotientGroup.out_eq' (QuotientGroup.mk s))

end doubleCosetEquivalences

/-- The class-formula inverse for an arbitrary chosen representative of
each orbit.  This form is used in transfer--norm naturality to choose the norm
representative `t⁻¹` attached to a transfer representative `t`. -/
@[simp]
theorem chosenOrbitClassEquiv_symm_apply
    {M : Type*} {X : Type*} [Group M] [MulAction M X]
    {φ : Quotient (orbitRel M X) → X}
    (hφ : Function.LeftInverse Quotient.mk'' φ)
    (q : Quotient (orbitRel M X))
    (r : M ⧸ stabilizer M (φ q)) :
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' M X hφ).symm
        ⟨q, r⟩ = r.out • φ q := by
  change (((MulAction.orbitEquivQuotientStabilizer M (φ q)).symm r :
      orbit M (φ q)) : X) = _
  refine Quotient.inductionOn' r ?_
  intro m
  calc
    (((MulAction.orbitEquivQuotientStabilizer M (φ q)).symm
        (QuotientGroup.mk m) : orbit M (φ q)) : X) = m • φ q :=
      MulAction.orbitEquivQuotientStabilizer_symm_apply M (φ q) m
    _ = (QuotientGroup.mk m).out • φ q := by
      symm
      simpa only [MulAction.ofQuotientStabilizer_mk] using
        congrArg (MulAction.ofQuotientStabilizer M (φ q))
          (QuotientGroup.out_eq' (QuotientGroup.mk m))

section relativeNormFormulas

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The relative norm reindexed by arbitrary chosen representatives of the
intermediate-subgroup orbits. -/
theorem relativeNorm_eq_sum_chosenOrbit_of_fintype
    (A : Rep ℤ G) (K S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (M : Subgroup K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)]
    {φ : Quotient (orbitRel M
      (K.toSubgroup ⧸ extensionSubgroup K S hSK)) →
        (K.toSubgroup ⧸ extensionSubgroup K S hSK)}
    (hφ : Function.LeftInverse Quotient.mk'' φ)
    [Fintype (Quotient (orbitRel M
      (K.toSubgroup ⧸ extensionSubgroup K S hSK)))]
    [(q : Quotient (orbitRel M
      (K.toSubgroup ⧸ extensionSubgroup K S hSK))) →
      Fintype (M ⧸ stabilizer M (φ q))]
    (a : ambientFixedAddSubgroup A S) :
    ((relativeNorm A K S hSK a : ambientFixedAddSubgroup A K) : A.V) =
      ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
          M (K.toSubgroup ⧸ extensionSubgroup K S hSK) hφ).symm ⟨q, r⟩) := by
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K S hSK)
  rw [relativeNorm_apply_coe, relativeNormValue]
  let e := MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
    M (K.toSubgroup ⧸ extensionSubgroup K S hSK) hφ
  calc
    ∑ q, relativeCosetAction A K S hSK a q =
        ∑ p, relativeCosetAction A K S hSK a (e.symm p) :=
      (e.symm.sum_comp (relativeCosetAction A K S hSK a)).symm
    _ = _ := Fintype.sum_sigma _

@[implicit_reducible]
private noncomputable def relativeNormDoubleCosetSigmaFintype
    (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)] :
    Fintype (Σ q : Quotient (orbitRel
      (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK)),
      (extensionSubgroup K K' hK'K) ⧸
        MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out) := by
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K S hSK)
  exact Fintype.ofEquiv
    (K.toSubgroup ⧸ extensionSubgroup K S hSK)
    (relativeNormDoubleCosetEquiv K K' S hSK hK'K)

@[implicit_reducible]
private noncomputable def relativeNormDoubleCosetOrbitFintype
    (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)] :
    Fintype (Quotient (orbitRel (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK))) := by
  letI := relativeNormDoubleCosetSigmaFintype K K' S hSK hK'K
  exact Fintype.ofInjective
    (fun q => (⟨q, QuotientGroup.mk 1⟩ :
      Σ q : Quotient (orbitRel (extensionSubgroup K K' hK'K)
        (K.toSubgroup ⧸ extensionSubgroup K S hSK)),
        (extensionSubgroup K K' hK'K) ⧸
          MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out)) (by
      intro q q' h
      exact congrArg Sigma.fst h)

@[implicit_reducible]
private noncomputable def relativeNormDoubleCosetStabilizerFintype
    (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)]
    (q : Quotient (orbitRel (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK))) :
    Fintype ((extensionSubgroup K K' hK'K) ⧸
      MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out) := by
  letI := relativeNormDoubleCosetSigmaFintype K K' S hSK hK'K
  exact Fintype.ofInjective
    (fun r => (⟨q, r⟩ :
      Σ q : Quotient (orbitRel (extensionSubgroup K K' hK'K)
        (K.toSubgroup ⧸ extensionSubgroup K S hSK)),
        (extensionSubgroup K K' hK'K) ⧸
          MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out)) (by
      intro r r' h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- The double-coset norm formula with caller-supplied finite enumerations
of the orbit set and the stabilizer cosets.  This form is convenient in
arguments which already obtained those enumerations from a transfer
formula; the result is independent of their ordering. -/
theorem relativeNorm_eq_sum_doubleCoset_of_fintype
    (A : Rep ℤ G) (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)]
    [Fintype (Quotient (orbitRel (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK)))]
    [(q : Quotient (orbitRel (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK))) →
      Fintype ((extensionSubgroup K K' hK'K) ⧸
        MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out)]
    (a : ambientFixedAddSubgroup A S) :
    ((relativeNorm A K S hSK a : ambientFixedAddSubgroup A K) : A.V) =
      ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((relativeNormDoubleCosetEquiv K K' S hSK hK'K).symm ⟨q, r⟩) := by
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K S hSK)
  rw [relativeNorm_apply_coe, relativeNormValue]
  calc
    ∑ q, relativeCosetAction A K S hSK a q =
        ∑ p, relativeCosetAction A K S hSK a
          ((relativeNormDoubleCosetEquiv K K' S hSK hK'K).symm p) :=
      ((relativeNormDoubleCosetEquiv K K' S hSK hK'K).symm.sum_comp
        (relativeCosetAction A K S hSK a)).symm
    _ = ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((relativeNormDoubleCosetEquiv K K' S hSK hK'K).symm ⟨q, r⟩) :=
      Fintype.sum_sigma _

/-- The actual norm `N_{S/K}` reindexed first by intermediate-subgroup
orbits and then by stabilizer cosets.  This is the additive form of the
double-coset product decomposition in the proof of transfer--norm naturality. -/
theorem relativeNorm_eq_sum_doubleCoset
    (A : Rep ℤ G) (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)]
    (a : ambientFixedAddSubgroup A S) :
    let Ω := Quotient (orbitRel (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK))
    letI : Fintype Ω :=
      relativeNormDoubleCosetOrbitFintype K K' S hSK hK'K
    letI (q : Ω) : Fintype ((extensionSubgroup K K' hK'K) ⧸
        MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out) :=
      relativeNormDoubleCosetStabilizerFintype K K' S hSK hK'K q
    ((relativeNorm A K S hSK a : ambientFixedAddSubgroup A K) : A.V) =
      ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((relativeNormDoubleCosetEquiv K K' S hSK hK'K).symm ⟨q, r⟩) := by
  dsimp only
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K S hSK)
  let : Fintype (Quotient (orbitRel
      (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK))) :=
    relativeNormDoubleCosetOrbitFintype K K' S hSK hK'K
  let (q : Quotient (orbitRel (extensionSubgroup K K' hK'K)
      (K.toSubgroup ⧸ extensionSubgroup K S hSK))) :
      Fintype ((extensionSubgroup K K' hK'K) ⧸
        MulAction.stabilizer (extensionSubgroup K K' hK'K) q.out) :=
    relativeNormDoubleCosetStabilizerFintype K K' S hSK hK'K q
  exact relativeNorm_eq_sum_doubleCoset_of_fintype
    A K K' S hSK hK'K a

end relativeNormFormulas

end
end ClassFormation
