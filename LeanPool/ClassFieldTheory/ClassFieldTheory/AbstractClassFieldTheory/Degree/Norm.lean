/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.GroupTheory.Index
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Abstract.KummerDelta

/-! # Norm -/

@[expose] public section
namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# normalized degree and Frobenius theory: norms on abstract fields

This file constructs the norm attached to a finite extension of the
abstract fields.  An abstract field is represented, as in, by a closed
subgroup of the ambient profinite group.  The norm is the sum over left
cosets (the additive form of the multiplicative product), so it does
not require the extension to be Galois.
-/

noncomputable
section

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes `G` to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The value of a fixed coefficient at a left coset.  This is independent
of the representative precisely because the coefficient is fixed by the
smaller abstract-field subgroup. -/
def relativeCosetAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) : A.V :=
  Quotient.liftOn' q (fun k : K.toSubgroup => A.ρ k.1 a.1) (by
    intro x y hxy
    have hmem : x⁻¹ * y ∈ extensionSubgroup K L hLK :=
      QuotientGroup.leftRel_apply.mp hxy
    let l : L.toSubgroup := ⟨(x⁻¹ * y).1, hmem⟩
    have hy : y = x * ⟨l.1, hLK l.2⟩ := by
      apply Subtype.ext
      simp [l]
    rw [hy]
    change A.ρ x.1 a.1 = A.ρ (x.1 * l.1) a.1
    rw [map_mul]
    change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ l.1 a.1)
    rw [a.2 l])

/-- The relative coset action on a quotient representative is the corresponding group action. -/
@[simp]
theorem relativeCosetAction_mk
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1 :=
  rfl

/-- Left multiplication permutes the cosets of an arbitrary subgroup. -/
def leftMulCosetEquiv {G : Type*} [Group G]
    (H : Subgroup G) (g : G) : (G ⧸ H) ≃ (G ⧸ H) where
  toFun q := g • q
  invFun q := g⁻¹ • q
  left_inv q := by simp
  right_inv q := by simp

/-- Left multiplication sends the coset of `x` to the coset of `g * x`. -/
@[simp] theorem leftMulCosetEquiv_mk {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) :
    leftMulCosetEquiv H g (QuotientGroup.mk x) = QuotientGroup.mk (g * x) :=
  rfl

/-- The additive norm value from `A_L` to the ambient module. -/
def relativeNormValue
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) : A.V := by
  letI := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  exact ∑ q, relativeCosetAction A K L hLK a q

/-- The relative coset action is additive in the represented fixed element. -/
theorem relativeCosetAction_add
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a b : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A K L hLK (a + b) q =
      relativeCosetAction A K L hLK a q +
        relativeCosetAction A K L hLK b q := by
  refine Quotient.inductionOn' q ?_
  intro k
  simp only [relativeCosetAction_mk]
  exact map_add (A.ρ k.1) a.1 b.1

/-- Every relative coset acts trivially on the zero fixed element. -/
@[simp]
theorem relativeCosetAction_zero
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A K L hLK 0 q = 0 := by
  refine Quotient.inductionOn' q ?_
  intro k
  simp only [relativeCosetAction_mk]
  exact map_zero (A.ρ k.1)

/-- The relative norm value is fixed by the base subgroup action. -/
theorem relativeNormValue_fixed
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    A.ρ k.1 (relativeNormValue A K L hLK a) =
      relativeNormValue A K L hLK a := by
  let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      A.ρ k.1 (relativeCosetAction A K L hLK a q) =
        relativeCosetAction A K L hLK a
          (leftMulCosetEquiv (extensionSubgroup K L hLK) k q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [relativeCosetAction_mk, leftMulCosetEquiv_mk]
    change A.ρ k.1 (A.ρ x.1 a.1) = A.ρ (k.1 * x.1) a.1
    rw [map_mul]
    rfl
  rw [relativeNormValue]
  simp_rw [map_sum, hterm]
  exact (leftMulCosetEquiv (extensionSubgroup K L hLK) k).sum_comp
    (relativeCosetAction A K L hLK a)

/-- The norm homomorphism for a finite abstract extension `L | K`.

In the multiplicative notation of the construction this additive sum is the product
over a system of representatives of `G_K / G_L`.  Its codomain is the
actual fixed module `A_K`, with fixedness proved by coset reindexing. -/
def relativeNorm
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    ambientFixedAddSubgroup A L →+ ambientFixedAddSubgroup A K where
  toFun a := ⟨relativeNormValue A K L hLK a,
    relativeNormValue_fixed A K L hLK a⟩
  map_zero' := by
    apply Subtype.ext
    let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    simp [relativeNormValue]
  map_add' a b := by
    apply Subtype.ext
    let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    simp only [AddSubgroup.coe_add, relativeNormValue]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    exact relativeCosetAction_add A K L hLK a b q

/-- Coercing a relative norm gives the explicit sum over quotient representatives. -/
@[simp]
theorem relativeNorm_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    ((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
      relativeNormValue A K L hLK a :=
  rfl

end
end ClassFormation
