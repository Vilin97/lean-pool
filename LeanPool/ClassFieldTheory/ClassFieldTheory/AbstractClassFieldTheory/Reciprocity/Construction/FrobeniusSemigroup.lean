/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField

/-! # Frobenius Semigroup -/
namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: the Frobenius semigroup

The set `Frob(\widetilde L | K)` from  is closed under multiplication:
normalized degrees are positive natural numbers and add under products.
-/

noncomputable section

namespace DegreeData

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Multiplication in this construction's Frobenius semigroup. -/
def frobeniusMul (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.FrobeniusElements K L hLK := by
  let m := D.frobeniusExponent K L hLK σ
  let n := D.frobeniusExponent K L hLK τ
  refine ⟨σ.1 * τ.1, m + n,
    Nat.add_pos_left (D.frobeniusExponent_pos K L hLK σ) n, ?_⟩
  rw [map_mul,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK τ,
    pow_add]

/--
Multiplication of Frobenius elements is induced by multiplication of their quotient
representatives.
-/
instance frobeniusElementsMul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal] :
    Mul (D.FrobeniusElements K L hLK) :=
  ⟨D.frobeniusMul K L hLK⟩

/-- Establishes the identity `(σ * τ).1 = σ.1 * τ.1`. -/
@[simp]
theorem frobeniusMul_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    (σ * τ).1 = σ.1 * τ.1 :=
  rfl

/-- The induced multiplication makes the Frobenius elements a semigroup. -/
instance frobeniusElementsSemigroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal] :
    Semigroup (D.FrobeniusElements K L hLK) where
  mul_assoc σ τ υ := by
    apply Subtype.ext
    change (σ.1 * τ.1) * υ.1 = σ.1 * (τ.1 * υ.1)
    exact mul_assoc σ.1 τ.1 υ.1

/--
`extensionNormalizedDegree_frobenius` satisfies the multiplication formula
`D.extensionNormalizedDegree K L hLK (σ * τ).1 = D.extensionNormalizedDegree K L hLK σ.1 *
D.extensionNormalizedDegree K L hLK τ.1`.
-/
@[simp]
theorem extensionNormalizedDegree_frobenius_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.extensionNormalizedDegree K L hLK (σ * τ).1 =
      D.extensionNormalizedDegree K L hLK σ.1 *
        D.extensionNormalizedDegree K L hLK τ.1 :=
  map_mul _ _ _

end DegreeData

end
end ClassFormation
