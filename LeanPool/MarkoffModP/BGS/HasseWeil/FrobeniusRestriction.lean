/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PoleDivisor
import LeanPool.MarkoffModP.BGS.HasseWeil.TensorRestriction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Frobenius restriction over a finite constant field

Let `K` be a finite field and put `q = #K`.  The map
`x ↦ x ^ (q ^ n)` on any commutative `K`-algebra is the `n`-th iterate of
the relative Frobenius.  In particular it is a genuine `K`-algebra
endomorphism: no Frobenius-twisted scalar action is needed.

This file packages that endomorphism as an algebra homomorphism and as a
linear map, specializes the two tensor-restriction orientations, and records
the principal-divisor and pole-budget identities needed by the Stepanov
restriction argument.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped TensorProduct nonZeroDivisors Polynomial

noncomputable section

section FiniteFieldAlgebra

variable (K A : Type*) [Field K] [Fintype K]
  [CommRing A] [Algebra K A]

/-- The `n`-fold relative Frobenius on a commutative algebra over the finite
field `K`.  Its underlying function is `x ↦ x ^ ((#K) ^ n)`. -/
def powCardAlgHom (n : ℕ) : A →ₐ[K] A :=
  FiniteField.frobeniusAlgHom K A ^ n

@[simp]
theorem powCardAlgHom_apply (n : ℕ) (x : A) :
    powCardAlgHom K A n x = x ^ (Fintype.card K ^ n) := by
  simp only [powCardAlgHom, AlgHom.coe_pow,
    FiniteField.coe_frobeniusAlgHom, pow_iterate]

/-- The `K`-linear map underlying the `n`-fold relative Frobenius. -/
def powCardLinearMap (n : ℕ) : A →ₗ[K] A :=
  (powCardAlgHom K A n).toLinearMap

@[simp]
theorem powCardLinearMap_apply (n : ℕ) (x : A) :
    powCardLinearMap K A n x = x ^ (Fintype.card K ^ n) := by
  simp [powCardLinearMap]

@[simp]
theorem powCardLinearMap_add (n : ℕ) (x y : A) :
    powCardLinearMap K A n (x + y) =
      powCardLinearMap K A n x + powCardLinearMap K A n y := by
  exact map_add (powCardLinearMap K A n) x y

@[simp]
theorem powCardLinearMap_smul (n : ℕ) (c : K) (x : A) :
    powCardLinearMap K A n (c • x) = c • powCardLinearMap K A n x := by
  exact map_smul (powCardLinearMap K A n) c x

@[simp]
theorem powCardLinearMap_mul (n : ℕ) (x y : A) :
    powCardLinearMap K A n (x * y) =
      powCardLinearMap K A n x * powCardLinearMap K A n y := by
  exact map_mul (powCardAlgHom K A n) x y

variable {K A : Type*} [Field K] [Fintype K]
  [CommRing A] [Algebra K A]
variable {R S T : Submodule K A}

/-- The tensor restriction induced by `(x, y) ↦ x * y ^ ((#K) ^ n)`. -/
def powCardTensorRestriction
    (n : ℕ)
    (hmul : ∀ x : R, ∀ y : S,
      (x : A) * (y : A) ^ (Fintype.card K ^ n) ∈ T) :
    R ⊗[K] S →ₗ[K] T :=
  tensorRestriction (powCardAlgHom K A n) (fun x y => by
    simpa only [powCardAlgHom_apply] using hmul x y)

@[simp]
theorem powCardTensorRestriction_tmul
    (n : ℕ)
    (hmul : ∀ x : R, ∀ y : S,
      (x : A) * (y : A) ^ (Fintype.card K ^ n) ∈ T)
    (x : R) (y : S) :
    powCardTensorRestriction n hmul (x ⊗ₜ[K] y) =
      ⟨(x : A) * (y : A) ^ (Fintype.card K ^ n), hmul x y⟩ := by
  apply Subtype.ext
  simp [powCardTensorRestriction]

/-- The swapped tensor restriction induced by
`(x, y) ↦ x ^ ((#K) ^ n) * y`. -/
def powCardSwappedTensorRestriction
    (n : ℕ)
    (hmul : ∀ x : R, ∀ y : S,
      (x : A) ^ (Fintype.card K ^ n) * (y : A) ∈ T) :
    R ⊗[K] S →ₗ[K] T :=
  swappedTensorRestriction (powCardAlgHom K A n) (fun x y => by
    simpa only [powCardAlgHom_apply] using hmul x y)

@[simp]
theorem powCardSwappedTensorRestriction_tmul
    (n : ℕ)
    (hmul : ∀ x : R, ∀ y : S,
      (x : A) ^ (Fintype.card K ^ n) * (y : A) ∈ T)
    (x : R) (y : S) :
    powCardSwappedTensorRestriction n hmul (x ⊗ₜ[K] y) =
      ⟨(x : A) ^ (Fintype.card K ^ n) * (y : A), hmul x y⟩ := by
  apply Subtype.ext
  simp [powCardSwappedTensorRestriction]

end FiniteFieldAlgebra

section FiniteExtension

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance frobeniusRestrictionConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance frobeniusRestrictionConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Raising to `(#K) ^ n` scales every exhaustive place order by that
integer. -/
theorem finiteExtensionPrincipalDivisor_powCardLinearMap
    (x : L) (hx : x ≠ 0) (n : ℕ) :
    finiteExtensionPrincipalDivisor K L (powCardLinearMap K L n x) =
      (Fintype.card K ^ n) • finiteExtensionPrincipalDivisor K L x := by
  rw [powCardLinearMap_apply,
    finiteExtensionPrincipalDivisor_pow K L x hx]

/-- Pointwise form of the Frobenius order-scaling identity. -/
theorem finiteExtensionPrincipalDivisor_powCardLinearMap_apply
    (x : L) (hx : x ≠ 0) (n : ℕ)
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPrincipalDivisor K L (powCardLinearMap K L n x) v =
      ((Fintype.card K ^ n : ℕ) : ℤ) *
        finiteExtensionPrincipalDivisor K L x v := by
  rw [finiteExtensionPrincipalDivisor_powCardLinearMap K L x hx n]
  simp only [Finsupp.smul_apply, nsmul_eq_mul]

/-- The pole divisor is scaled by the same power of the constant-field
cardinality under iterated Frobenius. -/
theorem finiteExtensionPoleDivisor_powCardLinearMap
    (x : L) (hx : x ≠ 0) (n : ℕ) :
    finiteExtensionPoleDivisor K L (powCardLinearMap K L n x) =
      (Fintype.card K ^ n) • finiteExtensionPoleDivisor K L x := by
  classical
  ext v
  rw [finiteExtensionPoleDivisor_apply,
    finiteExtensionPrincipalDivisor_powCardLinearMap_apply K L x hx n v]
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  rw [finiteExtensionPoleDivisor_apply]
  have hs : (0 : ℤ) < (Fintype.card K ^ n : ℕ) := by
    exact_mod_cast pow_pos Fintype.card_pos n
  by_cases hv : finiteExtensionPrincipalDivisor K L x v < 0
  · have hscaled :
        ((Fintype.card K ^ n : ℕ) : ℤ) *
            finiteExtensionPrincipalDivisor K L x v < 0 :=
      mul_neg_of_pos_of_neg hs hv
    rw [ite_eq_left hscaled, ite_eq_left hv]
    ring
  · have hscaled : ¬
        ((Fintype.card K ^ n : ℕ) : ℤ) *
            finiteExtensionPrincipalDivisor K L x v < 0 :=
      not_lt_of_ge (mul_nonneg hs.le (le_of_not_gt hv))
    rw [ite_eq_right hscaled, ite_eq_right hv, mul_zero]

/-- Iterated Frobenius sends `L(D)` into `L((#K)^n D)`. -/
theorem powCardLinearMap_mem_scaledRiemannSpace
    {D : FiniteExtensionDivisor K L} {x : L}
    (hx : x ∈ finiteExtensionRiemannSpace K L D) (n : ℕ) :
    powCardLinearMap K L n x ∈ finiteExtensionRiemannSpace K L
      ((Fintype.card K ^ n) • D) := by
  simpa only [powCardLinearMap_apply] using
    finiteExtensionRiemannSpace_pow_mem K L hx (Fintype.card K ^ n)

/-- The pole budget for `(x, y) ↦ x * y ^ ((#K)^n)`. -/
theorem mul_powCardLinearMap_mem_poleDivisor_budget
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    x * powCardLinearMap K L n y ∈ finiteExtensionRiemannSpace K L
      (finiteExtensionPoleDivisor K L x +
        (Fintype.card K ^ n) • finiteExtensionPoleDivisor K L y) := by
  exact finiteExtensionRiemannSpace_mul_mem K L
    (mem_finiteExtensionRiemannSpace_poleDivisor K L x hx)
    (powCardLinearMap_mem_scaledRiemannSpace K L
      (mem_finiteExtensionRiemannSpace_poleDivisor K L y hy) n)

/-- The pole budget for the swapped product
`(x, y) ↦ x ^ ((#K)^n) * y`. -/
theorem powCardLinearMap_mul_mem_poleDivisor_budget
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    powCardLinearMap K L n x * y ∈ finiteExtensionRiemannSpace K L
      ((Fintype.card K ^ n) • finiteExtensionPoleDivisor K L x +
        finiteExtensionPoleDivisor K L y) := by
  exact finiteExtensionRiemannSpace_mul_mem K L
    (powCardLinearMap_mem_scaledRiemannSpace K L
      (mem_finiteExtensionRiemannSpace_poleDivisor K L x hx) n)
    (mem_finiteExtensionRiemannSpace_poleDivisor K L y hy)

/-- Tensor restriction between Riemann spaces in the unswapped orientation. -/
def powCardRiemannTensorRestriction
    (D E : FiniteExtensionDivisor K L) (n : ℕ) :
    finiteExtensionRiemannSpace K L D ⊗[K]
        finiteExtensionRiemannSpace K L E →ₗ[K]
      finiteExtensionRiemannSpace K L
        (D + (Fintype.card K ^ n) • E) :=
  powCardTensorRestriction n (fun x y =>
    finiteExtensionRiemannSpace_mul_mem K L x.property
      (finiteExtensionRiemannSpace_pow_mem K L y.property
        (Fintype.card K ^ n)))

@[simp]
theorem powCardRiemannTensorRestriction_tmul
    (D E : FiniteExtensionDivisor K L) (n : ℕ)
    (x : finiteExtensionRiemannSpace K L D)
    (y : finiteExtensionRiemannSpace K L E) :
    powCardRiemannTensorRestriction K L D E n (x ⊗ₜ[K] y) =
      ⟨(x : L) * (y : L) ^ (Fintype.card K ^ n),
        finiteExtensionRiemannSpace_mul_mem K L x.property
          (finiteExtensionRiemannSpace_pow_mem K L y.property
            (Fintype.card K ^ n))⟩ := by
  apply Subtype.ext
  simp [powCardRiemannTensorRestriction]

/-- Tensor restriction between Riemann spaces in the swapped orientation. -/
def powCardSwappedRiemannTensorRestriction
    (D E : FiniteExtensionDivisor K L) (n : ℕ) :
    finiteExtensionRiemannSpace K L D ⊗[K]
        finiteExtensionRiemannSpace K L E →ₗ[K]
      finiteExtensionRiemannSpace K L
        ((Fintype.card K ^ n) • D + E) :=
  powCardSwappedTensorRestriction n (fun x y =>
    finiteExtensionRiemannSpace_mul_mem K L
      (finiteExtensionRiemannSpace_pow_mem K L x.property
        (Fintype.card K ^ n)) y.property)

@[simp]
theorem powCardSwappedRiemannTensorRestriction_tmul
    (D E : FiniteExtensionDivisor K L) (n : ℕ)
    (x : finiteExtensionRiemannSpace K L D)
    (y : finiteExtensionRiemannSpace K L E) :
    powCardSwappedRiemannTensorRestriction K L D E n (x ⊗ₜ[K] y) =
      ⟨(x : L) ^ (Fintype.card K ^ n) * (y : L),
        finiteExtensionRiemannSpace_mul_mem K L
          (finiteExtensionRiemannSpace_pow_mem K L x.property
            (Fintype.card K ^ n))
          y.property⟩ := by
  apply Subtype.ext
  simp [powCardSwappedRiemannTensorRestriction]

end FiniteExtension

end

end BGS.HasseWeil
