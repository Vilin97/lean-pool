/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport

/-!
# Finite-support Hahn series with constant term one

The multiplicative set written `1 + K(G^{< 0})` in LM24 consists intrinsically of the
finite-support nonpositive Hahn series whose coefficient at exponent zero is one. Packaging it
as a submonoid retains precisely the multiplication used in Sections 6.5 and 8.3, without
incorrectly giving it additive or unital-subring structure.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [Field K]

/-- Finite-support nonpositive Hahn series whose coefficient at exponent zero is one. -/
def constantTermOneSubmonoid :
    Submonoid (FiniteSupportRing (G := G) (K := K)) where
  carrier := {p | constantCoeff (p : Nonpositive G K) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro p q hp hq
    change constantCoeff ((p * q : FiniteSupportRing (G := G) (K := K)) :
      Nonpositive G K) = 1
    change constantCoeff ((p : Nonpositive G K) * (q : Nonpositive G K)) = 1
    rw [map_mul, hp, hq, one_mul]

/-- The type of finite-support nonpositive Hahn series with constant term one. -/
abbrev ConstantTermOneFiniteSupport :=
  ↥(constantTermOneSubmonoid (G := G) (K := K))

/-- Membership in `constantTermOneSubmonoid` is the constant-coefficient-one condition. -/
@[simp]
theorem mem_constantTermOneSubmonoid_iff
    (p : FiniteSupportRing (G := G) (K := K)) :
    p ∈ constantTermOneSubmonoid ↔ constantCoeff (p : Nonpositive G K) = 1 :=
  Iff.rfl

/-- A constant-term-one finite-support series has constant coefficient one after coercion. -/
theorem ConstantTermOneFiniteSupport.constantCoeff_eq_one
    (p : ConstantTermOneFiniteSupport (G := G) (K := K)) :
    constantCoeff ((p : FiniteSupportRing (G := G) (K := K)) :
      Nonpositive G K) = 1 :=
  p.2

/-- A constant-term-one finite-support series is nonzero in the finite-support ring. -/
theorem ConstantTermOneFiniteSupport.ne_zero
    (p : ConstantTermOneFiniteSupport (G := G) (K := K)) :
    (p : FiniteSupportRing (G := G) (K := K)) ≠ 0 := by
  intro hp
  have hconstant := p.constantCoeff_eq_one
  rw [hp] at hconstant
  simp at hconstant

end HahnSeries.Nonpositive
