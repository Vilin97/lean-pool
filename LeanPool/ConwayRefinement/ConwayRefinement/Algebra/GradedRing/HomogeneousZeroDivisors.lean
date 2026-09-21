/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Graded rings without homogeneous zero divisors

A commutative ring graded by a linearly ordered cancellative monoid in which the product of two
nonzero homogeneous elements is nonzero is a domain: the zero ideal is homogeneous, and a
homogeneous ideal which is prime on homogeneous elements is prime
(`Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`).
-/

public section

variable {ι σ A : Type*} [CommRing A] [AddCommMonoid ι] [LinearOrder ι]
  [IsOrderedCancelAddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]

/-- A graded ring in which a product of homogeneous elements vanishes only if one factor does is
a domain. -/
theorem GradedRing.isDomain_of_homogeneous_eq_zero_or_eq_zero (𝒜 : ι → σ) [GradedRing 𝒜]
    [Nontrivial A]
    (h : ∀ {x y : A}, SetLike.IsHomogeneousElem 𝒜 x → SetLike.IsHomogeneousElem 𝒜 y →
      x * y = 0 → x = 0 ∨ y = 0) : IsDomain A :=
  have : (⊥ : Ideal A).IsPrime :=
    (Ideal.IsHomogeneous.bot 𝒜).isPrime_of_homogeneous_mem_or_mem bot_ne_top fun hx hy hxy ↦ by
      simpa only [Ideal.mem_bot] using h hx hy (Ideal.mem_bot.mp hxy)
  IsDomain.of_bot_isPrime A

end
