/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.GermPolynomialRing
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NegativeMonomialIdeal
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.OrdinalValueQuotient
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Proof that the ring of germs is a polynomial ring

The standalone ideal `J` is `negativeMonomialIdeal`, so its quotient is Berarducci's `Germ K`.
A minimal homogeneous generating system gives a polynomial presentation and hence unique
factorisation.
-/

public noncomputable section

namespace ConwayRefinement.Standalone.GermPolynomial

universe u

variable {K : Type u} [Field K]

/-- The ideal `J` is the span of the monomials `t^x` with `x < 0`. -/
theorem J_eq : J K = HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  rw [HahnSeries.Nonpositive.negativeMonomialIdeal_def]
  unfold J
  congr 1
  ext m
  constructor
  · rintro ⟨x, hx, hm⟩
    exact HahnSeries.Nonpositive.mem_negativeMonomials_iff.mpr
      ⟨⟨x, hx⟩, Subtype.ext (by rw [HahnSeries.Nonpositive.coe_single]; exact hm.symm)⟩
  · intro h
    obtain ⟨⟨x, hx⟩, rfl⟩ := HahnSeries.Nonpositive.mem_negativeMonomials_iff.mp h
    exact ⟨x, hx, HahnSeries.Nonpositive.coe_single _ _ _⟩

variable (K) in
/-- The standalone ring of germs is ring-equivalent to Berarducci's germ ring. -/
def germRingEquiv : Germ K ≃+* Berarducci.Germ K :=
  Ideal.quotEquivOfEq J_eq

namespace GermIsPolynomialRing

/-- The germ ring is a polynomial ring over its coefficient field. -/
theorem of_polynomiality (K : Type u) [Field K] : GermIsPolynomialRing K := by
  intro hK
  letI := hK
  obtain ⟨ι, wt, x, hx⟩ :=
    OrdinalGraded.exists_isMinimalSystem (Berarducci.principalGrading K)
  obtain ⟨σ⟩ := Berarducci.exists_lifts hx.mem
  exact ⟨ι, ⟨(σ.ordinalValueQuotientAlgEquiv hx).symm.toRingEquiv.trans (germRingEquiv K).symm⟩⟩

end GermIsPolynomialRing

namespace GermHasUniqueFactorization

/-- Every nonzero germ factors uniquely into irreducibles, up to order and association. -/
theorem of_polynomiality (K : Type u) [Field K] :
    GermHasUniqueFactorization K := by
  intro hK
  letI := hK
  obtain ⟨ι, ⟨equiv⟩⟩ := GermIsPolynomialRing.of_polynomiality K hK
  haveI hdom : IsDomain (Germ K) :=
    Function.Injective.isDomain equiv.symm.toRingHom equiv.symm.injective
  haveI : UniqueFactorizationMonoid (Germ K) :=
    equiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  refine ⟨hdom, fun a ha ↦ ?_, fun f g hf hg h ↦ UniqueFactorizationMonoid.factors_unique hf hg h⟩
  obtain ⟨f, hf, hfa⟩ := UniqueFactorizationMonoid.exists_prime_factors a ha
  exact ⟨f, fun b hb ↦ (hf b hb).irreducible, hfa⟩

end GermHasUniqueFactorization

end ConwayRefinement.Standalone.GermPolynomial
