/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Changing the grading of a weighted homogeneous polynomial

Weighted homogeneity is preserved when every weight and the total degree are mapped by the same
additive homomorphism.
-/

universe u v w

public section

namespace Finsupp

variable {M : Type v} {N : Type w} [AddCommMonoid M] [AddCommMonoid N] {σ : Type*}

/-- Applying an additive homomorphism to every weight applies it to the weight of the monomial. -/
theorem weight_comp_addMonoidHom (f : M →+ N) (wt : σ → M) (d : σ →₀ ℕ) :
    weight (fun i ↦ f (wt i)) d = f (weight wt d) := by
  rw [weight_apply, weight_apply, sum, sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (f.map_nsmul (d i) (wt i)).symm

end Finsupp

namespace MvPolynomial

variable {R : Type u} [CommSemiring R] {M : Type v} {N : Type w}
variable [AddCommMonoid M] [AddCommMonoid N] {σ : Type*}

/-- Map the grading of a weighted homogeneous polynomial through an additive homomorphism. -/
theorem IsWeightedHomogeneous.map_weight {wt : σ → M} {F : MvPolynomial σ R} {m : M}
    (hF : IsWeightedHomogeneous wt F m) (f : M →+ N) :
    IsWeightedHomogeneous (fun i ↦ f (wt i)) F (f m) := by
  intro d hd
  rw [Finsupp.weight_comp_addMonoidHom]
  exact congrArg f (hF hd)

end MvPolynomial
