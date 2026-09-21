/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Hahn series with nonpositive support

This file constructs the subring of Hahn series supported on the nonpositive cone of a partially
ordered additive commutative group. On this subring, evaluation at exponent zero is a ring
homomorphism. Pulling a coefficient subring back along that homomorphism gives an intrinsic model
of a truncation integer part.

For a linearly ordered exponent group and a coefficient field, the construction is the ring used
in LM24, Section 2.1, especially Remark 2.1.2. Mathlib's `IsPWO` support condition then agrees with
the paper's well-ordered-support convention, so `K((G^{≤ 0}))` is represented without reversing
the order on `G`. The declarations below generalize the coefficient field to a ring and the linear
order to a partial order because the constructions and proofs require only those assumptions.
-/

universe u v

public noncomputable section

namespace HahnSeries

variable (Γ : Type u) (R : Type v)
variable [AddCommGroup Γ] [PartialOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]

/-- The subring of Hahn series whose support consists of nonpositive exponents. -/
@[expose] def nonpositiveSubring : Subring R⟦Γ⟧ where
  carrier := {x | x.support ⊆ Set.Iic 0}
  zero_mem' := by simp
  one_mem' := by
    intro g hg
    have hg0 : g = 0 := support_single_subset hg
    simp [hg0]
  add_mem' := fun {x y} hx hy => by
    intro g hg
    rcases support_add_subset x y hg with hg | hg
    · exact hx hg
    · exact hy hg
  neg_mem' := fun {x} hx => (support_neg_subset x).trans hx
  mul_mem' := fun {x y} hx hy => by
    intro g hg
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hg
    exact add_nonpos (hx hi) (hy hj)

/-- Membership in `nonpositiveSubring` means that every support exponent is at most zero. -/
@[simp]
theorem mem_nonpositiveSubring {x : R⟦Γ⟧} :
    x ∈ nonpositiveSubring Γ R ↔ x.support ⊆ Set.Iic 0 :=
  (Iff.rfl)

/-- The type of Hahn series supported in the nonpositive exponents. -/
abbrev Nonpositive := ↥(nonpositiveSubring Γ R)

namespace Nonpositive

variable {Γ R}

/-- The support of a nonpositive Hahn series is contained in `Set.Iic 0`. -/
theorem support_subset (x : Nonpositive Γ R) :
    (x : R⟦Γ⟧).support ⊆ Set.Iic 0 :=
  x.2

/-- A constant Hahn series, regarded as a nonpositive Hahn series. -/
def C : R →+* Nonpositive Γ R :=
  (HahnSeries.C : R →+* R⟦Γ⟧).codRestrict (nonpositiveSubring Γ R) fun r g hg => by
    have hg0 : g = 0 := support_single_subset hg
    simp [hg0]

@[simp]
theorem coe_C (r : R) : ((C : R →+* Nonpositive Γ R) r : R⟦Γ⟧) = HahnSeries.C r :=
  (rfl)

/-- A single monomial with nonpositive exponent, regarded as a nonpositive Hahn series. -/
def single (g : Γ) (r : R) (hg : g ≤ 0) : Nonpositive Γ R :=
  ⟨HahnSeries.single g r, fun i hi => by
    rw [eq_of_mem_support_single hi]
    exact hg⟩

@[simp]
theorem coe_single (g : Γ) (r : R) (hg : g ≤ 0) :
    (single g r hg : R⟦Γ⟧) = HahnSeries.single g r :=
  (rfl)

private theorem eq_zero_of_mem_addAntidiagonal_zero {x y : Nonpositive Γ R} {ij : Γ × Γ}
    (hij : ij ∈ Finset.addAntidiagonal (x : R⟦Γ⟧).isPWO_support
      (y : R⟦Γ⟧).isPWO_support 0) :
    ij = (0, 0) := by
  rcases Finset.mem_addAntidiagonal.mp hij with ⟨hi, hj, hij⟩
  have hi_zero := eq_zero_of_add_nonneg_left (support_subset x hi) (support_subset y hj) hij.ge
  have hj_zero := eq_zero_of_add_nonneg_right (support_subset x hi) (support_subset y hj) hij.ge
  exact Prod.ext hi_zero hj_zero

/-- The coefficient at exponent zero of a product of nonpositive Hahn series is the product of
their coefficients at exponent zero. -/
@[simp]
theorem coeff_zero_mul (x y : Nonpositive Γ R) :
    ((x : R⟦Γ⟧) * (y : R⟦Γ⟧)).coeff 0 =
      (x : R⟦Γ⟧).coeff 0 * (y : R⟦Γ⟧).coeff 0 := by
  rw [HahnSeries.coeff_mul]
  by_cases hx : (x : R⟦Γ⟧).coeff 0 = 0
  · rw [hx, zero_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [eq_zero_of_mem_addAntidiagonal_zero hij]
    simp [hx]
  · by_cases hy : (y : R⟦Γ⟧).coeff 0 = 0
    · rw [hy, mul_zero]
      apply Finset.sum_eq_zero
      intro ij hij
      rw [eq_zero_of_mem_addAntidiagonal_zero hij]
      simp [hy]
    · apply Finset.sum_eq_single (0, 0)
      · intro ij hij hne
        exact (hne (eq_zero_of_mem_addAntidiagonal_zero hij)).elim
      · simp [Finset.mem_addAntidiagonal, HahnSeries.mem_support, hx, hy]

/-- Evaluation at exponent zero as a ring homomorphism on nonpositive Hahn series. -/
def constantCoeff : Nonpositive Γ R →+* R where
  toFun x := (x : R⟦Γ⟧).coeff 0
  map_zero' := HahnSeries.coeff_zero
  map_one' := by simp
  map_add' x y := HahnSeries.coeff_add
  map_mul' := coeff_zero_mul

/-- Evaluating `constantCoeff` returns the coefficient at exponent zero. -/
@[simp]
theorem constantCoeff_apply (x : Nonpositive Γ R) :
    constantCoeff x = (x : R⟦Γ⟧).coeff 0 :=
  (rfl)

end Nonpositive

/-- The subring of nonpositive Hahn series whose coefficient at exponent zero lies in `Z`. -/
def truncationIntegerPart (Γ : Type u) {R : Type v} [AddCommGroup Γ] [PartialOrder Γ]
    [IsOrderedAddMonoid Γ] [Ring R] (Z : Subring R) : Subring (Nonpositive Γ R) :=
  Z.comap Nonpositive.constantCoeff

/-- Membership in a truncation integer part is membership of the constant coefficient in `Z`. -/
@[simp]
theorem mem_truncationIntegerPart {Z : Subring R} {x : Nonpositive Γ R} :
    x ∈ truncationIntegerPart Γ Z ↔ (x : R⟦Γ⟧).coeff 0 ∈ Z :=
  (Iff.rfl)

end HahnSeries
