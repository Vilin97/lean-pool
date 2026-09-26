/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.MaxAddDegree
public import Mathlib.Algebra.Order.Monoid.ToMulBot
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Mathlib valuations as max-additive degrees

A Mathlib `Valuation` with values in `WithZero (Multiplicative M)` is a multiplicative max-additive
degree once its values are read additively, with bottom in place of the absorbing zero. This
reading turns Mathlib's multiplicative convention into LM24's additive one, and makes Mathlib's
stock of valuations available as examples and as a comparison point. Separation of the degree is
triviality of the valuation's support ideal; a nonzero support is allowed, exactly as LM24 allows
a nonzero kernel for its semi-valuations.
-/

universe u v

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- The max-additive degree of a Mathlib valuation: its value, written additively with bottom
at the support. -/
def ofValuation (w : Valuation R (WithZero (Multiplicative M))) : MaxAddDegree R M where
  toFun x := Multiplicative.toAdd (WithZero.toMulBot (w x))
  map_zero' := by simp
  map_one_le_zero' := by simp
  map_neg' x := by simp [w.map_neg]
  map_add_le_max' x y := w.map_add x y
  map_mul_le_add' x y := by simp [w.map_mul]

theorem ofValuation_apply (w : Valuation R (WithZero (Multiplicative M))) (x : R) :
    ofValuation w x = Multiplicative.toAdd (WithZero.toMulBot (w x)) :=
  (rfl)

instance (w : Valuation R (WithZero (Multiplicative M))) : (ofValuation w).IsMultiplicative :=
  ⟨fun x y ↦ by simp [ofValuation_apply, w.map_mul]⟩

@[simp]
theorem ofValuation_one (w : Valuation R (WithZero (Multiplicative M))) :
    ofValuation w 1 = 0 := by
  simp [ofValuation_apply]

@[simp]
theorem ofValuation_eq_bot_iff_mem_supp (w : Valuation R (WithZero (Multiplicative M)))
    (x : R) :
    ofValuation w x = ⊥ ↔ x ∈ w.supp := by
  rw [Valuation.mem_supp_iff]
  rfl

/-- The degree of a Mathlib valuation is separated exactly when the support ideal is zero. -/
theorem isSeparated_ofValuation_iff (w : Valuation R (WithZero (Multiplicative M))) :
    (ofValuation w).IsSeparated ↔ w.supp = ⊥ := by
  rw [isSeparated_iff, Ideal.ext_iff]
  simp only [ofValuation_eq_bot_iff_mem_supp, Ideal.mem_bot]

end MaxAddDegree
