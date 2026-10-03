/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Degree

/-!
# Boolean-ring identities used by feedback gates

Every canonical Boolean ANF is idempotent.  Consequently, if `f = u * c`,
then both factors absorb `f`.  The manuscript uses these identities at the
quartic seed and at both feedback stages; proving them once at the ANF level
prevents those arguments from silently treating Boolean multiplication as
ordinary polynomial multiplication.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem monomial_mul_self {m : Nat} (s : Monomial m) : s * s = s := by
  apply Monomial.ext
  exact Finset.union_self _

/-- Frobenius is the identity on the Boolean ANF algebra. -/
@[simp] theorem anf_mul_self {m : Nat} (p : ANF m) : p * p = p := by
  refine MonoidAlgebra.induction_on (motive := fun x => x * x = x) p ?_ ?_ ?_
  · intro s
    rw [MonoidAlgebra.of_apply]
    simp only [MonoidAlgebra.single_mul_single, one_mul]
    rw [monomial_mul_self]
  · intro x y hx hy
    rw [add_mul, mul_add, mul_add, hx, hy, mul_comm y x]
    calc
      x + x * y + (x * y + y) = x + (x * y + x * y) + y := by ac_rfl
      _ = x + y := by rw [anf_add_self, add_zero]
  · intro a x hx
    rcases f2_eq_zero_or_one a with rfl | rfl <;> simp [hx]

/-- A factor absorbs its product in the Boolean function algebra. -/
theorem left_absorbs_product {m : Nat} (u c : ANF m) :
    u * (u * c) = u * c := by
  rw [← mul_assoc, anf_mul_self]

/-- The other factor absorbs the same product. -/
theorem right_absorbs_product {m : Nat} (u c : ANF m) :
    (u * c) * c = u * c := by
  rw [mul_assoc, anf_mul_self]

theorem absorption_of_eq {m : Nat} {u c f : ANF m} (hf : f = u * c) :
    u * f = f ∧ f * c = f := by
  subst f
  exact ⟨left_absorbs_product u c, right_absorbs_product u c⟩

end

end N4
end UnrestrictedBooleanMul
