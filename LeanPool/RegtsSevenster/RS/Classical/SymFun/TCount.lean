/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.JTGuard
import LeanPool.RegtsSevenster.RS.Classical.SymFun.HProdCoeff

/-!
# The counting form of the double-sum identity

Substituting the tuple-count coefficients and the guard/margin
bridges into the signed double-sum identity: the signed count of
margin-constrained Sym-tuples over shifted compositions is `1`.
-/

namespace RS

open Finset Equiv

variable {k : ℕ}

open scoped Classical in
/-- **The counting form of the double-sum identity.** -/
theorem t_count (v : Fin k → ℕ)
    (hsort : ∀ i j : Fin k, i ≤ j → v j ≤ v i) :
    (∑ τ : Equiv.Perm (Fin k), ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (if (∀ i : Fin k,
              0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)) ∧
            (∀ i : Fin k,
              0 ≤ (v i : ℤ) + ((τ i : Fin k) : ℕ) - (i : ℕ))
          then (Fintype.card {W : ∀ i : Fin k,
              Sym (Fin k)
                (((v i : ℤ) + ((σ i : Fin k) : ℕ) -
                  (i : ℕ)).toNat) //
              ∀ j : Fin k, (∑ i, (W i).1.count j) =
                ((v j : ℤ) + ((τ j : Fin k) : ℕ) -
                  (j : ℕ)).toNat} : ℂ)
          else 0)) = 1 := by
  rw [← t_identity v (staircase_injective v hsort)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases hτ : stairShift τ ≤ diagExp v
  · have hτ' := (stair_guard_iff v τ).mp hτ
    rw [if_pos hτ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσ : ∀ i : Fin k,
        0 ≤ (v i : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
    · rw [if_pos ⟨hσ, hτ'⟩, if_pos hσ, coeff_hSub_prod]
      rw [show (Fintype.card {W : ∀ i : Fin k,
          Sym (Fin k)
            (((v i : ℤ) + ((σ i : Fin k) : ℕ) -
              (i : ℕ)).toNat) //
          ∀ j : Fin k, (∑ i, (W i).1.count j) =
            (diagExp v - stairShift τ) j}) =
        Fintype.card {W : ∀ i : Fin k,
          Sym (Fin k)
            (((v i : ℤ) + ((σ i : Fin k) : ℕ) -
              (i : ℕ)).toNat) //
          ∀ j : Fin k, (∑ i, (W i).1.count j) =
            ((v j : ℤ) + ((τ j : Fin k) : ℕ) -
              (j : ℕ)).toNat} from
        Fintype.card_congr (Equiv.subtypeEquivRight fun W =>
          forall_congr' fun j => by
            rw [stair_margin_eq v τ hτ j])]
      ring
    · rw [if_neg (fun hc => hσ hc.1), if_neg hσ]
      ring
  · rw [if_neg hτ, mul_zero]
    rw [Finset.sum_eq_zero fun σ _ => by
      rw [if_neg (fun hc =>
        hτ ((stair_guard_iff v τ).mpr hc.2)), mul_zero]]

end RS
