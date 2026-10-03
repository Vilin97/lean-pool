/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Local
public import LeanPool.Zeta32.Arith.Local.Entry

/-! Linear algebra of the local functional `locValue` (for S2b-1).

* `dist_locValue_add`, `dist_locValue_C_mul`, `dist_locValue_sum` : `locValue s · M` is linear;
* `locPoly_eq` : `locPoly s Q = Lbp Q' + 2 s Lbp Q`;
* `pf_nat` : partial fractions over the nodes `-m`, `m ∈ M`;
* `locValue_pf` : value of `locValue` on a partial-fraction form. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

noncomputable section

/-- `∏_{m ∈ M} (X + m)`. -/
def mprod (M : Finset ℕ) : ℚ[X] := ∏ m ∈ M, (X + C (m : ℚ))

lemma mprod_monic (M : Finset ℕ) : (mprod M).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

lemma natDegree_mprod (M : Finset ℕ) : (mprod M).natDegree = M.card := by
  unfold mprod
  rw [natDegree_prod_of_monic _ _ fun m _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

lemma dist_locPoly_add (s : ℚ) (P Q : ℚ[X]) : locPoly s (P + Q) = locPoly s P + locPoly s Q := by
  exact locPoly_add_linear s P Q

lemma locPoly_C_mul (s c : ℚ) (P : ℚ[X]) : locPoly s (C c * P) = c * locPoly s P := by
  exact locPoly_C_mul_linear s c P

lemma dist_locPoly_zero (s : ℚ) : locPoly s 0 = 0 := by
  exact locPoly_zero_linear s

lemma locPoly_monomial (s : ℚ) (e : ℕ) (a : ℚ) : locPoly s (monomial e a) = a * locMoment s e := by
  unfold locPoly
  rw [Polynomial.sum_monomial_index _ _ (by simp)]

/-- `locPoly s Q = Lbp Q' + 2 s Lbp Q`. -/
lemma locPoly_eq (s : ℚ) (Q : ℚ[X]) : locPoly s Q = Lbp (derivative Q) + 2 * s * Lbp Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [dist_locPoly_add, hP, hQ, derivative_add, Lbp_add, Lbp_add]; ring
  | monomial n a =>
    rw [locPoly_monomial, derivative_monomial, Lbp_monomial, Lbp_monomial, locMoment]
    ring

lemma dist_locValue_add (s : ℚ) (S T : ℚ[X]) (M : Finset ℕ) :
    locValue s (S + T) M = locValue s S M + locValue s T M := by
  exact locValue_add_linear s S T M

lemma dist_locValue_C_mul (s c : ℚ) (S : ℚ[X]) (M : Finset ℕ) :
    locValue s (C c * S) M = c * locValue s S M := by
  exact locValue_C_mul_linear s c S M

lemma locValue_zero (s : ℚ) (M : Finset ℕ) : locValue s 0 M = 0 := by
  exact locValue_zero_linear s M

lemma dist_locValue_sum {ι : Type*} (s : ℚ) (t : Finset ι) (S : ι → ℚ[X]) (M : Finset ℕ) :
    locValue s (∑ i ∈ t, S i) M = ∑ i ∈ t, locValue s (S i) M := by
  exact locValue_sum_linear s t S M

/-- Residue of `S / mprod M` at `-m`. -/
def resN (S : ℚ[X]) (M : Finset ℕ) (m : ℕ) : ℚ :=
  S.eval (-(m : ℚ)) / ∏ m' ∈ M.erase m, ((m' : ℚ) - m)

lemma lagrange_basis_eq_nat (M : Finset ℕ) (m : ℕ) :
    Lagrange.basis M (fun m : ℕ => -(m : ℚ)) m =
      C (∏ m' ∈ M.erase m, ((m' : ℚ) - m))⁻¹ * ∏ m' ∈ M.erase m, (X + C (m' : ℚ)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]
  congr 1
  · congr 2
    exact Finset.prod_congr rfl fun m' _ => by ring
  · exact Finset.prod_congr rfl fun m' _ => by rw [C_neg, sub_neg_eq_add]

/-- Partial fractions over the nodes `-m`, `m ∈ M`. -/
theorem pf_nat (S : ℚ[X]) (M : Finset ℕ) :
    S = (S /ₘ mprod M) * mprod M +
      ∑ m ∈ M, C (resN S M m) * ∏ m' ∈ M.erase m, (X + C (m' : ℚ)) := by
  have hinj : Set.InjOn (fun m : ℕ => -(m : ℚ)) M := fun a _ b _ h => by
    simpa using h
  have hmod : S %ₘ mprod M =
      ∑ m ∈ M, C (resN S M m) * ∏ m' ∈ M.erase m, (X + C (m' : ℚ)) := by
    rw [Lagrange.eq_interpolate_of_eval_eq (f := S %ₘ mprod M) (fun m : ℕ => S.eval (-(m : ℚ)))
      hinj
      (by
        have := degree_modByMonic_lt S (mprod_monic M)
        rwa [degree_eq_natDegree (mprod_monic M).ne_zero, natDegree_mprod] at this)
      (fun m hm => by
        have h1 := modByMonic_add_div S (mprod M)
        have h2 : (mprod M).eval (-(m : ℚ)) = 0 := by
          unfold mprod; rw [eval_prod]
          exact Finset.prod_eq_zero hm (by simp)
        conv_rhs => rw [← h1]
        rw [eval_add, eval_mul, h2, zero_mul, add_zero])]
    simp only [Lagrange.interpolate_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [lagrange_basis_eq_nat, resN, div_eq_mul_inv, C_mul, mul_assoc]
  conv_lhs => rw [← modByMonic_add_div S (mprod M)]
  rw [hmod, add_comm, mul_comm]

/-- `locValue` on a partial-fraction form. -/
theorem locValue_pf (s : ℚ) (M : Finset ℕ) (P : ℚ[X]) (a : ℕ → ℚ) :
    locValue s (P * mprod M + ∑ m ∈ M, C (a m) * ∏ m' ∈ M.erase m, (X + C (m' : ℚ))) M =
      locPoly s P + ∑ m ∈ M, a m * locPole s m := by
  set R := ∑ m ∈ M, C (a m) * ∏ m' ∈ M.erase m, (X + C (m' : ℚ)) with hR
  have hdegR : R.degree < (mprod M).degree := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr
      (fun h => (mprod_monic M).ne_zero (degree_eq_bot.mp h)))]
    intro m hm
    refine degree_lt_degree ?_
    refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
    rw [natDegree_mprod, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
    exact Finset.card_erase_lt_of_mem hm
  have hdiv : (P * mprod M + R) /ₘ mprod M = P :=
    (div_modByMonic_unique P R (mprod_monic M) ⟨by ring, hdegR⟩).1
  have heval : ∀ m ∈ M, (P * mprod M + R).eval (-(m : ℚ)) =
      a m * ∏ m' ∈ M.erase m, ((m' : ℚ) - m) := by
    intro m hm
    have h2 : (mprod M).eval (-(m : ℚ)) = 0 := by
      unfold mprod; rw [eval_prod]
      exact Finset.prod_eq_zero hm (by simp)
    rw [eval_add, eval_mul, h2, mul_zero, zero_add, hR, eval_finsetSum,
      Finset.sum_eq_single m]
    · rw [eval_mul, eval_C, eval_prod]
      congr 1
      exact Finset.prod_congr rfl fun m' _ => by simp; ring
    · intro m0 hm0 hne
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := m)
        (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hm⟩) (by simp), mul_zero]
    · intro h; exact absurd hm h
  unfold locValue
  rw [show ∏ m ∈ M, (X + C (m : ℚ)) = mprod M from rfl, hdiv]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hne : ∏ m' ∈ M.erase m, ((m' : ℚ) - m) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun m' hm' => sub_ne_zero.mpr (by
      exact_mod_cast (Finset.mem_erase.mp hm').1)
  rw [heval m hm, mul_div_cancel_right₀ _ hne]

end

end Zeta32.PrimeEdge

end
