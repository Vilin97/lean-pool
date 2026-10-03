/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.Family
public import LeanPool.Zeta32.Arith.Local.Val
public import LeanPool.Zeta5Irrational.Arith.TauBound
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Bernoulli functional and the binomial basis

* `Lb Q = ∑ Q_n B_n` (`B₁ = -1/2`), `Lbp Q = ∑ Q_n B'_n` (`B'₁ = +1/2`), `Lbp Q = Lb Q + Q_1`;
* `bin k = x(x-1)⋯(x-k+1)/k!`, `Lb (bin k) = (-1)^k/(k+1)`, `derivative_bin`, `newton`;
* `BinRep`: combinations of `bin 0, …, bin k` with coefficients of valuation `≥ r`;
* `VG_polynomialMoment`: if `v_p((X q)(m)) ≥ β` for `0 ≤ m ≤ d`, `deg (X q) ≤ d`, `d + 1 < p²`
  and `r` is `p`-integral, then `v_p(polynomialMoment r q) ≥ β - 2`.
-/

public section

-- adapted from mo271/Zeta5@f19a196:Apery/Arith/BinomBasis.lean
-- and .../Apery/Arith/TauBound.lean (mo271/Zeta5 by Moritz Firsching, Apache-2.0).
-- New here: the `bernoulli'` functional `Lbp` and the bound `VG_polynomialMoment` for the
-- polynomial part of our functional `U_r` (the proof notes, §0: `U_r(t^e) = (e+1)B_e + 2rB_{e+1}`).

open Finset Polynomial

namespace Zeta32.Arith.Local

export Zeta5Irrational (poly_eq_of_nat Lb Lb_add Lb_smul Lb_C_mul Lb_monomial Lb_X_pow
  Lb_sum Lb_shift)

/-- `Lbp Q = ∑_n Q_n B'_n` (the convention `B'₁ = +1/2` of `Zeta32.moment`). -/
@[expose]
noncomputable def Lbp (Q : ℚ[X]) : ℚ := Q.sum fun n a => a * bernoulli' n

lemma Lbp_add (P Q : ℚ[X]) : Lbp (P + Q) = Lbp P + Lbp Q := by
  unfold Lbp
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma Lbp_monomial (n : ℕ) (a : ℚ) : Lbp (monomial n a) = a * bernoulli' n := by
  unfold Lbp
  rw [Polynomial.sum_monomial_index _ _ (by simp)]

/-- `Lbp Q = Lb Q + Q_1`. -/
lemma Lbp_eq (Q : ℚ[X]) : Lbp Q = Lb Q + Q.coeff 1 := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [Lbp_add, Lb_add, coeff_add, hP, hQ]; ring
  | monomial n a =>
    rw [Lbp_monomial, Lb_monomial, coeff_monomial]
    by_cases hn : n = 1
    · subst hn; rw [bernoulli'_one, bernoulli_one]; simp; ring
    · rw [ite_eq_right hn, bernoulli_eq_bernoulli'_of_ne_one hn]; ring

/-! ### The binomial basis -/

export Zeta5Irrational (bin bin_eval_nat bin_zero bin_eval_zero bin_comp_add_one)

export Zeta5Irrational (descPochhammer_eval_neg_one bin_derivative_eval_zero Lb_bin
  eq_C_of_comp_add_one dcoef derivative_bin newton)

/-! ### Valuations in the binomial basis -/

variable {p : ℕ} [hp : Fact p.Prime]

export Zeta5Irrational (BinRep derivative_bin' VG_dcoef binRep_of_values)

namespace BinRep

export Zeta5Irrational.BinRep (derivative Lb mono)

end BinRep

/-- The value at `0` of a binomial representation is its `0`-th coefficient. -/
lemma BinRep.eval_zero {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) : VG p (Q.eval 0) r := by
  obtain ⟨e, rfl, he⟩ := h
  rw [eval_finsetSum]
  apply VG.sum
  intro m hm
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [eval_mul, eval_C]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; rw [bin_zero, eval_one, mul_one]; exact he 0 hmk
  · rw [bin_eval_zero h0, mul_zero]; exact VG.zero _

/-! ### The polynomial part of `U_r` -/

/-- `polynomialMoment r q = Lbp ((X q)') + 2 r Lbp (X q)`. -/
lemma polynomialMoment_eq (r : ℚ) (q : ℚ[X]) :
    polynomialMoment r q = Lbp (derivative (X * q)) + 2 * r * Lbp (X * q) := by
  induction q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hadd : polynomialMoment r (P + Q) = polynomialMoment r P + polynomialMoment r Q := by
      unfold polynomialMoment
      exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)
    rw [hadd, hP, hQ, mul_add, derivative_add, Lbp_add, Lbp_add]; ring
  | monomial n a =>
    have h1 : polynomialMoment r (monomial n a) = a * moment r n := by
      unfold polynomialMoment
      rw [Polynomial.sum_monomial_index _ _ (by simp)]
    rw [h1, X_mul_monomial, derivative_monomial, Lbp_monomial, Lbp_monomial,
      show n + 1 - 1 = n by omega, moment]
    push_cast; ring

omit hp in
lemma nat_log_le_one {d : ℕ} (hdp : d + 1 < p ^ 2) : Nat.log p (d + 1) ≤ 1 :=
  Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hdp)

/-- **Polynomial part**: loss at most `2`. -/
theorem VG_polynomialMoment {r : ℚ} (hr : VG p r 0) {q : ℚ[X]} {d : ℕ}
    (hd : (X * q).natDegree ≤ d) (hdp : d + 1 < p ^ 2) {β : ℚ}
    (hv : ∀ m ≤ d, VG p ((X * q).eval (m : ℚ)) β) :
    VG p (polynomialMoment r q) (β - 2) := by
  have hl1 : (Nat.log p (d + 1) : ℚ) ≤ 1 := by exact_mod_cast nat_log_le_one hdp
  have hl0 : (Nat.log p d : ℚ) ≤ 1 := by
    have : Nat.log p d ≤ Nat.log p (d + 1) := Nat.log_mono_right (Nat.le_succ d)
    have h2 := nat_log_le_one (p := p) hdp
    exact_mod_cast this.trans h2
  have h0 : BinRep p d β (X * q) := binRep_of_values hd hv
  have h1 : BinRep p d (β - 1) (derivative (X * q)) := h0.derivative.mono (by linarith)
  have h2 : BinRep p d (β - 2) (derivative (derivative (X * q))) :=
    h1.derivative.mono (by linarith)
  -- `Lbp` of the derivative
  have hA : VG p (Lbp (derivative (X * q))) (β - 2) := by
    rw [Lbp_eq]
    refine VG.add (h1.Lb.mono (by linarith)) ?_
    have := BinRep.eval_zero h2
    rw [← coeff_zero_eq_eval_zero, coeff_derivative] at this
    simpa using this
  have hB : VG p (Lbp (X * q)) (β - 1) := by
    rw [Lbp_eq]
    refine VG.add (h0.Lb.mono (by linarith)) ?_
    have := BinRep.eval_zero h1
    rw [← coeff_zero_eq_eval_zero, coeff_derivative] at this
    simpa using this
  have h2r : VG p (2 * r) 0 := by
    have := (VG.natCast (p := p) 2).mul hr
    simpa using this
  rw [polynomialMoment_eq]
  refine hA.add ?_
  have := h2r.mul hB
  exact this.mono (by linarith)

end Zeta32.Arith.Local

end
