/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Small.Binom

/-! the proof notes, §7 (c), the polynomial part of `U_r`.

`Bf f = Σ f_e B'_e` (`bernoulli'`, `B'_1 = +1/2`) is the functional `B` of the proof notes, §0
on polynomials.
* shift rule `B(f(t+1)) = B(f) + f'(1)` (from `sum_bernoulli'`);
* hence `B(binom(t,k)) = binom(t,k+1)'(1)`, so `v_p(B(binom(t,k))) ≥ -⌊log_p(k+1)⌋`
  (this replaces the closed form `(-1)^{k+1}/(k(k+1))`; only the valuation is used);
* `polynomialMoment r g = B((t g)') + 2r B(t g)`;
* if `deg g ≤ d` and `v_p(g(z)) ≥ β` for all `z ∈ ℤ`, then
  `v_p(polynomialMoment r g) ≥ β - 2⌊log_p(d+2)⌋ - v_p(den r)`. -/

public section

open Zeta32.Arith.Local

open Polynomial
open scoped BigOperators
namespace Zeta32.Arith.Small
open Zeta32
noncomputable section

/-- `B` on polynomials: `t^e ↦ B'_e`. -/
abbrev Bf (f : ℚ[X]) : ℚ := Zeta32.Arith.Local.Lbp f

lemma Bf_add (f g : ℚ[X]) : Bf (f + g) = Bf f + Bf g :=
  Zeta32.Arith.Local.Lbp_add f g

lemma Bf_C_mul (c : ℚ) (f : ℚ[X]) : Bf (C c * f) = c * Bf f := by
  unfold Bf Zeta32.Arith.Local.Lbp
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp),
    Polynomial.sum, Polynomial.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma Bf_zero : Bf 0 = 0 := by simp [Bf, Zeta32.Arith.Local.Lbp]

lemma Bf_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    Bf (∑ i ∈ s, f i) = ∑ i ∈ s, Bf (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bf_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Bf_add, ih]

lemma Bf_monomial (e : ℕ) (a : ℚ) : Bf (monomial e a) = a * bernoulli' e :=
  Zeta32.Arith.Local.Lbp_monomial e a

lemma Bf_eq_sum_range (f : ℚ[X]) {d : ℕ} (hd : f.natDegree ≤ d) :
    Bf f = ∑ k ∈ Finset.range (d+1), f.coeff k * bernoulli' k := by
  unfold Bf Zeta32.Arith.Local.Lbp
  exact Polynomial.sum_over_range' _ (fun _ => by simp) _ (by omega)

lemma Bf_X_add_one_pow (m : ℕ) : Bf ((X + 1 : ℚ[X]) ^ m) = bernoulli' m + m := by
  have hd : ((X + 1 : ℚ[X]) ^ m).natDegree ≤ m := by
    refine (natDegree_pow_le).trans ?_
    have : (X + 1 : ℚ[X]).natDegree = 1 := by
      rw [show (X + 1 : ℚ[X]) = X + C 1 by simp, natDegree_X_add_C]
    rw [this, mul_one]
  rw [Bf_eq_sum_range _ hd, Finset.sum_range_succ]
  simp only [coeff_X_add_one_pow, Nat.choose_self, Nat.cast_one, one_mul]
  rw [sum_bernoulli']
  ring

/-- Shift rule `B(f(t+1)) = B(f) + f'(1)` (the proof notes, §0). -/
theorem Bf_shift (f : ℚ[X]) : Bf (f.comp (X + 1)) = Bf f + (derivative f).eval 1 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [add_comp, Bf_add, Bf_add, hf, hg, derivative_add, eval_add]
    ring
  | monomial m a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, Bf_C_mul, Bf_X_add_one_pow,
      C_mul_X_pow_eq_monomial, Bf_monomial, derivative_monomial, eval_monomial]
    simp only [one_pow, mul_one]
    ring

lemma Bf_binomPoly (k : ℕ) : Bf (binomPoly k) = (derivative (binomPoly (k+1))).eval 1 := by
  have h := Bf_shift (binomPoly (k+1))
  rw [binomPoly_succ_comp_add_one, Bf_add] at h
  linarith

lemma Bf_binomPoly_VG (p : ℕ) [Fact p.Prime] (k : ℕ) :
    VG p (Bf (binomPoly k)) (-(Nat.log p (k+1) : ℚ)) := by
  rw [Bf_binomPoly]
  have h := derivative_eval_VG p (f := binomPoly (k+1)) (e := k+1)
    (by rw [binomPoly_natDegree]) 0 (fun m => binomPoly_eval_int_VG p (k+1) m) 1
  simpa using h

/-- `v_p(B(h)) ≥ β - ⌊log_p(d+1)⌋` if `deg h ≤ d` and `v_p(h(z)) ≥ β` on `ℤ`. -/
theorem Bf_VG (p : ℕ) [Fact p.Prime] {h : ℚ[X]} {d : ℕ} (hd : h.natDegree ≤ d) (β : ℚ)
    (hv : ∀ z : ℤ, VG p (h.eval (z : ℚ)) β) :
    VG p (Bf h) (β - (Nat.log p (d+1) : ℚ)) := by
  rw [newton_expansion hd 0]
  simp only [map_zero, sub_zero, comp_X]
  rw [Bf_sum]
  apply VG.sum
  intro k hk
  rw [Bf_C_mul]
  have hk' : k + 1 ≤ d + 1 := by simp at hk; omega
  have hc : VG p (newtonCoeff h 0 k) β :=
    newtonCoeff_VG p 0 β k fun i _ => by
      have := hv (i : ℤ)
      simpa using this
  have hb := (Bf_binomPoly_VG p k).mono
    (show -(Nat.log p (d+1) : ℚ) ≤ -(Nat.log p (k+1) : ℚ) by
      have : (Nat.log p (k+1) : ℚ) ≤ Nat.log p (d+1) := by exact_mod_cast Nat.log_mono_right hk'
      linarith)
  simpa [sub_eq_add_neg] using hc.mul hb

lemma polynomialMoment_monomial (r : ℚ) (e : ℕ) (a : ℚ) :
    polynomialMoment r (monomial e a) = a * moment r e := by
  unfold polynomialMoment
  rw [Polynomial.sum_monomial_index]
  simp

lemma polynomialMoment_add (r : ℚ) (f g : ℚ[X]) :
    polynomialMoment r (f + g) = polynomialMoment r f + polynomialMoment r g := by
  unfold polynomialMoment
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma polynomialMoment_C_mul (r c : ℚ) (f : ℚ[X]) :
    polynomialMoment r (C c * f) = c * polynomialMoment r f := by
  unfold polynomialMoment
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp),
    Polynomial.sum, Polynomial.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `U_r` on polynomials: `polynomialMoment r g = B((t g)') + 2r B(t g)` (the proof notes, §0). -/
theorem polynomialMoment_eq_Bf (r : ℚ) (g : ℚ[X]) :
    polynomialMoment r g = Bf (derivative (X * g)) + 2 * r * Bf (X * g) := by
  induction g using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [polynomialMoment_add, hf, hg, mul_add, derivative_add, Bf_add, Bf_add]
    ring
  | monomial e a =>
    rw [polynomialMoment_monomial, X_mul_monomial, derivative_monomial, Bf_monomial,
      Bf_monomial, moment, Nat.add_sub_cancel]
    push_cast
    ring

lemma VG_two_mul_rat (p : ℕ) [Fact p.Prime] (r : ℚ) :
    VG p (2 * r) (-(padicValNat p r.den : ℚ)) := by
  have h := (VG.natCast (p := p) 2).mul (VG.ratDen (p := p) r)
  simpa using h

/-- the proof notes, §7 (c): `v_p(U_r(g)) ≥ β - 2⌊log_p(d+2)⌋ - v_p(den r)` for `deg g ≤ d` and
`v_p(g(z)) ≥ β` on `ℤ`. -/
theorem polynomialMoment_VG (p : ℕ) [Fact p.Prime] (r : ℚ) {g : ℚ[X]} {d : ℕ}
    (hd : g.natDegree ≤ d) (β : ℚ) (hv : ∀ z : ℤ, VG p (g.eval (z : ℚ)) β) :
    VG p (polynomialMoment r g)
      (β - 2 * (Nat.log p (d+2) : ℚ) - (padicValNat p r.den : ℚ)) := by
  rw [polynomialMoment_eq_Bf]
  have hXd : (X * g).natDegree ≤ d + 1 := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_X]; omega
  have hXv : ∀ z : ℤ, VG p ((X * g).eval (z : ℚ)) β := by
    intro z
    rw [eval_mul, eval_X]
    simpa using (VG.intCast (p := p) z).mul (hv z)
  have hDd : (derivative (X * g)).natDegree ≤ d := by
    refine (natDegree_derivative_le _).trans ?_
    omega
  have hDv : ∀ z : ℤ, VG p ((derivative (X * g)).eval (z : ℚ)) (β - (Nat.log p (d+1) : ℚ)) :=
    fun z => derivative_eval_VG p hXd β hXv z
  have h1 := Bf_VG p hDd _ hDv
  have h2 := Bf_VG p hXd β hXv
  have h3 := (VG_two_mul_rat p r).mul h2
  have hl : (Nat.log p (d+1) : ℚ) ≤ Nat.log p (d+2) := by
    exact_mod_cast Nat.log_mono_right (by omega)
  have hl0 : (0 : ℚ) ≤ Nat.log p (d+2) := Nat.cast_nonneg _
  have hden : (0 : ℚ) ≤ padicValNat p r.den := Nat.cast_nonneg _
  refine VG.add (h1.mono ?_) (h3.mono ?_)
  · linarith
  · linarith

end
end Zeta32.Arith.Small

end
