/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.BinomBasis
public import LeanPool.Zeta5Irrational.Arith.Val
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

/-! # The bound (3.9) for the polynomial functional `τ(P) = L(P''')/24`

If `deg P ≤ d` and `v_p(P(m)) ≥ β` for `m = 0, …, d`, then
`v_p(τ(P)) ≥ β - 4 ⌊log_p (d+1)⌋ - v_p(24)`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

/-- `τ(P) = L(P''')/24`. -/
@[expose] noncomputable def tau (P : ℚ[X]) : ℚ :=
  Lb (derivative^[3] P) / 24

/-- `Q` is a combination of `bin 0, …, bin k` with coefficients of valuation `≥ r`. -/
@[expose] def BinRep (p : ℕ) (k : ℕ) (r : ℚ) (Q : ℚ[X]) : Prop :=
  ∃ e : ℕ → ℚ, Q = ∑ m ∈ range (k + 1), C (e m) * bin m ∧ ∀ m ≤ k, VG p (e m) r

lemma derivative_bin' {k m : ℕ} (hm : m ≤ k) :
    (bin m).derivative = ∑ n ∈ range (k + 1), C (if n < m then dcoef (m - n) else 0) * bin n := by
  rw [derivative_bin]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not (range (k + 1)) (fun n => n < m)]
  rw [Finset.sum_eq_zero (s := (range (k + 1)).filter fun n => ¬n < m)
      (fun n hn => by rw [Finset.mem_filter] at hn; rw [ite_eq_right hn.2, C_0, zero_mul]),
    add_zero]
  apply Finset.sum_nbij' (fun n => m - n) (fun j => m - j)
  · intro n hn; simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢;
    simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj ⊢
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  · intro n hn; simp only [Finset.mem_filter, Finset.mem_range] at hn; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rw [ite_eq_left hn.2, show m - (m - n) = n by omega]

lemma VG_dcoef {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) : VG p (dcoef j) (-(Nat.log p k : ℚ)) := by
  unfold dcoef
  rw [div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ (j - 1)) 0 := by
    rcases neg_one_pow_eq_or ℚ (j - 1) with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  simpa using h1.mul (VG.inv_nat hj hjk)

/-- Differentiation loses at most `⌊log_p k⌋` in the binomial basis. -/
theorem BinRep.derivative {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) :
    BinRep p k (r - Nat.log p k) Q.derivative := by
  obtain ⟨e, rfl, he⟩ := h
  refine ⟨fun n => ∑ m ∈ range (k + 1), e m * (if n < m then dcoef (m - n) else 0), ?_, ?_⟩
  · rw [Polynomial.derivative_sum]
    simp_rw [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [Finset.sum_congr rfl fun m hm => by
        rw [derivative_bin' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [C_mul]; ring
  · intro n _
    apply VG.sum
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    split_ifs with hnm
    · have := (he m hmk).mul (VG_dcoef (p := p) (j := m - n) (k := k) (by omega) (by omega))
      simpa [sub_eq_add_neg] using this
    · rw [mul_zero]; exact VG.zero _

/-- The Bernoulli functional loses at most `⌊log_p (k+1)⌋`. -/
theorem BinRep.Lb {k : ℕ} {r : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) :
    VG p (Lb Q) (r - Nat.log p (k + 1)) := by
  obtain ⟨e, rfl, he⟩ := h
  rw [Lb_sum]
  apply VG.sum
  intro m hm
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [Lb_C_mul, Lb_bin, div_eq_mul_inv]
  have h1 : VG p ((-1 : ℚ) ^ m) 0 := by
    rcases neg_one_pow_eq_or ℚ m with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  have h2 : VG p (((m : ℚ) + 1)⁻¹) (-(Nat.log p (k + 1) : ℚ)) := by
    have := VG.inv_nat (p := p) (j := m + 1) (n := k + 1) (by omega) (by omega)
    simpa using this
  have := (he m hmk).mul (h1.mul h2)
  simpa [sub_eq_add_neg] using this

omit hp in
lemma BinRep.mono {k : ℕ} {r s : ℚ} {Q : ℚ[X]} (h : BinRep p k r Q) (hs : s ≤ r) :
    BinRep p k s Q := by
  obtain ⟨e, he, hv⟩ := h
  exact ⟨e, he, fun m hm => (hv m hm).mono hs⟩

/-- Values at `0, …, d` give a binomial representation. -/
theorem binRep_of_values {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) {β : ℚ}
    (hv : ∀ m ≤ d, VG p (P.eval (m : ℚ)) β) : BinRep p d β P := by
  refine ⟨fun k => (fwdDiff 1)^[k] P.eval 0, newton P hd, fun k hk => ?_⟩
  change VG p ((fwdDiff 1)^[k] P.eval 0) β
  rw [fwdDiff_iter_eq_sum_shift]
  apply VG.sum
  intro j hj
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  rw [zero_add, zsmul_eq_mul, nsmul_eq_mul, mul_one]
  have h1 : VG p (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) : ℤ) : ℚ) 0 := VG.intCast _
  have := h1.mul (hv j hjd)
  simpa using this

lemma VG_inv_24 : VG p ((24 : ℚ)⁻¹) (-(padicValNat p 24 : ℚ)) := by
  apply VG.inv (by norm_num)
  rw [show (24 : ℚ) = ((24 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
  exact le_refl _

/-- **(3.9)**: `v_p(τ(P)) ≥ β - 4 ⌊log_p (d+1)⌋ - v_p(24)` if `deg P ≤ d` and
`v_p(P(m)) ≥ β` for `0 ≤ m ≤ d`. -/
theorem tau_bound {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) {β : ℚ}
    (hv : ∀ m ≤ d, VG p (P.eval (m : ℚ)) β) :
    VG p (tau P) (β - 4 * Nat.log p (d + 1) - padicValNat p 24) := by
  have h0 := binRep_of_values hd hv
  have hl : (Nat.log p d : ℚ) ≤ Nat.log p (d + 1) := by
    exact_mod_cast Nat.log_mono_right (Nat.le_succ d)
  have h3 : BinRep p d (β - 3 * Nat.log p (d + 1)) (derivative^[3] P) := by
    have := h0.derivative.derivative.derivative
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact this.mono (by linarith)
  have := h3.Lb.mul (VG_inv_24 (p := p))
  unfold tau
  rw [div_eq_mul_inv]
  exact this.mono (by linarith)

end Zeta5Irrational
