/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Interfaces
public import LeanPool.Zeta32.Arith.Local.Val

/-! the proof notes, §8.1 (i), (ii-norm): the scale valuation with one Legendre level,
the reduction `cost ≤ -(v_p(scale) + allocCost)`, and the real relaxation of the allocation cost
(completed square + Cauchy–Schwarz). -/

public section
namespace Zeta32.Arith.Relaxed
open Zeta32

lemma padicValRat_finset_prod {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  exact Zeta32.Arith.Local.padicValRat_finset_prod s f hf

lemma padicValRat_factorial_one_level {p m : ℕ} [Fact p.Prime]
    (hm : m < p ^ 2) :
    padicValRat p (m.factorial : ℚ) = (m / p : ℤ) := by
  rw [padicValRat.of_nat, padicValNat_factorial
    (Nat.log_lt_of_lt_pow' (by norm_num) hm)]
  simp

lemma padicValRat_scale_one_level {p n : ℕ} (hp : p.Prime)
    (hsq : 5 * n < p ^ 2) :
    padicValRat p (scale n) =
      (3*n : ℤ) * ((5*n)/p : ℤ) - (12*n : ℤ) * (n/p : ℤ) -
        2 * ∑ i ∈ Finset.range (3*n), (i/p : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hnle : n ≤ 5*n := by omega
  have h3nle : 3*n ≤ 5*n := by omega
  have hfac5 : (5*n).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hfacn : n.factorial ≠ 0 := Nat.factorial_ne_zero _
  have hfac3 : ∀ i ∈ Finset.range (3*n), i.factorial ≠ 0 := by
    intro i hi
    exact Nat.factorial_ne_zero _
  have hsnpow : (((5*n).factorial : ℚ) / (n.factorial : ℚ)^4) ≠ 0 := by
    positivity
  have hfn : (∏ i ∈ Finset.range (3*n), ((i.factorial : ℚ)^2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (by exact_mod_cast (hfac3 i hi))
  have hsnval : padicValRat p (Sn n) =
      ((5*n)/p : ℤ) - 4*(n/p : ℤ) := by
    unfold Sn
    rw [padicValRat.div (by exact_mod_cast hfac5)
      (pow_ne_zero _ (by exact_mod_cast hfacn))]
    rw [padicValRat_factorial_one_level hsq]
    rw [padicValRat.pow]
    have hfacnval := padicValRat_factorial_one_level (lt_of_le_of_lt hnle hsq)
    rw [hfacnval]
    norm_num [Int.cast_mul]
  have hfnval : padicValRat p (Fn n) =
      2 * ∑ i ∈ Finset.range (3*n), (i/p : ℤ) := by
    unfold Fn
    rw [padicValRat_finset_prod]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [padicValRat.pow,
        padicValRat_factorial_one_level
          (lt_of_le_of_lt
            (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) h3nle) hsq)]
      norm_num [Int.cast_mul]
    · intro i hi
      exact pow_ne_zero _ (by exact_mod_cast (hfac3 i hi))
  unfold scale
  rw [padicValRat.div (by
      apply pow_ne_zero
      exact_mod_cast hsnpow) (by
      change (∏ i ∈ Finset.range (3*n), ((i.factorial : ℚ)^2)) ≠ 0
      exact hfn)]
  rw [padicValRat.pow, hsnval, hfnval]
  push_cast
  ring

lemma cost_le_of_coeff_lower (r : ℚ) (n p : ℕ) (C : ℝ)
    (hpoly : Qtilde r n ≠ 0)
    (hC : ∀ i, (Qtilde r n).coeff i ≠ 0 →
      C ≤ (padicValRat p ((Qtilde r n).coeff i) : ℝ)) :
    cost r n p ≤ -C := by
  unfold cost
  change -sInf ({v : ℝ | ∃ i, (Qtilde r n).coeff i ≠ 0 ∧
    v = (padicValRat p ((Qtilde r n).coeff i) : ℝ)}) ≤ -C
  apply neg_le_neg
  apply le_csInf
  · obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hpoly
    exact ⟨_, ⟨i, Polynomial.mem_support_iff.mp hi, rfl⟩⟩
  · intro v hv
    rcases hv with ⟨i, hi, rfl⟩
    exact hC i hi

lemma cost_le_of_scaled_greedy (r : ℚ) (n p : ℕ) (hp : p.Prime)
    (hQ : Q r n ≠ 0) (hG : Zeta32.GreedyBound r n p) :
    cost r n p ≤ -(((padicValRat p (scale n) : ℤ) : ℝ) +
      ((allocCost n p (Classical.choose hG) : ℤ) : ℝ)) := by
  have : Fact p.Prime := ⟨hp⟩
  let k := Classical.choose hG
  have hcoeff := (Classical.choose_spec hG).2
  have hscale : scale n ≠ 0 := (scale_pos n).ne'
  have hQtilde : Qtilde r n ≠ 0 := by
    intro hz
    have hmul : Polynomial.C (scale n) * Q r n = 0 := by
      simpa [Qtilde] using hz
    exact hQ ((mul_eq_zero.mp hmul).resolve_left
      (Polynomial.C_eq_zero.not.mpr hscale))
  have hC : ∀ i, (Qtilde r n).coeff i ≠ 0 →
      ((padicValRat p (scale n) : ℤ) : ℝ) +
        ((allocCost n p k : ℤ) : ℝ) ≤
          (padicValRat p ((Qtilde r n).coeff i) : ℝ) := by
    intro i hi
    have hqi : (Q r n).coeff i ≠ 0 := by
      intro hz
      have hz' : (Qtilde r n).coeff i = 0 := by
        simp [Qtilde, hz]
      exact hi hz'
    have hval' : (allocCost n p k : ℤ) ≤ padicValRat p ((Q r n).coeff i) := by
      simpa [k] using hcoeff i hqi
    have hmul : (Qtilde r n).coeff i = scale n * (Q r n).coeff i := by
      simp [Qtilde]
    rw [hmul, padicValRat.mul hscale hqi]
    have hval'' : padicValRat p (scale n) + allocCost n p k ≤
        padicValRat p (scale n) + padicValRat p ((Q r n).coeff i) := by
      simpa [add_comm] using
        add_le_add_left hval' (padicValRat p (scale n))
    exact_mod_cast hval''
  have hcost := cost_le_of_coeff_lower r n p
    (((padicValRat p (scale n) : ℤ) : ℝ) + ((allocCost n p k : ℤ) : ℝ)) hQtilde hC
  simpa [k, Int.cast_add, sub_eq_add_neg, add_assoc] using hcost

lemma sum_sq_lower_range (p : ℕ) (hp : 0 < p) (f : ℕ → ℝ) :
    (∑ b ∈ Finset.range p, f b) ^ 2 / p ≤
      ∑ b ∈ Finset.range p, f b ^ 2 := by
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range p) f (fun _ => (1 : ℝ))
  have hcauchy' : (∑ b ∈ Finset.range p, f b) ^ 2 ≤
      (∑ b ∈ Finset.range p, f b ^ 2) * p := by
    simpa using hcauchy
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hpR]
  nlinarith [hcauchy']

/-- the proof notes, §8.1 (i): real relaxation of the allocation cost, with `S = Σ c_b`, `Q₂ = Σ
c_b²`
(so `h(c-1) - Var/4 = h(S/p-1) + S²/(4p) - Q₂/4`). -/
lemma allocation_relaxation (p h : ℕ) (hp : 0 < p) (c : ℕ → ℤ)
    (k : ℕ → ℕ) (hk : (∑ b ∈ Finset.range p, k b) = h) :
    (h : ℝ) ^ 2 / p + (h : ℝ) * ((∑ b ∈ Finset.range p, (c b : ℝ)) / p - 1) +
        (∑ b ∈ Finset.range p, (c b : ℝ)) ^ 2 / (4 * p) -
        (∑ b ∈ Finset.range p, (c b : ℝ) ^ 2) / 4 ≤
      ∑ b ∈ Finset.range p,
        ((k b : ℝ) * (c b : ℝ) + (k b : ℝ) * ((k b : ℝ) - 1)) := by
  set S : ℝ := ∑ b ∈ Finset.range p, (c b : ℝ) with hS
  set Q2 : ℝ := ∑ b ∈ Finset.range p, (c b : ℝ) ^ 2 with hQ2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hkR : (∑ b ∈ Finset.range p, (k b : ℝ)) = h := by
    have hc := congrArg (fun z : ℕ => (z : ℝ)) hk
    simpa using hc
  have hsq := sum_sq_lower_range p hp (fun b => (k b : ℝ) + ((c b : ℝ) - 1) / 2)
  have hsum : (∑ b ∈ Finset.range p, ((k b : ℝ) + ((c b : ℝ) - 1) / 2)) =
      (h : ℝ) + (S - p) / 2 := by
    rw [Finset.sum_add_distrib, hkR, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp [hS]
  have hsq2 : (∑ b ∈ Finset.range p, (((c b : ℝ) - 1) / 2) ^ 2) = (Q2 - 2 * S + p) / 4 := by
    have : ∀ b ∈ Finset.range p, (((c b : ℝ) - 1) / 2) ^ 2 =
        ((c b : ℝ) ^ 2 - 2 * (c b : ℝ) + 1) / 4 := fun b _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [hS, hQ2]
  have hcompleted :
      (∑ b ∈ Finset.range p,
        ((k b : ℝ) * (c b : ℝ) + (k b : ℝ) * ((k b : ℝ) - 1))) =
      (∑ b ∈ Finset.range p,
        ((k b : ℝ) + ((c b : ℝ) - 1) / 2) ^ 2) -
      (∑ b ∈ Finset.range p, (((c b : ℝ) - 1) / 2) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hcompleted, hsq2]
  rw [hsum] at hsq
  have key : (h : ℝ) ^ 2 / p + (h : ℝ) * (S / p - 1) + S ^ 2 / (4 * p) - Q2 / 4 =
      ((h : ℝ) + (S - p) / 2) ^ 2 / p - (Q2 - 2 * S + p) / 4 := by
    field_simp
    ring
  rw [key]
  linarith

lemma allocCost_real (n p : ℕ) (k : ℕ → ℕ) :
    ((allocCost n p k : ℤ) : ℝ) = ∑ b ∈ Finset.range p,
      ((k b : ℝ) * (colVal n p b : ℝ) + (k b : ℝ) * ((k b : ℝ) - 1)) := by
  unfold allocCost
  push_cast
  rfl

end Zeta32.Arith.Relaxed
end
