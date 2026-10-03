/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Formula
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Ordered-finpartition resummations

The factorial weights in the composition estimate have a closed form when
summed over Mathlib's ordered finpartitions.  This is the coefficient-level
form of the 10469 resummation needed by Proposition 10528.
-/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open Polynomial

/-- Product of the factorials of the part sizes of an ordered finpartition. -/
def orderedPartitionFactorialProduct {n : ℕ} (c : OrderedFinpartition n) : ℕ :=
  ∏ i : Fin c.length, (c.partSize i).factorial

/-- The weighted ordered-finpartition polynomial. The weight of a partition
with `s` parts of sizes `r₁,…,rₛ` is `X^s s! ∏ rᵢ!`. -/
def orderedPartitionWeightPolynomial (n : ℕ) : Polynomial ℝ :=
  ∑ c : OrderedFinpartition n,
    Polynomial.X ^ c.length *
      Polynomial.C ((c.length.factorial * orderedPartitionFactorialProduct c : ℕ) : ℝ)

theorem Resummation.orderedPartition_partSize_sum {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Fin c.length, c.partSize i = n := by
  classical
  calc
    ∑ i : Fin c.length, c.partSize i =
        Fintype.card (Σ i : Fin c.length, Fin (c.partSize i)) := by
          simp [Fintype.card_sigma]
    _ = Fintype.card (Fin n) := Fintype.card_congr c.equivSigma
    _ = n := Fintype.card_fin n

theorem Resummation.orderedPartition_partSize_add_one_sum {n : ℕ}
    (c : OrderedFinpartition n) :
    ∑ i : Fin c.length, (c.partSize i + 1) = n + c.length := by
  rw [Finset.sum_add_distrib, Resummation.orderedPartition_partSize_sum]
  simp

theorem Resummation.factorialProduct_extendLeft {n : ℕ} (c : OrderedFinpartition n) :
    orderedPartitionFactorialProduct c.extendLeft =
      orderedPartitionFactorialProduct c := by
  dsimp [orderedPartitionFactorialProduct, OrderedFinpartition.extendLeft]
  change (∏ j : Fin (c.length + 1),
      (Fin.cons (α := fun _ : Fin (c.length + 1) ↦ ℕ) 1 c.partSize j).factorial) = _
  rw [Fin.prod_univ_succ]
  simp

theorem Resummation.factorialProduct_extendMiddle {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) :
    orderedPartitionFactorialProduct (c.extendMiddle i) =
      (c.partSize i + 1) * orderedPartitionFactorialProduct c := by
  classical
  dsimp [orderedPartitionFactorialProduct, OrderedFinpartition.extendMiddle]
  have hfun : (fun j : Fin c.length ↦
      (Function.update c.partSize i (c.partSize i + 1) j).factorial) =
      Function.update (fun j : Fin c.length ↦ (c.partSize j).factorial) i
        ((c.partSize i + 1).factorial) := by
    funext j
    by_cases h : j = i <;> simp [h]
  have hprodfun := congrArg (fun f : Fin c.length → ℕ ↦ ∏ j, f j) hfun
  change (∏ j : Fin c.length,
      (Function.update c.partSize i (c.partSize i + 1) j).factorial) = _ at hprodfun
  calc
    (∏ j : Fin c.length,
        (Function.update c.partSize i (c.partSize i + 1) j).factorial) =
      ∏ j : Fin c.length, Function.update (fun j : Fin c.length ↦
        (c.partSize j).factorial) i ((c.partSize i + 1).factorial) j := hprodfun
    _ = _ := by
      rw [Finset.prod_update_of_mem (s := Finset.univ) (i := i)
    (f := fun j : Fin c.length ↦ (c.partSize j).factorial)
    (b := (c.partSize i + 1).factorial) (Finset.mem_univ i)]
      rw [Nat.factorial_succ]
      have hprod := Finset.mul_prod_erase (Finset.univ : Finset (Fin c.length))
        (fun j : Fin c.length ↦ (c.partSize j).factorial) (Finset.mem_univ i)
      simpa [Finset.sdiff_singleton_eq_erase, mul_assoc] using congrArg
        (fun z : ℕ ↦ (c.partSize i + 1) * z) hprod

theorem Resummation.x_mul_derivative_x_pow_C (s : ℕ) (a : ℝ) :
    Polynomial.X * Polynomial.derivative
      (Polynomial.X ^ s * Polynomial.C a : Polynomial ℝ) =
      Polynomial.X ^ s * Polynomial.C ((s : ℝ) * a) := by
  cases s with
  | zero => simp
  | succ s =>
      rw [Polynomial.derivative_mul, Polynomial.derivative_X_pow_succ,
        Polynomial.derivative_C]
      simp only [mul_zero, add_zero]
      calc
        Polynomial.X *
            (Polynomial.C ((s : ℝ) + 1) * Polynomial.X ^ s * Polynomial.C a) =
          Polynomial.X ^ (s + 1) *
            (Polynomial.C ((s : ℝ) + 1) * Polynomial.C a) := by
              rw [pow_succ]
              ring
        _ = Polynomial.X ^ (s + 1) *
            Polynomial.C (((s : ℝ) + 1) * a) := by
              rw [← Polynomial.C_mul]
        _ = Polynomial.X ^ (s + 1) *
            Polynomial.C (((s + 1 : ℕ) : ℝ) * a) := by
              congr 1
              rw [Nat.cast_succ]

theorem Resummation.x_derivative_orderedPartitionWeightPolynomial (n : ℕ) :
    Polynomial.X * Polynomial.derivative (orderedPartitionWeightPolynomial n) =
      ∑ c : OrderedFinpartition n,
        Polynomial.X ^ c.length *
          Polynomial.C ((c.length : ℝ) *
            ((c.length.factorial * orderedPartitionFactorialProduct c : ℕ) : ℝ)) := by
  classical
  unfold orderedPartitionWeightPolynomial
  rw [Polynomial.derivative_sum]
  rw [Finset.mul_sum]
  simp_rw [Resummation.x_mul_derivative_x_pow_C]

theorem Resummation.orderedPartitionSomeWeightSum {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Fin c.length,
        Polynomial.X ^ c.length * Polynomial.C
          ((c.length.factorial * (c.partSize i + 1) *
            orderedPartitionFactorialProduct c : ℕ) : ℝ) =
      Polynomial.X ^ c.length * Polynomial.C
        ((c.length.factorial * (n + c.length) *
          orderedPartitionFactorialProduct c : ℕ) : ℝ) := by
  classical
  let s := c.length.factorial
  let p := orderedPartitionFactorialProduct c
  have hsumNat : ∑ i : Fin c.length, s * (c.partSize i + 1) * p =
      s * (n + c.length) * p := by
    calc
      ∑ i : Fin c.length, s * (c.partSize i + 1) * p =
          (∑ i : Fin c.length, s * (c.partSize i + 1)) * p := by
            rw [Finset.sum_mul]
      _ = (s * ∑ i : Fin c.length, (c.partSize i + 1)) * p := by
            rw [Finset.mul_sum]
      _ = s * (n + c.length) * p := by
            rw [Resummation.orderedPartition_partSize_add_one_sum]
  calc
    ∑ i : Fin c.length,
        Polynomial.X ^ c.length * Polynomial.C
          ((s * (c.partSize i + 1) * p : ℕ) : ℝ) =
      Polynomial.X ^ c.length *
        ∑ i : Fin c.length, Polynomial.C ((s * (c.partSize i + 1) * p : ℕ) : ℝ) := by
          rw [← Finset.mul_sum]
    _ = Polynomial.X ^ c.length *
        Polynomial.C ((∑ i : Fin c.length, s * (c.partSize i + 1) * p : ℕ) : ℝ) := by
          congr 1
          rw [← map_sum]
          simp [Nat.cast_sum]
    _ = Polynomial.X ^ c.length *
        Polynomial.C ((s * (n + c.length) * p : ℕ) : ℝ) := by
          rw [hsumNat]

theorem Resummation.orderedPartitionWeightPolynomial_succ_expansion (n : ℕ) :
    orderedPartitionWeightPolynomial (n + 1) =
      ∑ c : OrderedFinpartition n,
        (Polynomial.X ^ (c.length + 1) *
            Polynomial.C (((c.length + 1).factorial *
              orderedPartitionFactorialProduct c : ℕ) : ℝ) +
          ∑ i : Fin c.length,
            Polynomial.X ^ c.length * Polynomial.C
              ((c.length.factorial * (c.partSize i + 1) *
                orderedPartitionFactorialProduct c : ℕ) : ℝ)) := by
  classical
  unfold orderedPartitionWeightPolynomial
  calc
    (∑ c : OrderedFinpartition (n + 1),
        Polynomial.X ^ c.length *
          Polynomial.C ((c.length.factorial *
            orderedPartitionFactorialProduct c : ℕ) : ℝ)) =
      ∑ p : (c : OrderedFinpartition n) × Option (Fin c.length),
        Polynomial.X ^ (p.1.extend p.2).length *
          Polynomial.C (((p.1.extend p.2).length.factorial *
            orderedPartitionFactorialProduct (p.1.extend p.2) : ℕ) : ℝ) := by
        symm
        exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv n) _ _ (fun _ ↦ rfl)
    _ = ∑ c : OrderedFinpartition n, ∑ o : Option (Fin c.length),
        Polynomial.X ^ (c.extend o).length *
          Polynomial.C (( (c.extend o).length.factorial *
            orderedPartitionFactorialProduct (c.extend o) : ℕ) : ℝ) := by
        rw [Fintype.sum_sigma]
    _ = _ := by
        simp only [Fintype.sum_option, OrderedFinpartition.extend_none,
          OrderedFinpartition.extend_some, OrderedFinpartition.extendLeft_length,
          OrderedFinpartition.extendMiddle_length, Resummation.factorialProduct_extendLeft,
          Resummation.factorialProduct_extendMiddle, Nat.factorial_succ, Nat.cast_mul,
          Nat.cast_add, Nat.cast_one]
        congr 1
        ext c
        congr 1
        ext i
        ring_nf

theorem Resummation.orderedPartitionWeightPolynomial_succ (n : ℕ) :
    orderedPartitionWeightPolynomial (n + 1) =
      (Polynomial.C (n : ℝ) + Polynomial.X) *
          orderedPartitionWeightPolynomial n +
        (Polynomial.X + 1) *
          (Polynomial.X * Polynomial.derivative (orderedPartitionWeightPolynomial n)) := by
  classical
  rw [Resummation.orderedPartitionWeightPolynomial_succ_expansion,
    Resummation.x_derivative_orderedPartitionWeightPolynomial, orderedPartitionWeightPolynomial]
  calc
    (∑ c : OrderedFinpartition n,
        (Polynomial.X ^ (c.length + 1) *
            Polynomial.C (((c.length + 1).factorial *
              orderedPartitionFactorialProduct c : ℕ) : ℝ) +
          ∑ i : Fin c.length,
            Polynomial.X ^ c.length * Polynomial.C
              ((c.length.factorial * (c.partSize i + 1) *
                orderedPartitionFactorialProduct c : ℕ) : ℝ))) =
      ∑ c : OrderedFinpartition n,
        (Polynomial.X ^ (c.length + 1) *
            Polynomial.C (((c.length + 1).factorial *
              orderedPartitionFactorialProduct c : ℕ) : ℝ) +
          Polynomial.X ^ c.length * Polynomial.C
            ((c.length.factorial * (n + c.length) *
              orderedPartitionFactorialProduct c : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Resummation.orderedPartitionSomeWeightSum]
    _ = ∑ c : OrderedFinpartition n,
        ((Polynomial.C (n : ℝ) + Polynomial.X) *
            (Polynomial.X ^ c.length *
              Polynomial.C ((c.length.factorial *
                orderedPartitionFactorialProduct c : ℕ) : ℝ)) +
          (Polynomial.X + 1) *
            (Polynomial.X ^ c.length *
              Polynomial.C ((c.length : ℝ) *
                ((c.length.factorial * orderedPartitionFactorialProduct c : ℕ) : ℝ)))) := by
        apply Finset.sum_congr rfl
        intro c hc
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1]
        ring_nf
    _ = (Polynomial.C (n : ℝ) + Polynomial.X) *
          (∑ c : OrderedFinpartition n,
            Polynomial.X ^ c.length *
              Polynomial.C ((c.length.factorial *
                orderedPartitionFactorialProduct c : ℕ) : ℝ)) +
        (Polynomial.X + 1) *
          (∑ c : OrderedFinpartition n,
            Polynomial.X ^ c.length *
              Polynomial.C ((c.length : ℝ) *
                ((c.length.factorial * orderedPartitionFactorialProduct c : ℕ) : ℝ))) := by
        calc
          _ =
              (∑ c : OrderedFinpartition n,
                (Polynomial.C (n : ℝ) + Polynomial.X) *
                  (Polynomial.X ^ c.length *
                    Polynomial.C ((c.length.factorial *
                      orderedPartitionFactorialProduct c : ℕ) : ℝ))) +
              (∑ c : OrderedFinpartition n,
                (Polynomial.X + 1) *
                  (Polynomial.X ^ c.length *
                    Polynomial.C ((c.length : ℝ) *
                      ((c.length.factorial * orderedPartitionFactorialProduct c : ℕ) : ℝ)))) := by
                rw [Finset.sum_add_distrib]
          _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem Resummation.orderedPartitionWeightPolynomial_zero :
    orderedPartitionWeightPolynomial 0 = 1 := by
  classical
  simp [orderedPartitionWeightPolynomial, orderedPartitionFactorialProduct]

theorem Resummation.derivative_weight_shape (n : ℕ) :
    Polynomial.derivative
        (Polynomial.C ((n + 1).factorial : ℝ) * Polynomial.X *
          (1 + Polynomial.X) ^ n) =
      Polynomial.C ((n + 1).factorial : ℝ) *
        ((1 + Polynomial.X) ^ n + Polynomial.X *
          Polynomial.C (n : ℝ) * (1 + Polynomial.X) ^ (n - 1)) := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_mul]
  simp only [Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_pow, zero_mul, zero_add]
  ring

theorem Resummation.orderedPartitionWeightPolynomial_closed_succ (n : ℕ) :
    orderedPartitionWeightPolynomial (n + 1) =
      Polynomial.C ((n + 1).factorial : ℝ) * Polynomial.X *
        (1 + Polynomial.X) ^ n := by
  induction n with
  | zero =>
      rw [Resummation.orderedPartitionWeightPolynomial_succ 0,
          Resummation.orderedPartitionWeightPolynomial_zero]
      simp
  | succ n ih =>
      rw [Resummation.orderedPartitionWeightPolynomial_succ (n + 1), ih,
        Resummation.derivative_weight_shape]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1]
      by_cases hn : n = 0
      · subst n
        simp
        ring
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp only [Nat.succ_sub_one] at *
        simp_rw [pow_succ]
        ring_nf

/-- The factorial-weighted ordered-finpartition form of the 10469
resummation. This is the all-order coefficient sum used in Composition
estimate 10528; substituting `R := d * C_g * R_h` gives the paper's
`d R (1 + d R)^(n-1) n!` factor. -/
theorem orderedFinpartitionFactorialResummation10469 {n : ℕ} (hn : 0 < n)
    (R : ℝ) :
    ∑ c : OrderedFinpartition n,
        R ^ c.length * (c.length.factorial : ℝ) *
          (orderedPartitionFactorialProduct c : ℝ) =
      (n.factorial : ℝ) * R * (1 + R) ^ (n - 1) := by
  have hpoly := Resummation.orderedPartitionWeightPolynomial_closed_succ (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hpoly
  have heval := congrArg (Polynomial.eval R) hpoly
  simpa [Polynomial.eval_finsetSum, Polynomial.eval_prod,
    orderedPartitionWeightPolynomial,
    orderedPartitionFactorialProduct,
    Nat.cast_mul, mul_assoc] using heval

/-- One block's signed-binomial factorial weight in the 10421 resummation. -/
def orderedPartitionHalfBinomialBlockWeight (r : ℕ) : ℝ :=
  (r.factorial : ℝ) * Ring.choose (1 / 2 : ℝ) r

/-- Product of the 10421 block weights over an ordered finpartition. -/
def orderedPartitionHalfBinomialBlockProduct {n : ℕ}
    (c : OrderedFinpartition n) : ℝ :=
  ∏ i : Fin c.length, orderedPartitionHalfBinomialBlockWeight (c.partSize i)

/-- The signed 10421 weight of one ordered finpartition. -/
def orderedPartitionHalfBinomialWeight {n : ℕ} (c : OrderedFinpartition n) : ℝ :=
  (-1 : ℝ) ^ c.length * (c.length.factorial : ℝ) *
    orderedPartitionHalfBinomialBlockProduct c

/-- The sum of the signed 10421 weights over ordered finpartitions. -/
def orderedPartitionHalfBinomialSum (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, orderedPartitionHalfBinomialWeight c

/-- The signed half-binomial factorial weights obey their first-order
recurrence. This is the coefficient identity used in the flow Dn induction. -/
theorem orderedPartitionHalfBinomialBlockWeight_succ (r : ℕ) :
    orderedPartitionHalfBinomialBlockWeight (r + 1) =
      (1 / 2 - (r : ℝ)) * orderedPartitionHalfBinomialBlockWeight r := by
  have hdesc (k : ℕ) :
      orderedPartitionHalfBinomialBlockWeight k =
        (descPochhammer ℤ k).smeval (1 / 2 : ℝ) := by
    unfold orderedPartitionHalfBinomialBlockWeight
    rw [Ring.descPochhammer_eq_factorial_smul_choose]
    simp [nsmul_eq_mul]
  rw [hdesc (r + 1), descPochhammer_succ_right, Polynomial.smeval_mul,
    hdesc r]
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, nsmul_eq_mul]
  ring

theorem Resummation.orderedPartitionHalfBinomialBlockProduct_extendLeft {n : ℕ}
    (c : OrderedFinpartition n) :
    orderedPartitionHalfBinomialBlockProduct c.extendLeft =
      (1 / 2 : ℝ) * orderedPartitionHalfBinomialBlockProduct c := by
  dsimp [orderedPartitionHalfBinomialBlockProduct, OrderedFinpartition.extendLeft]
  change (∏ j : Fin (c.length + 1), orderedPartitionHalfBinomialBlockWeight
      (Fin.cons (α := fun _ : Fin (c.length + 1) ↦ ℕ) 1 c.partSize j)) = _
  rw [Fin.prod_univ_succ]
  norm_num [orderedPartitionHalfBinomialBlockWeight, Ring.choose_eq_smul,
    descPochhammer]

theorem Resummation.orderedPartitionHalfBinomialBlockProduct_extendMiddle {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    orderedPartitionHalfBinomialBlockProduct (c.extendMiddle i) =
      (1 / 2 - (c.partSize i : ℝ)) *
        orderedPartitionHalfBinomialBlockProduct c := by
  classical
  dsimp [orderedPartitionHalfBinomialBlockProduct, OrderedFinpartition.extendMiddle]
  have hfun : (fun j : Fin c.length ↦
      orderedPartitionHalfBinomialBlockWeight
        (Function.update c.partSize i (c.partSize i + 1) j)) =
      Function.update (fun j : Fin c.length ↦
        orderedPartitionHalfBinomialBlockWeight (c.partSize j)) i
        (orderedPartitionHalfBinomialBlockWeight (c.partSize i + 1)) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [orderedPartitionHalfBinomialBlockWeight_succ]
    · simp [h]
  calc
    (∏ j : Fin c.length, orderedPartitionHalfBinomialBlockWeight
        (Function.update c.partSize i (c.partSize i + 1) j)) =
      ∏ j : Fin c.length, Function.update
        (fun j : Fin c.length ↦ orderedPartitionHalfBinomialBlockWeight (c.partSize j)) i
        (orderedPartitionHalfBinomialBlockWeight (c.partSize i + 1)) j := by
          exact congrArg (fun f : Fin c.length → ℝ ↦ ∏ j, f j) hfun
    _ = (1 / 2 - (c.partSize i : ℝ)) *
        orderedPartitionHalfBinomialBlockProduct c := by
          rw [Finset.prod_update_of_mem (s := Finset.univ) (i := i)
            (f := fun j : Fin c.length ↦ orderedPartitionHalfBinomialBlockWeight
              (c.partSize j)) (b := orderedPartitionHalfBinomialBlockWeight
              (c.partSize i + 1)) (Finset.mem_univ i)]
          rw [orderedPartitionHalfBinomialBlockWeight_succ]
          have hprod := Finset.mul_prod_erase (Finset.univ : Finset (Fin c.length))
            (fun j : Fin c.length ↦ orderedPartitionHalfBinomialBlockWeight
              (c.partSize j)) (Finset.mem_univ i)
          simpa [orderedPartitionHalfBinomialBlockProduct,
            Finset.sdiff_singleton_eq_erase, mul_assoc] using congrArg
              (fun z : ℝ ↦ (1 / 2 - (c.partSize i : ℝ)) * z) hprod

theorem Resummation.orderedPartitionHalfBinomialWeight_extendLeft {n : ℕ}
    (c : OrderedFinpartition n) :
    orderedPartitionHalfBinomialWeight c.extendLeft =
      -(((c.length + 1 : ℕ) : ℝ) / 2) *
        orderedPartitionHalfBinomialWeight c := by
  simp only [orderedPartitionHalfBinomialWeight, OrderedFinpartition.extendLeft_length,
    Resummation.orderedPartitionHalfBinomialBlockProduct_extendLeft, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  ring

theorem Resummation.orderedPartitionHalfBinomialWeight_extendMiddle {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    orderedPartitionHalfBinomialWeight (c.extendMiddle i) =
      (1 / 2 - (c.partSize i : ℝ)) *
        orderedPartitionHalfBinomialWeight c := by
  simp only [orderedPartitionHalfBinomialWeight,
    OrderedFinpartition.extendMiddle_length,
    Resummation.orderedPartitionHalfBinomialBlockProduct_extendMiddle]
  ring

theorem Resummation.orderedPartitionHalfBinomialSum_succ (n : ℕ) :
    orderedPartitionHalfBinomialSum (n + 1) =
      -((n : ℝ) + 1 / 2) * orderedPartitionHalfBinomialSum n := by
  classical
  unfold orderedPartitionHalfBinomialSum
  calc
    (∑ c : OrderedFinpartition (n + 1), orderedPartitionHalfBinomialWeight c) =
      ∑ p : (c : OrderedFinpartition n) × Option (Fin c.length),
        orderedPartitionHalfBinomialWeight (p.1.extend p.2) := by
          symm
          exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv n) _ _ (fun _ ↦ rfl)
    _ =
      ∑ c : OrderedFinpartition n, ∑ o : Option (Fin c.length),
        orderedPartitionHalfBinomialWeight (c.extend o) := by
          rw [Fintype.sum_sigma]
    _ = ∑ c : OrderedFinpartition n,
        (orderedPartitionHalfBinomialWeight c.extendLeft +
          ∑ i : Fin c.length,
            orderedPartitionHalfBinomialWeight (c.extendMiddle i)) := by
          simp only [Fintype.sum_option, OrderedFinpartition.extend_none,
            OrderedFinpartition.extend_some]
    _ = ∑ c : OrderedFinpartition n,
        (-(((c.length + 1 : ℕ) : ℝ) / 2) *
            orderedPartitionHalfBinomialWeight c +
          (∑ i : Fin c.length, (1 / 2 - (c.partSize i : ℝ))) *
            orderedPartitionHalfBinomialWeight c) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Resummation.orderedPartitionHalfBinomialWeight_extendLeft]
          simp_rw [Resummation.orderedPartitionHalfBinomialWeight_extendMiddle]
          rw [← Finset.sum_mul]
    _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          have hsize : ∑ i : Fin c.length, (c.partSize i : ℝ) = n := by
            exact_mod_cast Resummation.orderedPartition_partSize_sum c
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, hsize]
          simp only [Nat.cast_add, Nat.cast_one]
          ring

/-- The all-order 10421 signed-binomial resummation in ordered-finpartition
form. -/
theorem orderedFinpartitionResummation10421 (n : ℕ) :
    orderedPartitionHalfBinomialSum n =
      2 * ((n + 1).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 1) := by
  induction n with
  | zero =>
      simp [orderedPartitionHalfBinomialSum, orderedPartitionHalfBinomialWeight,
        orderedPartitionHalfBinomialBlockProduct, orderedPartitionHalfBinomialBlockWeight,
        Ring.choose_eq_smul, descPochhammer]
  | succ n ih =>
      rw [Resummation.orderedPartitionHalfBinomialSum_succ, ih]
      have hblock := orderedPartitionHalfBinomialBlockWeight_succ (n + 1)
      change ((n + 2).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 2) =
        (1 / 2 - ((n + 1 : ℕ) : ℝ)) *
          (((n + 1).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 1)) at hblock
      have hblock' : ((n + 1 + 1).factorial : ℝ) *
          Ring.choose (1 / 2 : ℝ) (n + 1 + 1) =
          -((n : ℝ) + 1 / 2) *
            (((n + 1).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 1)) := by
        rw [show n + 1 + 1 = n + 2 by omega, hblock]
        push_cast
        ring
      calc
        -((n : ℝ) + 1 / 2) *
            (2 * ((n + 1).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 1)) =
          2 * (-((n : ℝ) + 1 / 2) *
            (((n + 1).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 1))) := by ring
        _ = 2 * (((n + 1 + 1).factorial : ℝ) *
              Ring.choose (1 / 2 : ℝ) (n + 1 + 1)) := by rw [← hblock']
        _ = 2 * ((n + 1 + 1).factorial : ℝ) *
              Ring.choose (1 / 2 : ℝ) (n + 1 + 1) := by ring

end AVenhance.FaaDiBruno

end
