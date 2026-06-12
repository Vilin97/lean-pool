/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/

import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Multiset.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Pi.Interval

/-!
# The Vandermonde coefficient formula

Lemma 3.1 of Alon-Nathanson-Ruzsa: a closed form for the coefficient of
`∏ i, X i ^ c i` in `(X 0 + ⋯ + X k) ^ m * ∏_{i > j} (X i - X j)`,
culminating in `Vandermonde_coefficient_formula`.
-/

open MvPolynomial
open Finset
open Matrix
open BigOperators

variable {k : ℕ}

/-- Falling factorial (s)_r = s(s-1)...(s-r + 1) -/
def fallingFactorial (s : ℕ) (r : ℕ) : ℕ :=
  if r = 0 then 1
  else ∏ i ∈ range r, (s - i)

/-- Vandermonde matrix (c^j) -/
def vandermondeMatrix (c : Fin (k + 1) → ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of (fun i j : Fin (k + 1) => (c i : ℚ) ^ (j : ℕ))

/-- Falling factorial matrix ((c)_j) -/
def fallingFactorialMatrix (c : Fin (k + 1) → ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of (fun i j : Fin (k + 1) => (fallingFactorial (c i) j : ℚ))

/-- Expected value: m! / (∏ c!) * ∏_{i>j} (c - c) -/
def expectedValue (c : Fin (k + 1) → ℕ) (m : ℕ) : ℚ :=
  (m.factorial : ℚ) * (∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
    if j.val < i.val then ((c i : ℚ) - (c j : ℚ)) else 1) /
    (∏ i : Fin (k + 1), ((c i).factorial : ℚ))

/-- Convert a function c : Fin (k + 1) → ℕ to Finsupp -/
def toFinsupp (c : Fin (k + 1) → ℕ) : (Fin (k + 1)) →₀ ℕ :=
  ⟨Finset.univ.filter (fun i => c i ≠ 0), c, fun i => by simp⟩

/- Vandermonde Coefficient Formula (Lemma 3.1):
    Let c₀, ..., cₖ be nonnegative integers and suppose that ∑ᵢ cᵢ = m + (k + 1 choose 2),
    where m is a nonnegative integer. Then the coefficient of ∏ᵢ xᵢ^{cᵢ} in the polynomial
    (x₀ + x₁ + ⋯ + xₖ)^m ∏_{i>j} (xᵢ - xⱼ) is
    (m! / ∏ᵢ cᵢ!) ∏_{i>j} (cᵢ - cⱼ).

    Proof (from the paper):
    The product ∏_{k ≥ i > j ≥ 0} (xᵢ - xⱼ) is precisely the Vandermonde determinant
    det(xᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k} which is equal to the sum
    ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} ∏_{i=0}^k xᵢ^{σ(i)},
    where S_{k + 1} denotes the set of all permutations of the k + 1 symbols 0, ..., k.

    It thus follows that the required coefficient, which we denote by C, is given by
    C = ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} m! / ((c₀ - σ(0))!(c₁ - σ(1))!⋯(cₖ - σ(k))!).

    Similarly, the product ∏_{k ≥ i > j ≥ 0} (cᵢ - cⱼ) is the Vandermonde determinant
    det(cᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}.

    For two integers r ≥ 1 and s let (s)_r denote the product s(s-1)⋯(s-r + 1) and define
    also (s)_₀ = 1 for all s. Observe that the matrix ((cᵢ)_j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}
    can be obtained from the matrix (cᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k} by subtracting
    appropriate linear combinations of the columns with indices less than j from the
    column indexed by j, for each j = k, k-1, ..., 1. Therefore, these two matrices
    have the same determinant.

    It thus follows that
    (m! / ∏ᵢ cᵢ!) ∏_{i>j} (cᵢ - cⱼ) = (m! / ∏ᵢ cᵢ!) det((cᵢ)_j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}
    = (m! / ∏ᵢ cᵢ!) ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} (c₀)_{σ(0)}(c₁)_{σ(1)}⋯(cₖ)_{σ(k)}
    = ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} m! / ((c₀ - σ(0))!(c₁ - σ(1))!⋯(cₖ - σ(k))!) = C,
    completing the proof. □
-/
noncomputable section AristotleLemmas

lemma det_fallingFactorial_eq_det_vandermonde (c : Fin (k + 1) → ℕ) :
  (fallingFactorialMatrix c).det = (vandermondeMatrix c).det := by
    -- By definition of $V$, we can write $F$ as $V * M$ where $M$ is an upper triangular matrix
    -- with ones on the diagonal.
    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
        fallingFactorialMatrix c = vandermondeMatrix c * M ∧ (∀ i, M i i = 1) ∧
            (∀ i j, i > j → M i j = 0) := by
      -- For each $j$, we can express $(falling\_factorial (c i) j)$ as a linear combination of $c
      -- i^l$ for $l \leq j$.
      have h_comb : ∀ i j, fallingFactorial (c i) j = ∑ l ∈ Finset.range (j + 1),
          (Polynomial.coeff
              (Polynomial.C 1 * (∏ m ∈ Finset.range j, (Polynomial.X - Polynomial.C (m : ℚ))))
              l) * (c i : ℚ) ^ l := by
        intro i j
        have h_poly :
            (∏ m ∈ Finset.range j, (Polynomial.X - Polynomial.C (m : ℚ))) =
              ∑ l ∈ Finset.range (j + 1),
                Polynomial.C ((Polynomial.coeff
                    (∏ m ∈ Finset.range j, (Polynomial.X - Polynomial.C (m : ℚ))) l) : ℚ) *
                  Polynomial.X ^ l := by
          nth_rw 1 [Polynomial.as_sum_range_C_mul_X_pow (∏ m ∈ Finset.range j,
              (Polynomial.X - Polynomial.C (m : ℚ)))]
          rw [Polynomial.natDegree_prod]
              <;> norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          exact fun i hi => Polynomial.X_sub_C_ne_zero _
        replace h_poly := congr_arg (Polynomial.eval (c i : ℚ)) h_poly
        simp_all? +decide [Polynomial.eval_prod, Polynomial.eval_finsetSum]
        unfold fallingFactorial
        simp_all only [Nat.cast_ite, Nat.cast_one, Nat.cast_prod]
        split
        next h =>
          subst h
          simp_all only [range_zero, prod_empty, zero_add, range_one, Polynomial.coeff_one,
              ite_mul, pow_zero,
            mul_one, zero_mul, sum_ite_eq', mem_singleton, ↓reduceIte]
        next h =>
          by_cases hi : c i < j <;> simp_all +decide only [prod_range, not_lt]
          · -- both products vanish since the factor at index ⟨c i, hi⟩ is c i - c i = 0
            rw [← h_poly]
            rw [Finset.prod_eq_zero (i := (⟨c i, hi⟩ : Fin j))
                  (Finset.mem_univ _)
                  (by change ((c i - ↑(⟨c i, hi⟩ : Fin j) : ℕ) : ℚ) = 0
                      simp)]
            symm
            apply Finset.prod_eq_zero (i := (⟨c i, hi⟩ : Fin j)) (Finset.mem_univ _)
            change (↑(c i) - ↑↑(⟨c i, hi⟩ : Fin j) : ℚ) = 0
            simp
          · exact Eq.trans
              (Finset.prod_congr rfl fun _ _ => by
                rw [Nat.cast_sub (by linarith [Fin.is_lt ‹_›])])
              h_poly
      -- Let $M$ be the matrix whose $(i, j)$-th entry is the coefficient of $c_i^l$ in the
      -- expansion of $(falling\_factorial (c i) j)$.
      use Matrix.of (fun i j => Polynomial.coeff (Polynomial.C 1 * (∏ m ∈ Finset.range j,
          (Polynomial.X - Polynomial.C (m : ℚ)))) i)
      -- aesop used to split the conjunction and simplify Polynomial.C 1 * _; do this explicitly
      simp only [Polynomial.C_1, one_mul] at h_comb ⊢
      refine ⟨?_, ?_, ?_⟩
      · ext i j
        simp? +decide [Matrix.mul_apply]
        convert h_comb i j using 1
        rw [Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Fin.is_le j)))]
        · rw [Finset.sum_range]
          simp +decide [mul_comm, vandermondeMatrix]
        · intro x a a_1
          simp_all only [Nat.succ_eq_add_one, mem_range, not_lt, mul_eq_zero, pow_eq_zero_iff',
              Nat.cast_eq_zero, ne_eq]
          exact Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by
            erw [Polynomial.natDegree_prod _ _ fun i hi => Polynomial.X_sub_C_ne_zero _]
            simpa [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] using by linarith
      · intro i
        simp only [Matrix.of_apply]
        -- The leading coefficient of the product of linear factors is 1.
        have h_leading_coeff :
            Polynomial.leadingCoeff (∏ x ∈ Finset.range i.val,
                (Polynomial.X - Polynomial.C (x : ℚ))) = 1 := by
          rw [Polynomial.leadingCoeff_prod]
          exact Finset.prod_eq_one fun _ _ => Polynomial.leadingCoeff_X_sub_C _
        rw [Polynomial.leadingCoeff,
            Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero _]
          at h_leading_coeff
        simp_all only [map_natCast]
        simpa [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] using h_leading_coeff
      · intro i j hij
        simp only [Matrix.of_apply]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        erw [Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero _]
        erw [Finset.sum_congr rfl fun _ _ => Polynomial.natDegree_X_sub_C _]
        simp_all only [sum_const, card_range, smul_eq_mul, mul_one, Fin.val_fin_lt]
    -- Since $M$ is upper triangular with ones on the diagonal, its determinant is 1.
    have h_det_M : Matrix.det M = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · simp_all only [gt_iff_lt, prod_const_one]
      · simp_all only [gt_iff_lt]
        obtain ⟨left, right⟩ := hM
        obtain ⟨left_1, right⟩ := right
        exact right
    simp_all only [gt_iff_lt, det_mul, mul_one]

lemma fallingFactorial_eq_factorial_div (n k : ℕ) :
  fallingFactorial n k = if k ≤ n then n.factorial / (n - k).factorial else 0 := by
    unfold fallingFactorial
    rcases le_or_gt k n with hn | hk
    · simp_all only [↓reduceIte]
      split
      next h =>
        subst h
        simp_all only [zero_le, tsub_zero]
        rw [Nat.div_self (Nat.factorial_pos _)]
      next h =>
        rw [Nat.div_eq_of_eq_mul_right]
        · positivity
        · rw [← Nat.choose_mul_factorial_mul_factorial hn]
          rw [mul_comm]
          congr 1
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          rw [Nat.descFactorial_eq_prod_range]
    · split
      next h =>
        subst h
        simp_all only [not_lt_zero]
      next h =>
        split
        next h_1 =>
          linarith
        next h_1 =>
          simp_all only [not_le]
          rw [Finset.prod_eq_zero_iff]
          simp_all only [mem_range]
          apply Exists.intro
          · apply And.intro
            · exact hk
            · simp_all only [tsub_self]

/-- Symmetric group sum expression C = ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} * m! / ∏ᵢ (cᵢ - σ(i))!
    Corrected to use proper sign and handle 0 case. -/
def symmetricSumFixed (c : Fin (k + 1) → ℕ) (m : ℕ) : ℚ :=
  ∑ σ : Equiv.Perm (Fin (k + 1)),
    if (∀ i, σ i ≤ c i) then
      ((σ.sign : ℤ) : ℚ) *
      ((m.factorial : ℚ) / ∏ i : Fin (k + 1), ((c i - (σ i : ℕ)).factorial : ℚ))
    else 0

lemma symmetricSumFixed_eq_expectedValue (c : Fin (k + 1) → ℕ) (m : ℕ) :
  symmetricSumFixed c m = expectedValue c m := by
    -- By definition of $expected\_value$, we know that
    -- $expected\_value c m = \frac{m!}{\prod_{i=0}^k c_i!} \cdot \prod_{i > j} (c_i - c_j)$.
    have h_def : expectedValue c m = (m.factorial : ℚ) *
        Matrix.det (vandermondeMatrix c) / (∏ i, ((c i).factorial : ℚ)) := by
      -- The determinant of the Vandermonde matrix is the product of (c_i - c_j) for i > j.
      have h_det_vandermonde : Matrix.det (vandermondeMatrix c) = ∏ i, ∏ j,
          if j.val < i.val then ((c i : ℚ) - (c j : ℚ)) else 1 := by
        -- By definition of Vandermonde matrix, we know that its determinant is given by the product
        -- of the differences of the entries.
        have h_vandermonde_det : ∀ (x : Fin (k + 1) → ℚ),
            Matrix.det (Matrix.of (fun i j => x i ^ j.val)) = ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
            if j.val < i.val then (x i - x j) else 1 := by
          intro x
          erw [Matrix.det_vandermonde]
          rw [Finset.prod_comm]
          simp +decide [Finset.prod_ite, Finset.filter_lt_eq_Ioi]
        convert h_vandermonde_det (fun i => c i) using 1
      unfold expectedValue
      simp_all only [Fin.val_fin_lt]
    unfold symmetricSumFixed
    -- We'll use the fact that $\det(\text{falling\_factorial\_matrix} c) = \sum_{\sigma}
    -- \text{sgn}(\sigma) \prod_i (c_i)_{\sigma(i)}$.
    have h_det_fallingFactorial : Matrix.det (fallingFactorialMatrix c) = ∑ σ :
        Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign σ : ℚ) *
        (∏ i, (fallingFactorial (c i) (σ i).val : ℚ)) := by
      rw [Matrix.det_apply']
      refine Finset.sum_bij (fun σ _ => σ.symm) ?_ ?_ ?_ ?_
      · intro a ha
        simp_all only [mem_univ]
      · intro a₁ ha₁ a₂ ha₂ a
        simp_all only [mem_univ]
        simpa using congr_arg Equiv.symm a
      · intro b a
        simp_all only [mem_univ, exists_const]
        exact ⟨b.symm, by simp +decide⟩
      · intro a ha
        simp_all only [Equiv.Perm.sign_symm, mul_eq_mul_left_iff, Int.cast_eq_zero, Units.ne_zero,
            or_false]
        simp_all only [mem_univ]
        conv_rhs => rw [← Equiv.prod_comp a]
        exact Finset.prod_congr rfl fun i _ => by
          simp_all only [mem_univ, Equiv.symm_apply_apply]
          rfl
    -- By definition of $falling\_factorial$, we know that $\prod_i (c_i)_{\sigma(i)} = \prod_i
    -- \frac{c_i!}{(c_i - \sigma(i))!}$ if $\forall i, \sigma(i) \le c_i$, else 0.
    have h_fallingFactorial : ∀ σ : Equiv.Perm (Fin (k + 1)),
        (∏ i, (fallingFactorial (c i) (σ i).val : ℚ)) = if ∀ i,
        (σ i).val ≤ c i then (∏ i, ((c i).factorial : ℚ)) / (∏ i,
            ((c i - (σ i).val).factorial : ℚ)) else 0 := by
      intro σ; split_ifs
          <;> simp_all? (config := {decide := Bool.true}) [fallingFactorial_eq_factorial_div]
      · rw [← Finset.prod_div_distrib, Finset.prod_congr rfl]
        intros
        rw [Nat.cast_div (Nat.factorial_dvd_factorial <| Nat.sub_le _ _) (by positivity)]
      · rw [Finset.prod_eq_zero_iff]
        rename_i h
        simp_all only [mem_univ, ite_eq_right_iff, Nat.cast_eq_zero, Nat.div_eq_zero_iff, true_and]
        obtain ⟨w, h⟩ := h
        exact ⟨w, fun hw => False.elim <| h.not_ge hw⟩
    -- By combining the results from h_det_fallingFactorial and h_fallingFactorial, we can
    -- conclude the proof.
    have h_final : Matrix.det (vandermondeMatrix c) = (∏ i, ((c i).factorial : ℚ)) *
        (∑ σ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign σ : ℚ) * (if ∀ i,
            (σ i).val ≤ c i then 1 / (∏ i, ((c i - (σ i).val).factorial : ℚ)) else 0)) := by
      convert h_det_fallingFactorial using 1
      · convert det_fallingFactorial_eq_det_vandermonde c |> Eq.symm
      · rw [Finset.mul_sum _ _ _]; exact Finset.sum_congr rfl fun _ _ =>
          by rw [h_fallingFactorial]; split_ifs <;> ring
    rw [h_def, h_final]
    norm_num [Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv,
        Finset.prod_eq_zero_iff, Nat.factorial_ne_zero]

/-- Multinomial expansion of $(\sum_i X_i)^m$ as a sum over weak compositions of `m`.
Extracted from `coeff_term` to keep that proof under the 200-line limit. -/
private lemma sum_X_pow_eq_multinomial_sum (m : ℕ) :
    (∑ i : Fin (k + 1), MvPolynomial.X i : MvPolynomial (Fin (k + 1)) ℚ) ^ m =
        ∑ d ∈ Finset.filter (fun d : Fin (k + 1) → ℕ => ∑ i,
            d i = m) (Finset.Iic (fun _ => m)), (Nat.factorial m / (∏ i,
                Nat.factorial (d i))) • (∏ i, (MvPolynomial.X i) ^ (d i)) := by
  rw [Finset.sum_pow]
  refine Finset.sum_bij (fun d _ => fun i => Multiset.count i d) ?h_mem ?h_inj
      ?h_surj ?h_eq
  case h_mem =>
    intro a _
    simp only [Finset.mem_filter, Finset.mem_Iic]
    refine ⟨?_, ?_⟩
    · exact fun i => le_trans (Multiset.count_le_card _ _) (by simp)
    · -- ∑ i, Multiset.count i ↑a = a.card = m
      classical
      rw [Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)]
      exact a.prop
  case h_inj =>
    intro a₁ _ a₂ _ heq
    apply Sym.coe_injective
    apply Multiset.ext.mpr
    exact fun i => congr_fun heq i
  case h_surj =>
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Iic] at hb
    obtain ⟨_, hb_sum⟩ := hb
    refine ⟨⟨Finset.univ.val.bind fun i => Multiset.replicate (b i) i, ?_⟩, ?_, ?_⟩
    · simp only [Multiset.card_bind, Function.comp_def,
        Multiset.card_replicate]
      change ∑ i, b i = m
      exact hb_sum
    · simp
    · ext i
      simp? +decide [Multiset.count_bind]
      induction i using Fin.inductionOn
          <;> simp_all? (config := {decide := Bool.true})
              [Multiset.count_replicate, List.sum_ofFn]
      exact fun h => absurd h (ne_of_lt (Fin.succ_pos _))
  case h_eq =>
    intro a _
    classical
    -- Equate `countPerms` with `m! / ∏ (count!)` and extend the inner
    -- product on `(↑a).toFinset` to `Finset.univ` (off-support terms are 1).
    beta_reduce
    rw [Finset.prod_multiset_map_count]
    have h_count_perms : (↑a : Multiset (Fin (k + 1))).countPerms
        = m.factorial /
          ∏ x ∈ (↑a : Multiset (Fin (k + 1))).toFinset,
            (Multiset.count x ↑a).factorial := by
      rw [Multiset.countPerms, Finsupp.multinomial_eq, Nat.multinomial]
      have hsupp :
          ((↑a : Multiset (Fin (k + 1))).toFinsupp.support) =
            (↑a : Multiset (Fin (k + 1))).toFinset := by
        ext x; simp [Multiset.toFinsupp, Multiset.mem_toFinset]
      rw [hsupp]
      have hsum_card :
          ((↑a : Multiset (Fin (k + 1))).toFinset.sum
              (fun x => Multiset.count x ↑a))
            = (↑a : Multiset (Fin (k + 1))).card :=
        Multiset.toFinset_sum_count_eq _
      have hcard_eq : (↑a : Multiset (Fin (k + 1))).card = m := a.2
      rw [show
          (((↑a : Multiset (Fin (k + 1))).toFinset.sum
              fun x => (↑a : Multiset (Fin (k + 1))).toFinsupp x) : ℕ)
            = m from by
          simp only [Multiset.toFinsupp_apply]
          rw [hsum_card, hcard_eq]]
      apply congrArg
      apply Finset.prod_congr rfl
      intros; rfl
    have h_prod_extend :
        (∏ x ∈ (↑a : Multiset (Fin (k + 1))).toFinset,
            (Multiset.count x (↑a : Multiset (Fin (k + 1)))).factorial)
          = ∏ x : Fin (k + 1),
              (Multiset.count x (↑a : Multiset (Fin (k + 1)))).factorial := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro x _ hx
      rw [Multiset.count_eq_zero.mpr (by simpa using hx)]
      rfl
    -- The LHS is `↑countPerms * ∏ m_1 ∈ (↑a).toFinset, X m_1 ^ count`.
    -- The RHS is `(m! / ∏ i, count!) • ∏ i, X i ^ count`.
    rw [nsmul_eq_mul]
    -- Now both sides are `_ * _`; congr on the two factors.
    congr 1
    · -- ↑countPerms = ↑(m! / ∏ i, count!)
      rw [← h_prod_extend]
      exact congrArg _ h_count_perms
    · -- ∏ m_1 ∈ (↑a).toFinset, X m_1 ^ count = ∏ i, X i ^ count
      apply Finset.prod_subset (Finset.subset_univ _)
      intro x _ hx
      rw [Multiset.count_eq_zero.mpr (by simpa using hx), pow_zero]

lemma coeff_term (c : Fin (k + 1) → ℕ) (m : ℕ) (σ : Equiv.Perm (Fin (k + 1)))
    (h_sum : ∑ i, c i = m + ((k + 1).choose 2)) :
    MvPolynomial.coeff (toFinsupp c) (
        (∑ i : Fin (k + 1), X i) ^ m * ∏ i : Fin (k + 1), X i ^ (σ i : ℕ)) =
    if (∀ i, σ i ≤ c i) then (m.factorial : ℚ) / ∏ i : Fin (k + 1),
        ((c i - (σ i : ℕ)).factorial : ℚ) else 0 := by
      rw [MvPolynomial.coeff_mul]
      split
      next h =>
          rw [Finset.sum_eq_single (toFinsupp (fun i => c i - (σ i : ℕ)),
              toFinsupp (fun i => (σ i : ℕ)))]
          · norm_num +zetaDelta at *
            rw [show (∏ i : Fin (k + 1),
                  MvPolynomial.X i ^ (σ i : ℕ) : MvPolynomial (Fin (k + 1)) ℚ) =
                MvPolynomial.monomial (toFinsupp fun i => (σ i : ℕ)) 1 from ?_]
            · rw [MvPolynomial.coeff_monomial]
              simp_all only [↓reduceIte, mul_one]
              -- Apply the multinomial theorem to expand $(\sum_{i=0}^k X_i)^m$.
              have h_multinomial := sum_X_pow_eq_multinomial_sum (k := k) m
              -- Since $\sum_{i=0}^k (c_i - \sigma(i)) = m$, the coefficient of $X^{c-\sigma}$ in
              -- the multinomial expansion is $m! / \prod_{i=0}^k (c_i - \sigma(i))!$.
              have h_coeff : ∑ i, (c i - (σ i : ℕ)) = m := by
                zify at *
                rw [Finset.sum_congr rfl fun _ _ => Nat.cast_sub <| by linarith [h ‹_›]];
                simp_all only [Nat.cast_le, nsmul_eq_mul, sum_sub_distrib]
                rw [Equiv.sum_comp σ fun x => (x : ℤ)]; norm_num [Nat.choose_two_right]; ring_nf
                exact Eq.symm (Nat.recOn k (by norm_num) fun n ih => by
                  norm_num [Fin.sum_univ_castSucc] at *
                  linarith [
                    Nat.div_mul_cancel
                      (show 2 ∣ n + 1 + (n + 1) ^ 2
                        from even_iff_two_dvd.mp (by simp +arith +decide [parity_simps])),
                    Nat.div_mul_cancel
                      (show 2 ∣ n + (n) ^ 2
                        from even_iff_two_dvd.mp (by simp +arith +decide [parity_simps]))])
              rw [h_multinomial, MvPolynomial.coeff_sum]
              rw [Finset.sum_eq_single (fun i => c i - (σ i : ℕ))]
              · norm_num [MvPolynomial.coeff_smul, MvPolynomial.coeff_X_pow,
                  Finset.prod_pow_eq_pow_sum]
                erw [MvPolynomial.coeff_C_mul]
                rw [Nat.cast_div_charZero]
                · rw [show (∏ i : Fin (k + 1),
                        MvPolynomial.X i ^ (c i - (σ i : ℕ)) :
                          MvPolynomial (Fin (k + 1)) ℚ) =
                      MvPolynomial.monomial (toFinsupp fun i => c i - (σ i : ℕ)) 1 from ?_]
                  · norm_num [MvPolynomial.coeff_monomial]
                  · simp +decide [MvPolynomial.monomial_eq]
                    rfl
                · rw [← h_coeff]
                  norm_num +zetaDelta at *
                  exact Nat.prod_factorial_dvd_factorial_sum univ fun i => c i - ↑(σ i)
              · intro d hd hd'; rw [MvPolynomial.coeff_smul]
                simp_all (config := { decide := Bool.true }) only [nsmul_eq_mul, mul_eq_zero,
                  Nat.cast_eq_zero, Nat.div_eq_zero_iff]
                rw [show (∏ i : Fin (k + 1),
                      MvPolynomial.X i ^ d i : MvPolynomial (Fin (k + 1)) ℚ) =
                    MvPolynomial.monomial (toFinsupp d) 1 from ?_]
                · simp +zetaDelta only [coeff_monomial, ite_eq_right_iff,
                      one_ne_zero, imp_false] at *
                  contrapose! hd'
                  ext i; replace hd' := congr_arg (fun f => f i) hd'.2; aesop
                · simp? (config := {decide := Bool.true}) [MvPolynomial.monomial_eq]
                  unfold toFinsupp; aesop
              · simp +zetaDelta only [mem_filter, mem_Iic, not_and, nsmul_eq_mul] at *
                exact fun h => False.elim <|
                    h (fun i => h_coeff ▸ Finset.single_le_sum
                          (fun a _ => Nat.zero_le (c a - (σ a : ℕ))) (Finset.mem_univ i))
                      h_coeff
            · rw [MvPolynomial.monomial_eq]
              simp_all only [C_1, Finsupp.prod_pow, one_mul]
              rfl
          · intro b a a_1
            simp_all only [mem_antidiagonal, ne_eq, mul_eq_zero]
            obtain ⟨fst, snd⟩ := b
            simp_all only [Prod.mk.injEq, not_and]
            contrapose! a_1
            -- By definition of $snd$, we know that $snd(i) = \sigma(i)$ for all $i$.
            have hsnd : ∀ i, snd i = (σ i : ℕ) := by
              intro i; specialize a_1; replace a := congr_arg (fun f => f i) a;
              simp_all only [ne_eq, Finsupp.coe_add, Pi.add_apply]
              obtain ⟨left, right⟩ := a_1
              -- Since snd is a monomial in the product of X_i^( i), its support is exactly the set
              -- of indices where  i is non-zero. Therefore, (snd i) must equal ( i : ℕ).
              have h_snd_support : snd = ∑ i, Finsupp.single i (σ i : ℕ) := by
                simp_all? (config := {decide := Bool.true}) [MvPolynomial.X_pow_eq_monomial]
                -- Since snd is a monomial in the product of X_i^( i), its support is exactly the
                -- set of indices where  i is non-zero. Therefore, snd must be equal to the sum of
                -- the singletons of  i.
                have h_snd_support : snd = ∑ i, Finsupp.single i (σ i : ℕ) := by
                  have h_prod : ∏ i,
                      (MvPolynomial.monomial (Finsupp.single i (σ i : ℕ)) 1 :
                        MvPolynomial (Fin (k + 1)) ℚ) =
                      MvPolynomial.monomial (∑ i, Finsupp.single i (σ i : ℕ)) 1 := by
                    induction (Finset.univ : Finset (Fin (k + 1))) using Finset.induction
                    · simp_all only [prod_empty, sum_empty, monomial_zero', C_1]
                    · simp_all only [not_false_eq_true, prod_insert, monomial_mul, mul_one,
                          sum_insert]
                  simp_all only [coeff_monomial, ite_eq_right_iff, one_ne_zero, imp_false,
                      Decidable.not_not]
                exact h_snd_support
              simp +decide [h_snd_support, Finsupp.single_apply]
            simp_all? +decide [Finsupp.ext_iff, toFinsupp]
            exact fun i => eq_tsub_of_add_eq <| a i
          · contrapose!
            unfold toFinsupp
            intro a
            simp_all only [Finset.mem_antidiagonal, mul_ne_zero_iff, ne_eq]
            obtain ⟨left, right⟩ := a
            ext a : 1
            simp_all only [Finsupp.coe_add, Finsupp.coe_mk, Pi.add_apply, Nat.sub_add_cancel]
      next h =>
        rw [Finset.sum_eq_zero]
        intros
        rename_i x a
        simp_all only [not_forall, not_le, mem_antidiagonal, mul_eq_zero]
        obtain ⟨fst, snd⟩ := x
        obtain ⟨w, h⟩ := h
        simp_all only
        rw [Finsupp.ext_iff] at a
        specialize a w
        simp_all only [Finsupp.coe_add, Pi.add_apply]
        -- Since $snd w < \sigma w$, the exponent of $w$ in $snd$ is less than $\sigma w$, which
        -- means the coefficient of $snd$ in the product of $X_i^{\sigma i}$ is zero.
        have h_snd_w : snd w < σ w := by
          unfold toFinsupp at a
          simp_all only [ne_eq, Finsupp.coe_mk]
          linarith
        rw [Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ w]
        rw [MvPolynomial.coeff_mul]
        have fwd : LE.le (α := ℕ) (snd w : ℕ) (σ w : Fin (k + 1)).1 := le_of_lt h_snd_w
        have fwd_1 : c w ≤ (σ w).1 := le_of_lt h
        refine Or.inr <| Finset.sum_eq_zero fun x hx => ?_
        simp_all only [mem_antidiagonal, mul_eq_zero]
        subst hx
        simp_all only [Finsupp.coe_add, Pi.add_apply]
        obtain ⟨fst_1, snd⟩ := x
        simp_all only
        rw [MvPolynomial.coeff_X_pow]
        simp_all only [ite_eq_right_iff, one_ne_zero, imp_false]
        apply Or.inr
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [Finsupp.single_eq_same, add_lt_iff_neg_right, not_lt_zero]

end AristotleLemmas

theorem Vandermonde_coefficient_formula (c : Fin (k + 1) → ℕ) (m : ℕ)
    (h_sum : ∑ i : Fin (k + 1), c i = m + ((k + 1).choose 2)) :
    MvPolynomial.coeff (toFinsupp c)
      ((∑ i : Fin (k + 1), X i) ^ m *
       ∏ i : Fin (k + 1), ∏ j : Fin (k + 1), if j < i then (X i - X j) else 1)
    = expectedValue c m := by
  -- The coefficient of $X^c$ in $P$ is the sum over $\sigma$ of $\text{sgn}(\sigma)$ times the
  -- coefficient of $X^c$ in $(\sum X_i)^m \prod_i X_i^{\sigma(i)}$.
  have h_coeff : MvPolynomial.coeff (toFinsupp c) (
      (∑ i, MvPolynomial.X i) ^ m * ∏ i,
      (∏ j,
          if j < i then (MvPolynomial.X i - MvPolynomial.X j) else 1))
              = ∑ σ : Equiv.Perm (Fin (k + 1)), ((σ.sign : ℤ) : ℚ)
                  * MvPolynomial.coeff (toFinsupp c) ((∑ i, MvPolynomial.X i) ^ m * ∏ i,
                      (MvPolynomial.X i) ^ (σ i : ℕ)) := by
    -- The Vandermonde determinant is equal to the sum over permutations of the sign of the
    -- permutation times the product of x^((i)).
    have h_vandermonde : ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
        (if j < i then (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin (k + 1)) ℚ) else 1)
            = ∑ σ : Equiv.Perm (Fin (k + 1)), ((σ.sign : ℤ) : ℚ) • ∏ i : Fin (k + 1),
                (MvPolynomial.X i : MvPolynomial (Fin (k + 1)) ℚ) ^ (σ i : ℕ) := by
      have h_coeff : ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
          (if j < i then (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin (k + 1)) ℚ)
              else 1) =
            Matrix.det (Matrix.of (fun i j : Fin (k + 1) =>
              (MvPolynomial.X j : MvPolynomial (Fin (k + 1)) ℚ) ^ (i : ℕ))) := by
        erw [Matrix.det_transpose, Matrix.det_vandermonde]
        rw [Finset.prod_sigma', Finset.prod_sigma']
        rw [← Finset.prod_filter]
        refine Finset.prod_bij (fun x hx => ⟨x.snd, x.fst⟩) ?_ ?_ ?_ ?_
        · intro a ha
          simp_all only [mem_sigma, mem_univ, mem_Ioi, true_and]
          simp_all only [univ_sigma_univ, mem_filter, mem_univ, true_and]
        · intro a₁ ha₁ a₂ ha₂ a
          simp_all only [Sigma.mk.injEq, heq_eq_eq]
          simp_all only [univ_sigma_univ, mem_filter, mem_univ, true_and, and_self]
          obtain ⟨fst, snd⟩ := a₁
          obtain ⟨fst_1, snd_1⟩ := a₂
          obtain ⟨left, right⟩ := a
          subst left right
          simp_all only
        · intro b a
          simp_all only [mem_sigma, mem_univ, mem_Ioi, true_and, univ_sigma_univ, mem_filter,
              exists_prop, Sigma.exists]
          obtain ⟨fst, snd⟩ := b
          simp_all only [Sigma.mk.injEq, heq_eq_eq, ↓existsAndEq, true_and, exists_eq_right]
        · intro a ha
          simp_all only
      rw [h_coeff, Matrix.det_apply']
      simp +decide [Algebra.smul_def]
    simp +decide only [h_vandermonde, mul_smul_comm, Finset.mul_sum _ _ _]
    rw [MvPolynomial.coeff_sum]; aesop
  rw [h_coeff]
  rw [Finset.sum_congr rfl fun σ _ => by rw [coeff_term c m σ h_sum]]
  norm_num +zetaDelta at *
  convert symmetricSumFixed_eq_expectedValue c m using 1
