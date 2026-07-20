/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Gibbs

/-!
# Shannon.Entropy.Joint

Joint distributions on product types, marginals, conditional entropy,
and the chain rule for Shannon entropy.

These definitions and theorems support the Section 6 properties by providing
the infrastructure for multi-variable entropy identities.

## Main definitions

- `marginalFst`, `marginalSnd`: marginal distributions from a joint distribution
- `prodDist`: product (independent) distribution from two marginals
- `IsIndependent`: predicate for independence of a joint distribution
- `condEntropy`: conditional entropy `H_X(Y) = -∑ p(x,y) log(p(x,y)/p(x))`
- `mutualInfo`: mutual information `I(X;Y) = H(X) + H(Y) - H(X,Y)`

## Main results

- `chain_rule`: `H(X,Y) = H(X) + H_X(Y)`
- `entropyNat_prodDist`: `H(X × Y) = H(X) + H(Y)` for independent distributions
- `marginalFst_prodDist`, `marginalSnd_prodDist`: marginals of product distributions
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Finset Real

/-! ## Marginals and product distributions -/

/-- First marginal: `(marginalFst p)(a) = ∑_b p(a, b)`. -/
def marginalFst {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ProbDist α :=
  ⟨fun a => ∑ b, p (a, b),
    fun a => Finset.sum_nonneg fun b _ => prob_nonneg p (a, b),
    by simp_rw [← Fintype.sum_prod_type, prob_sum_eq_one p]⟩

/-- Second marginal: `(marginalSnd p)(b) = ∑_a p(a, b)`. -/
def marginalSnd {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ProbDist β :=
  ⟨fun b => ∑ a, p (a, b),
    fun b => Finset.sum_nonneg fun a _ => prob_nonneg p (a, b),
    by simp_rw [← Fintype.sum_prod_type_right, prob_sum_eq_one p]⟩

/-- Product distribution: `(prodDist p q)(a, b) = p(a) * q(b)`. -/
def prodDist {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist α) (q : ProbDist β) : ProbDist (α × β) :=
  ⟨fun ab => p ab.1 * q ab.2,
    fun ab => mul_nonneg (prob_nonneg p ab.1) (prob_nonneg q ab.2),
    by simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, prob_sum_eq_one q,
               mul_one, prob_sum_eq_one p]⟩

/-! ## Independence, conditional entropy, mutual information -/

/-- A joint distribution is independent when it factors as the product of its marginals. -/
def IsIndependent {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : Prop :=
  ∀ a b, p (a, b) = marginalFst p a * marginalSnd p b

/-- Conditional entropy `H_X(Y) = -∑_{x,y} p(x,y) log(p(x,y) / p_X(x))`.

This measures the average remaining uncertainty in `Y` once `X` is known.
The formula uses Lean's `0 / 0 = 0` and `log 0 = 0` conventions: when
`p_X(x) = 0` we also have `p(x,y) = 0`, so the term vanishes. -/
def condEntropy {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ℝ :=
  -∑ ab : α × β, p ab * Real.log (p ab / marginalFst p ab.1)

/-- Mutual information `I(X;Y) = H(X) + H(Y) - H(X,Y)`. -/
def mutualInfo {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) : ℝ :=
  entropyNat (marginalFst p) + entropyNat (marginalSnd p) - entropyNat p

/-! ## Support lemmas -/

/-- If a first marginal is zero, every joint probability with that first
coordinate is zero (since the marginal is a sum of nonnegative terms). -/
lemma prob_eq_zero_of_marginalFst_eq_zero {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) (a : α) (ha : marginalFst p a = 0) (b : β) :
    p (a, b) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun b' _ => prob_nonneg p (a, b'))).mp ha b
    (Finset.mem_univ b)

/-- A positive joint probability implies a positive first marginal. -/
lemma marginalFst_pos_of_prob_pos {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) (a : α) (b : β) (h : 0 < p (a, b)) :
    0 < marginalFst p a :=
  lt_of_lt_of_le h
    (Finset.single_le_sum (fun b' _ => prob_nonneg p (a, b')) (Finset.mem_univ b))

/-! ## Marginals of product distributions -/

/-- The first marginal of a product distribution recovers the first factor. -/
theorem marginalFst_prodDist {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist α) (q : ProbDist β) :
    marginalFst (prodDist p q) = p := by
  ext a; change ∑ b, p a * q b = p a; rw [← Finset.mul_sum, prob_sum_eq_one q, mul_one]

/-- The second marginal of a product distribution recovers the second factor. -/
theorem marginalSnd_prodDist {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist α) (q : ProbDist β) :
    marginalSnd (prodDist p q) = q := by
  ext b; change ∑ a, p a * q b = q b; rw [← Finset.sum_mul, prob_sum_eq_one p, one_mul]

/-! ## Chain rule -/

/-- **Chain rule for entropy**: `H(X,Y) = H(X) + H_X(Y)`.

The proof expands `H(X)` over the product type by distributing the marginal
weight, then combines termwise using `log(p/m) = log p - log m`. -/
theorem chain_rule {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) :
    entropyNat p = entropyNat (marginalFst p) + condEntropy p := by
  unfold entropyNat condEntropy
  suffices h : ∑ ab : α × β, p ab * Real.log (p ab) =
      (∑ a, marginalFst p a * Real.log (marginalFst p a)) +
      (∑ ab : α × β, p ab * Real.log (p ab / marginalFst p ab.1)) by linarith
  have hmargsplit : ∑ a, marginalFst p a * Real.log (marginalFst p a) =
      ∑ ab : α × β, p ab * Real.log (marginalFst p ab.1) := by
    simp_rw [show ∀ a, marginalFst p a * Real.log (marginalFst p a) =
        ∑ b, p (a, b) * Real.log (marginalFst p a) from fun a => by rw [← Finset.sum_mul]; rfl]
    exact (Fintype.sum_prod_type (fun ab => p ab * Real.log (marginalFst p ab.1))).symm
  rw [hmargsplit, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ab _
  by_cases hp : p ab = 0
  · simp [hp]
  · have hpab : 0 < p ab := lt_of_le_of_ne (prob_nonneg p ab) (Ne.symm hp)
    have hm : 0 < marginalFst p ab.1 := marginalFst_pos_of_prob_pos p ab.1 ab.2 hpab
    rw [Real.log_div (ne_of_gt hpab) (ne_of_gt hm)]; ring

/-! ## Product distribution entropy -/

/-- **Additivity for independent distributions**: `H(X × Y) = H(X) + H(Y)`.

The proof uses `log(p(a) * q(b)) = log p(a) + log q(b)` for each nonzero term,
then separates the double sum using `∑ qᵢ = 1` and `∑ pᵢ = 1`. -/
theorem entropyNat_prodDist {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist α) (q : ProbDist β) :
    entropyNat (prodDist p q) = entropyNat p + entropyNat q := by
  unfold entropyNat
  suffices h : ∑ ab : α × β, (prodDist p q) ab * Real.log ((prodDist p q) ab) =
      (∑ a, p a * Real.log (p a)) + (∑ b, q b * Real.log (q b)) by linarith
  simp_rw [show ∀ ab : α × β, (prodDist p q) ab = p ab.1 * q ab.2 from fun _ => rfl,
    Fintype.sum_prod_type]
  have key : ∀ a b, p a * q b * Real.log (p a * q b) =
      q b * (p a * Real.log (p a)) + p a * (q b * Real.log (q b)) := fun a b => by
    by_cases hpa : p a = 0
    · simp [hpa]
    · by_cases hqb : q b = 0
      · simp [hqb]
      · rw [Real.log_mul (ne_of_gt (lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hpa)))
              (ne_of_gt (lt_of_le_of_ne (prob_nonneg q b) (Ne.symm hqb)))]
        ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    prob_sum_eq_one q, one_mul, ← Finset.sum_mul, prob_sum_eq_one p, one_mul]

end

end LeanPool.Shannon1948Formalization
