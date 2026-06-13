/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Joint

/-!
# Shannon.Entropy.Properties

The fundamental properties of Shannon entropy from Section 6 of Shannon (1948,
pp. 11-12). These are consequences of the entropy formula, proved using the
Gibbs inequality and concavity of `negMulLog`.

## Main results

1. `entropyNat_eq_zero_iff` — `H(p) = 0` iff `p` is deterministic
2. `entropyNat_eq_log_card_iff` — `H(p) = log |α|` iff `p` is uniform
3. `entropyNat_jointLe_add` — subadditivity: `H(X,Y) ≤ H(X) + H(Y)`
4. `entropyNat_doublyStochastic_le` — Schur-concavity: doubly stochastic averaging
5. `condEntropy_le_entropyNat` — conditioning reduces entropy: `H_X(Y) ≤ H(Y)`
6. `condEntropy_nonneg` — conditional entropy is nonnegative
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Finset Real

/-! ## Property 1: H = 0 iff deterministic -/

/-- A distribution is deterministic if some outcome has probability one. -/
def IsDeterministic {α : Type} [Fintype α] (p : ProbDist α) : Prop :=
  ∃ a₀, p a₀ = 1

/-- If every probability is 0 or 1 and the total is 1, exactly one is 1. -/
private lemma deterministic_of_all_zero_or_one {α : Type} [Fintype α]
    (p : ProbDist α) (h : ∀ a, p a = 0 ∨ p a = 1) :
    IsDeterministic p := by
  by_contra hnd
  simp only [IsDeterministic, not_exists] at hnd
  have hall0 : ∀ a, p a = 0 := fun a => (h a).resolve_right (hnd a)
  linarith [prob_sum_eq_one p,
    Finset.sum_eq_zero (s := Finset.univ) (f := fun a => p a) (fun a _ => hall0 a)]

/-- **Property 1**: `H(p) = 0` if and only if `p` is deterministic.

Forward: `H = 0` means each `negMulLog(pᵢ) = 0`, forcing each `pᵢ ∈ {0, 1}`;
the sum constraint `∑ pᵢ = 1` then gives exactly one `pᵢ = 1`.
Backward: `1 · log 1 = 0` and `0 · log 0 = 0`. -/
theorem entropyNat_eq_zero_iff {α : Type} [Fintype α]
    (p : ProbDist α) :
    entropyNat p = 0 ↔ IsDeterministic p := by
  classical
  constructor
  · intro hH
    rw [entropyNat_eq_sum_negMulLog] at hH
    have hterms : ∀ a, Real.negMulLog (p a) = 0 := by
      have hnonneg : ∀ a ∈ Finset.univ, 0 ≤ Real.negMulLog (p a) :=
        fun a _ => Real.negMulLog_nonneg (prob_nonneg p a) (prob_le_one p a)
      exact fun a => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hH a (Finset.mem_univ a)
    apply deterministic_of_all_zero_or_one p
    intro a
    have hmul : p a * Real.log (p a) = 0 := by
      have := hterms a; unfold Real.negMulLog at this; linarith
    rcases mul_eq_zero.mp hmul with h0 | hlog
    · left; linarith [prob_nonneg p a]
    · rw [Real.log_eq_zero] at hlog
      rcases hlog with h0 | h1 | hneg1
      · left; exact h0
      · right; exact h1
      · linarith [prob_nonneg p a]
  · intro ⟨a₀, ha₀⟩
    rw [entropyNat_eq_sum_negMulLog]
    apply Finset.sum_eq_zero
    intro a _
    by_cases haa : a = a₀
    · rw [haa, ha₀]; exact Real.negMulLog_one
    · have hrest : ∑ b ∈ Finset.univ.erase a₀, p b = 0 := by
        have h1 := prob_sum_eq_one p
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a₀)] at h1
        linarith
      have : p a = 0 := le_antisymm
        ((Finset.sum_eq_zero_iff_of_nonneg (fun b _ => prob_nonneg p b)).mp
          hrest a (Finset.mem_erase.mpr ⟨haa, Finset.mem_univ a⟩)).le
        (prob_nonneg p a)
      rw [this]; exact Real.negMulLog_zero

/-! ## Property 2: H maximized at uniform -/

/-- **Property 2**: `H(p) = log |α|` if and only if `p` is uniform.

The forward direction uses strict concavity of `negMulLog` (strict Jensen):
if any `pᵢ ≠ 1/|α|`, then `H(p) < log |α|`, contradicting `H(p) = log |α|`. -/
theorem entropyNat_eq_log_card_iff {α : Type} [Fintype α] [Nonempty α]
    (p : ProbDist α) :
    entropyNat p = Real.log (Fintype.card α) ↔
    ∀ a, p a = 1 / Fintype.card α := by
  have hcard_pos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  constructor
  · intro hH
    by_contra hne
    push Not at hne
    obtain ⟨a₀, ha₀⟩ := hne
    have hlt : entropyNat p < Real.log (Fintype.card α) := by
      rw [entropyNat_eq_sum_negMulLog]
      have hlogcard : Real.log (Fintype.card α) =
          Fintype.card α * Real.negMulLog (1 / Fintype.card α) := by
        unfold Real.negMulLog
        rw [Real.log_div one_ne_zero hcard_ne, Real.log_one, zero_sub]; field_simp
      rw [hlogcard]
      have hexists : ∃ k ∈ Finset.univ, (fun a => p a) a₀ ≠ (fun a => p a) k := by
        by_contra h_all_eq
        push Not at h_all_eq
        have hall : ∀ k, p k = p a₀ := fun k => (h_all_eq k (Finset.mem_univ k)).symm
        have hsum : (∑ a, p a) = Fintype.card α * p a₀ := by
          simp_rw [hall]; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [prob_sum_eq_one p] at hsum
        exact ha₀ (by field_simp at hsum ⊢; linarith)
      have hscjensen := Real.strictConcaveOn_negMulLog.lt_map_sum
        (t := Finset.univ) (w := fun _ => 1 / (Fintype.card α : ℝ)) (p := fun a => p a)
        (fun _ _ => by positivity)
        (by simp [Finset.card_univ, hcard_ne])
        (fun _ _ => prob_nonneg p _)
        ⟨a₀, Finset.mem_univ a₀, hexists⟩
      rw [show ∑ a, (1 / (Fintype.card α : ℝ)) • p a = 1 / Fintype.card α from by
        simp [smul_eq_mul, ← Finset.mul_sum, prob_sum_eq_one p]] at hscjensen
      calc ∑ a, Real.negMulLog (p a)
          = Fintype.card α * ∑ a, (1 / (Fintype.card α : ℝ)) • Real.negMulLog (p a) := by
            simp only [smul_eq_mul]; rw [← Finset.mul_sum]; field_simp
        _ < Fintype.card α * Real.negMulLog (1 / ↑(Fintype.card α)) :=
            mul_lt_mul_of_pos_left hscjensen hcard_pos
    linarith
  · intro hunif
    rw [entropyNat_eq_sum_negMulLog]
    simp_rw [hunif, Finset.sum_const, Finset.card_univ]
    unfold Real.negMulLog
    rw [Real.log_div one_ne_zero hcard_ne, Real.log_one, zero_sub]
    simp [nsmul_eq_mul]

/-! ## Property 3: Subadditivity -/

/-- **Property 3** (subadditivity): `H(X,Y) ≤ H(X) + H(Y)`.

The proof applies `gibbs_inequality` with `q = prodDist (marginalFst p) (marginalSnd p)`,
i.e., the product of marginals. The Gibbs sum telescopes to
`H(X,Y) - H(X) - H(Y) ≤ 0`. -/
theorem entropyNat_jointLe_add {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) :
    entropyNat p ≤ entropyNat (marginalFst p) + entropyNat (marginalSnd p) := by
  let q := prodDist (marginalFst p) (marginalSnd p)
  have hsupp : ∀ ab, 0 < p ab → 0 < q ab := by
    intro ⟨a, b⟩ hab
    exact mul_pos (marginalFst_pos_of_prob_pos p a b hab)
      (lt_of_lt_of_le hab
        (Finset.single_le_sum (fun a' _ => prob_nonneg p (a', b)) (Finset.mem_univ a)))
  have hgibbs := gibbs_inequality p q hsupp
  suffices h : ∑ ab, p ab * Real.log (q ab / p ab) =
      entropyNat p - entropyNat (marginalFst p) - entropyNat (marginalSnd p) by linarith
  unfold entropyNat
  have hterm : ∀ ab : α × β,
      p ab * Real.log (q ab / p ab) =
      p ab * Real.log (marginalFst p ab.1) +
      p ab * Real.log (marginalSnd p ab.2) -
      p ab * Real.log (p ab) := by
    intro ab
    by_cases hp : p ab = 0
    · simp [hp]
    · have hpab : 0 < p ab := lt_of_le_of_ne (prob_nonneg p ab) (Ne.symm hp)
      have hm1 : 0 < marginalFst p ab.1 := marginalFst_pos_of_prob_pos p ab.1 ab.2 hpab
      have hm2 : 0 < marginalSnd p ab.2 :=
        lt_of_lt_of_le hpab
          (Finset.single_le_sum (fun a' _ => prob_nonneg p (a', ab.2)) (Finset.mem_univ ab.1))
      simp only [show q ab = marginalFst p ab.1 * marginalSnd p ab.2 from rfl]
      rw [Real.log_div (ne_of_gt (mul_pos hm1 hm2)) (ne_of_gt hpab),
          Real.log_mul (ne_of_gt hm1) (ne_of_gt hm2)]
      ring
  simp_rw [hterm, sub_eq_add_neg, Finset.sum_add_distrib]
  have hm1sum : ∑ ab : α × β, p ab * Real.log (marginalFst p ab.1) =
      ∑ a, marginalFst p a * Real.log (marginalFst p a) := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul]
    rfl
  have hm2sum : ∑ ab : α × β, p ab * Real.log (marginalSnd p ab.2) =
      ∑ b, marginalSnd p b * Real.log (marginalSnd p b) := by
    rw [Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    rfl
  rw [hm1sum, hm2sum, Finset.sum_neg_distrib]; linarith

/-! ## Property 4: Schur-concavity (doubly stochastic averaging) -/

open Matrix in
/-- Apply a doubly stochastic matrix `A` to a probability distribution `p`,
yielding the distribution with `(Ap)_i = ∑_j A_{ij} p_j`. -/
def doublyStochasticApply {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ doublyStochastic ℝ n) (p : ProbDist n) : ProbDist n :=
  ⟨fun i => ∑ j, A i j * p j,
    fun i => Finset.sum_nonneg fun j _ =>
      mul_nonneg (nonneg_of_mem_doublyStochastic hA) (prob_nonneg p j),
    by rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
       simp_rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hA, one_mul]
       exact prob_sum_eq_one p⟩

open Matrix in
/-- **Property 4** (Schur-concavity): `H(p) ≤ H(Ap)` for doubly stochastic `A`.

The proof applies Jensen's inequality for `negMulLog` row-by-row with weights
`A_{ij}`, then sums over rows and uses column-stochasticity to collapse. -/
theorem entropyNat_doublyStochastic_le {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ doublyStochastic ℝ n) (p : ProbDist n) :
    entropyNat p ≤ entropyNat (doublyStochasticApply A hA p) := by
  rw [entropyNat_eq_sum_negMulLog, entropyNat_eq_sum_negMulLog]
  have hrow : ∀ i, ∑ j, A i j * negMulLog (p j) ≤
      negMulLog (doublyStochasticApply A hA p i) := fun i => by
    change ∑ j, A i j * negMulLog (p j) ≤ negMulLog (∑ j, A i j * p j)
    have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := fun j => A i j)
      (p := fun j => (p j : ℝ)) (fun j _ => nonneg_of_mem_doublyStochastic hA)
      (sum_row_of_mem_doublyStochastic hA i) (fun j _ => prob_nonneg p j)
    simpa [smul_eq_mul] using this
  have hlhs : ∑ i, ∑ j, A i j * negMulLog (p j) = ∑ j, negMulLog (p j) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hA, one_mul]
  calc ∑ a, negMulLog (p a)
      = ∑ i, ∑ j, A i j * negMulLog (p j) := hlhs.symm
    _ ≤ ∑ i, negMulLog (doublyStochasticApply A hA p i) :=
        Finset.sum_le_sum (fun i _ => hrow i)

/-! ## Properties 5-6: Conditioning reduces entropy -/

/-- **Property 6**: conditional entropy is nonnegative.

Each ratio `p(x,y)/p_X(x) ≤ 1` (since `p(x,y) ≤ ∑_y p(x,y) = p_X(x)`),
so `log(p(x,y)/p_X(x)) ≤ 0` and each summand is nonpositive. -/
theorem condEntropy_nonneg {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) :
    0 ≤ condEntropy p := by
  unfold condEntropy
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro ab _
  by_cases hp : p ab = 0
  · simp [hp]
  · have hpab : 0 < p ab := lt_of_le_of_ne (prob_nonneg p ab) (Ne.symm hp)
    have hm : 0 < marginalFst p ab.1 := marginalFst_pos_of_prob_pos p ab.1 ab.2 hpab
    exact mul_nonpos_of_nonneg_of_nonpos hpab.le (Real.log_nonpos (div_pos hpab hm).le
      ((div_le_one hm).mpr
        (Finset.single_le_sum (fun b _ => prob_nonneg p (ab.1, b)) (Finset.mem_univ ab.2))))

/-- **Property 5**: conditioning reduces entropy, `H_X(Y) ≤ H(Y)`.

From the chain rule `H(X,Y) = H(X) + H_X(Y)` and subadditivity
`H(X,Y) ≤ H(X) + H(Y)`, we get `H_X(Y) ≤ H(Y)`. -/
theorem condEntropy_le_entropyNat {α β : Type} [Fintype α] [Fintype β]
    (p : ProbDist (α × β)) :
    condEntropy p ≤ entropyNat (marginalSnd p) :=
  le_of_add_le_add_left (a := entropyNat (marginalFst p))
    ((chain_rule p).symm ▸ entropyNat_jointLe_add p)

end

end LeanPool.Shannon1948Formalization
