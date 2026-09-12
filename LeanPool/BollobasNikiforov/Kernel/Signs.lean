/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.Kernel.Data
import LeanPool.BollobasNikiforov.Kernel.SM
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Sign lemmas for the kernel auxiliaries `P` and `Z`

The expansions and nonnegativity statements for `P` and `Z` in `docs/sol.tex` §3
(`eq:functions`, after `eq:factor`).
-/

@[expose] public section

namespace BollobasNikiforov

open Finset
open scoped BigOperators

noncomputable section

variable {k : ℕ} (t q : Fin k → ℝ)

/-! ### Truncated squares -/

lemma truncSq_nonneg (ti x : ℝ) : 0 ≤ truncSq ti x :=
  sq_nonneg _

lemma truncSq_eq_zero {ti x : ℝ} (h : x ≤ ti) : truncSq ti x = 0 := by
  simp [truncSq, max_eq_right (sub_nonpos.mpr h)]

lemma truncSq_eq_sq {ti x : ℝ} (h : ti ≤ x) : truncSq ti x = (x - ti) ^ 2 := by
  simp [truncSq, max_eq_left (sub_nonneg.mpr h)]

lemma h_nonneg (hq : ∀ i, 0 < q i) (x : ℝ) : 0 ≤ h t q x :=
  sum_nonneg fun i _ ↦ mul_nonneg (hq i).le (truncSq_nonneg (t i) x)

/-! ### KR14: `Z ≥ 0` -/

/-- `Z(x) = γ x² + (γ + a₀) h(x)` is nonnegative for `x ≥ 0`. -/
lemma Z_nonneg (γ : ℝ) (hq : ∀ i, 0 < q i) (hγ : 0 < γ) {x : ℝ} (_hx : 0 ≤ x) :
    0 ≤ Z t q γ x := by
  unfold Z
  exact add_nonneg (mul_nonneg hγ.le (sq_nonneg x))
    (mul_nonneg (add_nonneg hγ.le (a0_pos t q hq).le) (h_nonneg t q hq x))

/-! ### Pairwise summation helper -/

/-- Split a vanishing-diagonal double sum into strictly upper-triangular pairs. -/
lemma sum_add_swap_lt (f : Fin k → Fin k → ℝ) (hf : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j =
      ∑ i, ∑ j ∈ univ.filter (fun j ↦ i < j), (f i j + f j i) := by
  have hunion (i : Fin k) :
      univ.erase i =
        univ.filter (fun j ↦ i < j) ∪ univ.filter (fun j ↦ j < i) := by
    ext j
    simp only [mem_erase, mem_union, mem_filter, mem_univ, and_true, true_and]
    rw [ne_comm]
    exact ne_iff_lt_or_gt
  have hdisj (i : Fin k) :
      Disjoint (univ.filter (fun j ↦ i < j)) (univ.filter (fun j ↦ j < i)) := by
    simp only [disjoint_left, mem_filter, mem_univ, true_and]
    intro j hij hji
    exact lt_asymm hij hji
  have hsplit (i : Fin k) :
      ∑ j, f i j =
        f i i + ∑ j ∈ univ.filter (fun j ↦ i < j), f i j +
          ∑ j ∈ univ.filter (fun j ↦ j < i), f i j := by
    have hi : i ∈ univ := mem_univ i
    rw [← sum_erase_add _ _ hi, hunion, sum_union (hdisj i)]
    ac_rfl
  simp_rw [hsplit, hf, zero_add]
  have hswap :
      ∑ i, ∑ j ∈ univ.filter (fun j ↦ j < i), f i j =
        ∑ i, ∑ j ∈ univ.filter (fun j ↦ i < j), f j i := by
    rw [sum_comm' (s := univ) (t := fun i ↦ univ.filter (fun j ↦ j < i))
      (t' := univ) (s' := fun j ↦ univ.filter (fun i ↦ j < i))
      (h := fun x y ↦ by simp [and_comm])]
  rw [sum_add_distrib, hswap, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_add_distrib]

/-! ### KR15: expansion of `P` -/

lemma m_one : m t q 1 = ∑ i, q i * t i := by
  simp [m]

/-- Algebraic expansion of `P` into a linear term, a sum of truncated-square
defects, and a pairwise increment. -/
lemma P_expand (x : ℝ) :
    P t q x =
      a0 t q * x +
        ∑ i, q i * t i * (x ^ 2 - truncSq (t i) x) +
          ∑ i, ∑ j ∈ univ.filter (fun j ↦ i < j),
            q i * q j * (t j - t i) *
              (truncSq (t i) x - truncSq (t j) x) := by
  set a : Fin k → ℝ := fun i ↦ truncSq (t i) x
  have hlin : m t q 1 * x ^ 2 - h1 t q x = ∑ i, q i * t i * (x ^ 2 - a i) := by
    simp only [m_one, h1, mul_sub]
    rw [sum_mul, ← sum_sub_distrib]
  have hcross :
      m t q 1 * h t q x - m t q 0 * h1 t q x =
        ∑ i, ∑ j, q i * q j * (t i - t j) * a j := by
    simp only [m, h, h1, pow_one, pow_zero, mul_one]
    rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  have hpairs :
      ∑ i, ∑ j, q i * q j * (t i - t j) * a j =
        ∑ i, ∑ j ∈ univ.filter (fun j ↦ i < j),
          q i * q j * (t j - t i) * (a i - a j) := by
    let f : Fin k → Fin k → ℝ := fun i j ↦ q i * q j * (t i - t j) * a j
    have hf : ∀ i, f i i = 0 := by intro i; simp [f]
    have hfi : ∀ i j, f i j + f j i = q i * q j * (t j - t i) * (a i - a j) := by
      intro i j
      simp only [f]
      ring
    simpa [f, hfi] using sum_add_swap_lt (k := k) f hf
  have hP :
      P t q x =
        a0 t q * x + (m t q 1 * x ^ 2 - h1 t q x) +
          (m t q 1 * h t q x - m t q 0 * h1 t q x) := by
    simp only [P, a0]
    ring
  simp only [hP, hlin, hcross, hpairs, a]

/-! ### KR16: each summand of `P` is nonnegative -/

/-- For `x ≥ 0` and `0 < tᵢ`, one has `0 ≤ x² - (x - tᵢ)₊²`. -/
lemma sq_sub_truncSq_nonneg {ti x : ℝ} (hx : 0 ≤ x) (hti : 0 < ti) :
    0 ≤ x ^ 2 - truncSq ti x := by
  rcases le_total x ti with hxt | htx
  · rw [truncSq_eq_zero hxt, sub_zero]
    exact sq_nonneg x
  · rw [truncSq_eq_sq htx, sq_sub_sq]
    have hdiff : x - (x - ti) = ti := by ring
    have hsum : x + (x - ti) = 2 * x - ti := by ring
    rw [hdiff, hsum]
    have h2x : ti ≤ 2 * x := by
      calc
        ti ≤ x := htx
        _ ≤ x + x := le_add_of_nonneg_left hx
        _ = 2 * x := (two_mul x).symm
    exact mul_nonneg (sub_nonneg.mpr h2x) hti.le

/-- For `x ≥ 0` and `0 < tᵢ ≤ tⱼ`, the truncated squares are antitone in the
threshold. -/
lemma truncSq_sub_truncSq_nonneg {ti tj x : ℝ} (_hx : 0 ≤ x) (_hti : 0 < ti)
    (htij : ti ≤ tj) : 0 ≤ truncSq ti x - truncSq tj x := by
  rcases le_total x ti with hx_le_ti | hti_le_x
  · have hx_le_tj : x ≤ tj := hx_le_ti.trans htij
    rw [truncSq_eq_zero hx_le_ti, truncSq_eq_zero hx_le_tj, sub_zero]
  · rcases le_total x tj with hx_le_tj | htj_le_x
    · rw [truncSq_eq_sq hti_le_x, truncSq_eq_zero hx_le_tj, sub_zero]
      exact sq_nonneg _
    · rw [truncSq_eq_sq hti_le_x, truncSq_eq_sq htj_le_x, sq_sub_sq]
      have hdiff : x - ti - (x - tj) = tj - ti := by ring
      have hsum : x - ti + (x - tj) = 2 * x - ti - tj := by ring
      rw [hdiff, hsum]
      have : ti + tj ≤ x + x := add_le_add (htij.trans htj_le_x) htj_le_x
      exact mul_nonneg (by linarith [this]) (sub_nonneg.mpr htij)

/-! ### KR17: `P ≥ 0` -/

/-- `P(x) ≥ 0` for `x ≥ 0` when the nodes are positive and nondecreasing and the
weights are positive. -/
lemma P_nonneg (hq : ∀ i, 0 < q i) (ht : ∀ i, 0 < t i) (hmono : Monotone t)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ P t q x := by
  rw [P_expand]
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact mul_nonneg (a0_pos t q hq).le hx
  · exact sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (hq i).le (ht i).le) (sq_sub_truncSq_nonneg hx (ht i))
  · refine sum_nonneg fun i _ ↦ sum_nonneg fun j hj ↦ ?_
    have hij : i < j := (mem_filter.mp hj).2
    have htij : t i ≤ t j := hmono hij.le
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hq i).le (hq j).le) (sub_nonneg.mpr htij))
      (truncSq_sub_truncSq_nonneg hx (ht i) htij)

end

end BollobasNikiforov
