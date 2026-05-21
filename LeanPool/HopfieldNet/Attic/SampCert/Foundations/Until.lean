/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.Foundations.While
import LeanPool.HopfieldNet.Attic.SampCert.Util.Util

/-!
# ``probUntil`` Properties

This file proves evaluation and normalization results about ``probUntil``.

## Implementation Notes

Many lemmas in this file deal are stated for truncations of the ``probUntil`` program
to a finite number of attempts. Because this term is not used outside this file, we
will not factor out an explicit ``probUntilCut`` term.
-/

noncomputable section

open Classical Nat ENNReal BigOperators Finset

namespace SLang

variable {T : Type}

/--
Truncation of ``probUntil`` program to zero unrollings is identically zero.
-/
@[simp]
theorem probUntilCut_zero (st : T) (body : SLang T) (cond : T → Bool) (x : T) :
  probWhileCut (fun v => decide (cond v = false)) (fun _ => body) 0 st x = 0 := by
  simp [probWhileCut]

/--
Truncation of ``probUntil`` program to any number of unrollings will evaluate to zero, for
 values which do not satisfy ``cond``.
 -/
@[simp]
theorem probUntilCut_apply_unsat (body : SLang T) (cond : T → Bool) (fuel : ℕ) (i x : T) (h : ¬ cond x) :
  probWhileCut (fun v => decide (cond v = false)) (fun _ => body) fuel i x = 0 := by
  revert i
  induction fuel
  · simp only [zero_eq, probUntilCut_zero, implies_true]
  · rename_i fuel IH
    intro j
    simp only [probWhileCut, probWhileFunctional, decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply,
      bind_apply, pure_apply]
    split
    · simp only [IH, mul_zero, tsum_zero]
    · rename_i h'
      split
      · rename_i h'
        subst h'
        simp at h'
        simp [h'] at h
      · simp

/--
``probUntil`` evaluates to zero at all values which do not satisfy ``cond``.
-/
@[simp]
theorem probUntil_apply_unsat (body : SLang T) (cond : T → Bool) (x : T) (h : ¬ cond x) :
  probUntil (body : SLang T) (cond : T → Bool) x = 0 := by
  simp only [probUntil, Bind.bind, Bool.not_eq_true, bind_apply, probWhile]
  simp only [ENNReal.tsum_eq_zero]
  simp only [_root_.mul_eq_zero]
  simp only [iSup_eq_zero]
  intro i ; right ; intro j
  apply probUntilCut_apply_unsat
  exact h

lemma if_simpl (body : SLang T) (cond : T → Bool) (x_1 x : T) :
  (if x_1 = x then 0 else if cond x_1 = true then if x = x_1 then body x_1 else 0 else 0) = 0 := by
  split
  · simp
  · split
    · split
      · rename_i h1 h2 h3
        subst h3
        contradiction
      · simp
    · simp

-- Dead code
theorem repeat_1 (body : SLang T) (cond : T → Bool) (x : T) (h : cond x) :
  ∑' (i : T), body i * probWhileCut (fun v => decide (cond v = false)) (fun _ => body) 1 i x
    = body x := by
  simp [probWhileCut, probWhileFunctional, ite_apply]
  rw [tsum_split_ite']
  simp only [tsum_zero, zero_add]
  have FOO := tsum_split_coe_right cond (fun i => @ite ℝ≥0∞ (x = ↑i) (propDecidable (x = ↑i)) (body ↑i) 0)
  rw [FOO]
  clear FOO
  conv =>
    left
    rw [ENNReal.tsum_eq_add_tsum_ite x]
  simp only [h, zero_apply, mul_zero, tsum_zero, ↓reduceIte, mul_one,
    zero_add]
  conv =>
    left
    right
    right
    intro y
    rw [if_simpl]
  simp

lemma tsum_split_ite_exp (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (i : T), if cond i = false then f i else g i)
    = (∑' i : T, if cond i = false then f i else 0) + (∑' i : T, if cond i = true then g i else 0) := by
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro b
  split
  · split
    · rename_i h h'
      rw [h'] at h
      contradiction
    · simp
  · split
    · simp
    · rename_i h h'
      simp at h'
      rw [h'] at h
      contradiction

theorem probUntilCut_closed_form (body : SLang T) (cond : T → Bool) (fuel : ℕ) (x : T) (h1 : cond x) :
  ∑' (i : T), body i * probWhileCut (fun v => decide (cond v = false)) (fun _ => body) fuel i x
    = ∑ i in range fuel, body x * (∑' x : T, if cond x then 0 else body x)^i := by
  induction fuel
  · simp only [zero_eq, probUntilCut_zero, mul_zero, tsum_zero, range_zero, sum_empty]
  · rename_i fuel IH
    unfold probWhileCut
    unfold probWhileFunctional
    simp only [decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply, bind_apply, pure_apply, mul_ite,
      mul_one, mul_zero]
    rw [tsum_split_ite_exp]
    conv =>
      left
      right
      rw [ENNReal.tsum_eq_add_tsum_ite x]
      right
      right
      intro y
      rw [if_simpl]
    simp only [h1, ↓reduceIte, tsum_zero, add_zero]
    rw [IH]
    clear IH
    conv =>
      right
      rw [Finset.sum_range_succ']
    simp only [_root_.pow_zero, mul_one]
    conv =>
      right
      left
      right
      intro k
      rw [_root_.pow_succ]
    rw [← mul_sum]
    rw [← mul_sum]
    congr
    conv =>
      right
      right
      right
      intro x
      rw [mul_comm]
    rw [← mul_sum]
    have A : ∀ i : T, @ite ℝ≥0∞ (cond i = false) (instDecidableEqBool (cond i) false)
            (body i * (body x * ∑ i in range fuel, (∑' (x : T), @ite ℝ≥0∞ (cond x = true) (instDecidableEqBool (cond x) true) 0 (body x)) ^ i)) 0
            = @ite ℝ≥0∞ (cond i = false) (instDecidableEqBool (cond i) false)
            (body i) 0 * (body x * ∑ i in range fuel, (∑' (x : T), @ite ℝ≥0∞ (cond x = true) (instDecidableEqBool (cond x) true) 0 (body x)) ^ i) := by
      intro i
      split
      · simp
      · simp
    conv =>
      left
      right
      intro i
      rw [A]
    rw [ENNReal.tsum_mul_right]
    conv =>
      rw [← mul_assoc]
      left
      left
      rw [mul_comm]
    rw [mul_assoc]
    congr
    ext i
    split
    · rename_i h
      simp [h]
    · rename_i h
      simp [h]

/--
Expression for the limit of the closed form of truncated ``until``
-/
lemma probUntilCut_convergence (body : SLang T) (cond : T → Bool) (x : T) :
  ⨆ fuel, ∑ i in range fuel, body x * (∑' x : T, if cond x then 0 else body x)^i
    = body x * (1 - ∑' x : T, if cond x then 0 else body x)⁻¹ := by
  rw [← ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_geometric]

/--
Truncated ``until`` term is monotone in the maximum number of steps.
-/
theorem probUntilCut_monotone (body : SLang T) (cond : T → Bool) (x : T) :
  ∀ (a : T), Monotone fun i => body a * probWhileCut (fun v => decide (cond v = false)) (fun _ => body) i a x := by stop
  intro a
  have A := @probWhileCut_monotonic T (fun v => decide (cond v = false)) (fun _ => body) a x
  exact Monotone.const_mul' A (body a)

/--
``until`` term evaluates to ``body``, normalizing by the total mass of elements which satisfy ``cond``.
-/
@[simp]
theorem probUntil_apply_sat (body : SLang T) (cond : T → Bool) (x : T) (h : cond x) :
  probUntil (body : SLang T) (cond : T → Bool) x
    = body x * (1 - ∑' x : T, if cond x then 0 else body x)⁻¹ := by
  simp only [probUntil, Bind.bind, Bool.not_eq_true, bind_apply, probWhile]
  rw [← probUntilCut_convergence]
  conv =>
    right
    right
    intro fuel
    rw [← probUntilCut_closed_form _ _ _ _ h]
  rw [eq_comm]
  rw [ENNReal.tsum_eq_iSup_sum]
  conv =>
    right
    right
    intro s
    right
    intro a
    rw [mul_iSup]
  conv =>
    right
    right
    intro s
    rw [finsetSum_iSup_of_monotone (probUntilCut_monotone body cond x)]
  rw [iSup_comm]
  conv =>
    right
    right
    intro j
    rw [← ENNReal.tsum_eq_iSup_sum]

/--
Closed form for evaluation of ``until``. ``until`` is:
  - zero outside support of ``cond``
  - ``body`` inside the support of ``cond``
rescaled by the total mass outside the support of ``cond``.
-/
@[simp]
theorem probUntil_apply (body : SLang T) (cond : T → Bool) (x : T) :
  probUntil (body : SLang T) (cond : T → Bool) x =
  (if cond x then body x else 0) * (1 - ∑' x : T, if cond x then 0 else body x)⁻¹ := by
  split
  · rename_i h
    simp [h, probUntil_apply_sat]
  · rename_i h
    simp [h, probUntil_apply_unsat]

/--
When ``body`` is a proper PMF, ``until`` is
  - zero outside the support of ``cond``
  - ``body`` inside the support of ``cond``
normalized into a PMF.
-/
@[simp]
theorem probUntil_apply_norm (body : SLang T) (cond : T → Bool) (x : T) (norm : ∑' x : T, body x = 1) :
  probUntil (body : SLang T) (cond : T → Bool) x =
  (if cond x then body x else 0) * (∑' x : T, if cond x then body x else 0)⁻¹ := by
  rw [probUntil_apply body cond x]
  congr
  have A : ∀ x, body x = (if cond x then body x else 0) + (if cond x then 0 else body x) := by
    intro x
    split
    · simp
    · simp
  revert norm
  conv =>
    left
    left
    right
    intro y
    rw [A]
  clear A
  rw [tsum_add ENNReal.summable ENNReal.summable]
  intro B
  have F : (∑' (x : T), if cond x = true then 0 else body x) ≠ ⊤ := by
    by_contra h
    simp [h] at B
  rw [← B]
  rw [ENNReal.add_sub_cancel_right F]

end SLang
