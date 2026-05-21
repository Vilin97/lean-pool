/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Foundations.Basic
import LeanPool.HopfieldNet.SampCert.Samplers.Geometric.Code

/-!
# ``probGeometric`` properties

This file proves normalization and evaluation properties of the ``probGeometric`` sampler.
-/

noncomputable section

open Classical Nat

namespace SLang

section Geometric

variable (trial : SLang Bool)
variable (trial_spec : trial false + trial true = 1)
variable (trial_spec' : trial true < 1)

lemma ite_test (a b : ℕ) (x y : ENNReal) :
  @ite ENNReal (a = b) (propDecidable (a = b)) x y
   = @ite ENNReal (a = b) (instDecidableEqNat a b) x y := by
  split ; any_goals { trivial }

include trial_spec in
lemma trial_one_minus :
  trial false = 1 - trial true := by
  by_contra h
  rw [← trial_spec] at h
  rw [ENNReal.add_sub_cancel_right] at h
  · contradiction
  · by_contra h'
    rw [h'] at trial_spec
    simp at trial_spec

include trial_spec in
lemma trial_le_1 (i : ℕ) :
  trial true ^ i ≤ 1 := by
  induction i
  · simp
  · rename_i i IH
    rw [_root_.pow_succ]
    have A : trial true ≤ 1 := by
      by_contra h
      simp at h
      have B : 1 < trial false + trial true := by
        by_contra _
        simp at *
        have C : trial true ≤ 1 := le_iff_exists_add'.mpr (Exists.intro (trial false) (id trial_spec.symm))
        have D := not_le.mpr h
        contradiction
      rw [trial_spec] at B
      simp at B
    exact Left.mul_le_one IH A

include trial_spec' in
/--
A geometric series from a trial result (namely, with ratio less than 1) is finite.
-/
theorem trial_sum_ne_top :
  (∑' (n : ℕ), trial true ^ n) ≠ ⊤ := by
  rw [ENNReal.tsum_geometric]
  rw [ENNReal.inv_ne_top]
  by_contra h
  rw [tsub_eq_zero_iff_le] at h
  have A := not_le.mpr trial_spec'
  contradiction

include trial_spec' in
lemma trial_sum_ne_top' :
  ∑' (n : ℕ), trial true ^ n * trial true ≠ ⊤ := by
  have A := trial_sum_ne_top trial trial_spec'
  rw [ENNReal.tsum_eq_add_tsum_ite 0] at A
  simp [ite_test, tsum_shift'_1, pow_add] at A
  trivial

/--
The zero unrolling of ``probGeometric`` is the zero subdistribution.
-/
@[simp]
theorem geometric_zero (st₁ st₂ : Bool × ℕ) :
  probWhileCut geoLoopCond (geoLoopBody trial) 0 st₁ st₂ = 0 := by
  simp [probWhileCut]


lemma ite_simpl (x a : ℕ) (v : ENNReal) :
  (@ite ENNReal (x = a) (propDecidable (x = a)) 0 (@ite ENNReal (x = a) (instDecidableEqNat x a) v 0)) = 0 := by
  split
  · simp
  · simp

/--
Inductive formula for an unrolling of ``probGeometric`` starting in a ``(true, -)`` state.
-/
theorem geometric_succ_true (fuel n : ℕ) (st : Bool × ℕ) :
  probWhileCut geoLoopCond (geoLoopBody trial) (succ fuel) (true,n) st =
  (trial false) * probWhileCut geoLoopCond (geoLoopBody trial) fuel (false, n + 1) st +
    (trial true) * probWhileCut geoLoopCond (geoLoopBody trial) fuel (true, n + 1) st := by
  cases st
  rename_i b m
  simp [probWhileCut, probWhileFunctional, geoLoopCond, geoLoopBody, ite_apply, ENNReal.tsum_prod', tsum_bool]
  conv =>
    left
    · congr
      · rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
        right
        right
        intro x
        rw [ite_simpl]
      · rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
        right
        right
        intro x
        rw [ite_simpl]
  simp

/--
Inductive formula for an unrolling of ``probGeometric`` starting in a ``(false, -)`` state.
-/
@[simp]
theorem geometric_succ_false (fuel n : ℕ) (st : Bool × ℕ) :
  probWhileCut geoLoopCond (geoLoopBody trial) (succ fuel) (false,n) st =
  if st = (false,n) then 1 else 0 := by
  cases st
  simp [probWhileCut, probWhileFunctional, geoLoopCond, geoLoopBody, ite_apply, ENNReal.tsum_prod', tsum_bool]

/--
Evaluation for an unrolling of ``probGeometric`` on a ``(false, -)`` state
-/
@[simp]
theorem geometric_monotone_counter (fuel n : ℕ) (st : Bool × ℕ) (h1 : st ≠ (false,n)) (h2 : st.2 ≥ n) :
  probWhileCut geoLoopCond (geoLoopBody trial) fuel st (false, n) = 0 := by
  revert st
  induction fuel
  · simp
  · rename_i fuel IH
    intro st h1 h2
    cases st
    rename_i stb stn
    simp at h1
    simp at h2
    cases stb
    · simp
      exact Ne.symm (h1 rfl)
    · simp [geometric_succ_true]
      have A : (false, stn + 1) ≠ (false, n) := by
        simp
        have OR : n = stn ∨ n < stn := by exact Nat.eq_or_lt_of_le h2
        cases OR
        · rename_i h
          subst h
          exact Nat.ne_of_gt le.refl
        · rename_i h
          exact Nat.ne_of_gt (le.step h)
      have B : (true, stn + 1) ≠ (false, n) := by
        simp_all only [ne_eq, ge_iff_le, Prod.forall, Prod.mk.injEq, not_and, Bool.forall_bool, forall_const,
          Bool.true_eq_false, IsEmpty.forall_iff, true_and, and_self, not_false_eq_true]
      rw [IH _ A]
      rw [IH _ B]
      · simp
      · simp
        exact le.step h2
      · simp
        exact le.step h2

/--
Evaluation for an unrolling of ``probGeometric`` starting in a ``(true, -)`` state and ending in a ``(false, -)`` state.
-/
@[simp]
theorem geometric_progress (fuel n : ℕ) :
  probWhileCut geoLoopCond (geoLoopBody trial) (fuel + 2) (true,n) (false,n + fuel + 1) = (trial true)^fuel * (trial false) := by
  revert n
  induction fuel
  · intro n
    simp [geometric_succ_true]
  · rename_i fuel IH
    intro n
    rw [geometric_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    simp [A]
    have B : n + succ fuel + 1 = (n + 1) + fuel + 1 := by exact Nat.add_right_comm n (succ fuel) 1
    simp [B]
    simp [IH (n + 1)]
    rw [← mul_assoc]
    conv =>
      left
      left
      rw [mul_comm]
    rw [← _root_.pow_succ]

/--
Evaluation for a truncation of ``probGeometric``, starting in a ``(true, -)`` state and ending in a ``(false, -)`` state.
-/
theorem geometric_progress' (n : ℕ) (h : ¬ n = 0) :
  probWhileCut geoLoopCond (geoLoopBody trial) (n + 1) (true, 0) (false, n) = (trial true)^(n-1) * (trial false) := by
  have prog := geometric_progress trial (n - 1) 0
  simp at prog
  have A : n - 1 + 1 = n := by exact succ_pred h
  rw [A] at prog
  have B : n - 1 + 2 = n + 1 := by exact succ_inj.mpr A
  rw [B] at prog
  trivial

/--
Unrollings of ``probGeometric`` ending in a ``false`` state do not change given more fuel.
-/
theorem geometric_preservation (fuel fuel' n : ℕ) (h1 : fuel ≥ fuel') :
  probWhileCut geoLoopCond (geoLoopBody trial) (1 + fuel + 2) (true,n) (false,n + fuel' + 1)
  =
  probWhileCut geoLoopCond (geoLoopBody trial) (fuel + 2) (true,n) (false,n + fuel' + 1) := by
  revert fuel' n
  induction fuel
  · intro fuel' n h1
    have A : fuel' = 0 := by exact le_zero.mp h1
    subst A
    simp [geometric_succ_true]
  · rename_i fuel IH
    intro fuel' n h1
    conv =>
      congr
      · rw [geometric_succ_true]
      · rw [geometric_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    rw [A]
    have B : 1 + succ fuel + 1 = 1 + fuel + 2 := by exact rfl
    rw [B]
    have Pre : fuel ≥ fuel' - 1 := by exact sub_le_of_le_add h1
    have IH' := IH (fuel' - 1) (n + 1) Pre
    cases fuel'
    · simp at *
    · rename_i fuel'
      have C : succ fuel' - 1 = fuel' := by exact rfl
      rw [C] at IH'
      have D : n + 1 + fuel' + 1 = n + succ fuel' + 1 := by exact
        (Nat.add_right_comm n (succ fuel') 1).symm
      rw [D] at IH'
      rw [IH']
      exact rfl

/--
Truncations of ``probGeometric`` ending in a ``false`` state do not change given more fuel.
-/
theorem geometric_preservation' (n m : ℕ) (h1 : ¬ m = 0) (h2 : n ≥ m) :
  probWhileCut geoLoopCond (geoLoopBody trial) (n + 2) (true,0) (false,m)
  =
  probWhileCut geoLoopCond (geoLoopBody trial) (n + 1) (true,0) (false,m) := by
  have prog := geometric_preservation trial (n - 1) (m - 1) 0
  have P : ¬ n = 0 := by
      by_contra
      rename_i h
      subst h
      simp at h2
      subst h2
      contradiction
  have A : 1 + (n - 1) + 2 = n + 2 := by
    conv =>
      left
      left
      rw [add_comm]
    rw [Nat.add_right_cancel_iff]
    exact succ_pred P
  rw [A] at prog
  have B : 0 + (m - 1) + 1 = m := by
    rw [add_assoc]
    rw [Nat.zero_add]
    exact succ_pred h1
  rw [B] at prog
  have C : n - 1 + 2 = n + 1 := by
    have C' : 2 = 1 + 1 := by rfl
    rw [C']
    rw [← add_assoc]
    rw [Nat.add_right_cancel_iff]
    exact succ_pred P
  rw [C] at prog
  apply prog
  exact Nat.sub_le_sub_right h2 1

/--
Closed form for terminating executions of truncated ``probGeometric``.
-/
theorem geometric_characterization (n extra : ℕ) (h : ¬ n = 0) :
  probWhileCut geoLoopCond (geoLoopBody trial) (extra + (n + 1)) (true,0) (false,n) = (trial true)^(n-1) * (trial false) := by
  revert n
  induction extra
  · simp
    intro n h
    apply geometric_progress' trial _ h
  · rename_i extra IH
    intro n h
    have IH' := IH n h
    clear IH
    have A : extra + (n + 1) = (extra + n) + 1 := by exact rfl
    rw [A] at IH'
    rw [← geometric_preservation'] at IH'
    · have B : succ extra + (n + 1) = extra + n + 2 := by exact succ_add_eq_add_succ extra (n + 1)
      rw [B]
      trivial
    · trivial
    · exact Nat.le_add_left n extra

/--
Closed form for the limit of terminiating executions of truncated ``probGeometric``.
-/
theorem geometric_pwc_sup (n : ℕ) :
  ⨆ i, probWhileCut geoLoopCond (geoLoopBody trial) i (true, 0) (false, n) = if n = 0 then 0 else (trial true)^(n-1) * (trial false) := by
  refine iSup_eq_of_tendsto ?hf ?_
  · apply probWhileCut_monotonic
  · rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat (n + 1))]
    split
    · rename_i h
      subst h
      rw [ENNReal.tendsto_atTop_zero]
      intro ε _
      existsi 0
      intro n _
      simp [geometric_monotone_counter]
    · rename_i h
      conv =>
        congr
        intro E
        rw [geometric_characterization trial _ _ h]
      rw [tendsto_const_nhds_iff]

/--
Subprobability of ``probGeometric`` truncation returning ``true`` is zero.
-/
@[simp]
theorem geometric_returns_false (n fuel k : ℕ) (b : Bool) :
  probWhileCut geoLoopCond (geoLoopBody trial) fuel (b, k) (true,n) = 0 := by
  revert n b k
  induction fuel
  · intro n
    simp
  · rename_i fuel IH
    intro n k b
    simp [probWhileCut,probWhileFunctional,geoLoopBody,geoLoopCond]
    unfold probBind
    unfold probPure
    simp [ite_apply]
    split
    · rename_i h
      subst h
      simp [IH]
    · rename_i h
      simp at h
      subst h
      simp [IH]

lemma if_simpl_geo (x n : ℕ) :
  (@ite ENNReal (x = n) (propDecidable (x = n)) 0 (@ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 ((trial true ^ (x - 1) * trial false) * (@ite ENNReal (n = x) (propDecidable (n = (false, x).2)) 1 0)))) = 0 := by
  split
  · simp
  · split
    · simp
    · split
      · rename_i h
        subst h
        contradiction
      · simp

/--
Closed form for evaluation of ``probGeometric``.
-/
@[simp]
theorem probGeometric_apply (n : ℕ) :
  probGeometric trial n = if n = 0 then 0 else (trial true)^(n-1) * (trial false) := by
  simp only [probGeometric, Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp only [probWhile, ne_eq, Prod.mk.injEq, false_and, not_false_eq_true,
    geometric_returns_false, ciSup_const, zero_mul, tsum_zero, add_zero]
  simp only [ne_eq, Prod.mk.injEq, false_and, not_false_eq_true, geometric_pwc_sup, ite_mul,
    zero_mul]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp only [↓reduceIte, mul_one]
  conv =>
    left
    right
    right
    intro x
    rw [if_simpl_geo]
  simp only [tsum_zero, add_zero]

include trial_spec trial_spec' trial in
/--
``probGeometric`` is a proper distribution.
-/
@[simp]
theorem probGeometric_normalizes :
  (∑' n : ℕ, probGeometric trial n) = 1 := by
  simp only [probGeometric_apply]
  rw [tsum_shift'_1]
  simp only [add_tsub_cancel_right]
  rw [trial_one_minus trial trial_spec]
  have A : ∀ n : ℕ, 0 < trial true → trial true < 1 → trial true ^ n ≠ ⊤ := by
    intro n _ _
    have B := trial_le_1 trial trial_spec n
    by_contra h
    rw [h] at B
    contradiction
  conv =>
    left
    right
    intro n
    rw [ENNReal.mul_sub (A n)]
  clear A
  simp only [mul_one]
  rw [ENNReal.tsum_sub]
  · rw [ENNReal.tsum_eq_add_tsum_ite 0]
    simp only [_root_.pow_zero, ite_test, tsum_shift'_1]
    simp only [pow_add, pow_one]
    rw [ENNReal.add_sub_cancel_right]
    apply trial_sum_ne_top' trial trial_spec'
  · apply trial_sum_ne_top' trial trial_spec'
  · rw [Pi.le_def]
    intro i
    have A : 0 ≤ trial true ^ i := by exact _root_.zero_le (trial true ^ i)
    have B := trial_le_1 trial trial_spec 1
    have C := @mul_le_of_le_one_right ENNReal _ _ _ _ _ _ A B
    simp only [pow_one] at C
    trivial


include trial trial_spec trial_spec' in
/--
``probGeometric`` is a proper distribution on ``[1, ∞) ⊂ ℕ``.
-/
theorem probGeometric_normalizes' :
  (∑' n : ℕ, probGeometric trial (n + 1)) = 1 := by
  have A := probGeometric_normalizes trial trial_spec trial_spec'
  rw [ENNReal.tsum_eq_add_tsum_ite 0] at A
  simp only [probGeometric_apply, ↓reduceIte, zero_add] at A
  simp only [tsum_shift'_1, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right] at A
  simp only [probGeometric_apply, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right]
  trivial

end Geometric

end SLang
