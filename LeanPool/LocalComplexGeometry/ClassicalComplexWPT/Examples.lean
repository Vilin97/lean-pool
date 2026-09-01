/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.EdgeCases
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Audited examples for the public statement

These examples exercise the derivative convention, coefficient indexing,
monicity, genuine parameter dependence, nonconstant units, and the `n = 0`
and `d = 0` semantics of the public interface.
-/

open scoped BigOperators Topology


namespace ClassicalComplexWPT

/-- The distinguished monomial has exact order `d`; its `d`-th derivative is `d!`. -/
theorem exactOrder_monomial (n d : ℕ) :
    ExactOrderInLastVariable (fun x : Ambient n ↦ x.2 ^ d) d := by
  constructor
  · intro k hk
    change iteratedDeriv k (fun w : ℂ ↦ w ^ d) 0 = 0
    simpa [ne_of_lt hk] using
      (iteratedDeriv_fun_pow_zero (𝕜 := ℂ) (n := k) (m := d))
  · change iteratedDeriv d (fun w : ℂ ↦ w ^ d) 0 ≠ 0
    simp

/-- The monomial is prepared by zero lower coefficients and the constant unit one. -/
theorem isWeierstrassPreparation_monomial (n d : ℕ) :
    IsWeierstrassPreparation (fun x : Ambient n ↦ x.2 ^ d) d
      (fun _ _ ↦ 0) (fun _ ↦ 1) := by
  refine ⟨fun _ ↦ analyticAt_const, fun _ ↦ rfl, analyticAt_const, one_ne_zero, ?_⟩
  filter_upwards
  simp [preparedPolynomial]

/-- For every degree, `w^d + z₀` has exact distinguished-variable order `d`. -/
theorem exactOrder_pow_add_first (d : ℕ) :
    ExactOrderInLastVariable (fun x : Ambient 1 ↦ x.2 ^ d + x.1 0) d := by
  constructor
  · intro k hk
    change iteratedDeriv k (fun w : ℂ ↦ w ^ d + (0 : Base 1) 0) 0 = 0
    simpa [ne_of_lt hk] using
      (iteratedDeriv_fun_pow_zero (𝕜 := ℂ) (n := k) (m := d))
  · change iteratedDeriv d (fun w : ℂ ↦ w ^ d + (0 : Base 1) 0) 0 ≠ 0
    simp

/-- For positive degree, `w^d + z₀` has the advertised parameter-dependent prepared form. -/
theorem isWeierstrassPreparation_pow_add_first (d : ℕ) (hd : 0 < d) :
    IsWeierstrassPreparation (fun x : Ambient 1 ↦ x.2 ^ d + x.1 0) d
      (fun i z ↦ if (i : ℕ) = 0 then z 0 else 0) (fun _ ↦ 1) := by
  classical
  refine ⟨?_, ?_, analyticAt_const, one_ne_zero, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, ite_true]
      let pr : Base 1 →L[ℂ] ℂ :=
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)
      exact pr.analyticAt 0
    · simp only [hi, ite_false]
      exact analyticAt_const
  · intro i
    simp
  · filter_upwards with x
    simp only [one_mul]
    unfold preparedPolynomial
    rw [Finset.sum_eq_single ⟨0, hd⟩]
    · simp
    · intro b _ hb
      have hb0 : (b : ℕ) ≠ 0 := by
        intro h
        apply hb
        apply Fin.ext
        simpa using h
      simp [hb0]
    · simp

/-- A nonconstant unit times a prepared degree-one polynomial is still prepared. -/
theorem isWeierstrassPreparation_nonconstantUnit :
    IsWeierstrassPreparation
      (fun x : Ambient 1 ↦ (1 + x.2) * (x.2 + x.1 0)) 1
      (fun _ z ↦ z 0) (fun x ↦ 1 + x.2) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ rfl, ?_, by simp, ?_⟩
  · let pr : Base 1 →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)
    exact pr.analyticAt 0
  · exact analyticAt_const.add analyticAt_snd
  · filter_upwards
    simp [preparedPolynomial]

/-- Its distinguished slice has exact order one. -/
theorem exactOrder_nonconstantUnit :
    ExactOrderInLastVariable
      (fun x : Ambient 1 ↦ (1 + x.2) * (x.2 + x.1 0)) 1 := by
  constructor
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp [lastSlice]
  · unfold lastSlice
    simp only [Pi.zero_apply, add_zero]
    rw [iteratedDeriv_succ']
    simp only [iteratedDeriv_zero]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    norm_num

end ClassicalComplexWPT
