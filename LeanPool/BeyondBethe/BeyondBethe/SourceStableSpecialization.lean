/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.SourceStableClosure
import LeanPool.BeyondBethe.BeyondBethe.SourceStableTable
import Mathlib.Tactic

/-! # Source Stable Specialization -/

namespace BeyondBethe

/-!
# Finite real-boundary specialization

The source induction freezes every variable except the next left--right pair.
This file proves that operation from the one-coordinate closure theorem.  The
proof keeps the two classes of variables separated by a sum type and performs
an explicit induction on the recursively finite type `PairVariables`.
-/

noncomputable def partialSpecialization
    {κ τ : Type*} (p : MvPolynomial (κ ⊕ τ) ℂ) (x : κ → ℝ) :
    MvPolynomial τ ℂ :=
  p.eval₂ MvPolynomial.C (Sum.elim (fun i ↦ MvPolynomial.C (x i : ℂ)) MvPolynomial.X)

@[simp]
theorem partialSpecialization_eval
    {κ τ : Type*} (p : MvPolynomial (κ ⊕ τ) ℂ) (x : κ → ℝ)
    (z : τ → ℂ) :
    (partialSpecialization p x).eval z =
      p.eval (Sum.elim (fun i ↦ (x i : ℂ)) z) := by
  change MvPolynomial.eval₂ (RingHom.id ℂ) z
      (p.eval₂ MvPolynomial.C
        (Sum.elim (fun i ↦ MvPolynomial.C (x i : ℂ)) MvPolynomial.X)) = _
  rw [← MvPolynomial.eval₂_assoc]
  apply MvPolynomial.eval₂_congr
  intro i d hi hd
  cases i with
  | inl i => simp
  | inr i => simp

theorem partialSpecialization_zero
    {κ τ : Type*} (x : κ → ℝ) :
    partialSpecialization (0 : MvPolynomial (κ ⊕ τ) ℂ) x = 0 := by
  simp [partialSpecialization]

/-- Move the distinguished `none` coordinate of `Option κ` in front of all
remaining variables. -/
def optionSumEquiv (κ τ : Type*) : (Option κ ⊕ τ) ≃ Option (κ ⊕ τ) where
  toFun
    | Sum.inl none => none
    | Sum.inl (some i) => some (Sum.inl i)
    | Sum.inr j => some (Sum.inr j)
  invFun
    | none => Sum.inl none
    | some (Sum.inl i) => Sum.inl (some i)
    | some (Sum.inr j) => Sum.inr j
  left_inv x := by cases x with
    | inl x => cases x <;> rfl
    | inr x => rfl
  right_inv x := by cases x with
    | none => rfl
    | some x => cases x <;> rfl

noncomputable def sumOptionReindex
    {κ τ : Type*} (p : MvPolynomial (Option κ ⊕ τ) ℂ) :
    MvPolynomial (Option (κ ⊕ τ)) ℂ :=
  MvPolynomial.rename (optionSumEquiv κ τ) p

noncomputable def sumOptionSpecialization
    {κ τ : Type*} (p : MvPolynomial (Option κ ⊕ τ) ℂ) (c : ℝ) :
    MvPolynomial (κ ⊕ τ) ℂ :=
  optionConstantCoefficient (sumOptionReindex p) +
    MvPolynomial.C (c : ℂ) * optionLinearCoefficient (sumOptionReindex p)

theorem sumOptionReindex_multiaffine
    {κ τ : Type*} {p : MvPolynomial (Option κ ⊕ τ) ℂ}
    (hp : IsComplexMultiaffine p) :
    IsComplexMultiaffine (sumOptionReindex p) := by
  intro i
  change MvPolynomial.degreeOf i
      (MvPolynomial.rename (optionSumEquiv κ τ) p) ≤ 1
  have hdegree := MvPolynomial.degreeOf_rename_of_injective
    (optionSumEquiv κ τ).injective ((optionSumEquiv κ τ).symm i) (p := p)
  convert hdegree.trans_le (hp ((optionSumEquiv κ τ).symm i)) using 1
  simp

theorem sumOptionReindex_stable
    {κ τ : Type*} {p : MvPolynomial (Option κ ⊕ τ) ℂ}
    (hp : IsUpperHalfPlaneStable p) :
    IsUpperHalfPlaneStable (sumOptionReindex p) := by
  exact hp.rename (optionSumEquiv κ τ)

theorem sumOptionSpecialization_multiaffine
    {κ τ : Type*} (p : MvPolynomial (Option κ ⊕ τ) ℂ) (c : ℝ)
    (hp : IsComplexMultiaffine p) :
    IsComplexMultiaffine (sumOptionSpecialization p c) := by
  exact option_specialization_multiaffine (sumOptionReindex p) c
    (sumOptionReindex_multiaffine hp)

theorem sumOptionSpecialization_stableOrZero
    {κ τ : Type*} [Fintype κ] [Fintype τ]
    (p : MvPolynomial (Option κ ⊕ τ) ℂ) (c : ℝ)
    (hmulti : IsComplexMultiaffine p)
    (hstable : IsUpperHalfPlaneStable p) :
    sumOptionSpecialization p c = 0 ∨
      IsUpperHalfPlaneStable (sumOptionSpecialization p c) := by
  exact option_specialize_real_stableOrZero (sumOptionReindex p) c
    (sumOptionReindex_multiaffine hmulti none)
    (sumOptionReindex_stable hstable)

@[simp]
theorem optionSumEquiv_apply_inl_none {κ τ : Type*} :
    optionSumEquiv κ τ (Sum.inl none) = none := rfl

@[simp]
theorem optionSumEquiv_apply_inl_some {κ τ : Type*} (i : κ) :
    optionSumEquiv κ τ (Sum.inl (some i)) = some (Sum.inl i) := rfl

@[simp]
theorem optionSumEquiv_apply_inr {κ τ : Type*} (j : τ) :
    optionSumEquiv κ τ (Sum.inr j) = some (Sum.inr j) := rfl

theorem sumOptionSpecialization_eval
    {κ τ : Type*} (p : MvPolynomial (Option κ ⊕ τ) ℂ) (c : ℝ)
    (hmulti : IsComplexMultiaffine p) (z : κ ⊕ τ → ℂ) :
    (sumOptionSpecialization p c).eval z =
      p.eval (Sum.elim (fun
        | none => (c : ℂ)
        | some i => z (Sum.inl i)) (fun j => z (Sum.inr j))) := by
  let w : Option (κ ⊕ τ) → ℂ
    | none => (c : ℂ)
    | some i => z i
  have hlinear := option_eq_linearExtension (sumOptionReindex p)
    (sumOptionReindex_multiaffine hmulti none)
  have heval : (sumOptionReindex p).eval w =
      (linearExtension
        (optionConstantCoefficient (sumOptionReindex p))
        (optionLinearCoefficient (sumOptionReindex p))).eval w := by
    exact congrArg
      (fun q : MvPolynomial (Option (κ ⊕ τ)) ℂ ↦ q.eval w) hlinear
  rw [linearExtension_eval] at heval
  have hwcomp : w ∘ some = z := by rfl
  rw [hwcomp] at heval
  calc
    (sumOptionSpecialization p c).eval z =
        (optionConstantCoefficient (sumOptionReindex p)).eval z +
          (c : ℂ) * (optionLinearCoefficient (sumOptionReindex p)).eval z := by
            simp [sumOptionSpecialization]
    _ = (sumOptionReindex p).eval w := by
      exact heval.symm
    _ = p.eval (Sum.elim (fun
        | none => (c : ℂ)
        | some i => z (Sum.inl i)) (fun j => z (Sum.inr j))) := by
      rw [sumOptionReindex, MvPolynomial.eval_rename]
      apply congrArg (fun u ↦ p.eval u)
      funext i
      cases i with
      | inl i => cases i <;> rfl
      | inr i => rfl

theorem partialSpecialization_option
    {κ τ : Type*} (p : MvPolynomial (Option κ ⊕ τ) ℂ)
    (x : Option κ → ℝ) (hmulti : IsComplexMultiaffine p) :
    partialSpecialization p x =
      partialSpecialization (sumOptionSpecialization p (x none))
        (fun i ↦ x (some i)) := by
  apply MvPolynomial.funext
  intro z
  rw [partialSpecialization_eval, partialSpecialization_eval,
    sumOptionSpecialization_eval _ _ hmulti]
  apply congrArg (fun u ↦ p.eval u)
  funext i
  cases i with
  | inl i => cases i <;> rfl
  | inr i => rfl

/-- Specializing the recursively finite set of `PairVariables` to real values
preserves upper-half-plane stability in the variables that remain. -/
theorem pairVariables_partialSpecialization_stableOrZero :
    ∀ (n : ℕ) {τ : Type*} [Fintype τ]
      (p : MvPolynomial (PairVariables n ⊕ τ) ℂ)
      (x : PairVariables n → ℝ),
      IsComplexMultiaffine p → IsUpperHalfPlaneStable p →
      partialSpecialization p x = 0 ∨
        IsUpperHalfPlaneStable (partialSpecialization p x) := by
  intro n
  induction n with
  | zero =>
      intro τ _ p x hmulti hstable
      right
      intro z hz
      rw [partialSpecialization_eval]
      apply hstable
      intro i
      cases i with
      | inl i => exact PEmpty.elim i
      | inr i => exact hz i
  | succ n ih =>
      intro τ _ p x hmulti hstable
      change MvPolynomial (Option (Option (PairVariables n)) ⊕ τ) ℂ at p
      change Option (Option (PairVariables n)) → ℝ at x
      change partialSpecialization p x = 0 ∨
        IsUpperHalfPlaneStable (partialSpecialization p x)
      have hfirst := sumOptionSpecialization_stableOrZero p (x none) hmulti hstable
      rcases hfirst with hzero | hfirst
      · left
        rw [partialSpecialization_option p x hmulti, hzero,
          partialSpecialization_zero]
      · let p₁ := sumOptionSpecialization p (x none)
        let x₁ : Option (PairVariables n) → ℝ := fun i ↦ x (some i)
        have hm₁ : IsComplexMultiaffine p₁ :=
          sumOptionSpecialization_multiaffine p (x none) hmulti
        have hsecond := sumOptionSpecialization_stableOrZero p₁ (x₁ none) hm₁ hfirst
        rcases hsecond with hzero | hsecond
        · left
          rw [partialSpecialization_option p x hmulti]
          change partialSpecialization p₁ x₁ = 0
          rw [partialSpecialization_option p₁ x₁ hm₁, hzero,
            partialSpecialization_zero]
        · let p₂ := sumOptionSpecialization p₁ (x₁ none)
          let x₂ : PairVariables n → ℝ := fun i ↦ x₁ (some i)
          have hm₂ : IsComplexMultiaffine p₂ :=
            sumOptionSpecialization_multiaffine p₁ (x₁ none) hm₁
          have htail := ih p₂ x₂ hm₂ hsecond
          rw [partialSpecialization_option p x hmulti]
          change partialSpecialization p₁ x₁ = 0 ∨
            IsUpperHalfPlaneStable (partialSpecialization p₁ x₁)
          rw [partialSpecialization_option p₁ x₁ hm₁]
          exact htail

end BeyondBethe
