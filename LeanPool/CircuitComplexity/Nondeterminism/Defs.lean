/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Nondeterministic Quantification of Boolean Functions

This module defines existential and universal quantification over
inputs of Boolean functions, corresponding to nondeterministic
computation.

Given `f : BitString (k + m) → Bool`, existential quantification over the
first `k` variables produces `g : BitString m → Bool` defined by
`g(y) = true` iff there exists an assignment `x : BitString k` such that
`f(x ++ y) = true`. This models a nondeterministic circuit that
guesses the first `k` input bits.

## Main definitions

* `existQuantify` — existential quantification over first `k` inputs
* `forallQuantify` — universal quantification over first `k` inputs

## Main results

* `existQuantify_eq_true` — iff characterization via existential
* `forallQuantify_eq_true` — iff characterization via universal
* `forallQuantify_eq_not_existQuantify_not` — De Morgan duality
* `existQuantify_mono` — monotonicity under pointwise implication
-/

namespace CircuitComplexity


variable {k m : Nat}

/-- Existential quantification over the first `k` inputs of a Boolean function.
    Given `f : BitString (k + m) → Bool`, produces `g : BitString m → Bool` where
    `g(y) = true` iff `∃ x : BitString k, f(x ++ y) = true`.

    This models a nondeterministic circuit that guesses the first `k` inputs. -/
def existQuantify (f : BitString (k + m) → Bool) : BitString m → Bool :=
  fun y => decide (∃ x : BitString k, f (Fin.append x y) = true)

/-- Universal quantification over the first `k` inputs of a Boolean function. -/
def forallQuantify (f : BitString (k + m) → Bool) : BitString m → Bool :=
  fun y => decide (∀ x : BitString k, f (Fin.append x y) = true)

@[simp]
theorem existQuantify_eq_true {f : BitString (k + m) → Bool} {y : BitString m} :
    existQuantify f y = true ↔ ∃ x : BitString k, f (Fin.append x y) = true := by
  simp [existQuantify]

@[simp]
theorem forallQuantify_eq_true {f : BitString (k + m) → Bool} {y : BitString m} :
    forallQuantify f y = true ↔ ∀ x : BitString k, f (Fin.append x y) = true := by
  simp [forallQuantify]

/-- De Morgan duality: universal quantification equals negated existential
    of negation. -/
theorem forallQuantify_eq_not_existQuantify_not
    (f : BitString (k + m) → Bool) (y : BitString m) :
    forallQuantify f y = !(existQuantify (fun z => !(f z)) y) := by
  unfold forallQuantify existQuantify
  cases h : decide (∀ x : BitString k, f (Fin.append x y) = true) <;>
    simp_all [decide_eq_false_iff_not, not_forall]

/-- De Morgan duality: existential quantification equals negated universal
    of negation. -/
theorem existQuantify_eq_not_forallQuantify_not
    (f : BitString (k + m) → Bool) (y : BitString m) :
    existQuantify f y = !(forallQuantify (fun z => !(f z)) y) := by
  unfold existQuantify forallQuantify
  cases h : decide (∃ x : BitString k, f (Fin.append x y) = true) <;>
    simp_all [decide_eq_false_iff_not, not_exists]

/-- Monotonicity: if `f` implies `g` pointwise, existential quantification
    preserves this. -/
theorem existQuantify_mono {f g : BitString (k + m) → Bool}
    (h : ∀ z, f z = true → g z = true) {y : BitString m} :
    existQuantify f y = true → existQuantify g y = true := by
  simp only [existQuantify_eq_true]
  rintro ⟨x, hx⟩
  exact ⟨x, h _ hx⟩

/-- Monotonicity for universal quantification. -/
theorem forallQuantify_mono {f g : BitString (k + m) → Bool}
    (h : ∀ z, f z = true → g z = true) {y : BitString m} :
    forallQuantify f y = true → forallQuantify g y = true := by
  simp only [forallQuantify_eq_true]
  intro hf x
  exact h _ (hf x)

/-- Constant true: existential quantification is always true. -/
@[simp]
theorem existQuantify_const_true :
    existQuantify (k := k) (m := m) (fun _ => true) = fun _ => true := by
  funext y; simp [existQuantify]

/-- Constant false: existential quantification is always false. -/
@[simp]
theorem existQuantify_const_false :
    existQuantify (k := k) (m := m) (fun _ => false) = fun _ => false := by
  funext y; simp [existQuantify]

/-- Constant true: universal quantification is always true. -/
@[simp]
theorem forallQuantify_const_true :
    forallQuantify (k := k) (m := m) (fun _ => true) = fun _ => true := by
  funext y; simp [forallQuantify]

/-- Constant false: universal quantification is always false. -/
@[simp]
theorem forallQuantify_const_false :
    forallQuantify (k := k) (m := m) (fun _ => false) = fun _ => false := by
  funext y; simp [forallQuantify]

/-- Restrict a Boolean function by fixing its first input to a constant.
    Reduces the input size from `(k + 1) + m` to `k + m`. -/
def restrictFirst (f : BitString ((k + 1) + m) → Bool) (b : Bool) :
    BitString (k + m) → Bool :=
  fun z => f (fun i => if h : i.val = 0 then b else z ⟨i.val - 1, by omega⟩)

/-- Decomposition: quantifying over `k + 1` variables factors as quantifying
    over `k` variables for each value of the first variable.

    `(∃ a ∈ {0,1}^{k+1}, f(a,y)) ↔ (∃ x ∈ {0,1}^k, f(0∷x,y)) ∨ (∃ x ∈ {0,1}^k, f(1∷x,y))` -/
theorem existQuantify_succ (f : BitString ((k + 1) + m) → Bool) (y : BitString m) :
    existQuantify (k := k + 1) f y =
    ((existQuantify (k := k) (restrictFirst f false) y) ||
     (existQuantify (k := k) (restrictFirst f true) y)) := by
  have bool_eq : ∀ (a b : Bool), a = b ↔ (a = true ↔ b = true) := by decide
  rw [bool_eq]
  simp only [existQuantify_eq_true, Bool.or_eq_true, restrictFirst]
  constructor
  · rintro ⟨a, ha⟩
    by_cases hb : a ⟨0, by omega⟩ = true
    · right
      refine ⟨fun i => a ⟨i.val + 1, by omega⟩, ?_⟩
      convert ha using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs with h1 h2 h3 <;> simp_all <;> try omega
      · simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega
      · congr 1
        simp [Fin.ext_iff]
        omega
    · left
      refine ⟨fun i => a ⟨i.val + 1, by omega⟩, ?_⟩
      convert ha using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs with h1 h2 h3 <;> simp_all <;> try omega
      · simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega
      · congr 1
        simp [Fin.ext_iff]
        omega
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨fun i => if h : i.val = 0 then false else x ⟨i.val - 1, by omega⟩, ?_⟩
      convert hx using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs <;> simp_all <;> try omega
      · exfalso
        simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega
    · refine ⟨fun i => if h : i.val = 0 then true else x ⟨i.val - 1, by omega⟩, ?_⟩
      convert hx using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs <;> simp_all <;> try omega
      · exfalso
        simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega

end CircuitComplexity
