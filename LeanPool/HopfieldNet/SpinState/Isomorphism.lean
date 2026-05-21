/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SpinState.Basic
import LeanPool.HopfieldNet.HN.aux
import LeanPool.HopfieldNet.NN
import LeanPool.HopfieldNet.HN.Core
import LeanPool.HopfieldNet.HN.test

namespace HopfieldIsomorphism
set_option checkBinderAnnotations false
open SpinState HopfieldState NeuralNetwork State

variable {n : ℕ}
variable (i j : Fin n)
/-- Convert a SpinState to a real value (1 or -1) -/
def spinStateToReal (s : SpinState) : ℝ := s.toReal

/-- Convert a real value (1 or -1) to a SpinState -/
noncomputable
def realToSpinState (r : ℝ) : SpinState :=
  if r ≥ 0 then SpinState.up else SpinState.down
#exit
/-- Convert a HopfieldState to a Pattern -/
noncomputable
def stateToPattern {n : ℕ} [Nonempty (Fin n)] (x : HopfieldState n) : NeuralNetwork.State (HopfieldNetwork ℝ (Fin n)) :=
  { act := fun i => spinStateToReal (x i)
    hp := fun i => by
      cases h : x i
      · apply Or.inl  -- SpinState.up maps to 1
        calc spinStateToReal (x i) = spinStateToReal up := by rw [h]
                               _ = 1 := rfl
      · apply Or.inr  -- SpinState.down maps to -1
        calc spinStateToReal (x i) = spinStateToReal down := by rw [h]
                               _ = -1 := rfl
  }

/-- Convert a Pattern to a HopfieldState -/
noncomputable
def patternToState {n : ℕ} [Nonempty (Fin n)] (p : NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) : HopfieldState n :=
  fun i => realToSpinState (p.act i)

-- Proof that these conversions are inverses
lemma stateToPattern_patternToState {n : ℕ} [Nonempty (Fin n)] (x : HopfieldState n) :
  patternToState (stateToPattern x) = x := by
  ext i
  simp [patternToState, stateToPattern, spinStateToReal, realToSpinState]
  cases h : x i
  · -- Case: x i = up
    simp [patternToState, stateToPattern, spinStateToReal, realToSpinState]
    unfold SpinState.toReal
    have h1 : 1 ≥ 0 := by norm_num
    simp [h, h1]
  · -- Case: x i = down
    simp [patternToState, stateToPattern, spinStateToReal, realToSpinState]
    unfold SpinState.toReal
    have h1 : -1 < 0 := by norm_num
    have h2 : ¬(-1 ≥ 0) := not_le_of_lt h1
    simp [h, h2]


@[ext]
-- The Pattern extensionality
lemma Pattern.ext {R U : Type} [Zero R] {NN : NeuralNetwork R U}
    {p₁ p₂ : NN.State} (h : p₁.act = p₂.act) : p₁ = p₂ := by
  cases p₁ with | mk act₁ hp₁ =>
  cases p₂ with | mk act₂ hp₂ =>
  simp only at h
  congr  -- Use congruence closure


lemma patternToState_stateToPattern {n : ℕ} [Nonempty (Fin n)] (p : NeuralNetwork.State (HopfieldNetwork ℝ (Fin n))) :
  stateToPattern (patternToState p) = p := by
  -- Apply the Pattern.ext theorem
  apply Pattern.ext
  -- Prove that the activation functions are equal
  funext i
  simp only [patternToState, stateToPattern]

  -- Prove that spinStateToReal (realToSpinState (p.act i)) = p.act i
  cases p.hp i with
  | inl h => -- Case: p.act i = 1
    rw [h]
    have h1 : 1 ≥ 0 := by norm_num
    simp [realToSpinState, spinStateToReal, h1]
    rw [← h]
    exact id (Eq.symm h)
  | inr h => -- Case: p.act i = -1
    rw [h]
    have h1 : -1 < 0 := by norm_num
    have h2 : ¬(-1 ≥ 0) := by norm_num

    rw [<-h] -- Replace p.act i with -1
    have : spinStateToReal (realToSpinState (-1)) = -1 := by
      unfold realToSpinState
      simp [h2]
      unfold spinStateToReal SpinState.toReal
      simp_all only [Int.reduceNeg, Left.neg_neg_iff, zero_lt_one, ge_iff_le, Left.nonneg_neg_iff, Int.reduceLE,
        not_false_eq_true, ite_eq_left_iff, not_le, reduceCtorEq, imp_false, not_true_eq_false, ↓reduceIte]
    rw [h]
    rw [← h] -- Replace -1 with p.act i
    simp_all only [Int.reduceNeg, Left.neg_neg_iff, zero_lt_one, ge_iff_le, Left.nonneg_neg_iff, Int.reduceLE,
      not_false_eq_true]
