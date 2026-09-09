/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

@[expose] public section

/-! Uniform estimates for finite coefficient assembly, including zero and terminal grades. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerPacketProfileRecursion EulerFiniteGrades EulerPacketShiftArithmetic

variable {P T : ℝ} [Fact (0 < P)]

theorem wordBound_truncateFamily (M : ℕ) (f : ℕ → VectorField)
    (G : ∀ i, i ≤ M → Field P T (f i)) (q : ℕ) (R : ℝ) (A : ℕ → ℝ) (d : ℕ → ℕ)
    (hR : 0 ≤ R) (hA : ∀ i, 0 ≤ A i)
    (hG : ∀ i (hi : i ≤ M), (G i hi).WordBound q R (A i) (d i)) (n : ℕ) :
    (truncateFamily M f G n).WordBound q R (A n) (d n) := by
  by_cases hn : n ≤ M
  · simp only [truncateFamily,dite_eq_left hn]
    exact hG n hn
  · simp only [truncateFamily,dite_eq_right hn]
    exact (wordBound_zero P T q R (d n)).mono_amplitude hR (hA n)

theorem wordBound_assembleFamily (M : ℕ) (f c : ℕ → VectorField)
    (G : ∀ i, i ≤ M → Field P T (f i)) (H : ∀ i, i ≤ M → Field P T (c i))
    (R A : ℝ) (hR : 1 ≤ R) (hA : 1 ≤ A)
    (hG : ∀ i (hi : i ≤ M), (G i hi).WordBound 6 R (2*A^(2*i)) (highShift i))
    (hH : ∀ i (hi : i ≤ M), (H i hi).WordBound 6 R (A^(2*i)) (highShift i)) (n : ℕ) :
    (assembleFamily M f c G H n).WordBound 6 R (3*A^(2*n)) (highShift n) := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hg := wordBound_truncateFamily M f G 6 R (fun i => 2*A^(2*i)) highShift
    (zero_le_one.trans hR) (fun i => mul_nonneg (by norm_num) (pow_nonneg hA0 _)) hG
  have hh := wordBound_truncateFamily M c H 6 R (fun i => A^(2*i)) highShift
    (zero_le_one.trans hR) (fun i => pow_nonneg hA0 _) hH
  cases n with
  | zero =>
      exact (hg 0).mono_amplitude (zero_le_one.trans hR) (by norm_num)
  | succ n =>
      have hshift : highShift n ≤ highShift (n+1) := by unfold highShift; omega
      have hp : A^(2*n) ≤ A^(2*(n+1)) := pow_le_pow_right₀ hA (by omega)
      have hnext := (hh n).mono_shift hR (pow_nonneg hA0 _) hshift
      have hs := (hg (n+1)).add hnext
      exact hs.mono_amplitude (zero_le_one.trans hR) (by nlinarith)

end EulerPacketCylinderField.Field
