/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds

@[expose] public section

/-! Explicit finite-dimensional norm comparisons for the actual H³ energy. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerSmoothSobolev Finset

def tensorNorm (s : ℕ) (A : SmoothL2Field Space) : ℝ := ∑ n ∈ range (s+1), ‖A.jetLp n‖

theorem tensorNorm_eq (s : ℕ) (A : SmoothL2Field Space) :
    tensorNorm s A=realTensorSobolevNorm 3 s A.field := by
  simp only [tensorNorm,realTensorSobolevNorm,norm_jetLp]

theorem tensorNorm_nonneg (s : ℕ) (A : SmoothL2Field Space) : 0 ≤ tensorNorm s A :=
  sum_nonneg (fun _ _ => norm_nonneg _)

theorem wordBound_tensorNorm (s : ℕ) (A : SmoothL2Field Space) : WordBound s (tensorNorm s A) A :=
  by
  intro n hn w
  exact (wordField_toLp_norm_le A w).trans
    (single_le_sum (fun _ _ => norm_nonneg _) (mem_range.mpr (by omega)))

theorem tensorNorm_three_le (A : SmoothL2Field Space) (M : ℝ) (hA : WordBound 3 M A) :
    tensorNorm 3 A ≤ 40*M := by
  calc
    _ ≤ ∑ n ∈ range 4, (3 : ℝ)^n*M := sum_le_sum
      (fun n hn => wordBound_jet_norm hA (by have := mem_range.mp hn; omega))
    _ = _ := by norm_num [sum_range_succ]; ring

theorem tensorNorm_le_sqrt_energy (A : SmoothL2Field Space) :
    tensorNorm 3 A ≤ 40*Real.sqrt (wordEnergy 3 A) :=
  tensorNorm_three_le A _ (wordBound_sqrt_energy 3 A)

theorem energy_le_tensorNorm_sq (A : SmoothL2Field Space) :
    wordEnergy 3 A ≤ 40*(tensorNorm 3 A)^2 := by
  have hA := wordBound_tensorNorm 3 A
  calc
    _ ≤ ∑ n ∈ range 4, ∑ _w : Fin n → Fin 3, (tensorNorm 3 A)^2 := by
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro w _
      exact pow_le_pow_left₀ (norm_nonneg _) (hA n (by have := mem_range.mp hn; omega) w) 2
    _ = _ := by norm_num [sum_range_succ]; ring

theorem sqrt_energy_le_tensorNorm (A : SmoothL2Field Space) :
    Real.sqrt (wordEnergy 3 A) ≤ 7*tensorNorm 3 A := by
  have he := energy_le_tensorNorm_sq A
  have hs := Real.sq_sqrt (wordEnergy_nonneg 3 A)
  have ht := tensorNorm_nonneg 3 A
  have hr := Real.sqrt_nonneg (wordEnergy 3 A)
  nlinarith [sq_nonneg (tensorNorm 3 A)]

end EulerOrdinarySobolev
