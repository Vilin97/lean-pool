/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevOperations

@[expose] public section

/-! Scalar normalization preserves the external word radius and fixed Sobolev order. -/

noncomputable section

namespace EulerParameterWordGevrey

open EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

@[simp] theorem block_zero_function (directions : ι → P) (q n : ℕ) (x : P) :
    block directions q (fun _ : P => (0 : E)) n x = 0 := by
  have h := block_smul_le directions q (0 : ℝ) (fun _ : P => (0 : E)) contDiff_const n x
  have hl : block directions q (fun _ : P => (0 : E)) n x ≤ 0 := by
    simpa only [zero_smul, abs_zero, zero_mul] using h
  exact le_antisymm hl (block_nonneg directions q _ n x)

/-- Normalize a positive scalar envelope without changing R, d, or q. -/
theorem block_normalize_bound (directions : ι → P) (q : ℕ)
    (f : P → E) (hf : ContDiff ℝ ∞ f) (A : ℝ) (hA : 0 < A)
    (R C : ℝ) (d n : ℕ) (x : P)
    (hb : block directions q f n x ≤ A*(C*majorant R d n)) :
    block directions q (fun y => A⁻¹ • f y) n x ≤ C*majorant R d n := by
  have hs := block_smul_le directions q A⁻¹ f hf n x
  rw [abs_of_pos (inv_pos.mpr hA)] at hs
  calc
    _ ≤ A⁻¹*(A*(C*majorant R d n)) :=
      hs.trans (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hA.le))
    _ = C*majorant R d n := by rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]

/-- Restore the same scalar envelope after estimating a normalized actual solution. -/
theorem block_restore_bound (directions : ι → P) (q : ℕ)
    (f g : P → E) (hf : ContDiff ℝ ∞ f) (A : ℝ) (hA : 0 ≤ A)
    (he : ∀ y, g y = A • f y) (R C : ℝ) (d n : ℕ) (x : P)
    (hb : block directions q f n x ≤ C*majorant R d n) :
    block directions q g n x ≤ A*(C*majorant R d n) := by
  have heq : g = fun y => A • f y := funext he
  rw [heq]
  have hs := block_smul_le directions q A f hf n x
  rw [abs_of_nonneg hA] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hb hA)

/-- A vanishing zeroth external block forces the actual value to vanish. -/
theorem value_zero_of_block_zero_bound (directions : ι → P) (q : ℕ)
    (f : P → E) (x : P) (h : block directions q f 0 x ≤ 0) : f x = 0 := by
  rw [block_zero] at h
  exact norm_eq_zero.mp (le_antisymm ((norm_le_baseSize directions q f x).trans h) (norm_nonneg _))

end EulerParameterWordGevrey
