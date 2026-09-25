/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.StrictlySingular
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Strict singularity and Hilbert-space adjoints

This file proves that strict singularity of bounded operators between real Hilbert spaces is
preserved by, and hence invariant under, the Hilbert-space adjoint.
-/

@[expose] public section


namespace KaltonPeck.Support.StrictlySingular

noncomputable
section

open scoped InnerProduct NNReal

universe uE uF uV

/-- Strict singularity of a bounded operator between real Hilbert spaces passes to its
Hilbert-space adjoint. -/
theorem IsStrictlySingular.hilbert_adjoint
    {E : Type uE} {F : Type uF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {T : E →L[ℝ] F}
    (hT : IsStrictlySingular.{0, uE, uF, uV} T) :
    IsStrictlySingular.{0, uF, uE, uV} (T†) := by
  intro Z _ _ _ hZ S _ hAdjS
  apply hT Z hZ ((T†).comp S) hAdjS
  rcases hAdjS with ⟨K, hK⟩
  refine ⟨K * K * ‖S‖₊, AntilipschitzWith.of_le_mul_dist ?_⟩
  intro x y
  let d : Z := x - y
  let r : E := (T†) (S d)
  have hKnorm : ‖d‖ ≤ (K : ℝ) * ‖r‖ := by
    have h := hK.le_mul_dist x y
    simpa only [dist_eq_norm, map_sub, ContinuousLinearMap.comp_apply, d, r] using h
  have hGramEq : ‖r‖ ^ 2 = inner ℝ (S d) (T r) := by
    rw [← real_inner_self_eq_norm_sq]
    exact T.adjoint_inner_left r (S d)
  have hGram : ‖r‖ ^ 2 ≤ ‖S‖ * ‖d‖ * ‖T r‖ := by
    calc
      ‖r‖ ^ 2 = inner ℝ (S d) (T r) := hGramEq
      _ ≤ ‖S d‖ * ‖T r‖ := real_inner_le_norm _ _
      _ ≤ (‖S‖ * ‖d‖) * ‖T r‖ :=
        mul_le_mul_of_nonneg_right (S.le_opNorm d) (norm_nonneg _)
      _ = ‖S‖ * ‖d‖ * ‖T r‖ := rfl
  have hSquare :
      ‖d‖ ^ 2 ≤ ((K : ℝ) * ‖r‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg d)
      (mul_nonneg (NNReal.coe_nonneg K) (norm_nonneg r))).2 hKnorm
  have hCancel :
      ‖d‖ * ‖d‖ ≤
        ‖d‖ * ((K : ℝ) ^ 2 * ‖S‖ * ‖T r‖) := by
    calc
      ‖d‖ * ‖d‖ = ‖d‖ ^ 2 := by ring
      _ ≤ ((K : ℝ) * ‖r‖) ^ 2 := hSquare
      _ = (K : ℝ) ^ 2 * ‖r‖ ^ 2 := by ring
      _ ≤ (K : ℝ) ^ 2 * (‖S‖ * ‖d‖ * ‖T r‖) :=
        mul_le_mul_of_nonneg_left hGram (sq_nonneg (K : ℝ))
      _ = ‖d‖ * ((K : ℝ) ^ 2 * ‖S‖ * ‖T r‖) := by ring
  have hFinal :
      ‖d‖ ≤ (K : ℝ) ^ 2 * ‖S‖ * ‖T r‖ := by
    by_cases hd : d = 0
    · rw [hd, norm_zero]
      exact mul_nonneg
        (mul_nonneg (sq_nonneg (K : ℝ)) (norm_nonneg S))
        (norm_nonneg (T r))
    · exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr hd)).mp hCancel
  simpa only [dist_eq_norm, map_sub, ContinuousLinearMap.comp_apply,
    NNReal.coe_mul, coe_nnnorm, pow_two, d, r] using hFinal

/-- Strict singularity is invariant under Hilbert-space adjoint. -/
theorem isStrictlySingular_hilbert_adjoint_iff
    {E : Type uE} {F : Type uF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) :
    IsStrictlySingular.{0, uF, uE, uV} (T†) ↔
      IsStrictlySingular.{0, uE, uF, uV} T := by
  constructor
  · intro h
    simpa only [ContinuousLinearMap.adjoint_adjoint] using h.hilbert_adjoint
  · exact fun h => h.hilbert_adjoint

end

end KaltonPeck.Support.StrictlySingular

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
