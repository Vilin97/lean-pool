/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
Scalar amplitudes for actual terminal L² data. A unit-input estimate for a
genuine linear endpoint map gives the identical coefficient/radius guard
for every nonnegative amplitude, including zero.
-/

@[expose] public section


noncomputable section

namespace EulerLpCylinderTranslation

open ContinuousLinearMap EulerLiftedGradientSpace EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K U V ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Embedding terminal data as a constant time path has block norm at most one. -/
theorem constantPath_block_le (directions : ι → LiftTangent) (q : ℕ)
    (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => pathTranslate P b (ContinuousMap.const K Y)) n a ≤
      block directions q (fun b : LiftTangent => translate P b Y) n a := by
  have hb := block_comp_clm_le directions q
    (ContinuousLinearMap.const ℝ K : CylinderL2 P U →L[ℝ] C(K,CylinderL2 P U))
    (fun b : LiftTangent => translate P b Y) hY n a
  have hn : ‖(ContinuousLinearMap.const ℝ K : CylinderL2 P U →L[ℝ] C(K,CylinderL2 P U))‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro u
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg u)).2 (fun _ => le_rfl)
  exact hb.trans ((mul_le_mul_of_nonneg_right hn (block_nonneg directions q _ n a)).trans_eq
    (one_mul _))

theorem terminal_amplitude_bound (directions : ι → LiftTangent) (q : ℕ)
    (S : CylinderL2 P U →L[ℝ] C(K, CylinderL2 P V))
    (hs : ∀ Y : CylinderL2 P U, ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y) →
      ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (S Y)))
    (R C : ℝ) (d e : ℕ)
    (hunit : ∀ Y : CylinderL2 P U, ∀ _hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y),
      (∀ n, block directions q (fun a : LiftTangent => translate P a Y) n 0 ≤ majorant R d n) →
      ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a (S Y)) n 0 ≤ C*majorant R e
          n)
    (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))
    (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n, block directions q (fun a : LiftTangent => translate P a Y) n 0 ≤ A*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (S Y)) n 0 ≤ (C*A)*majorant R e n
        := by
  by_cases hAz : A = 0
  · have hy : Y = 0 := by
      have hh := value_zero_of_block_zero_bound directions q
        (fun a : LiftTangent => translate P a Y) 0 (by simpa only [hAz,zero_mul] using hb 0)
      simpa only [translate_zero] using hh
    simp only [hy,map_zero,block_zero_function,hAz,mul_zero,zero_mul,le_refl]
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    let Z : CylinderL2 P U := A⁻¹ • Y
    have hZ : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Z) := by
      simpa only [Z,map_smul] using hY.const_smul A⁻¹
    have hbZ (k : ℕ) : block directions q (fun a : LiftTangent => translate P a Z) k 0 ≤
        majorant R d k := by
      have hz := block_normalize_bound directions q (fun a : LiftTangent => translate P a Y)
        hY A hAp R 1 d k 0 (by simpa only [one_mul] using hb k)
      simpa only [Z,map_smul,one_mul] using hz
    have hr := block_restore_bound directions q
      (fun a : LiftTangent => pathTranslate P a (S Z))
      (fun a : LiftTangent => pathTranslate P a (S Y)) (hs Z hZ) A hA (by
        intro a
        simp only [Z,map_smul,smul_smul,mul_inv_cancel₀ hAz,one_smul]) R C e n 0
      (hunit Z hZ hbZ n)
    exact hr.trans_eq (by ring)

end EulerLpCylinderTranslation
