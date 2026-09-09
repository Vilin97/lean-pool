/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMap
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

/-! Fixed bounded maps preserve the same external-word radius for actual cylinder paths. -/

@[expose] public section


noncomputable section

namespace EulerCylinderConstantMap

open EulerLiftedGradientSpace EulerLpCylinderTranslation EulerParameterWordGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {ι : Type*} [Fintype ι]

theorem pathMap_block_bound (directions : ι → LiftTangent) (q : ℕ) (L : E →L[ℝ] F)
    (p : C(K, CylinderL2 P E))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => pathTranslate P b (pathMap P L p)) n a ≤
      ‖L‖ * block directions q (fun b : LiftTangent => pathTranslate P b p) n a := by
  have he : (fun b : LiftTangent => pathTranslate P b (pathMap P L p)) =
      pathMap P L ∘ (fun b : LiftTangent => pathTranslate P b p) :=
    funext (fun b => (pathMap_translation P L b p).symm)
  rw [he]
  have h := block_comp_clm_le (P := LiftTangent) (E := C(K,CylinderL2 P E))
    (F := C(K,CylinderL2 P F)) directions q (pathMap (K := K) P L)
    (fun b : LiftTangent => pathTranslate P b p) hp n a
  exact h.trans (mul_le_mul_of_nonneg_right (pathMap_norm (K := K) P L)
    (block_nonneg directions q (fun b : LiftTangent => pathTranslate P b p) n a))

end EulerCylinderConstantMap
