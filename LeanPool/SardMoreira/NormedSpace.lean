/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import Mathlib.Analysis.Normed.Module.Basic

/-!
# LeanPool.SardMoreira.NormedSpace
-/

namespace NNReal

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

protected theorem norm_smul (a : ℝ≥0) (x : E) : ‖a • x‖ = a * ‖x‖ := by
  simp [NNReal.smul_def, norm_smul]

protected theorem nnnorm_smul (a : ℝ≥0) (x : E) : ‖a • x‖₊ = a * ‖x‖₊ := by
  simp [NNReal.smul_def, nnnorm_smul]

protected theorem enorm_smul (a : ℝ≥0) (x : E) : ‖a • x‖ₑ = a * ‖x‖ₑ := by
  simp [enorm_eq_nnnorm, NNReal.nnnorm_smul]

protected theorem dist_smul (a : ℝ≥0) (x y : E) : dist (a • x) (a • y) = a * dist x y := by
  simp [NNReal.smul_def, dist_smul₀]

protected theorem nndist_smul (a : ℝ≥0) (x y : E) : nndist (a • x) (a • y) = a * nndist x y := by
  simp [NNReal.smul_def, nndist_smul₀]

protected theorem edist_smul (a : ℝ≥0) (x y : E) : edist (a • x) (a • y) = a * edist x y := by
  simp only [edist_nndist, NNReal.nndist_smul, ENNReal.coe_mul]

end NNReal
