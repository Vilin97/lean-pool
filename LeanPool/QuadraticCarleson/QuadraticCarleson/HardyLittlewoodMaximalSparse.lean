/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteLaminarMaximalSparse
import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodSparseReduction

/-!
# Sparse domination of the actual centered Hardy--Littlewood maximal operator

The finite principal-interval selection costs `10`; the three-grid reduction
and finite approximation cost `48`.  Thus the project-facing centered
boundary operator has a genuine sparse `(1,1)` bound with constant `480`
and exactly the approved `1/4` major-subset density.  All `p ≥ 1` follow by
monotonicity of normalized local averages.
-/

open MeasureTheory

namespace QuadraticCarleson.HardyLittlewoodMaximalSparse

open HardyLittlewoodBoundaryControl HardyLittlewoodSparseReduction
open FiniteLaminarMaximalSparse


theorem hasSparseOneOneBound_centeredHardyLittlewoodBoundaryOperator :
    HasSparseOnePBound 480 1 centeredHardyLittlewoodBoundaryOperator := by
  have h := hasSparseOneOneBound_centered_of_finite_laminar (K := 10) ?_
  · norm_num at h
    exact h
  intro S f g hlam
  obtain ⟨R, _, hR, hb⟩ := exists_sparse_domination_finiteLaminarMaximal S f g hlam
  refine ⟨↑R, hR, ?_⟩
  simpa only [finiteIntervalMaximal, ENNReal.ofReal_ofNat] using hb

theorem hasSparseOnePBound_centeredHardyLittlewoodBoundaryOperator
    {p : ℝ} (hp : 1 ≤ p) :
    HasSparseOnePBound 480 p centeredHardyLittlewoodBoundaryOperator :=
  hasSparseOnePBound_of_one hp hasSparseOneOneBound_centeredHardyLittlewoodBoundaryOperator


end QuadraticCarleson.HardyLittlewoodMaximalSparse
