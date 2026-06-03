/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# LeanPool.Monlib4.Preq.Equiv

Imported Lean Pool material for `LeanPool.Monlib4.Preq.Equiv`.
-/

theorem Equiv.Perm.ToPequiv.toMatrix_mem_unitaryGroup {n : Type _} [DecidableEq n]
    [Fintype n] {𝕜 : Type _} [CommRing 𝕜] [StarRing 𝕜] (σ : Equiv.Perm n) :
    (Equiv.toPEquiv σ).toMatrix ∈ Matrix.unitaryGroup n 𝕜 :=
  by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.one_apply,
      Function.Injective.eq_iff (Equiv.injective σ), eq_comm, h]
