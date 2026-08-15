/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.StateContraction.AuxVarRecursion

/-!
# Auxiliary Variable Recursion for Lyapunov Contraction

The sequence-indexed recursion is the zero-velocity sequence specialization of
the state-based one-step identity `auxVarOfState_step`.
-/

noncomputable section

namespace PLAcceleratedNesterovLean
open scoped Topology NNReal
open Manifold

variable {d : ℕ}

theorem auxVar_recursion (P : E d →L[ℝ] E d) (μ' η ρ : ℝ) (π : E d → E d)
    (f : E d → ℝ) (x₁ : E d) (n : ℕ)
    (hρ : ρ = (1 - Real.sqrt (μ' * η)) / (1 + Real.sqrt (μ' * η)))
    (ha_pos : 0 < Real.sqrt (μ' * η))
    (hη_pos : 0 < η)
    (hμ_pos : 0 < μ') :
    let sn := nesterovSeq f η ρ x₁ n
    let gn := gradient f (sn.lookahead η)
    let en := normalDisp π f η ρ x₁ n
    let ξn := curvatureError (↑P) π f η ρ x₁ n
    let a := Real.sqrt (μ' * η)
    auxVar P μ' π f η ρ x₁ (n + 1) =
    ((1 - a) • (sn.v - P sn.v) + Real.sqrt μ' • en -
     Real.sqrt η • (gn - P gn)) + Real.sqrt μ' • ξn := by
  rw [← auxVarOfState_eq_auxVar P μ' π f η ρ x₁ (n + 1)]
  change auxVarOfState P μ' π η
    (nesterovStep f η ρ (nesterovSeq f η ρ x₁ n)) = _
  simpa only [normalDispOfState_eq_normalDisp,
    curvatureErrorOfState_eq_curvatureError, auxVarOfState_eq_auxVar] using
    auxVarOfState_step P μ' η ρ π f (nesterovSeq f η ρ x₁ n)
      hρ ha_pos hη_pos hμ_pos

end PLAcceleratedNesterovLean
