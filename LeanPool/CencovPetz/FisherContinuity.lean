/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.SimplexTopology


/-!
# `CencovPetz.FisherContinuity`

Continuity of the finite Fisher bilinear form as a function of the simplex point.

This is a small topological lemma used to extend the finite Čencov/Chentsov identity from a dense
family of rational points to all simplex points under continuity hypotheses on a monotone metric
family.

## Main result

- `CencovPetz.Simplex.continuous_fisherBilin_apply`
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

namespace Simplex

variable {α : Type*} [Fintype α]

lemma continuous_fisherBilin_apply (u v : tangentSpace (α := α)) :
    Continuous fun p : Simplex α => fisherBilin p u v := by
  classical
  have hterm :
      ∀ a : α,
        Continuous fun p : Simplex α => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a := by
    intro a
    have hEval : Continuous fun p : Simplex α => p.p a :=
      Simplex.continuous_eval (α := α) a
    have hInv : Continuous fun p : Simplex α => (p.p a)⁻¹ :=
      hEval.inv₀ (fun p => p.p_ne_zero a)
    have hMul :
        Continuous fun p : Simplex α => (((u : α → ℝ) a) * ((v : α → ℝ) a)) * (p.p a)⁻¹ :=
      continuous_const.mul hInv
    simpa [div_eq_mul_inv, mul_assoc] using hMul
  have hsum :
      Continuous fun p : Simplex α =>
        ∑ a : α, ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a := by
    simpa using
      (continuous_finsetSum (s := (Finset.univ : Finset α))
        (f := fun a (p : Simplex α) => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a)
        (by
          simp_all))
  simpa [fisherBilin] using hsum

end Simplex
end LeanPool.CencovPetz
