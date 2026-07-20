/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.HessianPL
import LeanPool.PLAcceleratedNesterovLean.MorseBott.Submanifold

/-!
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Corollary 2.17: μ-PŁ ⟹ μ-MB (Main Theorem)

## Statement

If f : E → ℝ is C² and satisfies μ-PŁ around a local minimizer x₀ ∈ S,
then f satisfies μ-MB at x₀. The constant μ is preserved.

## Proof outline (algebraic shortcut, bypassing QG)

The proof combines two ingredients:

1. **C² + PŁ ⟹ Hessian coercive on ker(Hess)⊥** (via Rayleigh quotient):
   Direct proof using 1D Taylor + PŁ + eigenvector analysis, without
   going through quadratic growth (QG) or gradient flow.

2. **C² + PŁ ⟹ S is submanifold** (Theorem 2.16): Using constant rank of
   Hessian on S (Cor 2.13), gradient alignment (Lemma 2.14), and the implicit
   function theorem (Lemma 2.15).

Combining these two gives μ-MB.

## References

- Rebjock & Boumal, "Fast convergence to non-isolated minima: four equivalent
  conditions for C² functions", Corollary 2.17.
-/

open Filter Topology Metric

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § Main theorem: Corollary 2.17
-- ════════════════════════════════════════════════════════════════════════════

/-- **Corollary 2.17** (μ-PŁ ⟹ μ-MB).
    If f : E → ℝ is C² and satisfies μ-PŁ around a local minimizer x₀,
    then f satisfies μ-MB at x₀. The constant μ is preserved.

    Proof: Combine two facts:
    1. C² + PŁ ⟹ Hessian coercive on ker(Hess)⊥ (via Rayleigh quotient)
    2. C² + PŁ ⟹ S is C¹ submanifold with T = ker(Hess) (Thm 2.16)

    Note: This uses the algebraic shortcut (Rayleigh quotient + eigenvector
    analysis) to prove Hessian coercivity directly from PŁ, bypassing the
    gradient flow argument (PŁ ⟹ QG) and the distance lemma entirely. -/
theorem muPL_implies_muMB (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    IsMuMB f μ x₀ := by
  -- Step 1: PŁ ⟹ S is a C¹ submanifold with T = ker(Hess f(x₀))
  have hSub : IsLocalSubmanifoldAt (localMinSet f x₀) x₀ (hessianKer f x₀) :=
    MuPL.implies_submanifold f μ x₀ hμ hf hmin hPL
  -- Step 2: PŁ ⟹ Hessian coercive on normal space (directly, no QG needed)
  have hCoer : ∀ v ∈ (hessianKer f x₀).orthogonal,
      hessian f x₀ v v ≥ μ * ‖v‖ ^ 2 :=
    hessian_coercive_on_orthogonal_of_MuPL_impl f μ x₀ hμ hf hmin hPL
  -- Assemble
  exact ⟨hμ, hmin, hSub, hCoer⟩

end PLAcceleratedNesterovLean
