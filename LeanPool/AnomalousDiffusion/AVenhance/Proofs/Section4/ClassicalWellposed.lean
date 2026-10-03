/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonProvider
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonSmoothnessAssembly

/-! Proof bridge for classical well-posedness. The Galerkin limit and nested-horizon
compatibility are already constructed in `Infra.Classical`; only joint
smoothness of each closed integer-horizon limit remains an explicit input. -/

@[expose] public section

noncomputable section

open Set Homogenization

namespace AVenhance.Proofs

/-- Classical well-posedness from the committed integer-horizon Galerkin limits, conditional only
on the outstanding joint smoothness of those limits on their closed slabs.

The regularity hypothesis is stated on the actual family used by the existing
limit construction. The horizon agreement needed to glue the family is proved
by `classicalGalerkinIntegerHorizonFamily_consistent`, using the limit
regularity bridge. -/
theorem classical_wellposed_of_horizon_limit_regularity
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t : ℝ, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    (hLimitSmooth : ∀ (N : ℕ), 0 < N → ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (AVenhance.Infra.Classical.classicalGalerkinIntegerHorizonFamily
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per N))
      (Set.Icc (0 : ℝ) (N : ℝ) ×ˢ Set.univ)) :
    ∃ θ : ℝ → Vec 2 → ℝ,
      AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ ∧
        ∀ θ' : ℝ → Vec 2 → ℝ,
          AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ' →
            ∀ t : ℝ, 0 ≤ t → ∀ x, θ' t x = θ t x := by
  exact AVenhance.Infra.Classical.classicalGalerkinIntegerHorizonFamily_classical_wellposed
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per hLimitSmooth

/-- Exact proof for classical well-posedness. The integer-horizon limits are jointly smooth
by the all-order Galerkin word induction, including both time endpoints. -/
theorem classical_wellposed (φ : ℝ → Vec 2 → ℝ)
    (hφ : AVenhance.IsAdmissibleStream φ) (κ : ℝ) (hκ : 0 < κ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t : ℝ, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hper : AVenhance.IsZ2Periodic θ₀) :
    ∃ θ : ℝ → Vec 2 → ℝ,
      AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ ∧
        ∀ θ' : ℝ → Vec 2 → ℝ,
          AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ' →
            ∀ t : ℝ, 0 ≤ t → ∀ x, θ' t x = θ t x := by
  exact classical_wellposed_of_horizon_limit_regularity
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hper (by
      intro N hN
      exact AVenhance.Infra.Classical.classicalGalerkinIntegerHorizonFamily_contDiffOn
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hper N)

end AVenhance.Proofs

end
