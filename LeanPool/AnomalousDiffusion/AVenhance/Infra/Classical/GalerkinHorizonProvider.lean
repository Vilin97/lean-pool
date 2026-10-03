/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonConsistency
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonGluing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Uniqueness

/-! Conditional assembly of the integer-horizon Galerkin limits into the classical solution
    operator. -/

@[expose] public section

noncomputable section

open Set Homogenization

namespace AVenhance.Infra.Classical

/-- Once each integer-horizon limit is jointly smooth on its closed slab, the compatible Galerkin
family gives the exact classical existence-and-uniqueness conclusion. The smoothness premise is a
separate regularity obligation discharged by the limit-regularity modules. -/
theorem classicalGalerkinIntegerHorizonFamily_classical_wellposed
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    (hsmooth : ∀ (N : ℕ), 0 < N → ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per N)) (Icc (0 : ℝ) (N : ℝ) ×ˢ univ)) :
    ∃ θ : ℝ → Vec 2 → ℝ,
      AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ ∧
        ∀ θ' : ℝ → Vec 2 → ℝ,
          AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ' →
            ∀ t : ℝ, 0 ≤ t → ∀ x, θ' t x = θ t x := by
  let family := classicalGalerkinIntegerHorizonFamily φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per
  have hperiodic : ∀ (N : ℕ), 0 < N → ∀ t, 0 ≤ t →
      AVenhance.IsZ2Periodic (family N t) := by
    intro N hN t ht
    exact classicalGalerkinIntegerHorizonFamily_periodic φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per N t ht
  have hinitial : ∀ (N : ℕ), 0 < N → ∀ x, family N 0 x = θ₀ x := by
    intro N hN x
    exact classicalGalerkinIntegerHorizonFamily_initial φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per N x
  have hpde : ∀ (N : ℕ), 0 < N → ∀ t, t ∈ Ioo (0 : ℝ) (N : ℝ) → ∀ x,
      AVenhance.advDiffOp (AVenhance.streamVel φ) κ (family N) t x = F t x := by
    intro N hN t ht x
    have hNsucc : (N : ℝ) ≤ (Nat.succ N : ℝ) := by
      exact_mod_cast Nat.le_succ N
    exact classicalGalerkinIntegerHorizonFamily_advDiffOp φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per N t ⟨ht.1, lt_of_lt_of_le ht.2 hNsucc⟩ x
  have hcompatible : ∀ (M N : ℕ), M ≤ N → ∀ t, t ∈ Icc (0 : ℝ) (M : ℝ) →
      family M t = family N t := by
    intro M N hMN t ht
    exact classicalGalerkinIntegerHorizonFamily_consistent φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per M N hMN t ht
  obtain ⟨θ, hθ⟩ := classicalClassicalSol_of_consistent_horizon_family
    (AVenhance.streamVel φ) κ F θ₀ family hsmooth hperiodic hinitial hpde hcompatible
  refine ⟨θ, hθ, ?_⟩
  intro θ' hθ' t ht x
  exact streamVel_classical_unique φ hφ κ hκ F θ₀ hθ hθ' t ht x

end AVenhance.Infra.Classical

end
