/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! test duality for the additional divergence-form residual.

This module proves the HDot⁻¹ step needed for `R46`. The source does not provide
the L² estimate on its flux; that independent coefficient estimate remains an
input to the big-bound estimate argument.
-/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The vector field whose divergence is the transition-window residual. -/
def r46Flux (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  (I.flux κm m t).mulVec
    (∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k) t x))

/-- Pointwise, `R46` is exactly the divergence of its transition-window flux. -/
theorem R46_eq_cellDivergence (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) :
    R46 I hΦ m κm T t = cellDivergence (r46Flux I hΦ m κm T t) := by
  funext x
  simp [R46, r46Flux, cellDivergence, vecDiv, spaceGrad]

/-- The HDot⁻¹ norm of `R46` is controlled by the spatial L² norm of its
flux. This is the exact divergence-duality step; it does not assert the
source-missing estimate of that flux in terms of κ, ε, and θ₀. -/
theorem hMinusOneNorm_R46_le (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm T t))
    (hper : IsZ2Periodic (r46Flux I hΦ m κm T t)) :
    hMinusOneNorm (R46 I hΦ m κm T t) ≤
      ENNReal.ofReal (Real.sqrt (gradNormSq (r46Flux I hΦ m κm T t))) := by
  rw [R46_eq_cellDivergence I hΦ m κm T t]
  exact hMinusOneNorm_divergence_le _ hF hper

/-- Time-integrated divergence duality for `R46` in the exact BigBound carrier.
The right side is the space-time L² flux norm, expressed as a lower integral. -/
theorem timeHMinusOneNorm_R46_le (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ)
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm T t))
    (hper : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      IsZ2Periodic (r46Flux I hΦ m κm T t)) :
    timeHMinusOneNorm (fun t => R46 I hΦ m κm T t) ≤
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (r46Flux I hΦ m κm T t))) ^ 2) ^
          (1 / 2 : ℝ) := by
  apply timeHMinusOneNorm_le_of_bound
  intro t ht
  exact hMinusOneNorm_R46_le I hΦ m κm T t (hF t ht) (hper t ht)

end AVenhance.Infra.Section5
end
