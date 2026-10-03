/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPrimitive
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.CutoffAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.CutoffMemory
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KhomSymmetry

/-! The mean forcing coefficient in the actual diffusivity chain. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The physical preceding diffusivity is exactly the scalar homogenized
coefficient, by the recursion rather than a comparison hypothesis. -/
theorem iterate_previous_diffusivity_eq {β : ℝ} (I : Ingredients β)
    (κ : ℝ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    I.kappaAt κ (m - 1) (M - (m - 1)) =
      I.KhomScalar (I.kappaAt κ m (M - m)) m := by
  have hd : M - (m - 1) = (M - m) + 1 := by omega
  have hidx : m - 1 + 1 = m := by omega
  rw [hd, Ingredients.kappaAt, hidx]

/-- The mean forcing error retains both finite-averaging errors from E21c. -/
theorem iterate_mean_coefficient_bound {β : ℝ} (I : Ingredients β)
    (κ : ℝ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M)
    (hκ : 0 < I.kappaAt κ m (M - m))
    (hcondition : epsilon β I.Λ m ^ 2 ≤ I.kappaAt κ m (M - m) * tau β I.Λ m / 2) :
    ‖timeAvgMat (I.Kmat (I.kappaAt κ m (M - m)) m) -
      I.kappaAt κ (m - 1) (M - (m - 1)) • (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / I.kappaAt κ m (M - m)) *
      ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
          (epsilon β I.Λ m ^ 2 / (I.kappaAt κ m (M - m) * tau β I.Λ m)) ^ Nstar β +
        (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
          2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
          (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β) := by
  rw [iterate_previous_diffusivity_eq I κ hm hmM]
  have hs := (Infra.Section3.khom_eq_scalar_of_flux_continuous I hm _ hκ
    (Infra.Section3.flux_entry_time_continuous I hm _)).1
  rw [← hs]
  exact Infra.Section3.Kmat_average_sub_Khom_norm_le_finite I hm hκ hcondition

/-- The explicit two-error coefficient from the finite average comparison. -/
def iterateMeanErrorBound {β : ℝ} (I : Ingredients β) (κm : ℝ) (m : ℕ) : ℝ :=
  (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
    ((4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
        (epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m)) ^ Nstar β +
      (2 * Nstar β * I.Czeta * ((Nstar β).factorial : ℝ) *
        2 ^ Nstar β * 2 ^ Nstar β * I.Chat ^ 2 * 8 ^ Nstar β) *
        (tau β I.Λ m / tauP β I.Λ m) ^ Nstar β)

end AVenhance.Infra.Section4
