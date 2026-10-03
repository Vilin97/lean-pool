/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingEnergyReduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergyComplete

/-! The pointwise Section 3 flux-energy estimate in the finite-support form
used by the Section 5 consumers. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance
open Homogenization

/-- Uniform coefficient in the flux-energy estimate when the cutoff derivative
constants are bounded by `C₀`. -/
def lFluxToEnergyConstant (C₀ : ℝ) : ℝ :=
  ((C₀ + C₀) / (4 * Real.pi ^ 2)) * (1 / 2) +
    C₀ ^ 2 / (16 * Real.pi ^ 4)

/-- The source's full odd-mode energy double sum reduces to the finite cutoff
support, and the flux differs entrywise from that reduced energy by the
Section 3 scale error. The coefficient is independent of `I` among all
ingredients satisfying the displayed common cutoff bound `C₀`. -/
theorem l_flux_to_energy {β C₀ : ℝ} (I : Ingredients β)
    (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (t : ℝ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    (∀ x : Vec 2,
      let S := (xiMK_odd_support_finite I hm t).toFinset
      (∑ k ∈ S, ∑ l ∈ S,
        (I.xiMK m k.1 t * I.xiMK m l.1 t) •
          (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
              gradMatrix (I.chiMK κ m l.1 t) x)) =
        κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          ∑ k ∈ S, I.xiMK m k.1 t ^ 2 •
            (Matrix.transpose (gradMatrix (I.chiMK κ m k.1 t) x) *
              gradMatrix (I.chiMK κ m k.1 t) x)) ∧
    let S := (xiMK_odd_support_finite I hm t).toFinset
    ∀ i j,
      |(I.flux κ m t - movingEnergyReducedSourceMatrix I κ m t S) i j| ≤
        lFluxToEnergyConstant C₀ *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  constructor
  · intro x
    simpa using movingEnergy_odd_cutoff_double_sum_reduces I hm κ t x
  · dsimp only
    intro i j
    have hmatrix := movingFluxEnergy_matrix_error I hCz hCh hm κ hκ t hcondition
    have hreduce := movingCutoffEnergyMatrix_eq_source_reduced I hm κ t
    simpa [lFluxToEnergyConstant, hreduce] using hmatrix i j

end AVenhance.Infra.Section3

end
