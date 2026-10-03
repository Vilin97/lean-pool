/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KhomSymmetry
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KhomScalar

/-! Proof of the Section 3 statement `Ingredients.Khom_eq_scalar`. -/

@[expose] public section

noncomputable section

namespace AVenhance.Proofs.Ingredients

open AVenhance

theorem Khom_eq_scalar {β : ℝ} (I : AVenhance.Ingredients β)
    (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    I.Khom κ m = I.KhomScalar κ m • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      0 < I.KhomScalar κ m := by
  apply AVenhance.Infra.Section3.khom_eq_scalar_of_flux_continuous
    I hm κ hκ
  intro i j
  exact AVenhance.Infra.Section3.flux_entry_time_continuous I hm κ i j

end AVenhance.Proofs.Ingredients
