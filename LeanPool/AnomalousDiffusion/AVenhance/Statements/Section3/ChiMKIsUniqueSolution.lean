/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.IsCorrectorSol
public import LeanPool.AnomalousDiffusion.AVenhance.Proofs.Section3.ChiMKIsUniqueSolution

/-! Statement file: `chiMK_isUniqueSolution` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- Well-posedness / identification (flag F1): in the class of bounded `C²` functions, the
unique solution of `e.parabcorr.k` with `e = e_j` is the `j`-th component of `chiMK`
(with the sign of the correction). -/
theorem chiMK_isUniqueSolution (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (j : Fin 2) :
    let sol : ℝ → Vec 2 → ℝ := fun t x => I.chiMK κ m k t x j
    (ContDiff ℝ 2 (fun p : ℝ × Vec 2 => sol p.1 p.2) ∧ (∃ B : ℝ, ∀ t x, |sol t x| ≤ B) ∧
        I.IsCorrectorSol κ m k (basisVec j) sol) ∧
      ∀ χ : ℝ → Vec 2 → ℝ, ContDiff ℝ 2 (fun p : ℝ × Vec 2 => χ p.1 p.2) →
        (∃ B : ℝ, ∀ t x, |χ t x| ≤ B) → I.IsCorrectorSol κ m k (basisVec j) χ → χ = sol := by
  exact AVenhance.Proofs.Ingredients.chiMK_isUniqueSolution I κ hκ m hm k j

end Ingredients
end AVenhance
