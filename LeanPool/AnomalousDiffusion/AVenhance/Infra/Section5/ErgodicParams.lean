/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Params
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.FlowAverages
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicFlow

/-! Corrected parameter bookkeeping for the four §5.2 nondivergence terms.
The physical unit-cell frequency is ε_m⁻¹, not ε_(m-1)/ε_m. Composed
analyticity, its order-zero estimate, and both means remain explicit inputs. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Ingredients AVenhance.Infra.Ergodic
namespace AVenhance.Infra.Section5

/-- The actual integer fast frequency on the unit cell. -/
def ergodicFrequency (β : ℝ) (Λ m : ℕ) : ℕ :=
  if m = 0 then 1 else ⌈(Λ : ℝ) ^ ((q β) ^ m / (q β - 1))⌉₊

theorem ergodicFrequency_cast (β : ℝ) (Λ m : ℕ) :
    (ergodicFrequency β Λ m : ℝ) = (epsilon β Λ m)⁻¹ := by
  unfold ergodicFrequency epsilon
  split_ifs <;> simp

theorem ergodicFrequency_pos {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    0 < ergodicFrequency β Λ m := by
  have h : 0 < (ergodicFrequency β Λ m : ℝ) := by
    rw [ergodicFrequency_cast]
    exact inv_pos.2 (Infra.Cutoff.epsilon_pos hβ hβ' hΛ)
  exact_mod_cast h

end AVenhance.Infra.Section5
