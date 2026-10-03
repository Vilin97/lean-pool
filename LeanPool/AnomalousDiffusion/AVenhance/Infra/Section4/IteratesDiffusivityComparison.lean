/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq

/-! # Iterates Diffusivity Comparison

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4
open AVenhance

/-- The actual diffusivity chain supplies the new coefficient's
molecular scale bound; this is proved from its recursion, not an assumed input. -/
theorem iterate_kappaAt_abs_le_previous {β : ℝ} (I : Ingredients β) {κ : ℝ}
    (hκ : 0 < κ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    |I.kappaAt κ m (M - m)| ≤ I.kappaAt κ (m - 1) (M - (m - 1)) := by
  have hdepth : M - (m - 1) = (M - m) + 1 := by omega
  have hindex : m - 1 + 1 = m := by omega
  have hprev : I.kappaAt κ (m - 1) (M - (m - 1)) =
      I.KhomScalar (I.kappaAt κ m (M - m)) m := by
    rw [hdepth, Ingredients.kappaAt, hindex]
  rw [abs_of_pos (Infra.Section3.kappaAt_pos I hκ m (M - m)), hprev]
  exact Infra.Section3.khomScalar_ge_input I hm _ (Infra.Section3.kappaAt_pos I hκ m (M - m))

theorem iterate_kappaSeq_abs_le_previous {β : ℝ} (I : Ingredients β) {κ : ℝ}
    (hκ : 0 < κ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    |I.kappaSeq κ M m| ≤ I.kappaSeq κ M (m - 1) :=
  iterate_kappaAt_abs_le_previous I hκ hm hmM

end AVenhance.Infra.Section4
