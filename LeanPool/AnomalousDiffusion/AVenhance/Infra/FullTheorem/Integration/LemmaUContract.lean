/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With

/-! # Lemma U (uniform time-Hölder bound in `L²`)

For a bounded,
measurable, periodic, divergence-free drift and `0 < κ ≤ 1`, every weak solution with `H¹` datum
satisfies `‖θ(t) − θ(s)‖_{L²} ≤ C_U (1 + B) κ^{-1/2} |t − s|^{1/4} ‖θ₀‖_{H¹}`.  The constant is
    absolute. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Lemma U, as consumed by Lemma r.LeBron and the combined main theorem. -/
def LemmaUContract : Prop :=
  ∃ CU : ℝ, 0 < CU ∧
    ∀ b : ℝ → Vec 2 → Vec 2,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
        (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t)) → IsDivFree b →
    ∀ B : ℝ, 0 ≤ B → (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B) →
    ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
    ∀ (θ₀ : Vec 2 → ℝ) (Dθ₀ : Vec 2 → Vec 2), IsPeriodicH1With θ₀ Dθ₀ →
    ∀ (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2), IsWeakSolutionGrad b κ θ₀ θ Dθ →
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤
        CU * (1 + B) / Real.sqrt κ * |t - s| ^ ((1 : ℝ) / 4) *
          Real.sqrt (l2NormSq θ₀ + gradNormSq Dθ₀)

end AVenhance.Infra.FullTheorem
