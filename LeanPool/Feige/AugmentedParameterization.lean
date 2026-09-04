/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ConditionalProductKernel
import LeanPool.Feige.TwoPoint

/-!
# Two-point parameters for augmented latent coordinates

The atom-at-one branch is represented by the harmless degenerate
parametrization `γ = 0`, `β = 1`.  A genuine support pair `(x,y)` is
represented by `γ = 1-x`, `β = y-1`.
-/

open MeasureTheory

namespace Feige

noncomputable section

/-- The lower displacement encoded by an augmented parameter. -/
def augmentedGamma (p : AugmentedTwoPointParams) : ℝ :=
  match p with
  | Sum.inl _ => 0
  | Sum.inr q => 1 - q.1.1

/-- The upper displacement encoded by an augmented parameter. -/
def augmentedBeta (p : AugmentedTwoPointParams) : ℝ :=
  match p with
  | Sum.inl _ => 1
  | Sum.inr q => q.1.2 - 1

/-- The condition enjoyed by latent parameters sampled from a
nonnegative mean-one law: genuine lower support points are nonnegative and
genuine upper support points are strictly above one. -/
def AugmentedParamsNonnegative {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) : Prop :=
  ∀ i,
    match p i with
    | Sum.inl _ => True
    | Sum.inr q => 0 ≤ q.1.1 ∧ 1 < q.1.2

theorem augmentedGamma_nonneg {n : ℕ}
    {p : Fin n → AugmentedTwoPointParams} :
    ∀ i, 0 ≤ augmentedGamma (p i) := by
  intro i
  cases hpi : p i with
  | inl u => simp [augmentedGamma]
  | inr q =>
      change 0 ≤ 1 - q.1.1
      exact sub_nonneg.mpr q.2.1

theorem augmentedGamma_le_one {n : ℕ}
    {p : Fin n → AugmentedTwoPointParams}
    (hp : AugmentedParamsNonnegative p) :
    ∀ i, augmentedGamma (p i) ≤ 1 := by
  intro i
  specialize hp i
  cases hpi : p i with
  | inl u => simp [augmentedGamma]
  | inr q =>
      simp only [hpi] at hp
      change 1 - q.1.1 ≤ 1
      linarith [hp.1]

theorem augmentedBeta_pos {n : ℕ}
    {p : Fin n → AugmentedTwoPointParams}
    (hp : AugmentedParamsNonnegative p) :
    ∀ i, 0 < augmentedBeta (p i) := by
  intro i
  specialize hp i
  cases hpi : p i with
  | inl u => simp [augmentedBeta]
  | inr q =>
      simp only [hpi] at hp
      change 0 < q.1.2 - 1
      linarith [hp.2]

/-- Both branches of the augmented kernel are exactly the canonical
mean-one two-point measure for their `γ,β` parameters. -/
theorem augmentedTwoPointKernel_eq_twoPointMeasure
    (p : AugmentedTwoPointParams) :
    augmentedTwoPointKernel p =
      twoPointMeasure (lowValue (augmentedGamma p))
        (highValue (augmentedBeta p)) := by
  cases p with
  | inl u =>
      cases u
      rw [augmentedTwoPointKernel_atom]
      simp [augmentedGamma, augmentedBeta, lowValue, highValue,
        twoPointMeasure, twoPointLowerWeight, twoPointUpperWeight]
  | inr q =>
      rw [augmentedTwoPointKernel_pair]
      congr 1
      · simp [augmentedGamma, lowValue]
      · simp [augmentedBeta, highValue]

theorem augmentedConditionalProduct_eq_twoPointProduct {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) :
    augmentedConditionalProduct p =
      Measure.pi (fun i ↦
        twoPointMeasure (lowValue (augmentedGamma (p i)))
          (highValue (augmentedBeta (p i)))) := by
  unfold augmentedConditionalProduct
  congr 1
  funext i
  exact augmentedTwoPointKernel_eq_twoPointMeasure (p i)

end

end Feige
