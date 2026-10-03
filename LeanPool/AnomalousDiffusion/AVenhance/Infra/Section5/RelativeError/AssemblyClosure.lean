/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyDissipation

/-! # the main-theorem closure  Smooth analytic limit dissipation
(`smooth_analytic_limit_dissipation`), weak well-posedness (`weakWellposedInput_of_A1`) and the
same-drift difference energy identity feed `h1_reduction_conditional` with `p = p₊ < 2`, giving the
literal main theorem inequality for `H¹` data.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance Homogenization

/-- The main-theorem closure: H¹ data, via `h1_reduction_conditional` with `p = p₊ < 2`. -/
theorem anomalous_dissipation_of_relative (β C₀ : ℝ) (hβ : 6 / 5 ≤ β)
    (hA8 : Integration.IndyStepDownStatement β C₀) :
    ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      (∀ j : ℕ, ClassicalSolvable (streamVel (Φ j))) →
      ∀ Ctail : ℝ, 1 ≤ Ctail →
      ∀ φ : ℝ → Vec 2 → ℝ,
        AEStronglyMeasurable (fun p : ℝ × Vec 2 => φ p.1 p.2)
          (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (φ t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, Differentiable ℝ (φ t)) →
        (∀ M : ℕ, 1 ≤ M → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
          |φ t x - Φ M t x| ≤ Ctail * epsilon β I.Λ (M + 1) ^ β) →
        AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
          (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) →
        (∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ t x‖ ≤ B) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (streamVel φ t)) →
        IsDivFree (streamVel φ) →
      ∃ ϱ : ℝ → ℝ, (∀ L, 0 < ϱ L ∧ ϱ L ≤ 1) ∧
        ∀ (f : Vec 2 → ℝ) (Df : Vec 2 → Vec 2), IsPeriodicH1With f Df → MeanZeroOn unitCube f →
        ∀ (θ : ℝ → ℝ → Vec 2 → ℝ) (Dθ : ℝ → ℝ → Vec 2 → Vec 2),
          (∀ κ, 0 < κ → IsWeakSolutionGrad (streamVel φ) κ f (θ κ) (Dθ κ)) →
          ϱ (datumLength f Df) ^ 2 * l2NormSq f ≤
            limsup (fun κ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) := by
  obtain ⟨Λ₀, h13⟩ := smooth_analytic_limit_dissipation β C₀ hβ hA8
  refine ⟨Λ₀, ?_⟩
  intro I hz hx hh hΛ Φ hΦ hsolv Ctail hCt φ hφm hφp hφd htail hbm hbb hbp hdiv
  have hb : β < 4 / 3 := I.beta_lt
  obtain ⟨c, hc, hAn⟩ := h13 I hz hx hh hΛ Φ hΦ hsolv Ctail hCt φ hφm hφp hφd htail hbm hbb hbp
    hdiv
  exact h1_reduction_conditional hc (pPlus_pos_lt_two hβ hb)
    (weakWellposedInput_of_A1 _ hbm hbb hbp) hAn
    (differenceEnergyInput_of_divFree_and_l2Data _ hbm hbb hbp hdiv)

end AVenhance.Infra.Section5.RelativeError

end
