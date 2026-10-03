/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AssemblyTelescope
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.H1Reduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.WeakEnergyIdentity

/-! # Smooth analytic limit dissipation
Combines the base energy at the later start (`later_base_energy`), the telescoping chain
(`chain_lower_bound`, from conjunct (ii) of the step-down body), and the stream-difference
estimate (`weak_dissipation_ge_classical`) along `κ^{(M)} = ε_M^{2β/(q+1)} → 0⁺` to bound the
`limsup` of the dissipation of an arbitrary weak family for the limit drift `streamVel φ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance Homogenization

/-- . -/
theorem smooth_analytic_limit_dissipation (β C₀ : ℝ) (hβ : 6 / 5 ≤ β)
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
      ∃ c : ℝ, 0 < c ∧ AnalyticDissipationInput (streamVel φ) c (pPlus β) := by
  by_cases hb : β < 4 / 3
  swap
  · exact ⟨0, fun I => absurd I.beta_lt hb⟩
  have hβ1 : 1 < β := by linarith
  obtain ⟨Λ₁, hchain⟩ := chain_lower_bound β C₀ hβ hA8
  refine ⟨max Λ₁ 128, ?_⟩
  intro I hz hx hh hΛ Φ hΦ hsolv Ctail hCt φ hφm hφp hφd htail hbm hbb hbp hdiv
  have hΛ1 : Λ₁ ≤ (I.Λ : ℝ) := (le_max_left _ _).trans hΛ
  have h7 : 2 ^ 7 ≤ I.Λ := by
    have : (128 : ℝ) ≤ I.Λ := (le_max_right _ _).trans hΛ
    exact_mod_cast this
  obtain ⟨c₁, hc₁, hbase⟩ := later_base_energy β C₀ hβ I.Λ h7
  refine ⟨c₁ / 8, by positivity, ?_⟩
  intro g R hR hgL2 hgp hgm hgs hga θ Dθ hθ
  have hk : ∀ᶠ κ : ℝ in 𝓝[>] 0, 0 < κ := self_mem_nhdsWithin
  have hU : ∀ᶠ κ : ℝ in 𝓝[>] 0, κ * spaceTimeGradNormSq (Dθ κ) ≤ l2NormSq g / 2 :=
    hk.mono fun κ hκ =>
      divFree_energy_dissipation_bound (hθ κ hκ) hgL2 hbm hbb hbp hdiv
  have hbdd : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) (fun κ => κ * spaceTimeGradNormSq (Dθ κ)) :=
    ⟨_, hU⟩
  have hN : 0 ≤ l2NormSq g := integral_nonneg fun x => sq_nonneg _
  rcases hN.eq_or_lt with h0 | hg0
  · rw [← h0, mul_zero]
    apply le_limsup_of_le hbdd
    intro z hz'
    obtain ⟨κ, hκ0, hκz⟩ := ((hk.mono fun κ hκ =>
      mul_nonneg hκ.le (spaceTimeGradNormSq_nonneg' (Dθ κ))).and hz').exists
    exact hκ0.trans hκz
  · have hdisp : ∀ᶠ M : ℕ in atTop, c₁ / 8 * R ^ pPlus β * l2NormSq g ≤
        kappaCentre β I.Λ M * spaceTimeGradNormSq (Dθ (kappaCentre β I.Λ M)) := by
      filter_upwards [eventually_ge_atTop (laterStart β I.Λ R + 1),
        eta_div_kappaCentre_eventually hβ1 hb h7 (by linarith : 0 ≤ Ctail)] with M hM hη
      have hM1 : 1 ≤ M := by omega
      have hκpos := kappaCentre_pos hβ1 hb h7 M
      have hperm := kappaCentre_mem_permittedInterval hβ1 hb h7 M
      have hκp := kappaCentre_mem_permissibleSet hβ1 hb h7 hM1
      obtain ⟨θj, θM, hθj, hθM, hch⟩ := hchain I hz hx hh hΛ1 Φ hΦ hsolv _ hκp M hM1 hperm R hR
        (by omega) g hgs hgp hgm hga
      have hb1 := (hbase I rfl hz hx hh Φ hΦ _ hκp M hM1 hperm R hR (by omega) g hgs hgp hgm
        hga θj hθj).2
      have hdiff := weak_dissipation_ge_classical hbm hbb hbp hdiv hφm hφp hφd (fun _ _ _ => rfl)
        (streamSeq_isAdmissible hΦ M) hκpos hgs hgp hθM (hθ _ hκpos) (htail M hM1) hη
      have hnn : 0 ≤ c₁ * R ^ pPlus β * l2NormSq g :=
        mul_nonneg (mul_nonneg hc₁.le (Real.rpow_nonneg hR.le _)) hN
      linarith
    exact le_limsup_of_seq (F := fun κ => κ * spaceTimeGradNormSq (Dθ κ))
      (kappaCentre_tendsto hβ1 hb h7) hU hdisp

end AVenhance.Infra.Section5.RelativeError

end
