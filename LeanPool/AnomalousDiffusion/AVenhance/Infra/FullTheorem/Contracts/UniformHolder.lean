/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.UniformHolderContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.AnalyticUniform
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.UniformInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.UniformH1.Core
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.WeakWellposed

/-! # The general `H¹` case of `r.LeBron.2`, proved

Assembly of `UniformH1.holder_of_analytic` with the analytic case (`analyticUniform_contract`),
the heat approximation, `L²` contraction of differences, classical existence, and the energy
    identity,
for the drift `streamVel φ` of the limit stream. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem AVenhance.Infra.Parabolic.WeakUniqueness

theorem uniformHolder_contract (β C₀ : ℝ) : UniformHolderContract β C₀ := by
  by_cases hβr : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨1, 0, one_pos, fun I => ?_⟩
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hβr
  obtain ⟨hβ1, hβ2⟩ := hβr
  obtain ⟨μ, p, Λ₂, hμ, hp, hA⟩ := analyticUniform_contract β C₀
  obtain ⟨Ct, hCt1, hlim⟩ := AVenhance.limit_field_regular β
  refine ⟨μ / (1 + p), Λ₂, div_pos hμ (by linarith), ?_⟩
  intro I hz hx hh hΛ Φ hΦ φ htend
  obtain ⟨K, hK, hKb⟩ := hA I hz hx hh hΛ Φ hΦ φ htend
  refine ⟨11 + 4 * (2 : ℝ) ^ p * K, by positivity, ?_⟩
  intro θ₀ Dθ₀ hθ₀ hm κ hκ θ hθ
  -- the limit field
  obtain ⟨φ', htend', -, -, -, hhol'⟩ := hlim I Φ hΦ
  have hφφ : φ' = φ := by
    funext t x
    exact tendsto_nhds_unique (htend' t x) (htend t x)
  subst hφφ
  have hα0 : 0 < (β - 1) / 2 := by linarith
  have hα1 : (β - 1) / 2 < β - 1 := by linarith
  obtain ⟨hHolder, hdiv⟩ := hhol' _ hα0 hα1
  obtain ⟨Cb, hCb⟩ := hHolder.2.2.1
  have hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖streamVel φ' t x‖ ≤ C :=
    ⟨Cb, hCb⟩
  have hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => streamVel φ' p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :=
    hHolder.2.1.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
  have hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (streamVel φ' t) :=
    fun t ht => hHolder.1 t ht
  -- positivity of `κ`
  have hκ0 : 0 < κ := by
    obtain ⟨M, hM, hκM⟩ := Set.mem_iUnion₂.1 hκ
    have hε : 0 < epsilon β I.Λ M := Infra.Cutoff.epsilon_pos hβ1 hβ2 I.two_pow_seven_le
    exact lt_of_lt_of_le (by positivity) hκM.1
  refine UniformH1.holder_of_analytic hμ hp hK heatApproxH1_contract ?_ ?_ ?_ ?_ hθ₀ hm hθ
  · exact fun R hR g hg hgp hgm han θ' hθ' => hKb κ hκ R hR g hg hgp hgm han θ' hθ'
  · intro f g hf hg θ θ' hθ hθ' t ht
    obtain ⟨D, hD⟩ := hθ
    obtain ⟨D', hD'⟩ := hθ'
    exact weakDifference_contract hb_meas hb_bdd hb_per hdiv hκ0 hf hg hD hD' t ht
  · intro g hg
    obtain ⟨θ', h, -⟩ := AVenhance.weak_wellposed _ hb_meas hb_bdd hb_per κ hκ0 g hg
    exact ⟨θ', h⟩
  · intro f hf θ hθ t ht
    obtain ⟨D, hD⟩ := hθ
    have hid := weak_solution_divFree_energy_identity hD hf hb_meas hb_bdd hb_per hdiv t ht
    have hnn : 0 ≤ ∫ p in Set.Ioo (0 : ℝ) t ×ˢ unitCube, vecNormSq (D p.1 p.2) :=
      integral_nonneg fun p => vecNormSq_nonneg _
    have : 0 ≤ 2 * κ * (∫ p in Set.Ioo (0 : ℝ) t ×ˢ unitCube, vecNormSq (D p.1 p.2)) := by
      positivity
    linarith

end AVenhance.Infra.FullTheorem.Contracts
