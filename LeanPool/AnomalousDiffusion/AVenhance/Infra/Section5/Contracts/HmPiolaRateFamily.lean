/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmPiolaRateQ
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.HmSup

/-! # Family producer for the Piola source rate

`hmPiolaSourceRate_onA7` proves the spacetime `L²` rate `HmPiolaSourceRate` of the
divergence of the regular Piola flux `Σ_l ξ̂_l F_lᵀ (𝒥 - K) F_l ∇T`, unconditionally on
the big-bound premise block.  It combines

* the pointwise product-rule bound `|Piola| ≤ 32 A · hmPiolaQ`
  (`hmPiola_vecDiv_tsum_abs_le`), `A` bounding the entries of `𝒥 - K`;
* the flux coefficient rate `hm_flux_coefficient_rate_onA7` for `A`;
* the `L²` rate of the majorant `hmPiolaQ` (`hmPiolaQ_eLpNorm_rate_onA7`);
* the measurability of the actual Piola source on the time cube
  (`hm_actual_pairing_field_measurability`). -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4
open AVenhance.Infra.Section5.Integration

/-- **The Piola source rate**, produced on the big-bound premise block. -/
theorem hmPiolaSourceRate_onA7 (β C₀ : ℝ) :
    ∃ Creg C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        HmPiolaSourceRate I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T Creg
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨C₁flux, Cflux, hCflux, hFluxFamily⟩ :=
    hm_flux_coefficient_rate_onA7 β (max C₀ 1) (le_max_right C₀ 1)
  obtain ⟨C₁q, Cq, hCq, hQFamily⟩ := hmPiolaQ_eLpNorm_rate_onA7 β (max C₀ 1)
  refine ⟨32 * Cflux * Cq, max C₁flux C₁q, ?_⟩
  intro I hCzeta hCxi hChat hC₁ Φ hΦ κ hκPerm M hM hPerm R hR θ₀
    hθ₀smooth hθ₀periodic hθ₀mean hθ₀analytic m hmStart hmM θprev T hθprev hT
  have hFlux := hFluxFamily I
    (hCzeta.trans (le_max_left C₀ 1))
    (hCxi.trans (le_max_left C₀ 1))
    (hChat.trans (le_max_left C₀ 1))
    ((le_max_left C₁flux C₁q).trans hC₁)
    Φ hΦ κ hκPerm M hM hPerm R hR θ₀ hθ₀smooth hθ₀periodic hθ₀mean
    hθ₀analytic m hmStart hmM θprev T hθprev hT
  have hQ := hQFamily I
    (hCzeta.trans (le_max_left C₀ 1))
    (hCxi.trans (le_max_left C₀ 1))
    (hChat.trans (le_max_left C₀ 1))
    ((le_max_right C₁flux C₁q).trans hC₁)
    Φ hΦ κ hκPerm M hM hPerm R hR θ₀ hθ₀smooth hθ₀periodic hθ₀mean
    hθ₀analytic m hmStart hmM θprev T hθprev hT
  obtain ⟨hm2, hκm⟩ := onA7_basic I hPerm hR hmStart
  have hm1 : 1 ≤ m := by omega
  let κm : ℝ := I.kappaSeq κ M m
  let κprev : ℝ := I.kappaSeq κ M (m - 1)
  let Tn : ℝ → Vec 2 → ℝ := T (Nstar β)
  let μ : Measure (ℝ × Vec 2) := volume.restrict AVenhance.timeCube
  let E : ℝ := epsilon β I.Λ (m - 1)
  let Qm : ℝ := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm
  let B : ℝ := Real.sqrt (l2NormSq θ₀)
  let G : ℝ := Cq * B * (Real.sqrt κprev)⁻¹ * E ^ (-(1 + gamma β / 2))
  have hκm' : 0 < κm := by simpa [κm] using hκm
  have hE : 0 < E :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hQm : 0 ≤ Qm := by dsimp [Qm]; positivity
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κm Tn z.1 z.2) μ :=
    (hm_actual_pairing_field_measurability I hΦ hm1 hκm' hθprev hT).1
  have hQ' : eLpNorm (fun z : ℝ × Vec 2 => hmPiolaQ E Tn z.1 z.2) 2 μ ≤
      ENNReal.ofReal G := by
    simpa [μ, Tn, E, κprev, B, G,
      show (-1 - gamma β / 2) = -(1 + gamma β / 2) by ring] using hQ
  set c : ℝ := 32 * (Cflux * Qm) with hc
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hpoint : ∀ z ∈ AVenhance.timeCube,
      ‖hmFrozenPiolaSource I hΦ m κm Tn z.1 z.2‖ ≤
        ‖c * hmPiolaQ E Tn z.1 z.2‖ := by
    intro z hz
    have hTt : ContDiff ℝ (⊤ : ℕ∞) (Tn z.1) :=
      tIterate_space_contDiff I hΦ hT hθprev le_rfl hz.1.1.le
    have hb := hmPiola_active_flow_bounds I hΦ hm2 z.1
    have hA : ∀ i j : Fin 2,
        |(I.flux κm m z.1 - I.Kmat κm m z.1) i j| ≤ Cflux * Qm := by
      intro i j
      simpa [κm, Qm] using hFlux z.1 i j
    have hbound := hmPiola_vecDiv_tsum_abs_le I hΦ hm1 Tn hTt hE
      (fun l hl => (hb l hl).1)
      (fun l hl => (hb l hl).2.1)
      (fun l hl x p j q => by
        simpa [E, div_eq_mul_inv] using (hb l hl).2.2 x p j q)
      (I.flux κm m z.1 - I.Kmat κm m z.1) hA z.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc0 (hmPiolaQ_nonneg E hE Tn z.1 z.2))]
    exact hbound
  have hpointAE : ∀ᵐ z ∂μ,
      ‖hmFrozenPiolaSource I hΦ m κm Tn z.1 z.2‖ ≤
        ‖c * hmPiolaQ E Tn z.1 z.2‖ := by
    filter_upwards [ae_restrict_mem AVenhance.Infra.Section5.RelativeError.measurableSet_timeCube]
      with z hz using hpoint z hz
  have hmono := eLpNorm_mono_ae hmeas hpointAE (p := 2)
  have hscale : eLpNorm (fun z : ℝ × Vec 2 => c * hmPiolaQ E Tn z.1 z.2) 2 μ =
      ENNReal.ofReal c * eLpNorm (fun z : ℝ × Vec 2 => hmPiolaQ E Tn z.1 z.2) 2 μ := by
    have hfun : (fun z : ℝ × Vec 2 => c * hmPiolaQ E Tn z.1 z.2) =
        c • (fun z : ℝ × Vec 2 => hmPiolaQ E Tn z.1 z.2) := by
      funext z; simp
    rw [hfun, eLpNorm_const_smul, Real.enorm_of_nonneg hc0]
  change eLpNorm (fun z : ℝ × Vec 2 => hmFrozenPiolaSource I hΦ m κm Tn z.1 z.2) 2 μ ≤
    ENNReal.ofReal ((32 * Cflux * Cq) * B * Qm * (Real.sqrt κprev)⁻¹ *
      E ^ (-(1 + gamma β / 2)))
  calc
    _ ≤ eLpNorm (fun z : ℝ × Vec 2 => c * hmPiolaQ E Tn z.1 z.2) 2 μ := hmono
    _ = ENNReal.ofReal c *
        eLpNorm (fun z : ℝ × Vec 2 => hmPiolaQ E Tn z.1 z.2) 2 μ := hscale
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal G :=
      mul_le_mul_of_nonneg_left hQ' zero_le
    _ = ENNReal.ofReal (c * G) := (ENNReal.ofReal_mul hc0).symm
    _ = _ := by
      congr 1
      dsimp [c, G]
      ring

end AVenhance.Infra.Section5.Contracts

end
