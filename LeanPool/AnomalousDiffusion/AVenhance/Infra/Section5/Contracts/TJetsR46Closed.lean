/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJetsDatum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.R46Source

/-! # Uniform-amplitude `R46` wiring and its closed datum producer -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

/-- `R46`'s coefficient is uniform in the amplitude, chosen before the instance. -/
theorem r46Source_of_TGradient_uniform_amplitude (β C₀ A : ℝ) :
    ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
        ∀ B : ℝ, TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
          R46SourceContract I hΦ m (I.kappaSeq κ M m) T A B) := by
  refine ⟨0, ?_⟩
  intro I hCzeta hCxi hChat _hC₁ Φ hΦ κ hpermissible M hM hpermitted R hR _θ₀
    _hθsmooth _hθperiod _hmean _hanalytic m hm hmM θprev T hθprev hT B hTgrad
  obtain ⟨hm2, hκm⟩ := onA7_basic I hpermitted hR hm
  obtain ⟨_, _, hscales⟩ := LeftToShow.left_to_show_scales β C₀
  have hscale := hscales I hCzeta hCxi hChat κ hpermissible M hM hpermitted m hm2 hmM
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := lt_of_lt_of_le hκm hscale.2.1
  have hκmono := hscale.2.1
  let R := Infra.Construction.section2Radius I
  let Mscale := Infra.Construction.section2Amplitude I
  have hscalesCanonical : Infra.Construction.Section2Scales I R Mscale := by
    simpa [R, Mscale] using Infra.Construction.section2Scales_canonical I
  have happB2 : Infra.Construction.AppB2InverseFlowData I Φ hΦ R Mscale := by
    simpa [R, Mscale] using Infra.Construction.appB2InverseFlowData_of_smoothPeriodicFlow hΦ
      (Infra.Construction.section2Scales_canonical I)
  obtain ⟨_, ⟨Cmat, _hCmat, hflow⟩⟩ :=
    AVenhance.Proofs.section2_induction_outputs_from_source_data hscalesCanonical happB2
  have hTOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => T (Nstar β) p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl
  have hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞)
        (r46Flux I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t) := by
    intro t ht
    exact (tIterate_r46Flux_regular I hΦ (by omega) (I.kappaSeq κ M m)
      hT hθprev le_rfl ht.1).1
  change Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq
        (fun t x => spaceGrad (T (Nstar β) t) x)) ≤
    A * B at hTgrad
  have hflux := r46TimeL2_flux_le_of_flowBounds_and_energy I hΦ Cmat hflow
    m (by omega) (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1))
    A B (T (Nstar β)) hTOn hF hκm hκprev hκmono hTgrad
  change R46SourceContract I hΦ m (I.kappaSeq κ M m) T
    A B
  simpa [R46SourceContract, r46TimeL2] using hflux

/-- Exact datum `R46` source contract, with its T-gradient input discharged. -/
theorem r46Source_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        R46SourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, _, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨Cs, hsource⟩ := r46Source_of_TGradient_uniform_amplitude β Ccut A
  refine ⟨A, max Cj Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR
    θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR
    θ₀ hs hp hmean ha m hm hmM θprev T hθ hT (Real.sqrt (l2NormSq θ₀)) hj.1

end AVenhance.Infra.Section5.Contracts
