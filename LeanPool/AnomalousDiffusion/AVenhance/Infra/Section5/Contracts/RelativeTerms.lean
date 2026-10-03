/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.A7Assembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.MeanZero
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxes
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.R46Source

/-! # Centered relative term bounds from the exact source contracts

The amplitude is abstract. Slots 3, 4, and 8 use their centered source contracts directly;
no individual mean-zero assumption is made for the corresponding raw terms.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section5 Integration

/-- The exact contracts needed by the ten termwise negative-norm estimates at amplitude B. -/
structure RelativeTermInputs {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ) : Prop where
  cutoff1_meanZero : Cutoff1MeanZeroContract I hΦ m κm T
  cutoff1_source : Cutoff1SourceContract I hΦ m κm T C B
  twistie1_source : Twistie1HMinusSourceContract I hΦ m κm T C B
  twistie3_flux_smooth : Twistie3FluxSmoothContract I hΦ m κm T
  twistie3_flux_periodic : Twistie3FluxPeriodicContract I hΦ m κm T
  twistie3_source : Twistie3SourceContract I hΦ m κm T C B
  twistie4_centered_source : Twistie4CenteredSourceContract I hΦ m κm T C B
  twistie5_centered_source : Twistie5CenteredSourceContract I hΦ m κm T C B
  normie3_centered_source : Normie3CenteredSourceContract I hΦ m κm T C B
  normie1_flux_smooth : Normie1FluxSmoothContract I hΦ m κm T
  normie1_flux_periodic : Normie1FluxPeriodicContract I hΦ m κm T
  normie1_source : Normie1SourceContract I hΦ m κm T C B
  normie2_flux_smooth : Normie2FluxSmoothContract I hΦ m κm T
  normie2_flux_periodic : Normie2FluxPeriodicContract I hΦ m κm T
  normie2_source : Normie2SourceContract I hΦ m κm T C B
  tiny_source : TinyHMinusSourceContract I hΦ m κm κprev T C B
  R46_flux_smooth : R46FluxSmoothContract I hΦ m κm T
  R46_flux_periodic : R46FluxPeriodicContract I hΦ m κm T
  R46_source : R46SourceContract I hΦ m κm T C B
  term_continuous : TermContinuousContract I hΦ m κm κprev T

/-- Scalar duality, divergence duality, and the three centered contracts give the literal
relative contract. This helper does not assume the ten-term negative-norm conclusion. -/
theorem relativeTerms_of_inputs {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (C B : ℝ)
    (h : RelativeTermInputs I hΦ m κm κprev T C B) :
    RelativeTermsContract I hΦ m κm κprev T C B := by
  have hL2 (i : ℕ) (hi : i < 10) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :=
    Integration.memL2On_of_continuousOn_slice (h.term_continuous i hi) ht
  have hscale : C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt κm * B =
      C * Real.sqrt κm * epsilon β I.Λ (m - 1) ^ delta β * B := by ring
  intro i hi
  rw [← hscale]
  interval_cases i
  · exact timeHMinusOneNorm_le_L2_of_sourceScale
      (hL2 0 (by norm_num)) h.cutoff1_meanZero h.cutoff1_source
  · exact h.twistie1_source
  · exact (timeHMinusOneNorm_twistie3_le I hΦ m κm (T (Nstar β))
      h.twistie3_flux_smooth h.twistie3_flux_periodic).trans h.twistie3_source
  · exact h.twistie4_centered_source
  · exact h.twistie5_centered_source
  · exact (timeHMinusOneNorm_normie1_le I hΦ m κm (T (Nstar β))
      h.normie1_flux_smooth h.normie1_flux_periodic).trans h.normie1_source
  · exact (timeHMinusOneNorm_normie2_le I hΦ m κm (T (Nstar β))
      h.normie2_flux_smooth h.normie2_flux_periodic).trans h.normie2_source
  · exact h.tiny_source
  · exact h.normie3_centered_source
  · exact (timeHMinusOneNorm_R46_le I hΦ m κm (T (Nstar β))
      h.R46_flux_smooth h.R46_flux_periodic).trans h.R46_source

/-- Independent source producers at the relative amplitude S, with exactly the gate. -/
structure RelativeSourceProducers (β C₀ : ℝ) : Prop where
  cutoff1_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Cutoff1SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie1_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie1HMinusSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie3_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie3SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie4_centered_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie4CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie5_centered_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie5CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  normie3_centered_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  normie1_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Normie1SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  normie2_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Normie2SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  tiny_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      TinyHMinusSourceContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C (Real.sqrt
          (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev
          s) x))))
  R46_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      R46SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))

/-- Assemble the producer of the exact centered relative-term contract from the ten independent
source producers at S. The mean-zero, flux, and continuity contracts are discharged here. -/
theorem relativeTerms_of_source_producers (β C₀ : ℝ) (h : RelativeSourceProducers β C₀) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
        (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        RelativeTermsContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨c_cutoff1_source, l_cutoff1_source, h_cutoff1_source⟩ := h.cutoff1_source
  obtain ⟨c_twistie1_source, l_twistie1_source, h_twistie1_source⟩ := h.twistie1_source
  obtain ⟨c_twistie3_source, l_twistie3_source, h_twistie3_source⟩ := h.twistie3_source
  obtain ⟨c_twistie4_centered_source, l_twistie4_centered_source, h_twistie4_centered_source⟩ :=
      h.twistie4_centered_source
  obtain ⟨c_twistie5_centered_source, l_twistie5_centered_source, h_twistie5_centered_source⟩ :=
      h.twistie5_centered_source
  obtain ⟨c_normie3_centered_source, l_normie3_centered_source, h_normie3_centered_source⟩ :=
      h.normie3_centered_source
  obtain ⟨c_normie1_source, l_normie1_source, h_normie1_source⟩ := h.normie1_source
  obtain ⟨c_normie2_source, l_normie2_source, h_normie2_source⟩ := h.normie2_source
  obtain ⟨c_tiny_source, l_tiny_source, h_tiny_source⟩ := h.tiny_source
  obtain ⟨c_R46_source, l_R46_source, h_R46_source⟩ := h.R46_source
  obtain ⟨l_cutoff1_meanZero, h_cutoff1_meanZero⟩ := cutoff1MeanZero_contract β C₀
  obtain ⟨l_twistie3_flux_smooth, h_twistie3_flux_smooth⟩ := twistie3FluxSmooth_contract β C₀
  obtain ⟨l_twistie3_flux_periodic, h_twistie3_flux_periodic⟩ := twistie3FluxPeriodic_contract β C₀
  obtain ⟨l_normie1_flux_smooth, h_normie1_flux_smooth⟩ := normie1FluxSmooth_contract β C₀
  obtain ⟨l_normie1_flux_periodic, h_normie1_flux_periodic⟩ := normie1FluxPeriodic_contract β C₀
  obtain ⟨l_normie2_flux_smooth, h_normie2_flux_smooth⟩ := normie2FluxSmooth_contract β C₀
  obtain ⟨l_normie2_flux_periodic, h_normie2_flux_periodic⟩ := normie2FluxPeriodic_contract β C₀
  obtain ⟨l_R46_flux_smooth, h_R46_flux_smooth⟩ := r46FluxSmooth_contract β C₀
  obtain ⟨l_R46_flux_periodic, h_R46_flux_periodic⟩ := r46FluxPeriodic_contract β C₀
  obtain ⟨l_term_continuous, h_term_continuous⟩ := termContinuous_contract β C₀
  obtain ⟨L, _, hL⟩ := exists_nonneg_upper_bound [l_cutoff1_meanZero, l_cutoff1_source,
      l_twistie1_source, l_twistie3_flux_smooth, l_twistie3_flux_periodic, l_twistie3_source,
      l_twistie4_centered_source, l_twistie5_centered_source, l_normie3_centered_source,
      l_normie1_flux_smooth, l_normie1_flux_periodic, l_normie1_source, l_normie2_flux_smooth,
      l_normie2_flux_periodic, l_normie2_source, l_tiny_source, l_R46_flux_smooth,
      l_R46_flux_periodic, l_R46_source, l_term_continuous]
  obtain ⟨C, _, hC⟩ := exists_nonneg_upper_bound [c_cutoff1_source, c_twistie1_source,
      c_twistie3_source, c_twistie4_centered_source, c_twistie5_centered_source,
      c_normie3_centered_source, c_normie1_source, c_normie2_source, c_tiny_source, c_R46_source]
  refine ⟨C, L, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
    θm θprev T hθm hθprev hT hgate hlater
  have he : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β := Real.rpow_nonneg
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _
  have hS : 0 ≤ Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hscale {c : ℝ} (hc : c ≤ C) :
      ENNReal.ofReal (c * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (I.kappaSeq κ M m) *
        (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) ≤
      ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (I.kappaSeq κ M m) *
        (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc he)
        (Real.sqrt_nonneg _)) hS)
  have p_cutoff1_meanZero := h_cutoff1_meanZero I hz hx hh ((hL l_cutoff1_meanZero (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_cutoff1_source := h_cutoff1_source I hz hx hh ((hL l_cutoff1_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_twistie1_source := h_twistie1_source I hz hx hh ((hL l_twistie1_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_twistie3_flux_smooth := h_twistie3_flux_smooth I hz hx hh ((hL l_twistie3_flux_smooth (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie3_flux_periodic := h_twistie3_flux_periodic I hz hx hh ((hL
      l_twistie3_flux_periodic (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie3_source := h_twistie3_source I hz hx hh ((hL l_twistie3_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_twistie4_centered_source := h_twistie4_centered_source I hz hx hh ((hL
      l_twistie4_centered_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_twistie5_centered_source := h_twistie5_centered_source I hz hx hh ((hL
      l_twistie5_centered_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_normie3_centered_source := h_normie3_centered_source I hz hx hh ((hL
      l_normie3_centered_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_normie1_flux_smooth := h_normie1_flux_smooth I hz hx hh ((hL l_normie1_flux_smooth (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie1_flux_periodic := h_normie1_flux_periodic I hz hx hh ((hL l_normie1_flux_periodic
      (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie1_source := h_normie1_source I hz hx hh ((hL l_normie1_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_normie2_flux_smooth := h_normie2_flux_smooth I hz hx hh ((hL l_normie2_flux_smooth (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie2_flux_periodic := h_normie2_flux_periodic I hz hx hh ((hL l_normie2_flux_periodic
      (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie2_source := h_normie2_source I hz hx hh ((hL l_normie2_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_tiny_source := h_tiny_source I hz hx hh ((hL l_tiny_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_R46_flux_smooth := h_R46_flux_smooth I hz hx hh ((hL l_R46_flux_smooth (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_R46_flux_periodic := h_R46_flux_periodic I hz hx hh ((hL l_R46_flux_periodic (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_R46_source := h_R46_source I hz hx hh ((hL l_R46_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  have p_term_continuous := h_term_continuous I hz hx hh ((hL l_term_continuous (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  apply relativeTerms_of_inputs
  exact {
    cutoff1_meanZero := p_cutoff1_meanZero
    cutoff1_source := p_cutoff1_source.trans (hscale (hC c_cutoff1_source (by simp)))
    twistie1_source := p_twistie1_source.trans (hscale (hC c_twistie1_source (by simp)))
    twistie3_flux_smooth := p_twistie3_flux_smooth
    twistie3_flux_periodic := p_twistie3_flux_periodic
    twistie3_source := p_twistie3_source.trans (hscale (hC c_twistie3_source (by simp)))
    twistie4_centered_source := p_twistie4_centered_source.trans (hscale (hC
        c_twistie4_centered_source (by simp)))
    twistie5_centered_source := p_twistie5_centered_source.trans (hscale (hC
        c_twistie5_centered_source (by simp)))
    normie3_centered_source := p_normie3_centered_source.trans (hscale (hC
        c_normie3_centered_source (by simp)))
    normie1_flux_smooth := p_normie1_flux_smooth
    normie1_flux_periodic := p_normie1_flux_periodic
    normie1_source := p_normie1_source.trans (hscale (hC c_normie1_source (by simp)))
    normie2_flux_smooth := p_normie2_flux_smooth
    normie2_flux_periodic := p_normie2_flux_periodic
    normie2_source := p_normie2_source.trans (hscale (hC c_normie2_source (by simp)))
    tiny_source := p_tiny_source.trans (hscale (hC c_tiny_source (by simp)))
    R46_flux_smooth := p_R46_flux_smooth
    R46_flux_periodic := p_R46_flux_periodic
    R46_source := p_R46_source.trans (hscale (hC c_R46_source (by simp)))
    term_continuous := p_term_continuous
  }

/-- `R46` source producer at the actual relative amplitude. Its sole extra premise is the
exact gradient contract, and its constants are independent of the ingredient instance. -/
theorem r46Source_relative_of_TGradient (β C₀ A : ℝ) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R _θ₀ m _θm θprev T =>
        let S := Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))
        TGradientContract β (I.kappaSeq κ M (m - 1)) T A S →
          R46SourceContract I hΦ m (I.kappaSeq κ M m) T C S) := by
  refine ⟨A, 0, ?_⟩
  intro I hCzeta hCxi hChat _hC₁ Φ hΦ κ hpermissible M hM hpermitted R hR _θ₀
    _hθsmooth _hθperiod _hmean _hanalytic m hm hmM _θm θprev T _hθm hθprev hT
  dsimp only
  intro hTgrad
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
    A * (Real.sqrt (I.kappaSeq κ M (m - 1)) *
        Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))) at hTgrad
  have hflux := r46TimeL2_flux_le_of_flowBounds_and_energy I hΦ Cmat hflow
    m (by omega) (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1))
    A (Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))) (T (Nstar β)) hTOn hF
          hκm hκprev hκmono hTgrad
  change R46SourceContract I hΦ m (I.kappaSeq κ M m) T
    A (Real.sqrt (I.kappaSeq κ M (m - 1)) *
      Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))
  simpa [R46SourceContract, r46TimeL2] using hflux

/-- The nine source producer slots, excluding the separately supplied `R46` slot. -/
structure RelativeNineSourceProducers (β C₀ : ℝ) : Prop where
  cutoff1_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Cutoff1SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie1_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie1HMinusSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie3_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie3SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie4_centered_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie4CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  twistie5_centered_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Twistie5CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  normie3_centered_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m -
          1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  normie1_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Normie1SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  normie2_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      Normie2SourceContract I hΦ m (I.kappaSeq κ M m) T C (Real.sqrt (I.kappaSeq κ M (m - 1)) *
          Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))
  tiny_source : ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
    (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
      (6 : ℝ) / 5 ≤ β →
      epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
      TinyHMinusSourceContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C (Real.sqrt
          (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev
          s) x))))

/-- Complete the centered relative contract from the nine source producers and a gradient
producer at S. `R46`'s source is proved from the gradient contract, rather than assumed. -/
theorem relativeTerms_contract_of_nine_sources_and_gradient (β C₀ : ℝ)
    (hnine : RelativeNineSourceProducers β C₀)
    (hgradient : ∃ A C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ _hΦ κ M R _θ₀ m _θm θprev T =>
        (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        TGradientContract β (I.kappaSeq κ M (m - 1)) T A
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x))))) :
    ∃ C C₁ : ℝ, OnA8Instances β C₀ C₁
      (fun I _Φ hΦ κ M R _θ₀ m _θm θprev T =>
        (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        RelativeTermsContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C
          (Real.sqrt (I.kappaSeq κ M (m - 1)) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (θprev s) x)))) := by
  obtain ⟨A, Lg, hg⟩ := hgradient
  obtain ⟨Cr, Lr, hr⟩ := r46Source_relative_of_TGradient β C₀ A
  apply relativeTerms_of_source_producers β C₀
  refine {
    cutoff1_source := hnine.cutoff1_source
    twistie1_source := hnine.twistie1_source
    twistie3_source := hnine.twistie3_source
    twistie4_centered_source := hnine.twistie4_centered_source
    twistie5_centered_source := hnine.twistie5_centered_source
    normie3_centered_source := hnine.normie3_centered_source
    normie1_source := hnine.normie1_source
    normie2_source := hnine.normie2_source
    tiny_source := hnine.tiny_source
    R46_source := ?_
  }
  refine ⟨Cr, max Lg Lr, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM
    θm θprev T hθm hθprev hT hgate hlater
  have hG := hg I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR
    θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hgate hlater
  exact hr I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR
    θ₀ hθ hper hmean hana m hm hmM θm θprev T hθm hθprev hT hG

end AVenhance.Infra.Section5.Contracts
