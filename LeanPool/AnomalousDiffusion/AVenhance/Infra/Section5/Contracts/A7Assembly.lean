/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound

/-! # Big-bound estimate assembly from the individual contract producers

Each field below is a producer of exactly one contract. Its constants and threshold
are chosen before the ingredient instance. No field assumes the assembled big-bound estimate
    conclusion.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section5 Integration

/-- The independent big-bound estimate contract producers, including the grouped mean-zero
    contract. -/
structure A7ContractProducers (β C₀ : ℝ) : Prop where
  residual : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => ResidualContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ
        M (m - 1)) T)
  cutoff1_meanZero : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => Cutoff1MeanZeroContract I hΦ m (I.kappaSeq κ M m) T)
  cutoff1_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Cutoff1SourceContract I hΦ m (I.kappaSeq κ M m) T C
        (Real.sqrt (l2NormSq θ₀)))
  twistie1_hminus_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Twistie1HMinusSourceContract I hΦ m (I.kappaSeq κ M m) T
        C (Real.sqrt (l2NormSq θ₀)))
  twistie3_flux_smooth : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => Twistie3FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T)
  twistie3_flux_periodic : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => Twistie3FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T)
  twistie3_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Twistie3SourceContract I hΦ m (I.kappaSeq κ M m) T C
        (Real.sqrt (l2NormSq θ₀)))
  group_meanZero : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => GroupMeanZeroContract I hΦ m (I.kappaSeq κ M m) T)
  twistie4_centered_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Twistie4CenteredSourceContract I hΦ m (I.kappaSeq κ M m)
        T C (Real.sqrt (l2NormSq θ₀)))
  twistie5_centered_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Twistie5CenteredSourceContract I hΦ m (I.kappaSeq κ M m)
        T C (Real.sqrt (l2NormSq θ₀)))
  normie3_centered_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T
        C (Real.sqrt (l2NormSq θ₀)))
  normie1_flux_smooth : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => Normie1FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T)
  normie1_flux_periodic : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => Normie1FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T)
  normie1_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Normie1SourceContract I hΦ m (I.kappaSeq κ M m) T C
        (Real.sqrt (l2NormSq θ₀)))
  normie2_flux_smooth : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => Normie2FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T)
  normie2_flux_periodic : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => Normie2FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T)
  normie2_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => Normie2SourceContract I hΦ m (I.kappaSeq κ M m) T C
        (Real.sqrt (l2NormSq θ₀)))
  tiny_hminus_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => TinyHMinusSourceContract I hΦ m (I.kappaSeq κ M m)
        (I.kappaSeq κ M (m - 1)) T C (Real.sqrt (l2NormSq θ₀)))
  R46_flux_smooth : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => R46FluxSmoothContract I hΦ m (I.kappaSeq κ M m) T)
  R46_flux_periodic : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => R46FluxPeriodicContract I hΦ m (I.kappaSeq κ M m) T)
  R46_source : ∃ C C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R θ₀ m _θprev T => R46SourceContract I hΦ m (I.kappaSeq κ M m) T C
        (Real.sqrt (l2NormSq θ₀)))
  term_continuous : ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
    (fun I _Φ hΦ κ M _R _θ₀ m _θprev T => TermContinuousContract I hΦ m (I.kappaSeq κ M m)
        (I.kappaSeq κ M (m - 1)) T)

/-- A finite list of real constants has a nonnegative common upper bound. -/
theorem exists_nonneg_upper_bound (xs : List ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ xs, x ≤ C := by
  induction xs with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons x xs ih =>
    obtain ⟨C, hC, hx⟩ := ih
    refine ⟨max x C, hC.trans (le_max_right _ _), ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_max_left _ _
    · exact (hx y hy).trans (le_max_right _ _)

/-- Assemble the big-bound estimate inputs; source constants are enlarged only by monotonicity. -/
theorem bigbound_family_of_contracts (β C₀ : ℝ) (h : A7ContractProducers β C₀) :
    BigBoundFamilyContract β C₀ := by
  obtain ⟨l_residual, h_residual⟩ := h.residual
  obtain ⟨l_cutoff1_meanZero, h_cutoff1_meanZero⟩ := h.cutoff1_meanZero
  obtain ⟨c_cutoff1_source, l_cutoff1_source, h_cutoff1_source⟩ := h.cutoff1_source
  obtain ⟨c_twistie1_source, l_twistie1_source, h_twistie1_source⟩ := h.twistie1_hminus_source
  obtain ⟨l_twistie3_flux_smooth, h_twistie3_flux_smooth⟩ := h.twistie3_flux_smooth
  obtain ⟨l_twistie3_flux_periodic, h_twistie3_flux_periodic⟩ := h.twistie3_flux_periodic
  obtain ⟨c_twistie3_source, l_twistie3_source, h_twistie3_source⟩ := h.twistie3_source
  obtain ⟨l_group_meanZero, h_group_meanZero⟩ := h.group_meanZero
  obtain ⟨c_twistie4_centered_source, l_twistie4_centered_source, h_twistie4_centered_source⟩ :=
      h.twistie4_centered_source
  obtain ⟨c_twistie5_centered_source, l_twistie5_centered_source, h_twistie5_centered_source⟩ :=
      h.twistie5_centered_source
  obtain ⟨c_normie3_centered_source, l_normie3_centered_source, h_normie3_centered_source⟩ :=
      h.normie3_centered_source
  obtain ⟨l_normie1_flux_smooth, h_normie1_flux_smooth⟩ := h.normie1_flux_smooth
  obtain ⟨l_normie1_flux_periodic, h_normie1_flux_periodic⟩ := h.normie1_flux_periodic
  obtain ⟨c_normie1_source, l_normie1_source, h_normie1_source⟩ := h.normie1_source
  obtain ⟨l_normie2_flux_smooth, h_normie2_flux_smooth⟩ := h.normie2_flux_smooth
  obtain ⟨l_normie2_flux_periodic, h_normie2_flux_periodic⟩ := h.normie2_flux_periodic
  obtain ⟨c_normie2_source, l_normie2_source, h_normie2_source⟩ := h.normie2_source
  obtain ⟨c_tiny_source, l_tiny_source, h_tiny_source⟩ := h.tiny_hminus_source
  obtain ⟨l_R46_flux_smooth, h_R46_flux_smooth⟩ := h.R46_flux_smooth
  obtain ⟨l_R46_flux_periodic, h_R46_flux_periodic⟩ := h.R46_flux_periodic
  obtain ⟨c_R46_source, l_R46_source, h_R46_source⟩ := h.R46_source
  obtain ⟨l_term_continuous, h_term_continuous⟩ := h.term_continuous
  obtain ⟨L, _, hL⟩ := exists_nonneg_upper_bound [l_residual, l_cutoff1_meanZero,
      l_cutoff1_source, l_twistie1_source, l_twistie3_flux_smooth, l_twistie3_flux_periodic,
      l_twistie3_source, l_group_meanZero, l_twistie4_centered_source, l_twistie5_centered_source,
      l_normie3_centered_source, l_normie1_flux_smooth, l_normie1_flux_periodic, l_normie1_source,
      l_normie2_flux_smooth, l_normie2_flux_periodic, l_normie2_source, l_tiny_source,
      l_R46_flux_smooth, l_R46_flux_periodic, l_R46_source, l_term_continuous]
  obtain ⟨C, _, hC⟩ := exists_nonneg_upper_bound [c_cutoff1_source, c_twistie1_source,
      c_twistie3_source, c_twistie4_centered_source, c_twistie5_centered_source,
      c_normie3_centered_source, c_normie1_source, c_normie2_source, c_tiny_source, c_R46_source]
  refine ⟨L, C, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have he : 0 ≤ epsilon β I.Λ (m - 1) ^ delta β :=
    Real.rpow_nonneg (le_of_lt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)) _
  have hscale {c : ℝ} (hc : c ≤ C) :
      ENNReal.ofReal (c * epsilon β I.Λ (m - 1) ^ delta β *
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (l2NormSq θ₀)) ≤
      ENNReal.ofReal (C * epsilon β I.Λ (m - 1) ^ delta β *
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (l2NormSq θ₀)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc he)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have p_residual := h_residual I hz hx hh ((hL l_residual (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_cutoff1_meanZero := h_cutoff1_meanZero I hz hx hh ((hL l_cutoff1_meanZero (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_cutoff1_source := h_cutoff1_source I hz hx hh ((hL l_cutoff1_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie1_source := h_twistie1_source I hz hx hh ((hL l_twistie1_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie3_flux_smooth := h_twistie3_flux_smooth I hz hx hh ((hL l_twistie3_flux_smooth (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie3_flux_periodic := h_twistie3_flux_periodic I hz hx hh ((hL
      l_twistie3_flux_periodic (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie3_source := h_twistie3_source I hz hx hh ((hL l_twistie3_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_group_meanZero := h_group_meanZero I hz hx hh ((hL l_group_meanZero (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie4_centered_source := h_twistie4_centered_source I hz hx hh ((hL
      l_twistie4_centered_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_twistie5_centered_source := h_twistie5_centered_source I hz hx hh ((hL
      l_twistie5_centered_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie3_centered_source := h_normie3_centered_source I hz hx hh ((hL
      l_normie3_centered_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie1_flux_smooth := h_normie1_flux_smooth I hz hx hh ((hL l_normie1_flux_smooth (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie1_flux_periodic := h_normie1_flux_periodic I hz hx hh ((hL l_normie1_flux_periodic
      (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie1_source := h_normie1_source I hz hx hh ((hL l_normie1_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie2_flux_smooth := h_normie2_flux_smooth I hz hx hh ((hL l_normie2_flux_smooth (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie2_flux_periodic := h_normie2_flux_periodic I hz hx hh ((hL l_normie2_flux_periodic
      (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_normie2_source := h_normie2_source I hz hx hh ((hL l_normie2_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_tiny_source := h_tiny_source I hz hx hh ((hL l_tiny_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_R46_flux_smooth := h_R46_flux_smooth I hz hx hh ((hL l_R46_flux_smooth (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_R46_flux_periodic := h_R46_flux_periodic I hz hx hh ((hL l_R46_flux_periodic (by
      simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_R46_source := h_R46_source I hz hx hh ((hL l_R46_source (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  have p_term_continuous := h_term_continuous I hz hx hh ((hL l_term_continuous (by simp)).trans hΛ)
    Φ hΦ κ hκ M hM hperm R hR θ₀ hθ hper hmean hana m hm hmM θprev T hθprev hT
  exact {
    residual := p_residual
    cutoff1_meanZero := p_cutoff1_meanZero
    cutoff1_source := p_cutoff1_source.trans (hscale (hC c_cutoff1_source (by simp)))
    twistie1_hminus_source := p_twistie1_source.trans (hscale (hC c_twistie1_source (by simp)))
    twistie3_flux_smooth := p_twistie3_flux_smooth
    twistie3_flux_periodic := p_twistie3_flux_periodic
    twistie3_source := p_twistie3_source.trans (hscale (hC c_twistie3_source (by simp)))
    group_meanZero := p_group_meanZero
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
    tiny_hminus_source := p_tiny_source.trans (hscale (hC c_tiny_source (by simp)))
    R46_flux_smooth := p_R46_flux_smooth
    R46_flux_periodic := p_R46_flux_periodic
    R46_source := p_R46_source.trans (hscale (hC c_R46_source (by simp)))
    term_continuous := p_term_continuous
  }

/-- The literal big-bound estimate statement from only its individual contract producers. -/
theorem bigbound_of_contracts (β C₀ : ℝ) (h : A7ContractProducers β C₀) :
    BigBoundStatement β C₀ :=
  Integration.bigbound_of_inputs β C₀ (bigbound_family_of_contracts β C₀ h)

end AVenhance.Infra.Section5.Contracts
