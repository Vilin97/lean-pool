/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Joint Lower Semicontinuity of the Integral Pairing

  Phase 5, File 2 (BLUEPRINT §4F).
  J1 `continuous_probabilityMeasure_map_prodMk`: the pairing
  (x, γ) ↦ γ.map (Prod.mk x) is jointly continuous from H × P(W) to
  P(H × W) in the weak topologies.
  J2 `lowerSemicontinuous_lintegral_prodMk`: consequently, for jointly
  lower semicontinuous f : H × W → ℝ≥0∞, the integral
  (x, γ) ↦ ∫⁻ z, f (x, z) ∂γ is jointly lower semicontinuous
  (the lsc integral functional on P(H × W) after the continuous pairing).

  J1 is sequential (both sides metrizable), via the converse portmanteau
  criterion: for open G and r < γ ((Prod.mk x)⁻¹' G), inner regularity
  gives a compact K ⊆ (Prod.mk x)⁻¹' G with r < γ K; the tube lemma
  around {x} ×ˢ K produces open V ∋ x and O ⊇ K with V ×ˢ O ⊆ G;
  eventually xₙ ∈ V, so (Prod.mk xₙ)⁻¹' G ⊇ O, and
  liminf γₙ O ≥ γ O ≥ γ K > r by the open portmanteau applied to γₙ → γ.
  No tightness and no equicontinuity are needed.
-/
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.LintegralLsc

/-! ## J1: joint continuity of the pairing -/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

variable {H W : Type*}
  [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]



/-- **Joint continuity of the pairing** `(x, γ) ↦ γ.map (Prod.mk x)` from
    `H × P(W)` to `P(H × W)` (weak topologies, Polish spaces). -/
theorem continuous_probabilityMeasure_map_prodMk :
    Continuous (fun p : H × ProbabilityMeasure W =>
      ProbabilityMeasure.map p.2
        (Prod.mk p.1)) := by
  refine SeqContinuous.continuous fun ps p hps => ?_
  have hx : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hps
  have hγ : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hps
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf' fun G hG => ?_
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_prodMk_left hG.measurableSet]
  refine le_of_forall_lt fun r hr => ?_
  -- inner regularity: a compact K inside the section of G over p.1
  obtain ⟨K, hKsub, hKc, hK⟩ :=
    (hG.measurableSet.preimage measurable_prodMk_left).exists_lt_isCompact_of_ne_top
      (measure_ne_top _ _) hr
  -- tube lemma around {p.1} ×ˢ K
  have hxK : {p.1} ×ˢ K ⊆ G := by
    rintro ⟨a, z⟩ ⟨ha, hz⟩
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact hKsub hz
  obtain ⟨V, O, hVopen, hOopen, hxV, hKO, hVO⟩ :=
    generalized_tube_lemma isCompact_singleton hKc hG hxK
  -- eventually the moving section contains O
  have hev : ∀ᶠ n in atTop,
      ((ps n).2 : Measure W) O
        ≤ (((ps n).2 : Measure W).map (Prod.mk (ps n).1)) G := by
    filter_upwards [hx.eventually
      (hVopen.mem_nhds (Set.singleton_subset_iff.mp hxV))] with n hn
    rw [Measure.map_apply measurable_prodMk_left hG.measurableSet]
    exact measure_mono fun z hz => hVO ⟨hn, hz⟩
  calc r < (p.2 : Measure W) K := hK
    _ ≤ (p.2 : Measure W) O := measure_mono hKO
    _ ≤ atTop.liminf (fun n => ((ps n).2 : Measure W) O) :=
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto hγ hOopen
    _ ≤ atTop.liminf
          (fun n => (((ps n).2 : Measure W).map (Prod.mk (ps n).1)) G) :=
        liminf_le_liminf hev

/-! ## J2: joint lower semicontinuity of the integral pairing -/

/-- **Joint lower semicontinuity of the integral pairing.** For jointly
    lower semicontinuous `f : H × W → ℝ≥0∞`, the map
    `(x, γ) ↦ ∫⁻ z, f (x, z) ∂γ` is jointly lower semicontinuous on
    `H × P(W)`: it is the lsc integral functional on `P(H × W)`
    (`lowerSemicontinuous_lintegral_probabilityMeasure`) composed with
    the continuous pairing (J1). -/
theorem lowerSemicontinuous_lintegral_prodMk
    {f : H × W → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun p : H × ProbabilityMeasure W =>
      ∫⁻ z, f (p.1, z) ∂(p.2 : Measure W)) := by
  have hkey : (fun p : H × ProbabilityMeasure W =>
        ∫⁻ z, f (p.1, z) ∂(p.2 : Measure W))
      = (fun γ : ProbabilityMeasure (H × W) =>
          ∫⁻ q, f q ∂(γ : Measure (H × W)))
        ∘ (fun p : H × ProbabilityMeasure W =>
            ProbabilityMeasure.map p.2
              (Prod.mk p.1)) := by
    funext p
    simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
    rw [lintegral_map hf.measurable measurable_prodMk_left]
  rw [hkey]
  exact (lowerSemicontinuous_lintegral_probabilityMeasure hf).comp
    continuous_probabilityMeasure_map_prodMk

end
