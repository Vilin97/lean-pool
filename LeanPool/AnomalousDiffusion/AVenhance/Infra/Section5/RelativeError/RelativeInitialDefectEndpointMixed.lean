/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectEndpoint
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter

/-! Positive-time spatial-word adapter for the actual endpoint gradient.
The terminal correction needs one spatial letter, not a material trace. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set AVenhance AVenhance.Infra.Section4
namespace AVenhance.Infra.Section5.RelativeError

/-- Scalar one-letter word bounds give the actual four-index spatial-gradient
norm and its coordinate measurability on a positive-time source measure. -/
theorem relative_initial_endpoint_gradient_of_words {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n r : ℕ)
    {μ : Measure AmnrSpace}
    (hμ : μ ≪ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))))
    (hreg : ∀ i j k : Fin 2, ContDiffOn ℝ 1
      (fun z : AmnrSpace => I.Amnr hΦ m κ n T r z.1 z.2 i j k)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))))
    {B : ℝ}
    (hword : ∀ i j k p : Fin 2,
      eLpNorm (amnrWord
        (fun z => streamVel (Φ (m - 1)) z.1 z.2) [some p]
        (fun z => I.Amnr hΦ m κ n T r z.1 z.2 i j k)) 2 μ ≤ ENNReal.ofReal B) :
    (∀ i j k p : Fin 2, AEStronglyMeasurable
      (fun z => amnrSpatialGradientTensor I hΦ m κ T n r z i j k p) μ) ∧
    eLpNorm (amnrSpatialGradientTensor I hΦ m κ T n r) 2 μ ≤
      ENNReal.ofReal (16 * B) := by
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ univ
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have heq (i j k p : Fin 2) :
      (fun z => amnrSpatialGradientTensor I hΦ m κ T n r z i j k p) =ᵐ[μ]
        amnrWord (fun z => streamVel (Φ (m - 1)) z.1 z.2) [some p]
          (fun z => I.Amnr hΦ m κ n T r z.1 z.2 i j k) := by
    filter_upwards [hμ.ae_le (ae_restrict_mem hU.measurableSet)] with z hz
    have hh := amnrWord_spatial_slice_on_vertical_domain_finite hU (hreg i j k)
      (fun y => streamVel (Φ (m - 1)) y.1 y.2) [p] (by norm_num)
      z.1 (fun _ => ⟨hz.1, mem_univ _⟩) z.2
    exact hh.symm
  have hm (i j k p : Fin 2) : AEStronglyMeasurable
      (fun z => amnrSpatialGradientTensor I hΦ m κ T n r z i j k p) μ := by
    have hw := amnrWord_contDiffOn hU
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : AmnrSpace => (0 : Vec 2)) U)
      (hreg i j k) [some p] (n := 0) (by norm_num)
    have hmeas := (hw.continuousOn.aestronglyMeasurable hU.measurableSet
      (μ := volume)).mono_ac hμ
    have hind := amnrWord_spatial_independent (fun _ => (0 : Vec 2))
      (fun z => streamVel (Φ (m - 1)) z.1 z.2) [p]
      (fun z => I.Amnr hΦ m κ n T r z.1 z.2 i j k)
    rw [show [p].map some = [some p] from rfl] at hind
    rw [hind] at hmeas
    exact hmeas.congr (heq i j k p).symm
  have hc (i j k p : Fin 2) :
      eLpNorm (fun z => amnrSpatialGradientTensor I hΦ m κ T n r z i j k p) 2 μ ≤
        ENNReal.ofReal B := by
    rw [eLpNorm_congr_ae (heq i j k p)]
    exact hword i j k p
  have hAll : AEStronglyMeasurable (amnrSpatialGradientTensor I hΦ m κ T n r) μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact aemeasurable_pi_iff.mpr fun i => aemeasurable_pi_iff.mpr fun j =>
      aemeasurable_pi_iff.mpr fun k => aemeasurable_pi_iff.mpr fun p =>
        (hm i j k p).aemeasurable
  have h1 (i j k : Fin 2) :
      eLpNorm (fun z => amnrSpatialGradientTensor I hΦ m κ T n r z i j k) 2 μ ≤
        ENNReal.ofReal (2 * B) := by
    apply amnr_pi_L2_le_card
      ((continuous_apply k).comp_aestronglyMeasurable
        ((continuous_apply j).comp_aestronglyMeasurable
          ((continuous_apply i).comp_aestronglyMeasurable hAll)))
      (hc i j k)
  have h2 (i j : Fin 2) :
      eLpNorm (fun z => amnrSpatialGradientTensor I hΦ m κ T n r z i j) 2 μ ≤
        ENNReal.ofReal (4 * B) := by
    convert amnr_pi_L2_le_card
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply i).comp_aestronglyMeasurable hAll)) (h1 i j) using 1
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    congr 1
    ring
  have h3 (i : Fin 2) :
      eLpNorm (fun z => amnrSpatialGradientTensor I hΦ m κ T n r z i) 2 μ ≤
        ENNReal.ofReal (8 * B) := by
    convert amnr_pi_L2_le_card
      ((continuous_apply i).comp_aestronglyMeasurable hAll) (h2 i) using 1
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    congr 1
    ring
  refine ⟨hm, ?_⟩
  convert amnr_pi_L2_le_card hAll h3 using 1
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  congr 1
  ring

end AVenhance.Infra.Section5.RelativeError
