/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell

/-! Spatial skew transfer on every actual terminal-time cell. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesTruncatedStream.truncated_stream_pairing_continuous
    {ψ u v : ℝ → Vec 2 → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => ψ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun z : AmnrSpace => vecDot (spaceGrad (u z.1) z.2)
      ((ψ z.1 z.2 • sigmaMat).mulVec (spaceGrad (v z.1) z.2)))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
    ContinuousOn (fun z : AmnrSpace => u z.1 z.2 * vecDot
      (sigmaMat.mulVec (spaceGrad (ψ z.1) z.2)) (spaceGrad (v z.1) z.2))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hgu := (iterate_word_gradient_smooth_up_to_initial hu []).continuousOn
  have hgv := (iterate_word_gradient_smooth_up_to_initial hv []).continuousOn
  have hgψ := (iterate_word_gradient_smooth_up_to_initial hψ []).continuousOn
  have hp := hψ.continuousOn
  have hc := hu.continuousOn
  constructor
  · unfold vecDot Matrix.mulVec dotProduct
    apply continuousOn_finsetSum Finset.univ
    intro i _
    exact ((continuous_apply i).comp_continuousOn hgu).mul
      (continuousOn_finsetSum Finset.univ (fun j _ =>
        (hp.mul_const (sigmaMat i j)).mul ((continuous_apply j).comp_continuousOn hgv)))
  · unfold vecDot Matrix.mulVec dotProduct
    apply hc.mul
    apply continuousOn_finsetSum Finset.univ
    intro i _
    exact (continuousOn_finsetSum Finset.univ (fun j _ =>
      continuousOn_const.mul ((continuous_apply j).comp_continuousOn hgψ))).mul
      ((continuous_apply i).comp_continuousOn hgv)

/-- Skew transfer for actual smooth fields on timeCube, with all natural
 integrability discharged. The stream jet is differentiated once more. -/
theorem iterate_truncated_stream_pairing_transfer
    {ψ u v : ℝ → Vec 2 → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => ψ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hψp : ∀ t, 0 < t → IsZ2Periodic (ψ t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t)) :
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
      ((ψ z.1 z.2 • sigmaMat).mulVec (spaceGrad (v z.1) z.2))) =
    ∫ z in iterateTruncatedCell s, u z.1 z.2 * vecDot
      (sigmaMat.mulVec (spaceGrad (ψ z.1) z.2)) (spaceGrad (v z.1) z.2) := by
  obtain ⟨hl, hr⟩ := IteratesTruncatedStream.truncated_stream_pairing_continuous hψ hu hv
  have hleft := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    _ (by simpa only [iterateTruncatedCell, Measure.volume_eq_prod] using
      iterate_truncated_cell_integrable hl hs)
  have hright := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    _ (by simpa only [iterateTruncatedCell, Measure.volume_eq_prod] using
      (iterate_timeCube_integrable_of_continuousOn hr).mono_set (iterateTruncatedCell_subset hs1))
  simp only [← Measure.volume_eq_prod] at hleft hright
  unfold iterateTruncatedCell
  rw [hleft, hright]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hs {f : ℝ → Vec 2 → ℝ}
      (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => f z.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ)) : ContDiff ℝ (⊤ : ℕ∞) (f t) :=
    hf.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
      (fun _ => ⟨ht.1.le, Set.mem_univ _⟩)
  exact iterate_stream_pairing_transfer (hs hψ) (hs hu) (hs hv)
    (hψp t ht.1) (hup t ht.1) (hvp t ht.1)

/-- The transferred actual pairing uses scalar and gradient energies only;
 the large first stream derivative is absent from this bound. -/
theorem iterate_truncated_stream_pairing_bound
    {ψ u v : ℝ → Vec 2 → ℝ} {H : ℝ} (hH : 0 < H)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => ψ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hψp : ∀ t, 0 < t → IsZ2Periodic (ψ t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    (hjet : ∀ t x j, |spaceGrad (ψ t) x j| ≤ H) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
      ((ψ z.1 z.2 • sigmaMat).mulVec (spaceGrad (v z.1) z.2))| ≤
      H * ((∫ z in iterateTruncatedCell s, u z.1 z.2 ^ 2) +
        (∫ z in iterateTruncatedCell s, vecNormSq (spaceGrad (v z.1) z.2))) := by
  rw [iterate_truncated_stream_pairing_transfer hψ hu hv hs hs1 hψp hup hvp]
  have hr := (IteratesTruncatedStream.truncated_stream_pairing_continuous hψ hu hv).2
  have hui := iterate_truncated_cell_integrable (hu.continuousOn.pow 2) hs
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 ^ 2) (iterateTruncatedCell s) at hui
  have hvi := (iterate_word_gradient_energy_integrable hv []).mono_set
      (iterateTruncatedCell_subset hs1)
  have ht := integral_mono (iterate_truncated_cell_integrable hr.abs hs)
    ((hui.add hvi).const_mul H) (fun z => by
      apply iterate_scalar_transport_abs_bound hH
      intro j
      fin_cases j
      · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hjet z.1 z.2 1
      · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hjet z.1 z.2 0)
  dsimp only [Pi.pow_apply, Pi.add_apply] at ht
  rw [integral_const_mul, integral_add hui hvi] at ht
  exact abs_integral_le_integral_abs.trans ht

end AVenhance.Infra.Section4
