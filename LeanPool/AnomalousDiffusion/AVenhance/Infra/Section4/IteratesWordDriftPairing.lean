/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxPairing

/-! Exact forcing and drift pairings for the all-order differentiated energy. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Smooth fluxes have smooth divergence. -/
theorem iterate_divergence_smooth {H : Vec 2 → Vec 2}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) : ContDiff ℝ (⊤ : ℕ∞) (vecDiv H) := by
  unfold vecDiv
  exact ContDiff.sum (fun i _ => contDiff_pi.mp
    (iterate_gradient_smooth (contDiff_pi.mp hH i)) i)

/-- Every smooth divergence pairing on the cell is integrable. -/
theorem iterate_divergence_product_integrable {u : Vec 2 → ℝ} {H : Vec 2 → Vec 2}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    IntegrableOn (fun x => u x * vecDiv H x) unitCube :=
  iterate_continuous_cell_integrable (hu.continuous.mul (iterate_divergence_smooth hH).continuous)

/-- The full differentiated forcing pairing consists of the preceding
coefficient flux and the current stream error. The principal skew flux
cancels, and every spatial integrability premise is discharged. -/
theorem iterate_word_forcing_drift_pairing
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hAp : IsZ2Periodic A) (hvp : IsZ2Periodic v)
    {t : ℝ} (ht : 0 < t) (hup : IsZ2Periodic (u t)) (w : List (Fin 2)) :
    (∫ x in unitCube, iterateSpatialWord w (u t) x *
      (iterateSpatialWord w (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x -
        iterateWordMaterialError (fun z : AmnrSpace => streamVel φ z.1 z.2) w
          (fun z => u z.1 z.2) (t, x))) =
      -(∫ x in unitCube, vecDot (spaceGrad (iterateSpatialWord w (u t)) x)
        (iterateWordFlux A v w x)) -
      (∫ x in unitCube, vecDot (spaceGrad (iterateSpatialWord w (u t)) x)
        (iterateWordFlux (fun y => φ t y • sigmaMat) (u t) w x)) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  have hs : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    hu.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)
  have hφs : ContDiff ℝ (⊤ : ℕ∞) (φ t) := hφ.1.comp hmap
  have hφp : IsZ2Periodic (φ t) := by
    intro k x
    simpa using hφ.2 0 k t x
  have hB := iterate_stream_matrix_smooth hφs
  have hBp : IsZ2Periodic (fun y => φ t y • sigmaMat) := by
    intro k x
    dsimp only
    rw [hφp k x]
  have hw := iterateSpatialWord_smooth hs w
  have hwp := iterateSpatialWord_periodic hs hup w
  have hFA := iterateWordFlux_smooth hA hv w
  have hFB := iterateWordFlux_smooth hB hs w
  have hFC := iterate_matrix_gradient_smooth hB hw
  have hiA := iterate_divergence_product_integrable hw hFA
  have hiB := iterate_divergence_product_integrable hw hFB
  have hiC := iterate_divergence_product_integrable hw hFC
  have heq : (fun x => iterateSpatialWord w (u t) x *
      (iterateSpatialWord w (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x -
        iterateWordMaterialError (fun z : AmnrSpace => streamVel φ z.1 z.2) w
          (fun z => u z.1 z.2) (t, x))) =
      fun x => (iterateSpatialWord w (u t) x * vecDiv (iterateWordFlux A v w) x +
        iterateSpatialWord w (u t) x *
          vecDiv (iterateWordFlux (fun y => φ t y • sigmaMat) (u t) w) x) -
        iterateSpatialWord w (u t) x *
          vecDiv (fun y => (φ t y • sigmaMat).mulVec
            (spaceGrad (iterateSpatialWord w (u t)) y)) x := by
    funext x
    rw [iterateSpatialWord_matrix_forcing_divergence hA hv,
      iterateWordMaterialError_stream_flux hφ hu ht]
    ring
  have hiAB : IntegrableOn (fun x =>
      iterateSpatialWord w (u t) x * vecDiv (iterateWordFlux A v w) x +
      iterateSpatialWord w (u t) x *
        vecDiv (iterateWordFlux (fun y => φ t y • sigmaMat) (u t) w) x) unitCube :=
    hiA.add hiB
  rw [heq, integral_sub hiAB hiC, integral_add hiA hiB]
  rw [iterate_divergence_pairing hw hwp hFA (iterateWordFlux_periodic hA hv hAp hvp w),
    iterate_divergence_pairing hw hwp hFB (iterateWordFlux_periodic hB hs hBp hup w),
    iterate_divergence_pairing hw hwp hFC (iterate_matrix_gradient_periodic hw hBp hwp)]
  simp only [iterate_stream_principal_pairing_zero, integral_zero, neg_zero, sub_zero]
  ring

end AVenhance.Infra.Section4
