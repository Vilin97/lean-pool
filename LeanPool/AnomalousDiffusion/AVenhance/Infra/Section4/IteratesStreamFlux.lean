/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDriftExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingGradient

/-! Exact stream-function divergence flux used in the differentiated energy equation. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The stream coefficient is spatially smooth whenever the actual stream is. -/
theorem iterate_stream_matrix_smooth {φ : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x • sigmaMat) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact hφ.mul contDiff_const

/-- The sign of sigma gives divergence of φσ∇u equal to minus transport. -/
theorem iterate_stream_flux_divergence {φ u : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec 2) :
    vecDiv (fun y => (φ y • sigmaMat).mulVec (spaceGrad u y)) x =
      -vecDot (sigmaMat.mulVec (spaceGrad φ x)) (spaceGrad u x) := by
  rw [iterate_matrix_forcing_formula (iterate_stream_matrix_smooth hφ) hu]
  have hderiv (i j k : Fin 2) :
      spaceGrad (fun y => φ y * sigmaMat i j) x k =
        spaceGrad φ x k * sigmaMat i j := by
    unfold spaceGrad
    rw [fderiv_mul_const (hφ.differentiable (by simp) x)]
    simp only [smul_apply, smul_eq_mul]
    ring
  change (∑ i : Fin 2, ∑ j : Fin 2,
    (spaceGrad (fun y => φ y * sigmaMat i j) x i * spaceGrad u x j +
      φ x * sigmaMat i j * spaceGrad (fun y => spaceGrad u y j) x i)) = _
  simp only [hderiv]
  simp only [sigmaMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, add_zero, mul_neg,
        mul_one, neg_mul,
    zero_add, vecDot, Matrix.mulVec, dotProduct, one_mul, neg_add_rev, neg_neg]
  have hc := iterate_coordinate_derivatives_commute hu (0 : Fin 2) (1 : Fin 2) x
  rw [hc]
  ring

/-- Negation commutes with any spatial word. -/
theorem iterateSpatialWord_neg (f : Vec 2 → ℝ) (w : List (Fin 2)) :
    iterateSpatialWord w (-f) = -iterateSpatialWord w f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    unfold spaceGrad
    rw [fderiv_neg]
    rfl

/-- The expanded stream flux is the negative differentiated transport. -/
theorem iterate_stream_word_flux_divergence {φ u : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (w : List (Fin 2)) (x : Vec 2) :
    vecDiv (iterateWordFlux (fun y => φ y • sigmaMat) u w) x =
      -iterateSpatialWord w (fun y => vecDot
        (sigmaMat.mulVec (spaceGrad φ y)) (spaceGrad u y)) x := by
  have heq : vecDiv (fun y => (φ y • sigmaMat).mulVec (spaceGrad u y)) =
      -(fun y => vecDot (sigmaMat.mulVec (spaceGrad φ y)) (spaceGrad u y)) := by
    funext y
    exact iterate_stream_flux_divergence hφ hu y
  rw [← iterateSpatialWord_matrix_forcing_divergence (iterate_stream_matrix_smooth hφ) hu,
    heq, iterateSpatialWord_neg]
  rfl

/-- Material commutators for the stream velocity are exactly the
stream flux derivatives minus the principal skew flux. -/
theorem iterateWordMaterialError_stream_flux
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) (x : Vec 2) :
    iterateWordMaterialError (fun z : AmnrSpace => streamVel φ z.1 z.2) w
      (fun z => u z.1 z.2) (t, x) =
      -vecDiv (iterateWordFlux (fun y => φ t y • sigmaMat) (u t) w) x +
        vecDiv (fun y => (φ t y • sigmaMat).mulVec
          (spaceGrad (iterateSpatialWord w (u t)) y)) x := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  have hs : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    hu.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)
  have hφs : ContDiff ℝ (⊤ : ℕ∞) (φ t) := hφ.1.comp hmap
  have hb := (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth
  have he := iterateWordMaterialError_transport hb.contDiffOn hu ht w x
  have hbs : ContDiff ℝ (⊤ : ℕ∞) (streamVel φ t) := hb.comp hmap
  have hp := iterateSpatialWord_transport hbs hs w x
  rw [← hp] at he
  have hflux := iterate_stream_word_flux_divergence hφs hs w x
  have hprincipal := iterate_stream_flux_divergence hφs (iterateSpatialWord_smooth hs w) x
  change vecDiv (iterateWordFlux (fun y => φ t y • sigmaMat) (u t) w) x =
    -iterateSpatialWord w (fun y => vecDot (streamVel φ t y) (spaceGrad (u t) y)) x at hflux
  change vecDiv (fun y => (φ t y • sigmaMat).mulVec
    (spaceGrad (iterateSpatialWord w (u t)) y)) x =
    -vecDot (streamVel φ t x) (spaceGrad (iterateSpatialWord w (u t)) x) at hprincipal
  linarith only [he, hflux, hprincipal]

end AVenhance.Infra.Section4
