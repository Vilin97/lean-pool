/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Tactic

/-! # Differentiation of a moving metric pairing -/

@[expose] public noncomputable section

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- All three derivative terms of a varying bilinear pairing. -/
theorem hasDerivAt_moving_metric_pairing
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {g' : E →L[ℝ] E →L[ℝ] ℝ}
    {u w : ℝ → E} {u' w' : E} {t : ℝ}
    (hg : HasDerivAt g g' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => g s (u s) (w s))
      (g' (u t) (w t) + g t u' (w t) + g t (u t) w') t := by
  convert (hg.clm_apply hu).clm_apply hw using 1 <;> rfl

/-- For a metric connection, its two coefficient terms combine with the
ordinary derivatives to give the two covariant variation terms. -/
theorem hasDerivAt_metric_pairing_connection
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {g' : E →L[ℝ] E →L[ℝ] ℝ}
    {u w : ℝ → E} {u' w' : E} {t : ℝ} (A : E →L[ℝ] E)
    (hg : HasDerivAt g g' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hcompat : g' (u t) (w t) = g t (A (u t)) (w t) + g t (u t) (A (w t))) :
    HasDerivAt (fun s => g s (u s) (w s))
      (g t (u' + A (u t)) (w t) + g t (u t) (w' + A (w t))) t := by
  convert hasDerivAt_moving_metric_pairing hg hu hw using 1
  simp only [map_add, add_apply, hcompat]
  ring

/-- Equal scalar covariant evolution of two variations gives the scalar
metric evolution equation. The geometric identities must be supplied by
the actual metric connection and shape operator. -/
theorem hasDerivAt_metric_pairing_scaling
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {g' : E →L[ℝ] E →L[ℝ] ℝ}
    {u w : ℝ → E} {u' w' : E} {t c : ℝ} (A : E →L[ℝ] E)
    (hg : HasDerivAt g g' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hcompat : g' (u t) (w t) = g t (A (u t)) (w t) + g t (u t) (A (w t)))
    (hshapeU : u' + A (u t) = c • u t) (hshapeW : w' + A (w t) = c • w t) :
    HasDerivAt (fun s => g s (u s) (w s)) (2 * c * g t (u t) (w t)) t := by
  convert hasDerivAt_metric_pairing_connection A hg hu hw hcompat using 1
  rw [hshapeU, hshapeW]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- The derivative of the quadratic form of a symmetric continuous
bilinear metric is twice its pairing with the base vector. -/
theorem hasFDerivAt_symmetric_metric_quadratic
    (g : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u w, g u w = g w u) (v : E) :
    HasFDerivAt (fun w => g w w) ((2 : ℝ) • g v) v := by
  have hd := (g.hasFDerivAt (x := v)).clm_apply (hasFDerivAt_id v)
  convert hd using 1 <;> try rfl
  ext w
  simp only [smul_apply, add_apply, id_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hsym w v]
  ring

/-- Longitudinal terms in the variation equation do not change an angular
metric pairing. Orthogonality removes them explicitly. -/
theorem hasDerivAt_metric_pairing_scaling_longitudinal
    {g : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {g' : E →L[ℝ] E →L[ℝ] ℝ}
    {u w : ℝ → E} {u' w' N : E} {t c d e : ℝ} (A : E →L[ℝ] E)
    (hg : HasDerivAt g g' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hcompat : g' (u t) (w t) = g t (A (u t)) (w t) + g t (u t) (A (w t)))
    (hshapeU : u' + A (u t) = c • u t + d • N)
    (hshapeW : w' + A (w t) = c • w t + e • N)
    (hNu : g t (u t) N = 0) (hNw : g t N (w t) = 0) :
    HasDerivAt (fun s => g s (u s) (w s)) (2 * c * g t (u t) (w t)) t := by
  have hd := hasDerivAt_metric_pairing_connection A hg hu hw hcompat
  rw [hshapeU, hshapeW] at hd
  convert hd using 1
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, hNu, hNw,
    mul_zero, add_zero]
  ring

end LichnerowiczObata
