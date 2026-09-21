/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalRays

/-! # Recovering a bilinear metric from its radial and angular parts -/

@[expose] public noncomputable section

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Subtracting the radial projection produces an angular vector. -/
theorem radial_projection_remainder_orthogonal
    (g : E →L[ℝ] E →L[ℝ] ℝ) {u : E} (hu : g u u ≠ 0) (w : E) :
    g u (w - (g u w / g u u) • u) = 0 := by
  simp only [map_sub, map_smul, smul_eq_mul]
  field_simp
  ring

/-- A symmetric bilinear pairing is fixed by its radial Gauss identity
and its restriction to the angular subspace. -/
theorem bilinear_metric_of_radial_and_angular
    (g B : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ w v, g w v = g v w) (hB : ∀ w v, B w v = B v w)
    {u : E} (hu : g u u ≠ 0) {radial angular : ℝ}
    (hrad : ∀ w, B u w = radial * g u w)
    (hang : ∀ w v, g u w = 0 → g u v = 0 → B w v = angular * g w v)
    (w v : E) :
    B w v = angular * g w v +
      (radial - angular) * (g u w * g u v / g u u) := by
  let aw := g u w / g u u
  let av := g u v / g u u
  have he := hang (w - aw • u) (v - av • u)
    (radial_projection_remainder_orthogonal g hu w)
    (radial_projection_remainder_orthogonal g hu v)
  have hBu : B w u = radial * g u w := (hB w u).trans (hrad w)
  have hgu : g w u = g u w := hg w u
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at he
  rw [hBu, hrad v, hrad u, hgu] at he
  dsimp only [aw, av] at he
  field_simp [hu] at he ⊢
  nlinarith [he]

end LichnerowiczObata
