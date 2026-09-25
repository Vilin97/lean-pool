/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic

/-! # Peel Fubini -/

@[expose] public section

namespace Homogenization

open MeasureTheory Homogenization

/-!
# Coordinate-peeling Fubini on `Vec d`

Reusable slicing lemma: an integral over `Vec (n+1) = Fin (n+1) → ℝ` against
Lebesgue `volume` equals the iterated integral obtained by peeling off a chosen
coordinate `i` as the inner one-dimensional line integral (the remaining
coordinates outer).  The line through `z : Vec n` in direction `i` is
`t ↦ i.insertNth t z`.

This is the tool into which the single-face reflection transport feeds its
per-line one-dimensional integration by parts.
-/

noncomputable section

/-- **Coordinate-peeling Fubini.**
For `f : Vec (n+1) → ℝ` integrable against `volume` and a coordinate `i`, the
integral equals the iterated integral with the `i`-th coordinate innermost:
`∫ x, f x = ∫ z, ∫ t, f (i.insertNth t z)`. -/
theorem integral_peel_coord {n : ℕ} (i : Fin (n + 1))
    {f : Vec (n + 1) → ℝ}
    (hf : Integrable f (volume : Measure (Vec (n + 1)))) :
    (∫ x, f x ∂(volume : Measure (Vec (n + 1))))
      = ∫ z : Vec n, ∫ t : ℝ, f (i.insertNth t z)
          ∂(volume : Measure ℝ) ∂(volume : Measure (Vec n)) := by
  classical
  set μ : ∀ _ : Fin (n + 1), Measure ℝ := fun _ => volume with hμ
  have hmp := measurePreserving_piFinSuccAbove μ i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have hvol : (volume : Measure (Vec (n + 1))) = Measure.pi μ := volume_pi
  -- integrability of the change-of-variables integrand
  have hf' : Integrable (fun p => f (e.symm p))
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) := by
    have hpi : Integrable f (Measure.pi μ) := by rw [← hvol]; exact hf
    exact hmp.symm.integrable_comp_of_integrable hpi
  rw [hvol, ← hmp.symm.integral_comp' f, integral_prod_symm _ hf']
  rfl

end

end Homogenization
