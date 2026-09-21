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

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarHomeomorph
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Smooth ambient extensions of inverse round polar coordinates -/

@[expose] public noncomputable section
open scoped ContDiff
namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inverse polar formulas, defined in the ambient space. Their values
away from the regular sphere are only used as a local smooth extension. -/
def roundInverseCoordinates (R : ℝ) (p x : E) : E × ℝ :=
  ((Real.sin (Real.arccos (inner ℝ p x / R)))⁻¹ •
    (R⁻¹ • x - (inner ℝ p x / R) • p),
    R * Real.arccos (inner ℝ p x / R))

/-- The explicit ambient inverse agrees with the actual polar inverse on
every point of the punctured sphere. -/
theorem roundInverseCoordinates_eq_inverse {R : ℝ} (hR : 0 < R)
    (p : E) (hp : ‖p‖ = 1) (x : RoundPuncturedSphere R p) :
    roundInverseCoordinates R p (x.1 : E) =
      ((((roundPolarEquiv hR p hp).symm x).1 : E),
        (((roundPolarEquiv hR p hp).symm x).2 : ℝ)) := by
  apply Prod.ext
  · exact (roundPolarEquiv_inverse_angular hR p hp x).symm
  · exact (roundPolarEquiv_inverse_radius hR p hp x).symm

/-- No singular arccosine height occurs on the punctured sphere. -/
theorem roundPuncturedSphere_height_ne {R : ℝ} (hR : 0 < R)
    (p : E) (hp : ‖p‖ = 1) (x : RoundPuncturedSphere R p) :
    inner ℝ p (x.1 : E) / R ≠ -1 ∧ inner ℝ p (x.1 : E) / R ≠ 1 := by
  have hs := roundPolar_inverse_sine_ne_zero hR p hp x
  constructor
  · intro he
    apply hs
    simp [he]
  · intro he
    apply hs
    simp [he]

/-- At a regular sphere point, both inverse coordinates extend smoothly to
an ambient neighborhood, rather than merely continuously on the sphere. -/
theorem contDiffAt_roundInverseCoordinates {R : ℝ} (hR : 0 < R)
    (p : E) (hp : ‖p‖ = 1) (x : RoundPuncturedSphere R p) :
    ContDiffAt ℝ ∞ (roundInverseCoordinates R p) (x.1 : E) := by
  have hh : ContDiffAt ℝ ∞ (fun y : E => inner ℝ p y / R) (x.1 : E) := by
    exact (contDiffAt_const.inner ℝ contDiffAt_id).div_const R
  have hn := roundPuncturedSphere_height_ne hR p hp x
  have ha := (Real.contDiffAt_arccos hn.1 hn.2).comp (x.1 : E) hh
  have hs := ha.sin.inv (roundPolar_inverse_sine_ne_zero hR p hp x)
  have hv : ContDiffAt ℝ ∞ (fun y : E => R⁻¹ • y - (inner ℝ p y / R) • p)
      (x.1 : E) := by fun_prop
  exact (hs.smul hv).prodMk (contDiffAt_const.mul ha)

end LichnerowiczObata
