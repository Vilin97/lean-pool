/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSlice

/-!
# The slice bound of one field at every cell scale

A cell estimate for the parabolic Morrey class needs the radius factor
`r ^ (5 * (1 - P / κ))`, which a slice bound at one fixed scale cannot produce:
one ball's slice bound, integrated in time, carries no decay in the cell
radius.  What does produce it is the slice estimate applied at each cell's own
radius.

The statement below performs that transfer for one fixed space-time field.  The
field is tied to the pressure by being a weak spatial derivative on a common
open carrier at almost every time of the cell's window; the cell datum is a
slice bound for *some* weak spatial derivative on the cell's own ball.  Almost
everywhere uniqueness of weak partial derivatives then transports the cell's
bound to the one field.  Its conclusion is exactly the slice hypothesis of the
time integration that turns slice bounds into the cell power integral.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The slice bound proved at a cell's own radius, transported to a fixed
space-time field that is a weak spatial derivative of the pressure on a carrier
containing that cell's ball. -/
theorem ae_eLpNorm_slice_le_of_cell_scale_slice_bounds
    {B : Set Vec3} {i : Fin 3}
    {p : ParabolicPoint → ℝ} {Dp : ParabolicPoint → Vec3}
    {x : Vec3} {t r : ℝ} (hball : vec3Ball x r ⊆ B)
    {M : ℝ → ℝ≥0∞}
    (hfield : ∀ᵐ s ∂(volume.restrict (Ioc (t - r ^ 2) t)),
      LocallyIntegrableOn (fun y => Dp (y, s) i) B volume ∧
        HasWeakPartialDerivOn B i (fun y => p (y, s)) (fun y => Dp (y, s) i))
    (hcell : ∀ᵐ s ∂(volume.restrict (Ioc (t - r ^ 2) t)), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball x r) volume ∧
        HasWeakPartialDerivOn (vec3Ball x r) i (fun y => p (y, s)) g ∧
        eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x r)) ≤ M s) :
    ∀ᵐ s ∂(volume.restrict (Ioc (t - r ^ 2) t)),
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r)) ≤ M s := by
  filter_upwards [hfield, hcell] with s hs hg
  obtain ⟨hloc, hweak⟩ := hs
  obtain ⟨g, hgloc, hgweak, hgbound⟩ := hg
  exact eLpNorm_le_of_hasWeakPartialDerivOn (isOpen_vec3Ball x r) hball hloc hgloc
    hweak hgweak hgbound

end CKN.Core.Step4
