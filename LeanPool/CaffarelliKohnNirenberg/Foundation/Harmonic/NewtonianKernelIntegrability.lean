/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation

/-!
# Newtonian Kernel Integrability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure CKN.Foundation.Parabolic

namespace CKN.Foundation.Heat

/-- The Newtonian kernel `newtonianKernel z = 1/(4π|z|₂)` is locally integrable
    with respect to Lebesgue measure on `ℝ³`. -/
theorem locallyIntegrable_newtonianKernel :
    LocallyIntegrable newtonianKernel volume := by
  exact _root_.CKN.Foundation.Heat.newtonianKernel_locallyIntegrable

/-- For any `x : ℝ³`, the translated kernel `y ↦ newtonianKernel (x - y)` is also
    locally integrable with respect to Lebesgue measure. -/
theorem locallyIntegrable_newtonianKernel_sub (x : Vec3) :
    LocallyIntegrable (fun y : Vec3 => newtonianKernel (x - y)) volume := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hmap : Measure.map (fun y : Vec3 => x - y) volume = volume := hmp.map_eq
  have hmap' : LocallyIntegrable newtonianKernel
      (Measure.map (Homeomorph.subLeft x) volume) := by
    change LocallyIntegrable newtonianKernel
      (Measure.map (fun y : Vec3 => x - y) volume)
    rw [hmap]
    exact locallyIntegrable_newtonianKernel
  have hcomp := (locallyIntegrable_map_homeomorph (Homeomorph.subLeft x)
    (f := newtonianKernel)).1 hmap'
  change LocallyIntegrable (fun y : Vec3 => newtonianKernel (x - y)) volume at hcomp
  exact hcomp

end CKN.Foundation.Heat
