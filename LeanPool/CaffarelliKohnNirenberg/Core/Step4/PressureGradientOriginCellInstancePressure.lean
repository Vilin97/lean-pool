/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSlice

/-!
# Pressure slices on the whole solution interval

The local pressure integrability of a suitable weak solution supplies the
pressure premise of spatial weak-gradient gluing in `prop:bootstrap`.
A compact exhaustion of the time interval makes the exceptional set uniform
on the entire interval.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

open OriginInstance

/-- Pressure is spatially integrable on the origin ball at almost every time
of the whole solution interval, as needed in `prop:bootstrap`. -/
theorem pressure_slice_integrable_ae_on_origin_ball
    {Ω : Set Vec3} {I : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) :
    ∀ᵐ t ∂(volume.restrict I),
      IntegrableOn (fun x => p (x, t)) (vec3Ball (0 : Vec3) R) volume := by
  obtain ⟨J, _, hJord, hJcpt, hJI, hJunion, _⟩ :=
    exists_compact_ordConnected_exhaustion hsol.2.1 hsol.2.2.1
  obtain ⟨hΩ, _⟩ := originUnitBall_subset_of_dom hdom
  rw [← hJunion, ae_restrict_iUnion_iff]
  intro n
  have hbox := originLocalBox_of_time hR hRone hΩ (hJord n) (hJcpt n) (hJI n)
  have hpint := pressure_integrable_on_of_suitable_local_box hsol hbox subset_rfl
  have hpProd : Integrable p
      ((volume.restrict (vec3Ball (0 : Vec3) R)).prod (volume.restrict (J n))) := by
    rw [Measure.prod_restrict]
    exact hpint
  exact hpProd.prod_left_ae

/-- The locally integrable pressure slices required by the spatial gluing
step of `prop:bootstrap` follow from suitability alone. -/
theorem pressure_slice_locallyIntegrable_ae_on_origin_ball
    {Ω : Set Vec3} {I : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) :
    ∀ᵐ t ∂(volume.restrict I),
      LocallyIntegrableOn (fun x => p (x, t)) (vec3Ball (0 : Vec3) R) volume := by
  filter_upwards [pressure_slice_integrable_ae_on_origin_ball hsol hdom hR hRone]
    with t ht
  exact ht.locallyIntegrableOn

end CKN.Core.Step4
