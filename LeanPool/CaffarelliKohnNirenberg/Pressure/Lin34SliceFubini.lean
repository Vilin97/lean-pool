/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-!
# Lin34 Slice Fubini

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-!
# Fubini steps for the cylinder quantities of `prop:lin34`

The cylinder quantities `D(z,r)` and `Ĉ(z,ρ)` of `eq:Chat` in `paper/ckn.tex`
are defined as integrals over a parabolic cylinder, while the monotonicity and
scaling statements of `prop:lin34` are phrased in terms of the spatial slice
quantities obtained by fixing the time variable.  This file records the two
Fubini facts that pass between the two points of view.

The cylinder `parabolicCylinder x t r` is the product `vec3Ball x r ×ˢ Ioc (t - r ^ 2) t`
and the volume on `ParabolicPoint` is the product of the spatial and time
volumes, so an integrability hypothesis over the cylinder is an integrability
hypothesis for the product measure.  Applying the Fubini API with the time
variable as the outer variable then yields the integrability of the time slices.
-/

/-- The cylinder integrability hypothesis of `prop:lin34`, written as
integrability for the product of the restricted spatial and time measures. -/
private lemma integrableOn_cylinder_prod {g : ParabolicPoint → ℝ} {x : Vec3}
    {t r : ℝ}
    (hg : IntegrableOn g (parabolicCylinder x t r) volume) :
    Integrable g ((volume.restrict (vec3Ball x r)).prod
      (volume.restrict (Ioc (t - r ^ 2) t))) := by
  rw [Measure.prod_restrict]
  change IntegrableOn g (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t)
    ((volume : Measure Vec3).prod (volume : Measure ℝ))
  exact hg

/-- Fubini step of `prop:lin34`: if a function is integrable on the parabolic
cylinder `Q_r(z)`, then the spatial slice integrals integrate in time against the
time interval of the cylinder. -/
theorem lin34_slice_integrable_of_cylinder
    {g : ParabolicPoint → ℝ} {x : Vec3} {t r : ℝ}
    (hg : IntegrableOn g (parabolicCylinder x t r) volume) :
    Integrable (fun s : ℝ => ∫ y in vec3Ball x r, g (y, s))
      (volume.restrict (Ioc (t - r ^ 2) t)) := by
  exact (integrableOn_cylinder_prod hg).integral_prod_right

/-- Fubini step of `prop:lin34`: if a function is integrable on the parabolic
cylinder `Q_r(z)`, then for almost every time in the time interval of the
cylinder its spatial slice is integrable on the spatial ball. -/
theorem lin34_slice_integrableOn_ball_ae
    {g : ParabolicPoint → ℝ} {x : Vec3} {t r : ℝ}
    (hg : IntegrableOn g (parabolicCylinder x t r) volume) :
    ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t),
      IntegrableOn (fun y : Vec3 => g (y, s)) (vec3Ball x r) volume := by
  filter_upwards [integrableOn_cylinder_prod hg |>.prod_left_ae] with s hs
  exact hs

/-- `prop:lin34`: on a cylinder whose closure lies in the carrier of a suitable
weak solution, the pressure raised to the exponent `3 / 2` of `eq:Chat` is
integrable. -/
theorem lin34_integrableOn_pressure_pow_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 r) volume := by
  have hfin := sws_pressure_integral_lt_top hsol hr hsub
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hr hsub
  obtain ⟨-, -, hpmeas, -, -, -, -, -, -⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hmeas : AEStronglyMeasurable
      (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    have hcont : Continuous (fun a : ℝ => |a| ^ (3 / 2 : ℝ)) := by
      exact (Real.continuous_rpow_const (by norm_num)).comp continuous_abs
    exact hcont.comp_aestronglyMeasurable
      (hpmeas.mono_measure (Measure.restrict_mono hcyl le_rfl))
  have hfin' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) ≠ ⊤ := by
    have hfin'' := ne_of_lt hfin
    convert hfin'' using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Filter.Eventually.of_forall fun w => Real.rpow_nonneg
      (abs_nonneg _) _)).mp hfin'

end CKN
