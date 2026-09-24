/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSourceMorrey

/-!
# Time growth of the divergence source on origin cells

The component source in `eq:pressure-gradient-morrey` inherits the product
Morrey bound of velocity and its spatial gradient. Its spatial slice norms
then satisfy the clipped time growth in `prop:bootstrap`. This estimate is
for the uncentered divergence source; localization and subtraction of the
velocity average require additional terms.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- Integrating the uncentered source over a clipped origin cell preserves
its Morrey exponent and the explicit constant `3 KU KD + KF`. -/
theorem origin_divergence_source_clipped_time_bound
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {f : ParabolicPoint → Vec3} {i : Fin 3}
    {τ q κ R : ℝ} {KU KD KF : ℝ≥0∞}
    (hτ : 25 / 3 ≤ τ) (hq : 5 / 2 < q) (hκ : 6 / 5 ≤ κ)
    (hκτ : κ ≤ (1 / τ + 8 / 25)⁻¹) (hκq : κ ≤ q)
    (hR : 0 < R) (hRle : R ≤ 1)
    (hU : ∀ j, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R).indicator (fun z => u z j)) ≤ KU)
    (hD : ∀ j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R).indicator (fun z => Du z i j)) ≤ KD)
    (hF : morreyNorm (6 / 5 : ℝ) q
      ((parabolicCylinder (0 : Vec3) 0 R).indicator (fun z => f z i)) ≤ KF)
    (hUm : ∀ j, AEMeasurable (fun z => u z j)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 R)))
    (hDm : ∀ j, AEMeasurable (fun z => Du z i j)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 R)))
    (hFm : AEMeasurable (fun z => f z i)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 R)))
    (x : Vec3) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0,
      eLpNorm (fun y => ∑ j, Du (y, s) i j * u (y, s) j - f (y, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R)) ^ (6 / 5 : ℝ)) ≤
      (3 * KU * KD + KF) ^ (6 / 5 : ℝ) *
        ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) / κ))) := by
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 R) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hsource : AEMeasurable (fun z => ∑ j, Du z i j * u z j - f z i)
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 R)) := by
    have hm := (((hDm 0).mul (hUm 0)).add
      (((hDm 1).mul (hUm 1)).add ((hDm 2).mul (hUm 2)))).sub hFm
    simpa [Fin.sum_univ_succ, Pi.add_def, Pi.sub_def] using hm
  have hbound := pressure_divergence_source_morrey_component_le
    (z₀ := ((0 : Vec3), 0)) hτ hq hκ hκτ hκq hR hRle (Subset.refl _)
    hU hD hF (fun j => (aemeasurable_indicator_iff hS).mpr (hUm j))
    (fun j => (aemeasurable_indicator_iff hS).mpr (hDm j))
    ((aemeasurable_indicator_iff hS).mpr hFm)
  exact origin_clipped_slice_norm_time_bound (by norm_num) hsource hbound x t hr

end CKN.Core.Step4
