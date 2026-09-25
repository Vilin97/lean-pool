/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSourceMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseBudget
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginCost
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSidedCell
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierRestriction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Mathlib.Analysis.Real.Pi.Bounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantHolder

/-! # Numerical inputs for the origin pressure-gradient estimate

The divergence-source norm and its clipped time-power coefficient, and the
fixed-ball pressure and force time envelopes, are read off the data size and
the velocity budgets. These are the numerical bounds a selected field is
compared against.
-/

@[expose] public section

section

/-!
# Time growth of the divergence source on origin cells

The component source in `eq:pressure-gradient-morrey` inherits the product
Morrey bound of velocity and its spatial gradient. Its spatial slice norms
then satisfy the clipped time growth in `prop:bootstrap`. This estimate is
for the uncentered divergence source; localization and subtraction of the
velocity average require additional terms.
-/

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
end

end

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

private theorem origin_source_kappa_lower {q τ : ℝ}
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) :
    6 / 5 ≤ min ((1 / τ + 8 / 25)⁻¹) q := by
  have hτpos : 0 < τ := by linarith only [hτ]
  have hs : 0 < 1 / τ + 8 / 25 := by positivity
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 25 / 3) hτ
  have hu : 1 / τ + 8 / 25 ≤ 5 / 6 := by
    norm_num at hi
    rw [one_div]
    linarith only [hi]
  have hlo := (one_div_le_one_div (by norm_num : (0 : ℝ) < 5 / 6) hs).mpr hu
  apply le_min
  · norm_num only [one_div_div] at hlo
    simpa only [one_div] using hlo
  · linarith only [hq]

/-- The suitable-solution data give the uncentered divergence-source norm and
its clipped time-power bound. The time coefficient is the `6/5` power of
the component norm bound. All numerical data precede the solution. -/
theorem origin_divergence_source_numerical_bounds_of_sws
    (q τ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hR : 0 < R₁) (hR₁₀ : R₁ ≤ R₀) (hR₀le : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD)
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
      (fun z => vec3EuclideanNorm
        ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
          (fun w => fun i => ∑ j, Du w i j * u w j - f w i) z)) ≤
        3 * (3 * KU * KD + forceSourceMorreyBound q ε) ∧
    ∀ (i : Fin 3) (x : Vec3) (t : ℝ) (r : ℝ), 0 < r →
      (∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0,
        eLpNorm (fun y => ∑ j, Du (y, s) i j * u (y, s) j - f (y, s) i)
          (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
        (3 * KU * KD + forceSourceMorreyBound q ε) ^ (6 / 5 : ℝ) *
          ENNReal.ofReal (r ^ (5 * (1 - (6 / 5 : ℝ) /
            min ((1 / τ + 8 / 25)⁻¹) q))) := by
  have hRle : R₁ ≤ 1 := hR₁₀.trans hR₀le
  have hinner := parabolicCylinder_mono (x := (0 : Vec3)) (t := 0) hR.le hR₁₀
  have hU₁ : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => u z i)) ≤ KU := fun i =>
    (morreyNorm_indicator_mono_set (by norm_num) hinner _).trans (hU i)
  have hD₁ : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₁).indicator (fun z => Du z i j)) ≤ KD := fun i j =>
    (morreyNorm_indicator_mono_set (by norm_num) hinner _).trans (hD i j)
  let S := parabolicCylinder (0 : Vec3) 0 R₁
  have hS : MeasurableSet S := (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hsub : S ⊆ parabolicCylinder (0 : Vec3) 0 1 := parabolicCylinder_mono hR.le hRle
  obtain ⟨B, J, hbox, hQbox⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1
    (by norm_num : (0 : ℝ) < 1) hdom
  have hd := hsol.2.2.2.2.2.1 B J hbox
  have hm := Measure.restrict_mono_set volume (hsub.trans hQbox)
  have hu : ∀ i, AEMeasurable (fun z => u z i) (volume.restrict S) := fun i =>
    ((measurable_pi_apply i).comp_aemeasurable hd.1.aemeasurable).mono_measure hm
  have hdu : ∀ i j, AEMeasurable (fun z => Du z i j) (volume.restrict S) := fun i j =>
    ((measurable_pi_apply j).comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable hd.2.1.aemeasurable)).mono_measure hm
  have hf : ∀ i, AEMeasurable (fun z => f z i) (volume.restrict S) := fun i =>
    ((measurable_pi_apply i).comp_aemeasurable hd.2.2.2.1.aemeasurable).mono_measure hm
  have hforce : ∀ i, morreyNorm (6 / 5 : ℝ) q (S.indicator (fun z => f z i)) ≤
      forceSourceMorreyBound q ε := by
    intro i
    apply force_source_morrey_le_of_small_data q ε hq
      ((aemeasurable_indicator_iff hS).mpr (hf i)) hsize
    · apply Eventually.of_forall
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz]
        exact Real.abs_le_sqrt (Finset.single_le_sum
          (fun j _ => sq_nonneg (f z j)) (Finset.mem_univ i))
      · rw [Set.indicator_of_notMem hz, abs_zero]
        exact vec3EuclideanNorm_nonneg _
    · intro z hz
      exact Set.indicator_of_notMem (fun hs => hz (hsub hs)) _
  have hκ := origin_source_kappa_lower hq hτ
  constructor
  · exact pressure_divergence_source_morrey_le (z₀ := ((0 : Vec3), 0))
      hτ hq hκ (min_le_left _ _) (min_le_right _ _) hR hRle (Subset.refl S)
      hU₁ hD₁ hforce (fun i => (aemeasurable_indicator_iff hS).mpr (hu i))
      (fun i j => (aemeasurable_indicator_iff hS).mpr (hdu i j))
      (fun i => (aemeasurable_indicator_iff hS).mpr (hf i))
  · intro i x t r hr
    exact origin_divergence_source_clipped_time_bound hτ hq hκ
      (min_le_left _ _) (min_le_right _ _) hR hRle hU₁ (hD₁ i) (hforce i)
      hu (hdu i) (hf i) x t hr



end CKN.Core.Step4
