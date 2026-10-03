/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedCutoff
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable

/-!
# Almost-everywhere measurability of one-sided localized fields

The local measurability clauses of a suitable weak solution extend globally
after multiplication by the indicator of the intermediate cylinder. A
coefficient supported on a measurable set likewise localizes an a.e.
measurable scalar field without requiring a global representative.
-/

public section

open Set MeasureTheory
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Endgame

/-- A globally a.e. measurable coefficient supported on a measurable set
turns a scalar field measurable only on that set into a globally a.e.
measurable product. -/
theorem aemeasurable_mul_of_restrict_of_zero_outside
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {a g : ParabolicPoint → ℝ}
    (ha : AEMeasurable a volume) (hg : AEMeasurable g (volume.restrict S))
    (hsupp : ∀ z ∉ S, a z = 0) :
    AEMeasurable (fun z => a z * g z) volume := by
  have hgi : AEMeasurable (S.indicator g) volume := (aemeasurable_indicator_iff hS).mpr hg
  have heq : (fun z => a z * g z) = fun z => a z * S.indicator g z := by
    funext z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
    · rw [hsupp z hz, zero_mul, zero_mul]
  rw [heq]
  exact ha.mul hgi

/-- Every component of the velocity, weak gradient, pressure, and force,
indicated to the intermediate one-sided cylinder, is globally a.e.
measurable. All measurability is supplied by the local solution clauses. -/
theorem one_sided_indicated_components_aemeasurable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hunit : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I) :
    (∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) volume) ∧
    (∀ i j, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => Du z i j)) volume) ∧
    AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator p) volume ∧
    ∀ i, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => f z i)) volume := by
  obtain ⟨Ω', J, hbox, _hJopen, hunitbox⟩ :=
    exists_localBox_around_closed_unit hsol.1 hsol.2.1 hunit
  have hsub : parabolicCylinder (0 : Vec3) 0 (5 / 8) ⊆ spaceTimeSet Ω' J :=
    (parabolicCylinder_mono (by norm_num : (0 : ℝ) ≤ 5 / 8)
      (by norm_num : (5 / 8 : ℝ) ≤ 1)).trans (subset_closure.trans hunitbox)
  have hmeasure := Measure.restrict_mono (μ := volume) hsub le_rfl
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hu := hdata.1.aemeasurable.mono_measure hmeasure
  have hDu := hdata.2.1.aemeasurable.mono_measure hmeasure
  have hp := hdata.2.2.1.aemeasurable.mono_measure hmeasure
  have hf := hdata.2.2.2.1.aemeasurable.mono_measure hmeasure
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (5 / 8)) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  refine ⟨?_, ?_, (aemeasurable_indicator_iff hS).mpr hp, ?_⟩
  · intro i
    exact (aemeasurable_indicator_iff hS).mpr (aemeasurable_pi_iff.mp hu i)
  · intro i j
    exact (aemeasurable_indicator_iff hS).mpr
      (aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hDu i) j)
  · intro i
    exact (aemeasurable_indicator_iff hS).mpr (aemeasurable_pi_iff.mp hf i)

end CKN.Core.Endgame
