/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedCutoff
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradient
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# The concrete causal differentiated cutoff source

The paper source `-2 ∂ⱼφ uᵢ`, truncated to the past, is measurable using
only local suitable-solution data. Its support and Morrey bound follow
from the cutoff support, its derivative bound, and initial velocity norms.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3


noncomputable section

namespace CKN.Core.Endgame

/-- A scalar component of the differentiated cutoff source in the past. -/
@[expose]
def causalDerivativeComponent (φ : Vec3 × ℝ → ℝ) (u : ParabolicPoint → Vec3)
    (j i : Fin 3) : ParabolicPoint → ℝ :=
  {z : ParabolicPoint | z.2 ≤ 0}.indicator
    (fun z => CKN.Core.Step4.localizedGradientSourceH φ u j z i)

private theorem spatialPartial_zero_on_past_outside_intermediate
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (j : Fin 3) (z : ParabolicPoint) (ht : z.2 ≤ 0)
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) : spatialPartial φ j z = 0 := by
  apply spatialPartial_zero_of_not_mem_tsupport_public hφ _ j
  intro hmem
  exact hz (hsupp (z.1, z.2) hmem ht)

/-- The causal differentiated source vanishes outside the intermediate
cylinder, including at future times. -/
theorem causalDerivativeComponent_zero_outside_intermediate
    {φ : Vec3 × ℝ → ℝ} {u : ParabolicPoint → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (j i : Fin 3) {z : ParabolicPoint}
    (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) :
    causalDerivativeComponent φ u j i z = 0 := by
  unfold causalDerivativeComponent
  by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
  · rw [indicator_of_mem ht]
    change (-2 * spatialPartial φ j z) * u z i = 0
    rw [spatialPartial_zero_on_past_outside_intermediate hφ hsupp j z ht hz,
      mul_zero, zero_mul]
  · exact indicator_of_notMem ht _

/-- The causal differentiated source is globally measurable once the
indicated velocity component is measurable. No global velocity assumption
is required. -/
theorem causalDerivativeComponent_aemeasurable
    {φ : Vec3 × ℝ → ℝ} {u : ParabolicPoint → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (j i : Fin 3)
    (hu : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) volume) :
    AEMeasurable (causalDerivativeComponent φ u j i) volume := by
  have hpartial : Continuous (fun z : ParabolicPoint => spatialPartial φ j z) :=
    (spatialPartial_contDiff hφ j).continuous.comp continuous_parabolicPoint_to_prod
  have hPast : MeasurableSet {z : ParabolicPoint | z.2 ≤ 0} :=
    (isClosed_le continuous_snd_parabolicPoint continuous_const).measurableSet
  have heq : causalDerivativeComponent φ u j i =
      {z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => (-2 * spatialPartial φ j z) *
          (parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun w => u w i) z) := by
    funext z
    unfold causalDerivativeComponent
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8)
      · rw [indicator_of_mem hz]
        rfl
      · rw [indicator_of_notMem hz, mul_zero]
        change (-2 * spatialPartial φ j z) * u z i = 0
        rw [spatialPartial_zero_on_past_outside_intermediate hφ hsupp j z ht hz,
          mul_zero, zero_mul]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]
  rw [heq]
  exact ((aemeasurable_const.mul hpartial.aemeasurable).mul hu).indicator hPast

/-- The actual differentiated cutoff source inherits the initial velocity
Morrey bound, with all coefficients fixed before the solution. -/
theorem causal_derivative_source_of_suitableWeakSolution
    (C : ℝ) (KU : ℝ≥0∞) (hC : 0 ≤ C)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {φ : Vec3 × ℝ → ℝ}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8))
    (hder : ∀ z : Vec3 × ℝ, z.2 ≤ 0 → ∀ j, |spatialPartial φ j z| ≤ C)
    (hN : ∀ i : Fin 3, morreyNorm 3 (25 / 3)
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator (fun z => u z i)) ≤ KU) :
    ∀ j i : Fin 3, AEMeasurable (causalDerivativeComponent φ u j i) volume ∧
      morreyNorm (6 / 5) (25 / 3) (causalDerivativeComponent φ u j i) ≤
        ENNReal.ofReal (2 * C) *
          (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) := by
  obtain ⟨Ω', J, hbox, _hJ, hunit⟩ := exists_localBox_around_closed_unit hsol.1 hsol.2.1 hdom
  have hubox := (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hSunit : parabolicCylinder (0 : Vec3) 0 (5 / 8) ⊆
      closure (parabolicCylinder (0 : Vec3) 0 1) :=
    (parabolicCylinder_mono (by norm_num) (by norm_num)).trans subset_closure
  have huS : AEStronglyMeasurable u
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 (5 / 8))) :=
    hubox.mono_measure (Measure.restrict_mono (hSunit.trans hunit) le_rfl)
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 (5 / 8)) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hui : ∀ i : Fin 3,
      AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
        (fun z => u z i)) volume := by
    intro i
    exact (aemeasurable_indicator_iff hS).mpr
      ((continuous_apply i).comp_aestronglyMeasurable huS).aemeasurable
  intro j i
  refine ⟨causalDerivativeComponent_aemeasurable hφ.1 hsupp j i (hui i), ?_⟩
  exact past_derivative_source_morrey_le C KU hC φ u j i
    (fun z ht => hder (z.1, z.2) ht j)
    (spatialPartial_zero_on_past_outside_intermediate hφ.1 hsupp j) (hui i) (hN i)

end CKN.Core.Endgame
