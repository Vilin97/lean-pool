/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section4.ChartDetector
import LeanPool.ConnesRigidity.Paper.Section4.ChartOrbits
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.NormalizedHaar
import LeanPool.ConnesRigidity.Paper.Section3.DualTopology
import LeanPool.ConnesRigidity.Paper.Section3.DualShearMeasure
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SpectralCriterion
import LeanPool.ConnesRigidity.Paper.Section3.DualAutomorphism

/-!
Invariant dual-measure transport for Zhou's finite chart detector. Paper: §4.
-/

namespace Connes
namespace PaperChartMeasure

open MeasureTheory
open Construction
open Construction.PaperKernel
open BinaryPontryaginDual
open PaperDualHaar
open PaperDualTopology

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualTopology.CharacterSpace

/--
The `dualCharacterEquivOfAction` construction used in the Connes rigidity formalization.
-/
def dualCharacterEquivOfAction {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D)) (h : H) :
    CharacterSpace ≃+ CharacterSpace :=
  PaperDualAutomorphism.dualCharacterEquiv
    (Multiplicative.toAdd (action h))

/- The paper-facing action is kept on the additive character model. The
existing generic criterion uses the raw Pontryagin-dual model, so this
definition records the same transport without pretending those two types are
definitionally equal. Paper: §4.
-/
/--
The `paperDualCharacterAction` construction used in the Connes rigidity formalization.
-/
def paperDualCharacterAction {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D)) (h : H) :
    CharacterSpace → CharacterSpace := dualCharacterEquivOfAction action h

/-- The additive character action is continuous. Paper: §4. -/
theorem continuous_paperDualCharacterAction {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D)) (h : H) :
    Continuous (paperDualCharacterAction action h) :=
  PaperDualAutomorphism.dualCharacterEquiv_continuous
    (Multiplicative.toAdd (action h))

/-- The additive character action is measurable. Paper: §4. -/
theorem measurable_paperDualCharacterAction {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D)) (h : H) :
    Measurable (paperDualCharacterAction action h) :=
  (continuous_paperDualCharacterAction action h).measurable

/-- Invariant probability measure for the additive character action, whose
measurability is recorded above. Paper: §4.
-/
def IsInvariantPaperSpectralMeasure {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D))
    (μ : ProbabilityMeasure CharacterSpace) : Prop :=
  ∀ h : H,
    (μ : Measure CharacterSpace).map (paperDualCharacterAction action h) = μ

/--
The `linearDetector` construction used in the Connes rigidity formalization.
-/
def linearDetector (d : D) : Set CharacterSpace :=
  {χ | BinaryPontryaginDual.characterLinear (M := D)
      (Additive.toMul χ) d = 1}

theorem measurableSet_linearDetector (d : D) :
    MeasurableSet (linearDetector d) := by
  exact (PaperDualTopology.continuous_characterLinear_eval d).measurable
    (MeasurableSet.singleton 1)

theorem paperDualCharacterAction_preimage_linearDetector
    {H : CountableDiscreteGroup} (action : H →* Multiplicative (AddAut D))
    (h : H) (d e : D)
    (he : Multiplicative.toAdd (action h⁻¹) e = d) :
    paperDualCharacterAction action h ⁻¹' linearDetector e = linearDetector d := by
  ext χ
  change BinaryPontryaginDual.characterLinear (M := D)
      (Additive.toMul (paperDualCharacterAction action h χ)) e = 1 ↔
    BinaryPontryaginDual.characterLinear (M := D)
      (Additive.toMul χ) d = 1
  have heval :
      BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul (paperDualCharacterAction action h χ)) e =
        BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul χ) d := by
    apply ZMod.injective_toCircle
    rw [BinaryPontryaginDual.characterLinear_circle,
      BinaryPontryaginDual.characterLinear_circle]
    change (Additive.toMul
        (PaperDualAutomorphism.dualCharacterEquiv
          (Multiplicative.toAdd (action h)) χ))
          (Multiplicative.ofAdd e) =
      (Additive.toMul χ) (Multiplicative.ofAdd d)
    rw [PaperDualAutomorphism.dualCharacterEquiv_apply]
    have haction :
        (Multiplicative.toAdd (action h)).symm e =
          Multiplicative.toAdd (action h⁻¹) e := by
      simp
    rw [haction, he]
  rw [heval]

theorem detector_measure_eq_of_invariant
    {H : CountableDiscreteGroup} (action : H →* Multiplicative (AddAut D))
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSpectralMeasure action μ)
    (h : H) (d e : D)
    (he : Multiplicative.toAdd (action h⁻¹) e = d) :
    (μ : Measure CharacterSpace) (linearDetector e) =
      (μ : Measure CharacterSpace) (linearDetector d) := by
  calc
    (μ : Measure CharacterSpace) (linearDetector e) =
        (Measure.map (paperDualCharacterAction action h) μ)
          (linearDetector e) := by rw [hinv h]
    _ = (μ : Measure CharacterSpace)
        (paperDualCharacterAction action h ⁻¹' linearDetector e) := by
      rw [Measure.map_apply (measurable_paperDualCharacterAction action h)
        (measurableSet_linearDetector e)]
    _ = (μ : Measure CharacterSpace) (linearDetector d) := by
      rw [paperDualCharacterAction_preimage_linearDetector action h d e he]

end
end PaperChartMeasure
end Connes
