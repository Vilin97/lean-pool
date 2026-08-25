/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section4.AChartDetectorMeasure

/-!
Full §4 detector union for Zhou's compact dual. Paper: §4.
-/

namespace Connes
namespace PaperFullDetectorMeasure

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualTopology
open PaperDualHaar
open BinaryPontryaginDual
open PaperFiniteCharts
open PaperChartDetector
open PaperChartMeasure
open PaperChartDetectorMeasure
open PaperAChartDetectorMeasure

noncomputable section

/- The concrete field, kernel, module, tensor carrier, dual, and index types. Paper: §4.
-/
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := PaperKernel.C
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualTopology.CharacterSpace
/--
The `SymplecticIndex` construction used in the Connes rigidity formalization.
-/
abbrev SymplecticIndex := OpenAIPort.SymplecticIndex

/-- The A-coordinate value agrees with Zhou's transported dual coordinates. Paper: §3. -/
theorem aChartLinear_eq_coordinate (χ : CharacterSpace)
    (v : SymplecticIndex) (a : A) :
    aChartLinear χ v a =
      (PaperDualHaar.characterCoordinatesEquiv χ).1 a v := by
  simpa [aChartLinear, aCoordinateEmbedding] using
    (PaperDualTopology.character_coordinate_eval χ a v).symm

/- The nonzero locus of the full binary character functional. Paper: §4.
-/
/--
The `fullNonzeroLocus` construction used in the Connes rigidity formalization.
-/
def fullNonzeroLocus : Set CharacterSpace :=
  {χ : CharacterSpace |
    PaperDualHaar.characterLinearEquiv χ ≠ 0}

/-- A nonzero full character has a nonzero coordinate pair. Paper: §3 and §4. -/
theorem characterCoordinates_ne_zero_of_fullNonzero
    {χ : CharacterSpace} (hχ : χ ∈ fullNonzeroLocus) :
    PaperDualHaar.characterCoordinatesEquiv χ ≠ 0 := by
  intro hzero
  apply hχ
  have h' := congrArg
    (fun p : PaperFactorIsomorphism.DualCoordinates =>
      PaperDualCoordinates.dualEquiv.symm p) hzero
  simpa [PaperDualHaar.characterCoordinatesEquiv] using h'

/- A nonzero full character is detected by an A or C coordinate. Paper: §4. -/
theorem fullNonzeroLocus_subset_coordinate_loci
    (χ : CharacterSpace) (hχ : χ ∈ fullNonzeroLocus) :
    (∃ v : SymplecticIndex, χ ∈ aNonzeroLocus v) ∨
      χ ∈ PaperChartDetectorMeasure.chartNonzeroLocus := by
  have hcoords := characterCoordinates_ne_zero_of_fullNonzero hχ
  by_cases hz : (PaperDualHaar.characterCoordinatesEquiv χ).1 = 0
  · right
    intro hzero
    apply hcoords
    apply Prod.ext
    · exact hz
    · exact hzero
  · left
    obtain ⟨a, ha⟩ : ∃ a : A,
        (PaperDualHaar.characterCoordinatesEquiv χ).1 a ≠ 0 := by
      by_contra h
      apply hz
      apply LinearMap.ext
      intro a
      exact Classical.byContradiction (fun hne => h ⟨a, hne⟩)
    obtain ⟨v, hv⟩ : ∃ v : SymplecticIndex,
        (PaperDualHaar.characterCoordinatesEquiv χ).1 a v ≠ 0 := by
      by_contra h
      apply ha
      funext v
      exact Classical.byContradiction (fun hne => h ⟨v, hne⟩)
    refine ⟨v, ?_⟩
    intro hzero
    apply hv
    have h := congrArg (fun f : A →ₗ[k] k => f a) hzero
    exact (aChartLinear_eq_coordinate χ v a) ▸ h

/- The finite five-detector union used by Zhou's corollary. Paper: §4.
-/
/--
The `fullDetectorUnion` construction used in the Connes rigidity formalization.
-/
def fullDetectorUnion : Set CharacterSpace :=
  (⋃ v : SymplecticIndex, aNonzeroLocus v) ∪
    PaperChartDetectorMeasure.chartNonzeroLocus

/- The full nonzero locus is contained in the five-detector union. Paper: §4. -/
theorem fullNonzeroLocus_subset_fullDetectorUnion :
    fullNonzeroLocus ⊆ fullDetectorUnion := by
  intro χ hχ
  rcases fullNonzeroLocus_subset_coordinate_loci χ hχ with hA | hC
  · rcases hA with ⟨v, hv⟩
    exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨v, hv⟩)
  · exact Set.mem_union_right _ hC

/- The five-detector union obeys the summed twelve-detector bound. Paper: §4. -/
theorem fullDetectorUnion_measureReal_le_five
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ) :
    (μ : Measure CharacterSpace).real fullDetectorUnion ≤
      12 * ((∑ v : SymplecticIndex,
        (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal (basisVector 0)))) := by
  have hA := measureReal_iUnion_fintype_le
    (μ := (μ : Measure CharacterSpace))
    (fun v : SymplecticIndex => aNonzeroLocus v)
  have hC := chartNonzeroLocus_measureReal_le_twelve μ hinv
  have hsum : (∑ v : SymplecticIndex,
      (μ : Measure CharacterSpace).real (aNonzeroLocus v)) ≤
      ∑ v : SymplecticIndex, 12 *
        (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0)) := by
    exact Finset.sum_le_sum (fun v _ =>
      aNonzeroLocus_measureReal_le_twelve μ hinv v)
  calc
    (μ : Measure CharacterSpace).real fullDetectorUnion ≤
        (μ : Measure CharacterSpace).real
          (⋃ v : SymplecticIndex, aNonzeroLocus v) +
          (μ : Measure CharacterSpace).real
            PaperChartDetectorMeasure.chartNonzeroLocus := by
      exact measureReal_union_le _ _
    _ ≤ (∑ v : SymplecticIndex,
        (μ : Measure CharacterSpace).real (aNonzeroLocus v)) +
        (μ : Measure CharacterSpace).real
          PaperChartDetectorMeasure.chartNonzeroLocus := by
      exact add_le_add hA le_rfl
    _ ≤ (∑ v : SymplecticIndex, 12 *
        (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        12 * (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal (basisVector 0))) := by
      exact add_le_add hsum hC
    _ = 12 * ((∑ v : SymplecticIndex,
        (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal (basisVector 0)))) := by
      rw [← Finset.mul_sum]
      ring

/- The full nonzero locus obeys Zhou's five-detector measure bound. Paper: §4. -/
theorem fullNonzeroLocus_measureReal_le_five
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ) :
    (μ : Measure CharacterSpace).real fullNonzeroLocus ≤
      12 * ((∑ v : SymplecticIndex,
        (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal (basisVector 0)))) := by
  exact (measureReal_mono (fullNonzeroLocus_subset_fullDetectorUnion)).trans
    (fullDetectorUnion_measureReal_le_five μ hinv)

end
end PaperFullDetectorMeasure
end Connes
