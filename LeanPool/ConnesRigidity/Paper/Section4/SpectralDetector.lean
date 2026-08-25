/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section4.FullDetectorMeasure

/-!
The paper-facing spectral-energy form of Zhou's five-detector estimate.
Paper: §4.
-/

namespace Connes
namespace PaperSpectralDetector

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualHaar
open PaperDualTopology
open PaperChartMeasure
open PaperChartDetectorMeasure
open PaperAChartDetectorMeasure
open PaperFullDetectorMeasure

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
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace

/- The binary coordinate value used by the spectral energy. Paper: §4.
-/
/--
The `detectorValue` construction used in the Connes rigidity formalization.
-/
def detectorValue (χ : CharacterSpace) (d : D) : k :=
  BinaryPontryaginDual.characterLinear (M := D) (Additive.toMul χ) d

/-- The squared displacement of a character at one kernel element. Its exact
detector-mass value is proved immediately below. Paper: §4.
-/
def spectralEnergy (μ : ProbabilityMeasure CharacterSpace) (d : D) : ℝ :=
  ∫ χ : CharacterSpace,
    ‖((ZMod.toCircle (detectorValue χ d) : Circle) : ℂ) - 1‖ ^ 2
      ∂(μ : Measure CharacterSpace)

/-- The mass of the trivial character in the additive dual model. Paper: §4.
-/
def trivialAtom (μ : ProbabilityMeasure CharacterSpace) : ℝ :=
  (μ : Measure CharacterSpace).real ({0} : Set CharacterSpace)

/- Every binary detector value is one of the two field elements. Paper: §4. -/
theorem detectorValue_eq_zero_or_one (χ : CharacterSpace) (d : D) :
    detectorValue χ d = 0 ∨ detectorValue χ d = 1 := by
  generalize hv : detectorValue χ d = v
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

/- The pointwise binary energy is the indicator of a nontrivial value. Paper: §4. -/
theorem detectorEnergy_eq_four_indicator (χ : CharacterSpace) (d : D) :
    ‖((ZMod.toCircle (detectorValue χ d) : Circle) : ℂ) - 1‖ ^ 2 =
      (4 : ℝ) * Set.indicator (linearDetector d) (fun _ => (1 : ℝ)) χ := by
  by_cases hχ : χ ∈ linearDetector d
  · have hv : detectorValue χ d = 1 := hχ
    rw [Set.indicator_of_mem hχ, hv]
    have hone : ZMod.toCircle (1 : ZMod 2) = (-1 : Circle) := by
      apply Circle.ext
      calc
        (ZMod.toCircle (1 : ZMod 2) : ℂ) =
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
              (1 : ℕ) / (2 : ℕ)) := by
          simpa using (ZMod.toCircle_natCast (N := 2) 1)
        _ = -1 := by
          rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 : ℕ) /
              (2 : ℕ) = (Real.pi : ℂ) * Complex.I by ring,
            Complex.exp_pi_mul_I]
        _ = ((-1 : Circle) : ℂ) := by rfl
    rw [hone]
    norm_num [Complex.normSq, Complex.sq_norm, Complex.normSq_apply]
  · have hv : detectorValue χ d = 0 := by
      rcases detectorValue_eq_zero_or_one χ d with hv | hv
      · exact hv
      · exact False.elim (hχ hv)
    rw [Set.indicator_of_notMem hχ, hv]
    have hzeroCircle : ZMod.toCircle (0 : ZMod 2) = (1 : Circle) :=
      by simp only [AddChar.map_zero_eq_one]
    rw [hzeroCircle]
    norm_num

/- Binary detector energy is exactly four times the detector mass. Paper: §4. -/
theorem spectralEnergy_eq_four_mul_measure
    (μ : ProbabilityMeasure CharacterSpace) (d : D) :
    spectralEnergy μ d = 4 * (μ : Measure CharacterSpace).real
      (linearDetector d) := by
  have hpoint (χ : CharacterSpace) :
      ‖((ZMod.toCircle (detectorValue χ d) : Circle) : ℂ) - 1‖ ^ 2 =
        (4 : ℝ) * Set.indicator (linearDetector d) (fun _ => (1 : ℝ)) χ := by
    exact detectorEnergy_eq_four_indicator χ d
  rw [show spectralEnergy μ d =
      ∫ χ : CharacterSpace,
        (4 : ℝ) * Set.indicator (linearDetector d)
          (fun _ => (1 : ℝ)) χ ∂(μ : Measure CharacterSpace) by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpoint]
  rw [integral_const_mul]
  rw [integral_indicator_const (e := (1 : ℝ))
    (measurableSet_linearDetector d)]
  norm_num

/- The full detector union is the complement of the trivial character. Paper: §4. -/
theorem fullNonzeroLocus_eq_zero_compl :
    fullNonzeroLocus = ({0} : Set CharacterSpace)ᶜ := by
  ext χ
  change PaperDualHaar.characterLinearEquiv χ ≠ 0 ↔ χ ≠ 0
  constructor
  · intro hχ hzero
    apply hχ
    rw [hzero, map_zero]
  · intro hχ hzero
    apply hχ
    have hzero' : PaperDualHaar.characterLinearEquiv χ =
        PaperDualHaar.characterLinearEquiv (0 : CharacterSpace) := by
      simpa using hzero
    exact PaperDualHaar.characterLinearEquiv.injective hzero'

/- The trivial singleton is measurable from the binary detector coordinates. Paper: §4. -/
theorem measurableSet_zero :
    MeasurableSet ({0} : Set CharacterSpace) := by
  have hzero : ({0} : Set CharacterSpace) =
      ⋂ d : D, (linearDetector d)ᶜ := by
    ext χ
    constructor
    · intro hχ
      subst χ
      refine Set.mem_iInter.mpr (fun d => ?_)
      have hz : detectorValue (0 : CharacterSpace) d = 0 := by
        change (PaperDualHaar.characterLinearEquiv
          (0 : CharacterSpace)) d = 0
        rw [map_zero]
        rfl
      change detectorValue (0 : CharacterSpace) d ≠ 1
      rw [hz]
      decide
    · intro hχ
      apply Set.mem_singleton_iff.mpr
      apply PaperDualHaar.characterLinearEquiv.injective
      apply LinearMap.ext
      intro d
      change detectorValue χ d = detectorValue (0 : CharacterSpace) d
      have hz : detectorValue (0 : CharacterSpace) d = 0 := by
        change (PaperDualHaar.characterLinearEquiv
          (0 : CharacterSpace)) d = 0
        rw [map_zero]
        rfl
      rcases detectorValue_eq_zero_or_one χ d with hzero | hone
      · simpa [hz] using hzero
      · exfalso
        exact (Set.mem_iInter.mp hχ d) hone
  rw [hzero]
  exact MeasurableSet.iInter (fun d => (measurableSet_linearDetector d).compl)

/- The nontrivial mass is one minus the trivial atom. Paper: §4. -/
theorem fullNonzeroLocus_measureReal_eq_one_sub_trivialAtom
    (μ : ProbabilityMeasure CharacterSpace) :
    (μ : Measure CharacterSpace).real fullNonzeroLocus =
      1 - trivialAtom μ := by
  rw [fullNonzeroLocus_eq_zero_compl, measureReal_compl
    measurableSet_zero, probReal_univ]
  rfl

/- Zhou's five-detector corollary becomes a finite spectral-energy inequality. Paper: §4. -/
theorem full_spectral_detection (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSL3SpectralMeasure μ) :
    (1 / 3 : ℝ) * (1 - trivialAtom μ) ≤
      (∑ v : OpenAIPort.SymplecticIndex,
        spectralEnergy μ (aCoordinateEmbedding v
          (PaperFiniteCharts.basisVector 0))) +
      spectralEnergy μ (0, PaperKernel.diagonal
        (PaperFiniteCharts.basisVector 0)) := by
  have hmeasure := fullNonzeroLocus_measureReal_le_five μ hinv
  rw [fullNonzeroLocus_measureReal_eq_one_sub_trivialAtom μ] at hmeasure
  simp only [aDetector, chartDetector] at hmeasure
  rw [Finset.sum_congr rfl (fun v _ =>
    spectralEnergy_eq_four_mul_measure μ
      (aCoordinateEmbedding v (PaperFiniteCharts.basisVector 0)))]
  rw [spectralEnergy_eq_four_mul_measure μ
    (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0))]
  have hsum4 :
      (∑ v : OpenAIPort.SymplecticIndex,
        4 * (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        4 * (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal
            (PaperFiniteCharts.basisVector 0))) =
      4 * ((∑ v : OpenAIPort.SymplecticIndex,
        (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal
            (PaperFiniteCharts.basisVector 0)))) := by
    rw [← Finset.mul_sum]
    ring
  calc
    (1 / 3 : ℝ) * (1 - trivialAtom μ) ≤
        (1 / 3 : ℝ) * (12 * ((∑ v : OpenAIPort.SymplecticIndex,
          (μ : Measure CharacterSpace).real
            (aDetector v (PaperFiniteCharts.basisVector 0))) +
          (μ : Measure CharacterSpace).real
            (chartDetector (PaperKernel.diagonal
              (PaperFiniteCharts.basisVector 0))))) := by
      exact mul_le_mul_of_nonneg_left hmeasure (by norm_num)
    _ = 4 * ((∑ v : OpenAIPort.SymplecticIndex,
        (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal
            (PaperFiniteCharts.basisVector 0)))) := by ring
    _ = (∑ v : OpenAIPort.SymplecticIndex,
        4 * (μ : Measure CharacterSpace).real
          (aDetector v (PaperFiniteCharts.basisVector 0))) +
        4 * (μ : Measure CharacterSpace).real
          (chartDetector (PaperKernel.diagonal
            (PaperFiniteCharts.basisVector 0))) := hsum4.symm

end
end PaperSpectralDetector
end Connes
