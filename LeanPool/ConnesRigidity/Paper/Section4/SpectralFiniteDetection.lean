/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section4.SpectralDetectorBridge

/-!
Finite detector sets for the raw Zhou split extensions. Paper: §4.
-/

namespace Connes
namespace PaperSpectralFiniteDetection

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualTopology
open PaperAChartDetectorMeasure
open PaperSpectralDetectorBridge
open PaperPropertyT
open PaperSpectralPropertyT

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D
/--
The `VStar` construction used in the Connes rigidity formalization.
-/
abbrev VStar := PaperKernel.VStar
/--
The `SymplecticIndex` construction used in the Connes rigidity formalization.
-/
abbrev SymplecticIndex := OpenAIPort.SymplecticIndex

/- The coefficient functional separates the standard A chart vector. Paper: §4.
-/
/--
The `aZeroCoeff` construction used in the Connes rigidity formalization.
-/
def aZeroCoeff : A →ₗ[k] k where
  toFun a := (a 0).constantCoeff
  map_add' a b := by simp
  map_smul' r a := by simp [smul_eq_mul]

/-- The coefficient functional takes the base chart vector to one. Paper: §4. -/
lemma aZeroCoeff_basisVector_zero :
    aZeroCoeff (PaperFiniteCharts.basisVector 0) = 1 := by
  simp [aZeroCoeff, PaperFiniteCharts.basisVector]

/- The four A-coordinate detector elements are pairwise distinct. Paper: §4. -/
theorem aCoordinateEmbedding_injective :
    Function.Injective
      (fun v : SymplecticIndex =>
        PaperAChartDetectorMeasure.aCoordinateEmbedding v
          (PaperFiniteCharts.basisVector 0)) := by
  intro v w h
  have hfirst := congrArg Prod.fst h
  change (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
      (LinearMap.proj v : VStar)) =
    (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
      (LinearMap.proj w : VStar)) at hfirst
  by_contra hvw
  have hzero :
      PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
        ((LinearMap.proj v : VStar) + (LinearMap.proj w : VStar)) = 0 := by
    calc
      PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
          ((LinearMap.proj v : VStar) + (LinearMap.proj w : VStar)) =
        (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj v : VStar)) +
          (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj w : VStar)) := by
              rw [TensorProduct.tmul_add]
      _ = (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj w : VStar)) +
          (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj w : VStar)) := by rw [hfirst]
      _ = 0 := by
        calc
          (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
              (LinearMap.proj w : VStar)) +
              (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
                (LinearMap.proj w : VStar)) =
            (1 : k) • (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
              (LinearMap.proj w : VStar)) +
              (1 : k) • (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
                (LinearMap.proj w : VStar)) := by simp
          _ = ((1 : k) + 1) •
              (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
                (LinearMap.proj w : VStar)) := by
            rw [add_smul]
          _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  have hcontract := congrArg
    (fun z : PaperKernel.AVStar =>
      aZeroCoeff (PaperKernel.contractStar
        (LinearMap.applyₗ (R := k) (Pi.single v 1)) z)) hzero
  rw [PaperKernel.contractStar_tmul, map_zero, map_smul,
    aZeroCoeff_basisVector_zero] at hcontract
  have hone : (1 : k) = 0 := by
    simp [smul_eq_mul, hvw] at hcontract
  exact one_ne_zero hone

/- The finite A-detector embedding used by the §4 criterion. Paper: §4.
-/
/--
The `aDetectorEmbedding` construction used in the Connes rigidity formalization.
-/
def aDetectorEmbedding : SymplecticIndex ↪ D where
  toFun v := PaperAChartDetectorMeasure.aCoordinateEmbedding v
    (PaperFiniteCharts.basisVector 0)
  inj' := aCoordinateEmbedding_injective

/-- The C-coordinate detector singled out by the paper's five-detector bound. Paper: §4.
-/
def cDetector : D :=
  (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0))

/-- The finite A-detector image used by the five-detector set. Paper: §4.
-/
def aDetectorImage : Finset D := by
  classical
  exact Finset.univ.image aDetectorEmbedding

/-- The explicit finite detector set for both raw split extensions. Paper: §4.
-/
def detectorFinset : Finset D := by
  classical
  exact insert cDetector aDetectorImage

/-- The standard A chart vector is nonzero. Paper: §4. -/
lemma basisVector_zero_ne_zero :
    (PaperFiniteCharts.basisVector 0 : A) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  simp [PaperFiniteCharts.basisVector] at h0

/- The C detector is nonzero. Paper: §4. -/
lemma diagonal_basisVector_zero_ne_zero :
    (PaperKernel.diagonal (PaperFiniteCharts.basisVector 0) : PaperKernel.C) ≠ 0 := by
  intro h
  apply basisVector_zero_ne_zero
  have hdelta := congrArg PaperKernel.delta h
  rw [PaperKernel.delta_diagonal] at hdelta
  exact hdelta

/- The C detector does not duplicate an A-coordinate detector. Paper: §4. -/
lemma cDetector_not_mem_image :
    cDetector ∉ aDetectorImage := by
  classical
  intro hc
  rw [aDetectorImage] at hc
  rcases Finset.mem_image.mp hc with ⟨v, -, hv⟩
  have hsecond := congrArg Prod.snd hv
  apply diagonal_basisVector_zero_ne_zero
  simpa [cDetector, aDetectorEmbedding,
    PaperAChartDetectorMeasure.aCoordinateEmbedding] using hsecond.symm

/- Summation over the explicit detector set is the paper's five-detector sum. Paper: §4. -/
lemma detectorFinset_sum_eq (f : D → ℝ) :
    (∑ d ∈ detectorFinset, f d) =
      (∑ v : SymplecticIndex,
        f (PaperAChartDetectorMeasure.aCoordinateEmbedding v
          (PaperFiniteCharts.basisVector 0))) + f cDetector := by
  classical
  rw [detectorFinset, Finset.sum_insert cDetector_not_mem_image,
    aDetectorImage, Finset.sum_image]
  · simp only [aDetectorEmbedding]
    abel
  · exact aDetectorEmbedding.injective.injOn

/- Spectral displacement energies are nonnegative. Paper: §4. -/
lemma spectralDetectionEnergy_nonneg
    (μ : ProbabilityMeasure (DiscreteCharacterSpace PaperKernel.D))
    (d : D) :
    0 ≤ spectralDetectionEnergy μ d := by
  unfold spectralDetectionEnergy
  exact integral_nonneg (fun _ => sq_nonneg _)

/- The first concrete split extension has finite spectral detection. Paper: §4. -/
theorem lambda_one_hasFiniteSpectralDetection :
    HasFiniteSpectralDetection PaperSpectralPropertyT.lambdaOneExtension
      detectorFinset (1 / 3 : ℝ) := by
  intro μ hinv
  have h := PaperSpectralDetectorBridge.lambda_one_full_spectral_detection μ hinv
  rw [detectorFinset_sum_eq]
  simpa [cDetector] using h

/- The second concrete split extension has finite spectral detection. Paper: §4. -/
theorem lambda_two_hasFiniteSpectralDetection :
    HasFiniteSpectralDetection PaperSpectralPropertyT.lambdaTwoExtension
      detectorFinset (1 / 3 : ℝ) := by
  intro μ hinv
  have h := PaperSpectralDetectorBridge.lambda_two_full_spectral_detection μ hinv
  rw [detectorFinset_sum_eq]
  simpa [cDetector] using h

/- Package the proved detector set for the first split extension. Paper: §4.
-/
/--
The `lambdaOneSpectralData` construction used in the Connes rigidity formalization.
-/
def lambdaOneSpectralData :
    PaperSpectralPropertyT.SpectralData paperThetaOneHom where
  J := detectorFinset
  c := 1 / 3
  c_pos := by norm_num
  detection := lambda_one_hasFiniteSpectralDetection

/-- Package the proved detector set for the second split extension. Paper: §4.
-/
def lambdaTwoSpectralData :
    PaperSpectralPropertyT.SpectralData paperThetaTwoHom where
  J := detectorFinset
  c := 1 / 3
  c_pos := by norm_num
  detection := lambda_two_hasFiniteSpectralDetection

end
end PaperSpectralFiniteDetection
end Connes
