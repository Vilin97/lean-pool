/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Spectral consequences of the numerical radius

The spectrum of a bounded operator lies in the closed numerical-range disk.
Equivalently, every spectral value has modulus at most the numerical radius,
and the spectral radius is bounded by the numerical radius.
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import LeanPool.OperatorTheory.Operator.NumericalRange.Affine
import LeanPool.OperatorTheory.Operator.NumericalRange.Radius
import LeanPool.OperatorTheory.Operator.SpectralSet.SpectrumInNR

open Set
open scoped ENNReal InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The closure of the numerical range remains in the closed disk determined
by the numerical radius. -/
theorem closure_numericalRange_subset_closedBall_numericalRadius
    (A : E →L[ℂ] E) :
    closure (numericalRange A) ⊆ Metric.closedBall 0 (numericalRadius A) := by
  apply closure_minimal
  · intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_numericalRadius A hz
  · exact Metric.isClosed_closedBall

/-- The closed numerical range of a centered operator lies in its
zero-centered numerical-radius disk. -/
theorem closure_numericalRange_sub_smul_one_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    closure (numericalRange (A - c • (1 : E →L[ℂ] E))) ⊆
      Metric.closedBall 0
        (numericalRadius (A - c • (1 : E →L[ℂ] E))) :=
  closure_numericalRange_subset_closedBall_numericalRadius
    (A - c • (1 : E →L[ℂ] E))

/-- Every point of the closed numerical range has modulus at most the
numerical radius. -/
theorem norm_le_numericalRadius_of_mem_closure_numericalRange
    (A : E →L[ℂ] E) {z : ℂ} (hz : z ∈ closure (numericalRange A)) :
    ‖z‖ ≤ numericalRadius A := by
  have hz' := closure_numericalRange_subset_closedBall_numericalRadius A hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz'

/-- Every point in the closed numerical range of a centered operator has
modulus at most its centered numerical radius. -/
theorem norm_le_centered_numericalRadius_of_mem_closure_numericalRange_sub_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ closure (numericalRange (A - c • (1 : E →L[ℂ] E)))) :
    ‖z‖ ≤ numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  norm_le_numericalRadius_of_mem_closure_numericalRange
    (A - c • (1 : E →L[ℂ] E)) hz

/-- Centering the operator at `c` gives a closed disk of radius `w(A-cI)`
that contains the closed numerical range of `A`. -/
theorem closure_numericalRange_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    closure (numericalRange A) ⊆
      Metric.closedBall c (numericalRadius (A - c • 1)) := by
  apply closure_minimal
  · intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply norm_le_numericalRadius (A - c • 1)
    rw [numericalRange_sub_smul_one]
    exact ⟨z, hz, rfl⟩
  · exact Metric.isClosed_closedBall

/-- Every point of the closed numerical range lies within `w(A-cI)` of the
chosen center `c`. -/
theorem dist_le_centered_numericalRadius_of_mem_closure_numericalRange
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ closure (numericalRange A)) :
    dist z c ≤ numericalRadius (A - c • 1) := by
  exact closure_numericalRange_subset_closedBall_centered_numericalRadius
    A c hz

variable [CompleteSpace E]

/-- The spectrum is contained in the closed disk whose radius is the
numerical radius. -/
theorem spectrum_subset_closedBall_numericalRadius (A : E →L[ℂ] E) :
    spectrum ℂ A ⊆ Metric.closedBall 0 (numericalRadius A) :=
  (spectrum_subset_closure_numericalRange A).trans
    (closure_numericalRange_subset_closedBall_numericalRadius A)

/-- The spectrum of a centered operator lies in its zero-centered
numerical-radius disk. -/
theorem spectrum_sub_smul_one_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    spectrum ℂ (A - c • (1 : E →L[ℂ] E)) ⊆
      Metric.closedBall 0
        (numericalRadius (A - c • (1 : E →L[ℂ] E))) :=
  spectrum_subset_closedBall_numericalRadius
    (A - c • (1 : E →L[ℂ] E))

/-- Every spectral value has modulus at most the numerical radius. -/
theorem norm_le_numericalRadius_of_mem_spectrum
    (A : E →L[ℂ] E) {z : ℂ} (hz : z ∈ spectrum ℂ A) :
    ‖z‖ ≤ numericalRadius A := by
  have hz' := spectrum_subset_closedBall_numericalRadius A hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz'

/-- Every spectral value of a centered operator has modulus at most its
centered numerical radius. -/
theorem norm_le_centered_numericalRadius_of_mem_spectrum_sub_smul_one
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (A - c • (1 : E →L[ℂ] E))) :
    ‖z‖ ≤ numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  norm_le_numericalRadius_of_mem_spectrum
    (A - c • (1 : E →L[ℂ] E)) hz

/-- The spectrum lies in the disk centered at `c` with radius `w(A-cI)`. -/
theorem spectrum_subset_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    spectrum ℂ A ⊆ Metric.closedBall c (numericalRadius (A - c • 1)) :=
  (spectrum_subset_closure_numericalRange A).trans
    (closure_numericalRange_subset_closedBall_centered_numericalRadius A c)

/-- Every spectral value lies within `w(A-cI)` of the chosen center `c`. -/
theorem dist_le_centered_numericalRadius_of_mem_spectrum
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ} (hz : z ∈ spectrum ℂ A) :
    dist z c ≤ numericalRadius (A - c • 1) :=
  spectrum_subset_closedBall_centered_numericalRadius A c hz

/-- Every scalar whose modulus is larger than the numerical radius belongs
to the resolvent set. -/
theorem isUnit_smul_one_sub_of_numericalRadius_lt_norm
    (A : E →L[ℂ] E) {z : ℂ} (hz : numericalRadius A < ‖z‖) :
    IsUnit (z • (1 : E →L[ℂ] E) - A) := by
  have hnot : z ∉ spectrum ℂ A := by
    intro hzs
    exact hz.not_ge (norm_le_numericalRadius_of_mem_spectrum A hzs)
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (spectrum.notMem_iff.mp hnot)

/-- More generally, a scalar outside the disk centered at `c` with radius
`w(A-cI)` belongs to the resolvent set of `A`. -/
theorem isUnit_smul_one_sub_of_centered_numericalRadius_lt_dist
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : numericalRadius (A - c • 1) < dist z c) :
    IsUnit (z • (1 : E →L[ℂ] E) - A) := by
  have hz' : numericalRadius (A - c • 1) < ‖z - c‖ := by
    simpa only [dist_eq_norm] using hz
  have hu := isUnit_smul_one_sub_of_numericalRadius_lt_norm
    (A - c • (1 : E →L[ℂ] E)) hz'
  have hop :
      (z - c) • (1 : E →L[ℂ] E) - (A - c • 1) = z • 1 - A := by
    module
  rw [hop] at hu
  exact hu

/-- In particular, `1-A` is a unit whenever `w(A) < 1`. -/
theorem isUnit_one_sub_of_numericalRadius_lt_one
    (A : E →L[ℂ] E) (hA : numericalRadius A < 1) :
    IsUnit (1 - A) := by
  have hA' : numericalRadius A < ‖(1 : ℂ)‖ := by simpa using hA
  simpa only [one_smul] using
    (isUnit_smul_one_sub_of_numericalRadius_lt_norm A hA')

/-- The spectral radius is bounded by the numerical radius. -/
theorem spectralRadius_le_numericalRadius (A : E →L[ℂ] E) :
    spectralRadius ℂ A ≤ ENNReal.ofReal (numericalRadius A) := by
  unfold spectralRadius
  refine iSup₂_le fun z hz => ?_
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (norm_le_numericalRadius_of_mem_spectrum A hz)

/-- Centered form of the spectral-radius bound. -/
theorem spectralRadius_sub_smul_one_le_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    spectralRadius ℂ (A - c • (1 : E →L[ℂ] E)) ≤
      ENNReal.ofReal (numericalRadius (A - c • (1 : E →L[ℂ] E))) :=
  spectralRadius_le_numericalRadius
    (A - c • (1 : E →L[ℂ] E))

/-- Real-valued form of `spectralRadius_le_numericalRadius`. -/
theorem spectralRadius_toReal_le_numericalRadius (A : E →L[ℂ] E) :
    (spectralRadius ℂ A).toReal ≤ numericalRadius A := by
  calc
    (spectralRadius ℂ A).toReal ≤
        (ENNReal.ofReal (numericalRadius A)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (spectralRadius_le_numericalRadius A)
    _ = numericalRadius A :=
      ENNReal.toReal_ofReal (numericalRadius_nonneg A)

/-- Real-valued centered form of the spectral-radius bound. -/
theorem spectralRadius_sub_smul_one_toReal_le_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    (spectralRadius ℂ (A - c • (1 : E →L[ℂ] E))).toReal ≤
      numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  spectralRadius_toReal_le_numericalRadius
    (A - c • (1 : E →L[ℂ] E))

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
