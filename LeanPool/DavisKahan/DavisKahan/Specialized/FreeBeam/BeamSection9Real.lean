/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenvalueSequenceReal

/-! # Beam Section9Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# Source-facing real model for Davis--Kahan Section 9

This module assembles the real free-beam model used in Section 9.  It keeps the analytic
realization, classical fourth-derivative operator, positive spectral sequence, affine trial plane,
and multiplication perturbation on the same real `L²(0,1)` carrier used by the paper.

The finite-data certificate is therefore constructed from the real model itself rather than
borrowed from the complex specialization.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real


noncomputable section

open DavisKahan1970.Section9

/-- The Section 9 finite-data certificate, constructed from the real free-beam model. -/
def beamFiniteDataCertificate (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    FreeBeamFiniteDataCertificate ε where
  epsilon_pos := hε
  epsilon_lt_hundred := hε100
  thirdEigenvalue := exists_strictMono_range_eq_beamEigenvalues.choose 0
  third_eigenvalue_gt_five_hundred :=
    (exists_strictMono_range_eq_beamEigenvalues.choose_spec.2.2 0).1
  initialResidualGram := residualGram ε
  initial_residual_gram_eq := rfl
  ritzLow := ritzLow ε
  ritzHigh := ritzHigh ε
  ritz_low_eq := rfl
  ritz_high_eq := rfl
  recenteredResidualGram := orthogonalResidualGram ε
  recentered_residual_gram_eq := rfl

/-- A compact source-facing summary of the real Section 9 operator model.

It records the printed real scalar field, the self-adjoint closure of the classical free-end
fourth-derivative operator, the exact decomposition of the real spectrum into the two-dimensional
zero mode and the increasing positive sequence, and the source gap above `500`. -/
theorem beamRealModel_sourceFacts :
    _root_.IsSelfAdjoint beamOperator ∧
      closure classicalFreeBeamGraph =
        (beamOperator.graph : Set (BeamL2 × BeamL2)) ∧
      TauCeti.LinearPMap.realSpectrum beamOperator = insert 0 beamEigenvalues ∧
      (∃ f : ℕ → ℝ, StrictMono f ∧ Set.range f = beamEigenvalues ∧
        ∀ n, 500 < f n ∧ f n ∈ TauCeti.LinearPMap.realSpectrum beamOperator) := by
  exact ⟨beamOperator_isSelfAdjoint,
    closure_classicalFreeBeamGraph_eq_graph,
    realSpectrum_beamOperator_eq_insert_zero,
    exists_strictMono_range_eq_beamEigenvalues⟩

/-- The positive spectrum in the real Section 9 model is exactly the fourth powers of the
positive roots of `cos beta * cosh beta = 1`. -/
theorem beamRealPositiveSpectrum_sourceFacts :
    beamEigenvalues =
      {lam : ℝ | ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧ lam = beta ^ 4} :=
  beamEigenvalues_eq_characteristicFourthPowers

/-- The zero eigenspace is exactly the two-dimensional affine trial plane printed in Section 9. -/
theorem beamRealZeroMode_sourceFacts :
    Module.finrank ℝ beamTrial = 2 ∧
      ∀ (x : BeamL2) (h : x ∈ beamOperator.domain),
        beamOperator ⟨x, h⟩ = 0 ↔ x ∈ beamTrial :=
  ⟨finrank_beamTrial, fun _ h => beamOperator_eq_zero_iff_mem_beamTrial h⟩

/-- A source-facing summary of the real Section 9 perturbation and trial-space data. -/
theorem beamRealFiniteData_sourceFacts (ε : ℝ) (hε : 0 < ε) :
    (beamPerturbation ε).IsSymmetric ∧
      ‖beamPerturbation ε‖ ≤ ε ∧
      (‖centeredAffineLp trialOne‖ ^ 2 = 1 ∧
        ‖centeredAffineLp trialTwo‖ ^ 2 = 1 ∧
        ⟪centeredAffineLp trialOne, centeredAffineLp trialTwo⟫_ℝ = 0) := by
  refine ⟨beamPerturbation_isSelfAdjoint ε, ?_, beamTrial_orthonormal⟩
  simpa [abs_of_pos hε] using norm_beamPerturbation_le ε

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
