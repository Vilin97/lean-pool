/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSection9Real

/-! # Real Model -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Section 9: real free-beam source model

This module is the paper-facing surface for the analytic model used in the numerical example.
It exposes the real `L²(0,1)` free-beam realization, its identification as the self-adjoint
closure of the classical fourth derivative with the four printed free-end boundary conditions,
the increasing positive spectral sequence above `500`, and the exact finite Rayleigh--Ritz data.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section9


noncomputable section

/-- The real Hilbert space used by the Section 9 numerical example. -/
abbrev RealBeamL2 : Type :=
  DavisKahan.FreeBeam.Model.Real.BeamL2

/-- The self-adjoint real free-beam operator used by the Section 9 numerical example. -/
abbrev realBeamOperator :
    RealBeamL2 →ₗ.[ℝ] RealBeamL2 :=
  DavisKahan.FreeBeam.Model.Real.beamOperator

/-- The classical free-end fourth-derivative graph whose closure is `realBeamOperator`. -/
abbrev realClassicalFreeBeamGraph : Set (RealBeamL2 × RealBeamL2) :=
  DavisKahan.FreeBeam.Model.Real.classicalFreeBeamGraph

/-- **Paper-faithful operator model for Section 9.**

The real free-beam realization is self-adjoint and is exactly the graph closure of the
classical fourth derivative on functions satisfying
`u''(0)=u'''(0)=u''(1)=u'''(1)=0`. -/
theorem real_freeBeam_operator_isSelfAdjoint_and_graphClosure :
    _root_.IsSelfAdjoint realBeamOperator ∧
      closure realClassicalFreeBeamGraph =
        (realBeamOperator.graph : Set (RealBeamL2 × RealBeamL2)) :=
  DavisKahan.FreeBeam.Model.Real.beamOperator_is_closure_of_classical_freeBeam_fourthDerivative

/-- **Paper-faithful spectral model for Section 9.**

Besides the two-dimensional zero eigenspace, the real spectrum is an increasing sequence of
positive eigenvalues, every one of which is larger than `500`. -/
theorem real_freeBeam_spectrum_decomposition :
    TauCeti.LinearPMap.realSpectrum realBeamOperator =
        insert 0 DavisKahan.FreeBeam.Model.Real.beamEigenvalues ∧
      (∃ f : ℕ → ℝ, StrictMono f ∧
        Set.range f =
          DavisKahan.FreeBeam.Model.Real.beamEigenvalues ∧
        ∀ n, 500 < f n ∧ f n ∈ TauCeti.LinearPMap.realSpectrum realBeamOperator) := by
  exact ⟨
    DavisKahan.FreeBeam.Model.Real.realSpectrum_beamOperator_eq_insert_zero,
    DavisKahan.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues⟩

/-- **Paper-faithful multiplicity and indexing statement for the unperturbed
free beam.**

The zero eigenspace is exactly the two-dimensional affine trial plane.  The
positive eigenvalues admit the strictly increasing enumeration printed after
`alpha_1 = alpha_2 = 0`, with `f n` corresponding to the paper's
`alpha_{n+3}`; and every positive eigenvalue is geometrically simple.  The last
clause is essential: enumerating only the set of distinct positive spectral
values would not justify the paper's strict multiplicity-sensitive indexing. -/
theorem real_freeBeam_eigenvalue_indexing :
    Module.finrank ℝ DavisKahan.FreeBeam.Model.Real.beamTrial = 2 ∧
      (∀ (x : RealBeamL2) (h : x ∈ realBeamOperator.domain),
        realBeamOperator ⟨x, h⟩ = 0 ↔
          x ∈ DavisKahan.FreeBeam.Model.Real.beamTrial) ∧
      (∃ f : ℕ → ℝ, StrictMono f ∧
        Set.range f = DavisKahan.FreeBeam.Model.Real.beamEigenvalues ∧
        ∀ n, 500 < f n ∧ f n ∈ TauCeti.LinearPMap.realSpectrum realBeamOperator) ∧
      (∀ (lam : ℝ), 0 < lam →
        ∀ (x y : realBeamOperator.domain),
          (x : RealBeamL2) ≠ 0 →
          (y : RealBeamL2) ≠ 0 →
          realBeamOperator x = lam • (x : RealBeamL2) →
          realBeamOperator y = lam • (y : RealBeamL2) →
          ∃ c : ℝ, (y : RealBeamL2) = c • (x : RealBeamL2)) := by
  refine ⟨DavisKahan.FreeBeam.Model.Real.finrank_beamTrial, ?_, ?_, ?_⟩
  · intro x h
    exact DavisKahan.FreeBeam.Model.Real.beamOperator_eq_zero_iff_mem_beamTrial h
  · exact DavisKahan.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues
  · intro lam hlam x y hx0 hy0 hx hy
    exact DavisKahan.FreeBeam.Model.Real.positive_eigenvectors_eq_smul
      hlam hx0 hy0 hx hy

/-- The paper's positive free-beam spectral values are exactly the fourth powers of the
positive roots of `cos beta * cosh beta = 1`. -/
theorem real_freeBeam_positive_spectrum_eq_characteristicFourthPowers :
    DavisKahan.FreeBeam.Model.Real.beamEigenvalues =
      {lam : ℝ | ∃ beta : ℝ, 0 < beta ∧
        DavisKahan.FreeBeam.characteristic beta = 0 ∧
        lam = beta ^ 4} :=
  DavisKahan.FreeBeam.Model.Real.beamRealPositiveSpectrum_sourceFacts

/-- The paper's affine zero-mode plane is contained in the real beam-operator domain. -/
theorem real_freeBeam_trial_le_domain {x : RealBeamL2}
    (hx : x ∈ DavisKahan.FreeBeam.Model.Real.beamTrial) :
    x ∈ realBeamOperator.domain :=
  DavisKahan.FreeBeam.Model.Real.beamTrial_le_domain hx

/-- The real free-beam operator annihilates every vector in the paper's affine trial plane. -/
theorem real_freeBeam_operator_apply_trial {x : RealBeamL2}
    (hx : x ∈ DavisKahan.FreeBeam.Model.Real.beamTrial)
    (hdom : x ∈ realBeamOperator.domain) :
    realBeamOperator ⟨x, hdom⟩ = 0 :=
  DavisKahan.FreeBeam.Model.Real.beamOperator_apply_trial hx hdom

/-- The zero eigenspace is exactly the paper's two-dimensional affine trial plane. -/
theorem real_freeBeam_zero_eigenspace_eq_beamTrial :
    Module.finrank ℝ
        DavisKahan.FreeBeam.Model.Real.beamTrial = 2 ∧
      ∀ (x : RealBeamL2) (h : x ∈ realBeamOperator.domain),
        realBeamOperator ⟨x, h⟩ = 0 ↔
          x ∈ DavisKahan.FreeBeam.Model.Real.beamTrial :=
  DavisKahan.FreeBeam.Model.Real.beamRealZeroMode_sourceFacts

/-- **Davis--Kahan 1970, Section 9: the printed eigenvalue ordering
`alpha_1 = 0 = alpha_2 < alpha_3 < alpha_4 < ...`.**

The paper prints the free-beam spectrum with the zero eigenvalue occurring twice
and the positive eigenvalues strictly increasing.  Both halves are asserted here in
one place, because a reviewer checking the printed ordering should not have to
assemble it from three separate declarations.

The first conjunct is the multiplicity: the kernel of the beam operator is exactly
the affine trial plane, which is two-dimensional, so `0` is an eigenvalue of
multiplicity exactly two and `alpha_1 = alpha_2 = 0`.  The second is the strict
ordering: the positive eigenvalues admit a strictly monotone enumeration whose
range is all of them, and every one exceeds `500`, so they are separated from the
zero mode and `alpha_3 < alpha_4 < ...` with `0 < alpha_3`.

Both conjuncts are assembled from existing model facts; nothing new is proved here.
-/
theorem real_freeBeam_eigenvalue_ordering :
    (Module.finrank ℝ DavisKahan.FreeBeam.Model.Real.beamTrial = 2 ∧
      ∀ (x : RealBeamL2) (h : x ∈ realBeamOperator.domain),
        realBeamOperator ⟨x, h⟩ = 0 ↔
          x ∈ DavisKahan.FreeBeam.Model.Real.beamTrial) ∧
    ∃ f : ℕ → ℝ, StrictMono f ∧
      Set.range f = DavisKahan.FreeBeam.Model.Real.beamEigenvalues ∧
      ∀ n, 0 < f n := by
  refine ⟨real_freeBeam_zero_eigenspace_eq_beamTrial, ?_⟩
  obtain ⟨f, hmono, hrange, hgt⟩ :=
    DavisKahan.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues
  exact ⟨f, hmono, hrange, fun n => by linarith [(hgt n).1]⟩

/-- The exact finite-data certificate for the paper's real Section 9 model. -/
def realFreeBeamFiniteDataCertificate (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    FreeBeamFiniteDataCertificate ε :=
  DavisKahan.FreeBeam.Model.Real.beamFiniteDataCertificate ε hε hε100

/-- The real multiplication perturbation and orthonormal affine trial plane satisfy the
source hypotheses used by the finite Section 9 calculation. -/
theorem real_freeBeam_trial_and_perturbation (ε : ℝ) (hε : 0 < ε) :
    (DavisKahan.FreeBeam.Model.Real.beamPerturbation ε).IsSymmetric ∧
      ‖DavisKahan.FreeBeam.Model.Real.beamPerturbation ε‖ ≤ ε ∧
      (‖DavisKahan.FreeBeam.Model.Real.centeredAffineLp trialOne‖ ^ 2 = 1 ∧
        ‖DavisKahan.FreeBeam.Model.Real.centeredAffineLp trialTwo‖ ^ 2 = 1 ∧
        ⟪DavisKahan.FreeBeam.Model.Real.centeredAffineLp trialOne,
          DavisKahan.FreeBeam.Model.Real.centeredAffineLp trialTwo⟫_ℝ = 0) :=
  DavisKahan.FreeBeam.Model.Real.beamRealFiniteData_sourceFacts ε hε

end

end Section9
end DavisKahan1970
end TauCeti
