/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Algorithms.QPE
public import LeanPool.LeanQuantumAlg.Primitives.AmplitudeAmplification

/-!
# Amplitude estimation (exact, dyadic eigenphase)

Amplitude estimation reads the unknown good-state amplitude of an amplitude-
amplification instance by running quantum phase estimation on the amplification
operator [Lin22]. This module records the exact dyadic regime: QPE reads out the
phase-register basis vector, and the estimate `sin^2(pi*j/2^t)` equals the
good-state probability in the two-dimensional amplitude-amplification model.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- Exact amplitude estimation in the decoupled dyadic model. Phase estimation
enters through the raw-vector readout theorem, while the success probability is
the existing amplitude-amplification `PureState` probability theorem. -/
theorem AmplitudeEstimation.main_exact_dyadic (t : Nat) (j : Fin (2 ^ t)) (theta : Real)
    (htheta : theta = Real.pi * (j.val : Real) / (2 : Real) ^ t) :
    (invQFT t).applyVec (phaseState t ((j.val : Real) / (2 : Real) ^ t))
        = (ket j : StateVector t) ∧
      PureState.probOutcome (amplitudeAmplificationState theta 0) (1 : Fin (2 ^ 1))
          = Real.sin (Real.pi * (j.val : Real) / (2 : Real) ^ t) ^ 2 := by
  refine ⟨?_, ?_⟩
  · exact QuantumPhaseEstimation.main_exact_dyadic t j _ rfl
  · rw [amplitudeAmplificationState_good_probability]
    have hang : amplitudeAmplificationAngle theta 0 = theta := by
      unfold amplitudeAmplificationAngle
      push_cast
      ring
    rw [hang, htheta]

/-- Trusted resource profile for exact amplitude estimation in the decoupled
dyadic-eigenphase model. It records the QPE layer used by the exact readout;
source-level state-preparation and reflection oracles are outside this exact
model. -/
def amplitudeEstimationExactResourceProfile (t : Nat) : ResourceProfile :=
  qpeExactResourceProfile t

theorem amplitudeEstimationExactResourceProfile_exact (t : Nat) :
    ResourceProfile.HasExactCounts
      (amplitudeEstimationExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  exact qpeExactResourceProfile_exact t

/-- Exact amplitude estimation paired with the decoupled QPE resource profile. -/
theorem AmplitudeEstimation.main_exact_dyadic_with_resources
    (t : Nat) (j : Fin (2 ^ t)) (theta : Real)
    (htheta : theta = Real.pi * (j.val : Real) / (2 : Real) ^ t) :
    ((invQFT t).applyVec (phaseState t ((j.val : Real) / (2 : Real) ^ t))
        = (ket j : StateVector t) ∧
      PureState.probOutcome (amplitudeAmplificationState theta 0) (1 : Fin (2 ^ 1))
          = Real.sin (Real.pi * (j.val : Real) / (2 : Real) ^ t) ^ 2) ∧
      ResourceProfile.HasExactCounts
        (amplitudeEstimationExactResourceProfile t) (2 ^ t - 1) t (t ^ 2) 0 := by
  constructor
  · exact AmplitudeEstimation.main_exact_dyadic t j theta htheta
  · exact amplitudeEstimationExactResourceProfile_exact t

/-- Source-level exact-amplitude-estimation input in the same dyadic regime:
a source-style preparation/reflection amplitude-amplification model together
with a phase-register index for the exact QPE readout. -/
structure SourceAmplitudeEstimationInput where
  /-- The source-level amplitude-amplification model being estimated. -/
  source : SourceAmplitudeAmplificationModel
  /-- Number of phase-register qubits in the exact dyadic regime. -/
  t : Nat
  /-- The exact dyadic phase-register output. -/
  j : Fin (2 ^ t)
  /-- The source angle is exactly represented by `j / 2^t`. -/
  theta_eq : source.theta = Real.pi * (j.val : Real) / (2 : Real) ^ t

/-- Source-level exact amplitude-estimation bridge: the source preparation has
good-state probability `sin^2(theta)`, exact QPE reads the dyadic phase register,
and the same trusted exact-QPE resource profile is recorded. -/
theorem AmplitudeEstimation.main
    (E : SourceAmplitudeEstimationInput) :
    (PureState.probOutcome (E.source.preparation.apply ket0) (1 : Fin (2 ^ 1)) =
        Real.sin (Real.pi * (E.j.val : Real) / (2 : Real) ^ E.t) ^ 2 ∧
      (invQFT E.t).applyVec
          (phaseState E.t ((E.j.val : Real) / (2 : Real) ^ E.t))
          = (ket E.j : StateVector E.t)) ∧
      ResourceProfile.HasExactCounts
        (amplitudeEstimationExactResourceProfile E.t)
        (2 ^ E.t - 1) E.t (E.t ^ 2) 0 := by
  constructor
  · constructor
    · rw [SourceAmplitudeAmplificationModel.prepared_eq_state E.source,
        amplitudeAmplificationState_good_probability]
      unfold amplitudeAmplificationAngle
      norm_num
      rw [E.theta_eq]
    · exact (AmplitudeEstimation.main_exact_dyadic E.t E.j E.source.theta E.theta_eq).1
  · exact amplitudeEstimationExactResourceProfile_exact E.t

end

end QuantumAlg
