/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Primitives.AmplitudeAmplification
public import LeanPool.LeanQuantumAlg.Core.Cost

/-!
# Grover search in the good/bad-plane model

Grover search evolves in the two-dimensional plane spanned by the uniform
superposition over bad indices and the uniform superposition over good indices.
In that plane the phase oracle and diffusion reflection form exactly the same
rotation used by amplitude amplification [dW19, qcnotes.tex:2768], and after
`k` Grover iterates the success probability is `sin((2k+1)θ)^2`
[dW19, qcnotes.tex:2817].

This file states the Grover specialization against an explicit plane model:
`phaseOracle`, `diffusion`, and the hypothesis that their product is the
standard amplification rotation on the invariant good/bad plane. Building the
full `n`-qubit oracle/diffusion implementation and rounding the optimal
iteration count are separate refinements; the correctness theorem here is the
closed-form rotation core used by those refinements.

## Main results

- `LeanPool.LeanQuantumAlg.GroverSearch.main` — exact good/bad-plane state after `k` Grover
  iterates.
- `LeanPool.LeanQuantumAlg.grover_success_probability` — corresponding marked-subspace
  measurement probability.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The concrete Grover phase oracle for a marked-set predicate:
`|j⟩` receives phase `-1` exactly when `marked j` is true. -/
def phaseOracle {n : ℕ} (marked : Fin (2 ^ n) → Bool) : HilbertOperator n :=
  fun i j => if i = j then (if marked j then -1 else 1 : ℂ) else 0

theorem phaseOracle_apply_ket {n : ℕ} (marked : Fin (2 ^ n) → Bool) (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) =
      ((if marked j then -1 else 1 : ℂ) • (ket j : StateVector n)) := by
  by_cases hm : marked j
  · conv_rhs =>
      simp [hm]
    apply WithLp.ofLp_injective
    funext i
    rw [show (HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n)).ofLp i =
          HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) i from rfl,
      show ((-(ket j : StateVector n)).ofLp i) = (-(ket j : StateVector n)) i from rfl,
      HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracle, hm, PureState.ket_apply]
    · simp [phaseOracle, PureState.ket_apply, hij]
  · conv_rhs =>
      simp [hm]
    apply WithLp.ofLp_injective
    funext i
    rw [show (HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n)).ofLp i =
          HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) i from rfl,
      show ((ket j : StateVector n).ofLp i) = (ket j : StateVector n) i from rfl,
      HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracle, hm, PureState.ket_apply]
    · simp [phaseOracle, PureState.ket_apply, hij]

/-- A Grover search instance restricted to its invariant two-dimensional
bad/good plane. The initial state is `amplitudeAmplificationState θ 0`, so the
initial marked-subspace probability is `sin θ ^ 2`; the oracle and diffusion
assumptions are the explicit theorem inputs. -/
structure GroverModel where
  /-- Initial angle from the bad axis; for `t` marked items among `N`, the
  textbook relation is `sin θ = sqrt (t / N)`. -/
  θ : ℝ
  /-- Phase oracle: reflection through the bad subspace in the good/bad plane. -/
  phaseOracle : Gate 1
  /-- Diffusion reflection through the prepared uniform/start state. -/
  diffusion : Gate 1
  /-- One Grover iterate, diffusion after phase oracle, is the standard
  amplitude-amplification rotation on the invariant plane. -/
  iterate_eq : diffusion * phaseOracle = amplitudeAmplificationStep θ

/-- Grover correctness in the accepted two-dimensional scope: under the explicit
oracle/diffusion rotation hypothesis, `k` Grover iterates produce the standard
closed-form state. -/
theorem GroverSearch.main (M : GroverModel) (k : ℕ) :
    Gate.apply ((M.diffusion * M.phaseOracle) ^ k) (amplitudeAmplificationState M.θ 0) =
      amplitudeAmplificationState M.θ k := by
  rw [M.iterate_eq]
  exact amplitudeAmplificationStep_pow_apply M.θ k

/-- Grover success probability in the good/bad-plane model. Measuring the good
basis state after `k` Grover iterates succeeds with probability
`sin((2k+1)θ)^2`. -/
theorem GroverSearch.main_success_probability (M : GroverModel) (k : ℕ) :
    PureState.probOutcome
        (Gate.apply ((M.diffusion * M.phaseOracle) ^ k) (amplitudeAmplificationState M.θ 0))
        (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle M.θ k) ^ 2 := by
  rw [main, amplitudeAmplificationState_good_probability]

/-- Every Grover plane model is an amplitude-amplification model with the phase
oracle as the good reflection and the diffusion operator as the start-state
reflection. -/
def GroverModel.toAmplitudeAmplificationModel (M : GroverModel) :
    AmplitudeAmplificationModel where
  θ := M.θ
  goodReflection := M.phaseOracle
  startReflection := M.diffusion
  iterate_eq := M.iterate_eq

/-- Grover is the amplitude-amplification specialization where the good
reflection is the phase oracle and the start-state reflection is the diffusion
operator. -/
theorem GroverSearch.main_amplitude_amplification (M : GroverModel) (k : ℕ) :
    Gate.apply ((M.diffusion * M.phaseOracle) ^ k) (amplitudeAmplificationState M.θ 0) =
      Gate.apply ((M.toAmplitudeAmplificationModel.startReflection *
          M.toAmplitudeAmplificationModel.goodReflection) ^ k)
        (amplitudeAmplificationState M.toAmplitudeAmplificationModel.θ 0) := by
  rfl

namespace Grover

/-- The state after `k` Grover iterates, annotated with iterate cost `k`. -/
def timedIterate (M : GroverModel) (k : ℕ) : Timed (PureState 1) :=
  Timed.trusted k
    (Gate.apply ((M.diffusion * M.phaseOracle) ^ k)
      (amplitudeAmplificationState M.θ 0))

@[simp]
theorem timedIterate_ret (M : GroverModel) (k : ℕ) :
    (timedIterate M k).ret =
      Gate.apply ((M.diffusion * M.phaseOracle) ^ k)
        (amplitudeAmplificationState M.θ 0) := rfl

@[simp]
theorem timedIterate_time (M : GroverModel) (k : ℕ) :
    (timedIterate M k).time = k := rfl

/-- Grover correctness, phrased through the TimeM return value. -/
theorem timedIterate_correct (M : GroverModel) (k : ℕ) :
    (timedIterate M k).ret = amplitudeAmplificationState M.θ k := by
  exact GroverSearch.main M k

/-- The marked-subspace success probability after the timed Grover iterate. -/
theorem timedIterate_success_probability (M : GroverModel) (k : ℕ) :
    PureState.probOutcome (timedIterate M k).ret (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle M.θ k) ^ 2 := by
  rw [timedIterate_correct, amplitudeAmplificationState_good_probability]

/-- The timed Grover iterate has the same return value as its amplitude-amplification view. -/
theorem timedIterate_ret_eq_amplitudeAmplification
    (M : GroverModel) (k : ℕ) :
    (timedIterate M k).ret =
      (AmplitudeAmplification.timedIterate
        M.toAmplitudeAmplificationModel k).ret := rfl

/-- Trusted public resource profile for `k` Grover iterations on `n` index
qubits: `k` oracle queries and a linear-in-`n` elementary-gate representative
per iterate. -/
def resourceProfile (n k : ℕ) : ResourceProfile where
  oracleQueries := k
  hadamardGates := 0
  elementaryGates := k * n
  classicalOps := 0

theorem resourceProfile_exact (n k : ℕ) :
    ResourceProfile.HasExactCounts (resourceProfile n k) k 0 (k * n) 0 := by
  simp [ResourceProfile.HasExactCounts, resourceProfile]

/-- Grover supporting theorem for the public marked-count statement. The
relation between the concrete `n`-qubit oracle and this good/bad plane remains
an explicit model hypothesis; under the marked-count angle relation, the timed
iterate has the public success probability and resource profile. -/
theorem success_probability_with_resources
    (M : GroverModel) {n t k : ℕ}
    (_ht_pos : 0 < t) (_ht_le : t ≤ 2 ^ n)
    (hθ : M.θ = Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) :
    PureState.probOutcome (timedIterate M k).ret (1 : Fin (2 ^ 1)) =
        Real.sin (((2 : ℝ) * k + 1) *
          Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) ^ 2 ∧
      ResourceProfile.HasExactCounts (resourceProfile n k) k 0 (k * n) 0 := by
  constructor
  · rw [timedIterate_success_probability]
    simp [amplitudeAmplificationAngle, hθ]
  · exact resourceProfile_exact n k

end Grover

/-- Registered basis-action wrapper for the concrete Grover phase oracle. -/
theorem GroverSearch.main_phase_oracle_basis_action {n : ℕ}
    (marked : Fin (2 ^ n) → Bool) (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) =
      ((if marked j then -1 else 1 : ℂ) • (ket j : StateVector n)) := by
  exact phaseOracle_apply_ket marked j

/-- Registered resource wrapper for the marked-count Grover statement. -/
theorem GroverSearch.main_success_probability_with_resources
    (M : GroverModel) {n t k : ℕ}
    (ht_pos : 0 < t) (ht_le : t ≤ 2 ^ n)
    (hθ : M.θ = Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) :
    PureState.probOutcome (Grover.timedIterate M k).ret (1 : Fin (2 ^ 1)) =
        Real.sin (((2 : ℝ) * k + 1) *
          Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) ^ 2 ∧
      ResourceProfile.HasExactCounts (Grover.resourceProfile n k) k 0 (k * n) 0 := by
  exact Grover.success_probability_with_resources M ht_pos ht_le hθ

end

end QuantumAlg
