/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Components.Gates
public import LeanPool.LeanQuantumAlg.Core.Measurement
public import LeanPool.LeanQuantumAlg.Core.Cost

/-!
# Amplitude amplification in the good/bad plane

Amplitude amplification reduces to a two-dimensional invariant plane spanned by
an orthonormal bad state and good state. If the initial state has angle `θ` from
the bad axis, one amplification iterate rotates that plane by `2θ`; after `k`
iterations the good amplitude is `sin((2k+1)θ)` [dW19, qcnotes.tex:2954].

This module formalizes exactly that two-dimensional core. The ambient register
is the quotient plane, represented as one qubit: `|0⟩` is the bad axis and `|1⟩`
is the good axis. Concrete algorithms provide reflections whose product agrees
with `amplitudeAmplificationStep θ` on this plane.

## Main results

- `LeanPool.LeanQuantumAlg.AmplitudeAmplification.main` — exact state after `k`
  amplification iterates under explicit reflection-product assumptions.
- `LeanPool.LeanQuantumAlg.amplitude_amplification_success_probability` — the corresponding
  good-state measurement probability.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The angle after `k` amplitude-amplification iterates: `(2k+1)θ`. -/
def amplitudeAmplificationAngle (θ : ℝ) (k : ℕ) : ℝ := ((2 : ℝ) * k + 1) * θ

/-- The good/bad-plane state with bad amplitude `cos((2k+1)θ)` and good
amplitude `sin((2k+1)θ)`. In this two-dimensional model, `|0⟩` is the bad axis
and `|1⟩` is the good axis. -/
def amplitudeAmplificationStateVec (θ : ℝ) (k : ℕ) : StateVector 1 :=
  ((Real.cos (amplitudeAmplificationAngle θ k) : ℂ) • (ket0 : StateVector 1)) +
    ((Real.sin (amplitudeAmplificationAngle θ k) : ℂ) • ket1)

theorem norm_amplitudeAmplificationStateVec (θ : ℝ) (k : ℕ) :
    ‖amplitudeAmplificationStateVec θ k‖ = 1 := by
  rw [PureState.norm_eq_two_terms]
  conv_lhs =>
    simp [amplitudeAmplificationStateVec, ket0, ket1, PureState.ket_apply,
      PiLp.smul_apply, PiLp.add_apply]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_ofReal,
    Complex.normSq_ofReal]
  simpa [add_comm, sq] using Real.cos_sq_add_sin_sq (amplitudeAmplificationAngle θ k)

/-- The good/bad-plane state with bad amplitude `cos((2k+1)θ)` and good
amplitude `sin((2k+1)θ)`. In this two-dimensional model, `|0⟩` is the bad axis
and `|1⟩` is the good axis. -/
def amplitudeAmplificationState (θ : ℝ) (k : ℕ) : PureState 1 :=
  PureState.ofVec (amplitudeAmplificationStateVec θ k)
    (norm_amplitudeAmplificationStateVec θ k)

/-- One amplitude-amplification iterate on the good/bad plane: rotation by
`2θ`. Since `rotY φ` rotates the real plane by `φ/2`, this is `rotY (4θ)`. -/
def amplitudeAmplificationStep (θ : ℝ) : Gate 1 := rotY (4 * θ)

/-- The plane rotation used by amplitude amplification is unitary. -/
theorem amplitudeAmplificationStep_mem_unitaryGroup (θ : ℝ) :
    (amplitudeAmplificationStep θ : HilbertOperator 1) ∈
      Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  rotY_mem_unitaryGroup _

/-- One amplitude-amplification step increases the good/bad-plane angle by
`2θ`. -/
theorem amplitudeAmplificationStep_apply_state (θ : ℝ) (k : ℕ) :
    (amplitudeAmplificationStep θ).apply (amplitudeAmplificationState θ k) =
      amplitudeAmplificationState θ (k + 1) := by
  ext i
  have hangle : amplitudeAmplificationAngle θ (k + 1) =
      amplitudeAmplificationAngle θ k + 2 * θ := by
    unfold amplitudeAmplificationAngle
    norm_num
    ring
  fin_cases i
  · change (amplitudeAmplificationStep θ).apply (amplitudeAmplificationState θ k) 0 =
      amplitudeAmplificationState θ (k + 1) 0
    rw [Gate.apply_apply]
    conv_lhs =>
      simp [amplitudeAmplificationStep, amplitudeAmplificationState,
        amplitudeAmplificationStateVec, rotY, rotYOp, ket0, ket1, PureState.ket_apply]
    conv_rhs =>
      simp [amplitudeAmplificationState, amplitudeAmplificationStateVec, ket0, ket1,
        PureState.ket_apply, hangle]
    rw [Complex.cos_add]
    ring_nf
  · change (amplitudeAmplificationStep θ).apply (amplitudeAmplificationState θ k) 1 =
      amplitudeAmplificationState θ (k + 1) 1
    rw [Gate.apply_apply]
    conv_lhs =>
      simp [amplitudeAmplificationStep, amplitudeAmplificationState,
        amplitudeAmplificationStateVec, rotY, rotYOp, ket0, ket1, PureState.ket_apply]
    conv_rhs =>
      simp [amplitudeAmplificationState, amplitudeAmplificationStateVec, ket0, ket1,
        PureState.ket_apply, hangle]
    rw [Complex.sin_add]
    ring_nf

/-- Iterating the abstract amplification step gives the standard closed form
`cos((2k+1)θ)|bad⟩ + sin((2k+1)θ)|good⟩`. -/
theorem amplitudeAmplificationStep_pow_apply (θ : ℝ) (k : ℕ) :
    ((amplitudeAmplificationStep θ) ^ k).apply (amplitudeAmplificationState θ 0) =
      amplitudeAmplificationState θ k := by
  induction k with
  | zero =>
      simp [Gate.one_apply]
  | succ k ih =>
      rw [pow_succ', Gate.mul_apply, ih, amplitudeAmplificationStep_apply_state]

/-- An amplitude-amplification instance on the two-dimensional good/bad plane.
The fields are deliberately explicit: a good-state reflection, a start-state
reflection, and the proof that their product restricts to the standard rotation
on this plane. -/
structure AmplitudeAmplificationModel where
  /-- Initial angle from the bad axis; the initial good probability is
  `sin θ ^ 2`. -/
  θ : ℝ
  /-- Reflection that flips the good component and fixes the bad component. -/
  goodReflection : Gate 1
  /-- Reflection through the prepared start state. -/
  startReflection : Gate 1
  /-- The product of the two reflections acts as the amplification rotation on
  the invariant good/bad plane. -/
  iterate_eq : startReflection * goodReflection = amplitudeAmplificationStep θ

/-- Source-level reflection-product wrapper for the public amplitude-
amplification statement. In the good/bad plane, `ket0` is the bad axis
`|ψ₀⟩` and `ket1` is the good axis `|ψ₁⟩`. The preparation gate packages
`A|0⟩ = sin θ |ψ₁⟩ + cos θ |ψ₀⟩`, while `iterate_eq` records the source
iterate `A S₀ A† S_good` as the standard plane rotation. -/
structure SourceAmplitudeAmplificationModel where
  /-- Initial good-angle parameter. -/
  theta : ℝ
  /-- Source preparation unitary `A`, restricted to the invariant plane. -/
  preparation : Gate 1
  /-- Reflection around the initial computational state before preparation. -/
  zeroReflection : Gate 1
  /-- Reflection that flips the good component and fixes the bad component. -/
  goodReflection : Gate 1
  /-- Source preparation statement in public good/bad order. -/
  prepares_start :
    preparation.applyVec (ket0 : StateVector 1) =
      ((Real.sin theta : ℂ) • (ket1 : StateVector 1)) +
        ((Real.cos theta : ℂ) • (ket0 : StateVector 1))
  /-- The public reflection product, restricted to the invariant plane. -/
  iterate_eq :
    preparation * zeroReflection * preparation.conjTranspose * goodReflection =
      amplitudeAmplificationStep theta

namespace SourceAmplitudeAmplificationModel

/-- Forget the source-level preparation wrapper and expose the existing
two-dimensional amplitude-amplification model. -/
def toModel (M : SourceAmplitudeAmplificationModel) : AmplitudeAmplificationModel where
  θ := M.theta
  goodReflection := M.goodReflection
  startReflection := M.preparation * M.zeroReflection * M.preparation.conjTranspose
  iterate_eq := M.iterate_eq

/-- The source preparation statement is the initial good/bad-plane state used
by the core amplitude-amplification theorem. -/
theorem prepared_eq_state (M : SourceAmplitudeAmplificationModel) :
    M.preparation.apply ket0 = amplitudeAmplificationState M.theta 0 := by
  ext i
  change M.preparation.applyVec (ket0 : StateVector 1) i =
    amplitudeAmplificationStateVec M.theta 0 i
  rw [M.prepares_start]
  simp [amplitudeAmplificationStateVec, amplitudeAmplificationAngle,
    PiLp.smul_apply, PiLp.add_apply, add_comm]

end SourceAmplitudeAmplificationModel

/-- Amplitude amplification correctness in the accepted two-dimensional scope:
if the reflection product acts as the standard good/bad-plane rotation, then `k`
iterations produce the closed-form amplified state. -/
theorem AmplitudeAmplification.main (M : AmplitudeAmplificationModel) (k : ℕ) :
    Gate.apply ((M.startReflection * M.goodReflection) ^ k)
        (amplitudeAmplificationState M.θ 0) =
      amplitudeAmplificationState M.θ k := by
  rw [M.iterate_eq]
  exact amplitudeAmplificationStep_pow_apply M.θ k

/-- Source-level reflection-product form of amplitude amplification. This
states the public `A S₀ A† S_good` iterate through the same proved
two-dimensional rotation theorem. -/
theorem source_reflection_correct (M : SourceAmplitudeAmplificationModel) (k : ℕ) :
    Gate.apply
        ((M.preparation * M.zeroReflection * M.preparation.conjTranspose *
            M.goodReflection) ^ k)
        (M.preparation.apply ket0) =
      amplitudeAmplificationState M.theta k := by
  rw [SourceAmplitudeAmplificationModel.prepared_eq_state]
  exact AmplitudeAmplification.main M.toModel k

/-- Closed-form public-order source reflection statement:
`(A S₀ A† S_good)^k A|0⟩ =
sin((2k+1)θ)|ψ₁⟩ + cos((2k+1)θ)|ψ₀⟩` in the good/bad plane. -/
theorem source_reflection_closed_form (M : SourceAmplitudeAmplificationModel) (k : ℕ) :
    (Gate.apply
        ((M.preparation * M.zeroReflection * M.preparation.conjTranspose *
            M.goodReflection) ^ k)
        (M.preparation.apply ket0) : StateVector 1) =
      ((Real.sin (amplitudeAmplificationAngle M.theta k) : ℂ) •
          (ket1 : StateVector 1)) +
        ((Real.cos (amplitudeAmplificationAngle M.theta k) : ℂ) •
          (ket0 : StateVector 1)) := by
  rw [source_reflection_correct]
  simp [amplitudeAmplificationState, amplitudeAmplificationStateVec, add_comm]

/-- The success probability of the closed-form amplitude-amplified state is the
squared good amplitude. -/
theorem amplitudeAmplificationState_good_probability (θ : ℝ) (k : ℕ) :
    PureState.probOutcome (amplitudeAmplificationState θ k) (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle θ k) ^ 2 := by
  rw [PureState.probOutcome]
  conv_lhs =>
    simp [StateVector.probOutcome, amplitudeAmplificationState,
      amplitudeAmplificationStateVec, ket0, ket1, PureState.ket_apply,
      PiLp.smul_apply, PiLp.add_apply]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_sin, Complex.normSq_ofReal]
  ring

/-- Amplitude amplification success probability after `k` reflection-product
iterations. -/
theorem AmplitudeAmplification.main_success_probability
    (M : AmplitudeAmplificationModel) (k : ℕ) :
    PureState.probOutcome
        (Gate.apply ((M.startReflection * M.goodReflection) ^ k)
          (amplitudeAmplificationState M.θ 0))
        (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle M.θ k) ^ 2 := by
  rw [main, amplitudeAmplificationState_good_probability]

namespace AmplitudeAmplification

/-- The state after `k` amplification iterates, annotated with iterate cost `k`. -/
def timedIterate (M : AmplitudeAmplificationModel) (k : ℕ) : Timed (PureState 1) :=
  Timed.trusted k
    (Gate.apply ((M.startReflection * M.goodReflection) ^ k)
      (amplitudeAmplificationState M.θ 0))

@[simp]
theorem timedIterate_ret (M : AmplitudeAmplificationModel) (k : ℕ) :
    (timedIterate M k).ret =
      Gate.apply ((M.startReflection * M.goodReflection) ^ k)
        (amplitudeAmplificationState M.θ 0) := rfl

@[simp]
theorem timedIterate_time (M : AmplitudeAmplificationModel) (k : ℕ) :
    (timedIterate M k).time = k := rfl

/-- Amplitude-amplification correctness, phrased through the TimeM return value. -/
theorem timedIterate_correct (M : AmplitudeAmplificationModel) (k : ℕ) :
    (timedIterate M k).ret = amplitudeAmplificationState M.θ k := by
  exact AmplitudeAmplification.main M k

/-- The good-state success probability after the timed iterate. -/
theorem timedIterate_success_probability
    (M : AmplitudeAmplificationModel) (k : ℕ) :
    PureState.probOutcome (timedIterate M k).ret (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle M.θ k) ^ 2 := by
  rw [timedIterate_correct, amplitudeAmplificationState_good_probability]

end AmplitudeAmplification


end

end QuantumAlg
