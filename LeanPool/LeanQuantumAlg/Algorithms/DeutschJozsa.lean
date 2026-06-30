/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Primitives.WalshHadamard
public import LeanPool.LeanQuantumAlg.Primitives.PhaseKickback
public import LeanPool.LeanQuantumAlg.Core.Cost

/-!
# Deutsch-Jozsa algorithm

The Deutsch-Jozsa problem gives oracle access to a Boolean function on
`N = 2^n` inputs, promised either constant or balanced: all values equal,
or exactly half zero and half one [dW19, qcnotes.tex:1179, 1181-1182].

The algorithm uses one phase query between two layers of Hadamards
[dW19, qcnotes.tex:1193]. The Walsh-Hadamard layer and the XOR phase-query
pipeline are the shared `LeanPool.LeanQuantumAlg.WalshHadamard` primitive; this module adds
only the Deutsch-Jozsa-specific content. After the query, the second Hadamard
layer makes the amplitude of `|0^n⟩` equal to
`(2^n)⁻¹ * ∑ x, (-1)^{f x}` [dW19, qcnotes.tex:1245, 1251]. This scalar is
`1` or `-1` for constant inputs
and `0` for balanced inputs [dW19, qcnotes.tex:1253, 1255], so testing
whether the `|0^n⟩` amplitude is
nonzero decides the promise problem exactly.

## Main results

- `LeanPool.LeanQuantumAlg.deutschJozsa_query_phase` — one XOR query with a `|−⟩` target
  is the phase query used by the algorithm (via `WalshHadamard` + phase
  kickback).
- `LeanPool.LeanQuantumAlg.DeutschJozsa.circuitZeroAmplitude_eq_zeroAmplitude_mul` — the
  actual final joint amplitude (from `WalshHadamard.finalJointState`) is a
  nonzero scalar multiple of the standard signed phase average.
- `LeanPool.LeanQuantumAlg.DeutschJozsa.main` — under the explicit constant/balanced
  promise, the nonzero final amplitude test is equivalent to the oracle being
  constant.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate WalshHadamard

noncomputable section

variable {n : ℕ}

namespace DeutschJozsa

/-! ### The constant/balanced promise -/

/-- The constant side of the Deutsch-Jozsa promise. -/
def IsConstant (f : Oracle n) : Prop := ∃ c : Bool, ∀ x, f x = c

/-- Inputs on which the oracle returns `true`. -/
def trueInputs (f : Oracle n) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter fun x => f x

/-- Inputs on which the oracle returns `false`. -/
def falseInputs (f : Oracle n) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter fun x => ! f x

/-- The balanced side of the Deutsch-Jozsa promise: exactly as many `true`
inputs as `false` inputs. -/
def IsBalanced (f : Oracle n) : Prop :=
  (trueInputs f).card = (falseInputs f).card

/-- The explicit Deutsch-Jozsa promise. -/
def Promise (f : Oracle n) : Prop := IsConstant f ∨ IsBalanced f

/-! ### The `|0^n⟩` amplitude test -/

/-- The final input-register amplitude of the all-zero basis state `|0^n⟩`,
in the phase-query view. -/
def inputZeroAmplitude (f : Oracle n) : ℂ := finalState f 0

/-- The actual final joint amplitude of `|0^n⟩ ⊗ |0⟩`. It is a nonzero
scalar multiple of the input-register `|0^n⟩` amplitude because the target
qubit remains `|−⟩`. -/
def circuitZeroAmplitude (f : Oracle n) : ℂ :=
  finalJointState f (prodEquiv (0, (0 : Fin (2 ^ 1))))

/-- The numerator of the final `|0^n⟩` amplitude after the second Hadamard
layer: `∑ x, (-1)^{f x}`. -/
def zeroAmplitudeNumerator (f : Oracle n) : ℂ :=
  ∑ x, phaseSign f x

/-- The standard signed-average formula for the final `|0^n⟩` amplitude. -/
def zeroAmplitude (f : Oracle n) : ℂ :=
  ((2 ^ n : ℕ) : ℂ)⁻¹ * zeroAmplitudeNumerator f

/-- The algorithm reports "constant" exactly when the actual final joint
amplitude `|0^n⟩ ⊗ |0⟩` is nonzero. Under the Deutsch-Jozsa promise, this
test is exact. -/
def ReportsConstant (f : Oracle n) : Prop := circuitZeroAmplitude f ≠ 0

private theorem sum_phaseSign_eq_false_sub_true (f : Oracle n)
    (s : Finset (Fin (2 ^ n))) :
    s.sum (fun x => phaseSign f x) =
      ((s.filter (fun x => ! f x)).card : ℂ) -
        ((s.filter (fun x => f x)).card : ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih]
      by_cases h : f a
      · simp [phaseSign, h, ha, Finset.filter_insert,
          Finset.card_insert_of_notMem]
        ring
      · simp [phaseSign, h, ha, Finset.filter_insert,
          Finset.card_insert_of_notMem]
        ring

/-- The signed phase sum is the number of `false` inputs minus the number of
`true` inputs. -/
theorem zeroAmplitudeNumerator_eq_card_sub (f : Oracle n) :
    zeroAmplitudeNumerator f =
      ((falseInputs f).card : ℂ) - ((trueInputs f).card : ℂ) := by
  rw [zeroAmplitudeNumerator, sum_phaseSign_eq_false_sub_true]
  rfl

/-- Applying the closed-form second Hadamard layer to the post-query input
state makes the final `|0^n⟩` amplitude equal to the standard signed average. -/
theorem inputZeroAmplitude_eq_zeroAmplitude (f : Oracle n) :
    inputZeroAmplitude f = zeroAmplitude f := by
  rw [inputZeroAmplitude, finalState, Gate.apply_apply, zeroAmplitude,
    zeroAmplitudeNumerator]
  calc
    ∑ j, hadamardLayer n 0 j * afterPhaseQuery f j
        = ∑ j, (((2 ^ n : ℕ) : ℂ)⁻¹ * phaseSign f j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          change (invSqrtCard n * walshSign (0 : Fin (2 ^ n)) j)
              * (invSqrtCard n * phaseSign f j)
            = (((2 ^ n : ℕ) : ℂ)⁻¹ * phaseSign f j)
          rw [walshSign_zero_left, mul_one, ← mul_assoc, invSqrtCard_mul_self]
    _ = ((2 ^ n : ℕ) : ℂ)⁻¹ * ∑ x, phaseSign f x := by
          rw [Finset.mul_sum]

/-- The actual final joint amplitude tested by the algorithm is the input
`|0^n⟩` amplitude times the nonzero `|0⟩` component of `|−⟩`. -/
theorem circuitZeroAmplitude_eq_zeroAmplitude_mul (f : Oracle n) :
    circuitZeroAmplitude f = zeroAmplitude f * invSqrt2 := by
  rw [circuitZeroAmplitude, finalJointState_eq_finalState_tensor,
    PureState.tensor_apply_prod]
  change finalState f 0 * ketMinus 0 = zeroAmplitude f * invSqrt2
  rw [show finalState f 0 = zeroAmplitude f from inputZeroAmplitude_eq_zeroAmplitude f]
  simp [ketMinus_apply]

/-- Balanced oracles have zero final `|0^n⟩` amplitude. -/
theorem zeroAmplitude_of_balanced (f : Oracle n) (hf : IsBalanced f) :
    zeroAmplitude f = 0 := by
  rw [zeroAmplitude, zeroAmplitudeNumerator_eq_card_sub]
  unfold IsBalanced at hf
  rw [hf]
  ring

/-- Constant oracles have final `|0^n⟩` amplitude exactly `1` or `-1`,
depending on the constant value. -/
theorem zeroAmplitude_of_constant (f : Oracle n) (hf : IsConstant f) :
    ∃ c : Bool, zeroAmplitude f = if c then (-1 : ℂ) else 1 := by
  rcases hf with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  cases c
  · rw [zeroAmplitude, zeroAmplitudeNumerator]
    simp [phaseSign, hc, Finset.sum_const, Fintype.card_fin]
  · rw [zeroAmplitude, zeroAmplitudeNumerator]
    simp [phaseSign, hc, Finset.sum_const, Fintype.card_fin]

/-- Constant oracles are reported as constant by the amplitude test. -/
theorem reportsConstant_of_constant (f : Oracle n) (hf : IsConstant f) :
    ReportsConstant f := by
  rcases zeroAmplitude_of_constant f hf with ⟨c, hc⟩
  rw [ReportsConstant, circuitZeroAmplitude_eq_zeroAmplitude_mul, hc]
  cases c <;> simp [invSqrt2_ne_zero]

/-- Balanced oracles are not reported as constant by the amplitude test. -/
theorem not_reportsConstant_of_balanced (f : Oracle n) (hf : IsBalanced f) :
    ¬ ReportsConstant f := by
  rw [ReportsConstant, circuitZeroAmplitude_eq_zeroAmplitude_mul,
    zeroAmplitude_of_balanced f hf]
  simp

/-- The final Deutsch-Jozsa joint state, annotated with one oracle query. -/
def timedFinalJointState (f : WalshHadamard.Oracle n) : Timed (PureState (n + 1)) :=
  Timed.trusted 1 (WalshHadamard.finalJointState f)

@[simp]
theorem timedFinalJointState_ret (f : WalshHadamard.Oracle n) :
    (timedFinalJointState f).ret = WalshHadamard.finalJointState f := rfl

@[simp]
theorem timedFinalJointState_time (f : WalshHadamard.Oracle n) :
    (timedFinalJointState f).time = 1 := rfl

/-- Public resource profile for the Deutsch-Jozsa circuit:
one oracle query and two `n`-qubit Hadamard layers plus the target Hadamard. -/
def resourceProfile (n : ℕ) : ResourceProfile where
  oracleQueries := 1
  hadamardGates := 2 * n + 1
  elementaryGates := 2 * n + 1
  classicalOps := 0

theorem resourceProfile_exact (n : ℕ) :
    ResourceProfile.HasExactCounts (resourceProfile n) 1 (2 * n + 1) (2 * n + 1) 0 := by
  simp [ResourceProfile.HasExactCounts, resourceProfile]

/-- The final Deutsch-Jozsa joint state with its public resource profile. -/
def profiledFinalJointState (f : WalshHadamard.Oracle n) :
    Profiled (PureState (n + 1)) :=
  Profiled.trusted (resourceProfile n) (WalshHadamard.finalJointState f)

@[simp]
theorem profiledFinalJointState_ret (f : WalshHadamard.Oracle n) :
    (profiledFinalJointState f).ret = WalshHadamard.finalJointState f := rfl

@[simp]
theorem profiledFinalJointState_resources (f : WalshHadamard.Oracle n) :
    (profiledFinalJointState f).resources = resourceProfile n := rfl

/-- The TimeM return value is the same final state used by the amplitude test. -/
theorem reportsConstant_iff_timedFinalJointState
    (f : WalshHadamard.Oracle n) :
    ReportsConstant f ↔
      (timedFinalJointState f).ret (prodEquiv (0, (0 : Fin (2 ^ 1)))) ≠ 0 := by
  rfl

/-- One Deutsch-Jozsa oracle query with the target qubit in `|-⟩` is the
phase query `|x⟩ ↦ (-1)^{f x}|x⟩`. -/
theorem deutschJozsa_query_phase (f : WalshHadamard.Oracle n) (x : Fin (2 ^ n)) :
    ((WalshHadamard.oracleGate f).apply ((ket x).tensor ketMinus)
        : StateVector (n + 1))
      =
      WalshHadamard.phaseSign f x
        • (((ket x).tensor ketMinus : PureState (n + 1)) : StateVector (n + 1)) := by
  exact PhaseKickback.main f x

/-- **Deutsch-Jozsa correctness**: under the explicit promise that the oracle
is constant or balanced, the one-query amplitude test reports "constant" iff
the oracle is constant. -/
theorem main (f : WalshHadamard.Oracle n)
    (hf : Promise f) :
    ReportsConstant f ↔ IsConstant f := by
  constructor
  · intro hreport
    rcases hf with hconstant | hbalanced
    · exact hconstant
    · exact False.elim ((not_reportsConstant_of_balanced f hbalanced) hreport)
  · intro hconstant
    exact reportsConstant_of_constant f hconstant

/-- Deutsch-Jozsa correctness, phrased through the TimeM return value. -/
theorem timedFinalJointState_correct
    (f : WalshHadamard.Oracle n) (hf : Promise f) :
    (timedFinalJointState f).ret (prodEquiv (0, (0 : Fin (2 ^ 1)))) ≠ 0 ↔
      IsConstant f := by
  rw [← reportsConstant_iff_timedFinalJointState f]
  exact main f hf

/-- Deutsch-Jozsa supporting theorem for the public statement: under the
constant/balanced promise, the profiled circuit decides the constant side
exactly and records the accepted exact resource counts. -/
theorem main_with_resources
    (f : WalshHadamard.Oracle n) (hf : Promise f) :
    ((profiledFinalJointState f).ret (prodEquiv (0, (0 : Fin (2 ^ 1)))) ≠ 0 ↔
      IsConstant f) ∧
      ResourceProfile.HasExactCounts (profiledFinalJointState f).resources
        1 (2 * n + 1) (2 * n + 1) 0 := by
  constructor
  · rw [profiledFinalJointState_ret]
    exact timedFinalJointState_correct f hf
  · simp [resourceProfile_exact n]

end DeutschJozsa

end

end QuantumAlg
