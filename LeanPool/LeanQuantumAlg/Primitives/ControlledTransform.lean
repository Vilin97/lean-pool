/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Cost
public import LeanPool.LeanQuantumAlg.Primitives.PhaseKickback
public import LeanPool.LeanQuantumAlg.Primitives.QSP

/-!
# Controlled-unitary transformation (quantum phase processing / QET)

Quantum phase processing (QPP) — equivalently quantum eigenvalue transformation
(QET) — applies a trigonometric transformation to the *eigenphases* of an
`n`-qubit unitary `U` by interleaving the controlled unitary `c-U` with
single-qubit processing rotations on one ancilla
[WZYW23, arxiv_v3.tex:601]. It is the multi-qubit generalization of the
single-qubit trigonometric QSP (`LeanPool.LeanQuantumAlg.Primitives.QSP.Fourier`), obtained
by **replacing the signal gate `R_Z(x)` of QSP with `c-U`**
[WZYW23, arxiv_v3.tex:632].

This module formalizes the eigenstate (decoupled) regime, where the target
holds an eigenstate `U|u⟩ = e^{iθ}|u⟩`. The whole construction then collapses
to single-qubit QSP at the signal `x = θ`:

- on `|u⟩`, the signal `c-U` acts on the ancilla as the controlled-phase gate
  `phaseGate θ = diag(1, e^{iθ})` (eigenvalue phase kickback), which is the QSP
  encoding gate `R_Z(θ) = rotZStd θ` up to the global phase `e^{iθ/2}`
  (`TransformationOnControlledUnitary.main_phase_gate_signal`);
- consequently the QPP word `qppYZZYZ U φ θ₀ φ₀ ps` (the YZZYZ trainable blocks
  interleaved with `c-U`) on `|ψ⟩ ⊗ |u⟩` equals
  `(e^{iθ/2})^L · (qspYZZYZ φ θ₀ φ₀ ps θ |ψ⟩) ⊗ |u⟩`, i.e. the single-qubit
  YZZYZ word evaluated at the eigenphase, tensored with the untouched
  eigenstate — the **eigenspace decomposition of QPP**
  [WZYW23, arxiv_v3.tex:641].

Composing with the QSP characterization `qsp_yzzyz_iff` gives the phase-evolution
guarantee [WZYW23, arxiv_v3.tex:650]: every trigonometric transform achievable
by single-qubit QSP is realized on the eigenphase of `U` by a QPP word
(`qpp_realizes_target`).

The number of `c-U` calls equals the number of QSP signal slots, so the global
phase here is `(e^{iθ/2})^L`; Wang's alternating `c-U`/`c-U†` convention instead
leaves only the parity phase `(e^{-iθ/2})^{L mod 2}`.

## Main results

- `LeanPool.LeanQuantumAlg.controlled_apply_eigenstate` — on an eigenstate,
  `c-U` acts on the ancilla as the QSP signal gate up to a global phase:
  `c-U (|ψ⟩ ⊗ |u⟩) = (e^{iθ/2} · rotZStd θ |ψ⟩) ⊗ |u⟩`.
- `LeanPool.LeanQuantumAlg.TransformationOnControlledUnitary.main_phase_gate_signal`
  — `diag(1, e^{iθ}) = e^{iθ/2} · R_Z(θ)`, the controlled-phase gate as the QSP
  encoding gate up to global phase.
- `LeanPool.LeanQuantumAlg.TransformationOnControlledUnitary.main` — the
  eigenspace decomposition: the QPP word on `|ψ⟩ ⊗ |u⟩` is
  `(e^{iθ/2})^L · (qspYZZYZ … θ |ψ⟩) ⊗ |u⟩`.
- `LeanPool.LeanQuantumAlg.qpp_realizes_target` — every `IsYZPair` transform is realized on
  the eigenphase by some QPP word.
-/

@[expose] public section

namespace QuantumAlg

open PureState

noncomputable section

variable {n : ℕ}

/-! ### Single-qubit ancilla decomposition and gate scalars -/

/-- A one-qubit state is its `|0⟩`/`|1⟩` coordinate combination. -/
theorem single_qubit_vec_decomp (ψ : StateVector 1) :
    ψ =
      (ψ 0) • (ket0 : StateVector 1) + (ψ 1) • (ket1 : StateVector 1) := by
  ext i
  fin_cases i <;>
    simp [ket0, ket1, ket_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem single_qubit_decomp (ψ : PureState 1) :
    (ψ : StateVector 1) =
      (ψ 0) • (ket0 : StateVector 1) + (ψ 1) • (ket1 : StateVector 1) :=
  single_qubit_vec_decomp (ψ : StateVector 1)

/-! ### The controlled-phase action of `c-U` on an eigenstate -/

/-- The controlled-phase gate `diag(1, e^{iθ})`: the action that `c-U` induces on
the ancilla when the target holds an eigenstate of eigenphase `θ`. -/
def phaseGateOp (θ : ℝ) : HilbertOperator 1 :=
  !![1, 0; 0, Complex.exp ((θ : ℝ) * Complex.I)]

theorem phaseGateOp_mem_unitaryGroup (θ : ℝ) :
    phaseGateOp θ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGateOp, Matrix.mul_apply, Matrix.star_apply, conj_exp_I,
      exp_I_mul_exp_neg_I]

/-- The controlled-phase gate induced on an ancilla by an eigenphase `θ`. -/
def phaseGate (θ : ℝ) : Gate 1 :=
  Gate.ofUnitary (phaseGateOp θ) (phaseGateOp_mem_unitaryGroup θ)

@[simp]
theorem phaseGate_apply_ket0 (θ : ℝ) : (phaseGate θ).apply ket0 = ket0 := by
  ext i
  rw [ket0, Gate.apply_ket]
  fin_cases i <;> simp [phaseGate, phaseGateOp, ket_apply]

@[simp]
theorem phaseGate_apply_ket1 (θ : ℝ) :
    (phaseGate θ).applyVec (ket1 : StateVector 1) =
      Complex.exp ((θ : ℝ) * Complex.I) • (ket1 : StateVector 1) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [Gate.applyVec, HilbertOperator.applyVec, phaseGate, phaseGateOp, ket1,
      PureState.ket, PiLp.smul_apply, smul_eq_mul]

/-- The controlled-phase gate on a general ancilla state. -/
theorem phaseGate_applyVec (θ : ℝ) (ψ : StateVector 1) :
    (phaseGate θ).applyVec ψ
      = (ψ 0) • (ket0 : StateVector 1) +
        (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : StateVector 1) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [Gate.applyVec, HilbertOperator.applyVec, phaseGate, phaseGateOp, ket0, ket1,
      PureState.ket, Matrix.vecHead, Matrix.vecTail, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]

theorem phaseGate_apply (θ : ℝ) (ψ : PureState 1) :
    (phaseGate θ).applyVec (ψ : StateVector 1)
      = (ψ 0) • (ket0 : StateVector 1) +
        (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : StateVector 1) :=
  phaseGate_applyVec θ (ψ : StateVector 1)

/-- **Controlled-phase factorization on an eigenstate.** When the target holds
an eigenstate `U|u⟩ = e^{iθ}|u⟩`, the controlled unitary `c-U` acts on
`|ψ⟩ ⊗ |u⟩` as the controlled-phase gate on the ancilla, leaving the
eigenstate fixed [WZYW23, arxiv_v3.tex:641]. -/
theorem controlled_apply_eigenstate_phaseVec (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n)) (ψ : StateVector 1) :
    (Gate.controlled U).applyVec
        (StateVector.tensor ψ (u : StateVector n)) =
      StateVector.tensor ((phaseGate θ).applyVec ψ)
        (u : StateVector n) := by
  calc
    (Gate.controlled U).applyVec
        (StateVector.tensor ψ (u : StateVector n))
        =
      (Gate.controlled U).applyVec
        (StateVector.tensor
          ((ψ 0) • (ket0 : StateVector 1) + (ψ 1) • (ket1 : StateVector 1))
          (u : StateVector n)) := by
        exact congrArg
          (fun v : StateVector 1 =>
            (Gate.controlled U).applyVec (StateVector.tensor v (u : StateVector n)))
          (single_qubit_vec_decomp ψ)
    _ =
      StateVector.tensor
        ((ψ 0) • (ket0 : StateVector 1) +
          (Complex.exp ((θ : ℝ) * Complex.I) * ψ 1) • (ket1 : StateVector 1))
        (u : StateVector n) := by
        rw [GeneralizedPhaseKickback.main U u θ hu (ψ 0) (ψ 1)]
    _ =
      StateVector.tensor ((phaseGate θ).applyVec ψ)
        (u : StateVector n) := by
        rw [phaseGate_applyVec]

theorem controlled_apply_eigenstate_phase (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n)) (ψ : PureState 1) :
    (Gate.controlled U).applyVec
        (StateVector.tensor (ψ : StateVector 1) (u : StateVector n)) =
      StateVector.tensor ((phaseGate θ).applyVec (ψ : StateVector 1))
        (u : StateVector n) :=
  controlled_apply_eigenstate_phaseVec U u θ hu (ψ : StateVector 1)

/-! ### The controlled-phase gate is the QSP signal gate up to global phase -/

/-- `diag(1, e^{iθ}) = e^{iθ/2} · R_Z(θ)`: the controlled-phase gate is the QSP
encoding gate `rotZStd θ = R_Z(θ)` up to the global phase `e^{iθ/2}`
[WZYW23, arxiv_v3.tex:632]. -/
theorem TransformationOnControlledUnitary.main_phase_gate_signal (θ : ℝ) :
    (phaseGate θ : HilbertOperator 1) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) • (rotZStd θ : HilbertOperator 1) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (1 : ℂ) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I)
        * Complex.exp ((-(θ / 2) : ℝ) * Complex.I)
    rw [show (1 : ℂ) = Complex.exp 0 from (Complex.exp_zero).symm, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · change (0 : ℂ) = Complex.exp ((θ / 2 : ℝ) * Complex.I) * 0
    ring
  · change (0 : ℂ) = Complex.exp ((θ / 2 : ℝ) * Complex.I) * 0
    ring
  · change Complex.exp ((θ : ℝ) * Complex.I) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I)
        * Complex.exp (-((-(θ / 2) : ℝ) * Complex.I))
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- `c-U` on a general ancilla, in QSP-signal form: the QSP encoding gate
`rotZStd θ` up to the global phase `e^{iθ/2}`. -/
theorem phaseGate_applyVec_eq_smul_rotZStd (θ : ℝ) (ψ : StateVector 1) :
    (phaseGate θ).applyVec ψ
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStd θ).applyVec ψ := by
  have h := congrArg
    (fun A : HilbertOperator 1 => HilbertOperator.applyVec A ψ)
    (TransformationOnControlledUnitary.main_phase_gate_signal θ)
  simpa [Gate.applyVec, HilbertOperator.smul_applyVec] using h

theorem phaseGate_apply_eq_smul_rotZStd (θ : ℝ) (ψ : PureState 1) :
    (phaseGate θ).applyVec (ψ : StateVector 1)
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStd θ).applyVec (ψ : StateVector 1) :=
  phaseGate_applyVec_eq_smul_rotZStd θ (ψ : StateVector 1)

/-- **Eigenstate reduction of `c-U` to the QSP signal.** On an eigenstate
`U|u⟩ = e^{iθ}|u⟩`, the controlled unitary acts as the QSP encoding gate at
signal `θ`, up to the global phase `e^{iθ/2}`:
`c-U (|ψ⟩ ⊗ |u⟩) = (e^{iθ/2} · R_Z(θ)|ψ⟩) ⊗ |u⟩` [WZYW23, arxiv_v3.tex:641]. -/
theorem TransformationOnControlledUnitary.main_eigenstate_reductionVec
    (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n)) (ψ : StateVector 1) :
    (Gate.controlled U).applyVec
        (StateVector.tensor ψ (u : StateVector n))
      = StateVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStd θ).applyVec ψ)
          (u : StateVector n) := by
  rw [controlled_apply_eigenstate_phaseVec U u θ hu, phaseGate_applyVec_eq_smul_rotZStd]

theorem TransformationOnControlledUnitary.main_eigenstate_reduction
    (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n)) (ψ : PureState 1) :
    (Gate.controlled U).applyVec
        (StateVector.tensor (ψ : StateVector 1) (u : StateVector n))
      = StateVector.tensor
          (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
            (rotZStd θ).applyVec (ψ : StateVector 1))
          (u : StateVector n) :=
  TransformationOnControlledUnitary.main_eigenstate_reductionVec U u θ hu
    (ψ : StateVector 1)

/-! ### The QPP word and its eigenspace decomposition -/

/-- The **quantum phase processor** in the YZZYZ (W-Z-W) convention: the QSP
word `qspYZZYZ` with each signal slot `R_Z(x)` replaced by the controlled
unitary `c-U`, the trainable blocks `R_Y(θⱼ)·R_Z(φⱼ)` acting on the ancilla
[WZYW23, arxiv_v3.tex:601]. -/
def qppYZZYZ (U : Gate n) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) : Gate (1 + n) :=
  ps.foldl
    (fun W p => W * (Gate.controlled U * Gate.tensor (rotY p.1 * rotZStd p.2) (1 : Gate n)))
    (Gate.tensor (rotZStd φ * (rotY θ₀ * rotZStd φ₀)) (1 : Gate n))

@[simp]
theorem qppYZZYZ_nil (U : Gate n) (φ θ₀ φ₀ : ℝ) :
    qppYZZYZ U φ θ₀ φ₀ []
      = Gate.tensor (rotZStd φ * (rotY θ₀ * rotZStd φ₀)) (1 : Gate n) :=
  rfl

theorem qppYZZYZ_concat (U : Gate n) (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (p : ℝ × ℝ) :
    qppYZZYZ U φ θ₀ φ₀ (ps ++ [p])
      = qppYZZYZ U φ θ₀ φ₀ ps
        * (Gate.controlled U * Gate.tensor (rotY p.1 * rotZStd p.2) (1 : Gate n)) := by
  simp [qppYZZYZ, List.foldl_append]

/-- **Eigenspace decomposition of QPP** [WZYW23, arxiv_v3.tex:641]. On an
eigenstate `U|u⟩ = e^{iθ}|u⟩`, the QPP word acts as the single-qubit YZZYZ QSP
word at the signal `θ`, tensored with the untouched eigenstate, up to the
global phase `(e^{iθ/2})^L` (`L` = number of `c-U` calls):
`qppYZZYZ U φ θ₀ φ₀ ps (|ψ⟩ ⊗ |u⟩)`
`= ((e^{iθ/2})^L · qspYZZYZ φ θ₀ φ₀ ps θ |ψ⟩) ⊗ |u⟩`. -/
theorem TransformationOnControlledUnitary.main (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) (ψ : StateVector 1) :
    (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
        (StateVector.tensor ψ (u : StateVector n))
      = StateVector.tensor
          ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ ps.length
            • (qspYZZYZ φ θ₀ φ₀ ps θ).applyVec ψ)
          (u : StateVector n) := by
  induction ps using List.reverseRecOn generalizing ψ with
  | nil =>
      rw [qppYZZYZ_nil, qspYZZYZ_nil, List.length_nil, pow_zero, one_smul,
        Gate.tensor_applyVec_tensor, Gate.one_applyVec]
  | append_singleton ps p ih =>
      rw [qppYZZYZ_concat, Gate.mul_applyVec, Gate.mul_applyVec,
        Gate.tensor_applyVec_tensor, Gate.one_applyVec,
        TransformationOnControlledUnitary.main_eigenstate_reductionVec U u θ hu, ih,
        qspYZZYZ_concat,
        List.length_append, List.length_singleton]
      congr 1
      rw [Gate.applyVec_smul, smul_smul, ← pow_succ, ← Gate.mul_applyVec,
        ← Gate.mul_applyVec, mul_assoc]

/-! ### Phase evolution: realizing QSP transforms on the eigenphase -/

/-- **Quantum phase evolution** [WZYW23, arxiv_v3.tex:650]. Every trigonometric
transform admissible for single-qubit QSP (an `IsYZPair L A B`) is realized on
the eigenphase of `U` by a QPP word with `L` controlled-unitary calls: there are
angles `(φ, θ₀, φ₀, ps)` such that the QPP word maps `|ψ⟩ ⊗ |u⟩` to
`((e^{iθ/2})^L · qspMatYZ L A B θ |ψ⟩) ⊗ |u⟩` for every ancilla state. -/
theorem TransformationOnControlledUnitary.main_realizes_target
    (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧ ∀ ψ : PureState 1,
      (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
          (StateVector.tensor (ψ : StateVector 1) (u : StateVector n))
        = StateVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L
              • HilbertOperator.applyVec (qspMatYZ L A B θ) (ψ : StateVector 1))
            (u : StateVector n) := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ :=
    (TrigonometricQuantumSignalProcessing.main L A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, fun ψ => ?_⟩
  rw [TransformationOnControlledUnitary.main U u θ hu, hlen]
  have happly := congrArg
    (fun A : HilbertOperator 1 => HilbertOperator.applyVec A (ψ : StateVector 1))
    (hmat θ)
  simpa [Gate.applyVec] using congrArg
    (fun v : StateVector 1 =>
      StateVector.tensor
        ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L • v)
        (u : StateVector n))
    happly

/-- Trusted resource profile for the YZZYZ QPP word currently formalized here:
`L` controlled-`U` signal calls and `2L+3` one-qubit processing rotations. -/
def qppYZZYZResourceProfile (L : ℕ) : ResourceProfile where
  oracleQueries := L
  hadamardGates := 0
  elementaryGates := 2 * L + 3
  classicalOps := 0

theorem qppYZZYZResourceProfile_exact (L : ℕ) :
    ResourceProfile.HasExactCounts
      (qppYZZYZResourceProfile L) L 0 (2 * L + 3) 0 := by
  simp [ResourceProfile.HasExactCounts, qppYZZYZResourceProfile]

/-- QPP realization paired with the resource profile of the YZZYZ convention
formalized in this file. Conventions with alternating `controlled-U` and
`controlled-U†` have a different resource profile. -/
theorem qpp_realizes_target_with_resources (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    (∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧ ∀ ψ : PureState 1,
      (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
          (StateVector.tensor (ψ : StateVector 1) (u : StateVector n))
        = StateVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L
              • HilbertOperator.applyVec (qspMatYZ L A B θ) (ψ : StateVector 1))
            (u : StateVector n)) ∧
      ResourceProfile.HasExactCounts (qppYZZYZResourceProfile L) L 0 (2 * L + 3) 0 := by
  constructor
  · exact TransformationOnControlledUnitary.main_realizes_target U u θ hu L A B h
  · exact qppYZZYZResourceProfile_exact L

/-- Resource profile for the alternating controlled-`U` /
controlled-`U†` presentation of the QPP transform: `2L` controlled-unitary
queries and `4L+3` one-qubit processing rotations. This is a trusted resource
annotation for the source-level statement; the gate-level word formalized above
is the YZZYZ convention. -/
def qppAlternatingControlledResourceProfile (L : ℕ) : ResourceProfile where
  oracleQueries := 2 * L
  hadamardGates := 0
  elementaryGates := 4 * L + 3
  classicalOps := 0

theorem qppAlternatingControlledResourceProfile_exact (L : ℕ) :
    ResourceProfile.HasExactCounts
      (qppAlternatingControlledResourceProfile L) (2 * L) 0 (4 * L + 3) 0 := by
  simp [ResourceProfile.HasExactCounts, qppAlternatingControlledResourceProfile]

/-- QPP realization paired with the alternating controlled resource convention. The
realization component is the current eigenstate reduction to YZZYZ QSP; the
resource component records the source-level alternating controlled-`U` /
controlled-`U†` convention used by the source-level resource claim. -/
theorem qpp_realizes_target_with_alternating_controlled_resources
    (U : Gate n) (u : PureState n) (θ : ℝ)
    (hu : U.applyVec (u : StateVector n) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : StateVector n))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    (∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧ ∀ ψ : PureState 1,
      (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
          (StateVector.tensor (ψ : StateVector 1) (u : StateVector n))
        = StateVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L
              • HilbertOperator.applyVec (qspMatYZ L A B θ) (ψ : StateVector 1))
            (u : StateVector n)) ∧
      ResourceProfile.HasExactCounts
        (qppAlternatingControlledResourceProfile L) (2 * L) 0 (4 * L + 3) 0 := by
  constructor
  · exact TransformationOnControlledUnitary.main_realizes_target U u θ hu L A B h
  · exact qppAlternatingControlledResourceProfile_exact L

end

end QuantumAlg
