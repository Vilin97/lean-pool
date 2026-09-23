/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import LeanPool.LowWeightPauliDynamics.Pauli.Coeff

/-!
# The entrywise Pauli model as a genuine tensor product

`def:pauli_basis` builds the Pauli basis from tensor products of the one-qubit matrices `I`, `X`,
`Y`, `Z`, whereas this library computes with an entrywise model `toMatrix`. This file proves that
the two agree: `toMatrix s` is a power of `i` times the Kronecker product of the single-qubit
Pauli matrices of `s`.

The one-qubit matrices are specified independently, by their entries, and `tensorPauli` is built
recursively from Mathlib's Kronecker product. The comparison with `toMatrix` keeps the phase: the
positive tensor has phase exponent equal to the number of `Y` sites modulo four (`yPhase`),
whereas `herm` uses only the parity of that number. In particular, for two `Y` sites the two
representatives differ by a minus sign.

The algebra equivalence `bitsMatrixEquiv` at the end is noncomputable. It identifies the algebra
of matrices indexed by bit strings with the `2^n` by `2^n` matrices, without singling out a
binary or lexicographic ordering of the bit strings.

## Main definitions

* `qubitX`, `qubitY`, `qubitZ`, `qubitPauli`: the one-qubit Pauli matrices, by their entries.
* `tensorPauli n x z`: the iterated Kronecker product of the one-qubit Paulis with bits `x`, `z`.
* `yPhase x z`: the number of `Y` sites, modulo four.
* `tensorRepresentative p`: the Pauli string of class `p` whose matrix is `tensorPauli`.
* `bitsMatrixEquiv n`: matrices indexed by `Bits n` as matrices indexed by `Fin (2 ^ n)`.

## Main results

* `toMatrix_eq_phase_tensor`:
  `toMatrix s = iPow (s.phase - yPhase s.x s.z) • tensorPauli n s.x s.z`.
* `toMatrix_tensorRepresentative`: `toMatrix (tensorRepresentative p) = tensorPauli n p.1 p.2`.
* `isSelfAdjoint_tensorRepresentative`, `isSelfAdjoint_tensorPauli`: the positive tensors are
  Hermitian.
* `trace_star_tensorPauli_mul`, `trace_tensorPauli_mul`: they are orthogonal for the trace
  pairing, with `Tr (P Q) = 2 ^ n` if `P = Q` and `0` otherwise.
* `bitsMatrixEquiv_star`: the change of index type preserves the adjoint.
-/

namespace Lean4LPD.PauliString

open Matrix Finset

/-- The one-qubit X matrix in `def:pauli_basis`. -/
def qubitX : Matrix (ZMod 2) (ZMod 2) ℂ := ![![0, 1], ![1, 0]]

/-- The one-qubit Y matrix in `def:pauli_basis`. -/
def qubitY : Matrix (ZMod 2) (ZMod 2) ℂ := ![![0, -Complex.I], ![Complex.I, 0]]

/-- The one-qubit Z matrix in `def:pauli_basis`. -/
def qubitZ : Matrix (ZMod 2) (ZMod 2) ℂ := ![![1, 0], ![0, -1]]

/-- The positive I/X/Z/Y representative of the local binary class, as in
`def:pauli_basis`. -/
def qubitPauli (x z : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  if x = 0 then (if z = 0 then 1 else qubitZ) else (if z = 0 then qubitX else qubitY)

/-- The phase-free one-qubit factor `X^x Z^z`, by its entries. This is the local factor of the
entrywise model `toMatrix`; at `x = z = 1` it equals `-iY`, not the `Y` of `def:pauli_basis`. -/
noncomputable def qubitXZ (x z : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun a b => if a = b + x then negOnePow (z * b) else 0

/-- The one-qubit phase correction: `X^x Z^z` is `i ^ (-(x z))` times the positive Pauli
matrix of `def:pauli_basis`. Only the `Y` site `x = z = 1` carries a nontrivial phase. -/
theorem qubitXZ_eq_phase_qubitPauli (x z : ZMod 2) :
    qubitXZ x z = iPow (-((x * z).val : ZMod 4)) • qubitPauli x z := by
  ext a b
  rw [Matrix.smul_apply, smul_eq_mul]
  have cases2 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  rcases cases2 x with rfl | rfl <;> rcases cases2 z with rfl | rfl <;>
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 1 = Complex.I ^ 0 * (-1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 0 * (1)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 0 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 3 * (0)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 1 = Complex.I ^ 3 * (-Complex.I)
    norm_num [pow_succ, Complex.I_sq]
  · change (-1 : ℂ) ^ 0 = Complex.I ^ 3 * (Complex.I)
    norm_num [pow_succ, Complex.I_sq]
  · change (0 : ℂ) = Complex.I ^ 3 * (0)
    norm_num [pow_succ, Complex.I_sq]

/-- The exact Y-site phase modulo four, finer than the parity used by `herm`.
This is the positive tensor-product convention in `def:pauli_basis`. -/
def yPhase {n : ℕ} (x z : Bits n) : ZMod 4 := ∑ i, ((x i * z i).val : ZMod 4)

/-- Head/tail decomposition of the Y-site phase, supporting `def:pauli_basis`. -/
theorem yPhase_succ {n : ℕ} (x z : Bits (n + 1)) :
    yPhase x z = ((x 0 * z 0).val : ZMod 4) + yPhase (Fin.tail x) (Fin.tail z) := by
  simp only [yPhase, Fin.sum_univ_succ, Fin.tail]

/-- Iterated, genuine Kronecker product of the independently specified one-qubit Paulis.
The empty tensor is the one-by-one identity (`def:pauli_basis`). -/
noncomputable def tensorPauli : (n : ℕ) → Bits n → Bits n → Matrix (Bits n) (Bits n) ℂ
  | 0, _, _ => 1
  | n + 1, x, z =>
      Matrix.reindex (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2))
        (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2))
        ((qubitPauli (x 0) (z 0)).kronecker (tensorPauli n (Fin.tail x) (Fin.tail z)))

/-- The bit-indexed tensor product acts by the local matrix entry times its tail entry,
as required by `def:pauli_basis`. -/
theorem tensorPauli_succ_apply {n : ℕ} (x z a b : Bits (n + 1)) :
    tensorPauli (n + 1) x z a b =
      qubitPauli (x 0) (z 0) (a 0) (b 0) *
        tensorPauli n (Fin.tail x) (Fin.tail z) (Fin.tail a) (Fin.tail b) := rfl

/-- Drop the first tensor factor, retaining the global phase in the remaining string;
an auxiliary definition for `def:pauli_basis`. -/
def dropFirst {n : ℕ} (s : PauliString (n + 1)) : PauliString n :=
  ⟨Fin.tail s.x, Fin.tail s.z, s.phase⟩

/-- The entrywise model factors into a one-qubit X^x Z^z entry and its tail. This is the
algebraic step relating `toMatrix` to `def:pauli_basis`. -/
theorem toMatrix_split {n : ℕ} (s : PauliString (n + 1)) (a b : Bits (n + 1)) :
    toMatrix s a b = qubitXZ (s.x 0) (s.z 0) (a 0) (b 0) *
      toMatrix (dropFirst s) (Fin.tail a) (Fin.tail b) := by
  have heq : a = b + s.x ↔ a 0 = b 0 + s.x 0 ∧
      Fin.tail a = Fin.tail b + Fin.tail s.x := by
    constructor
    · intro h
      exact ⟨congrFun h 0, funext fun i => congrFun h i.succ⟩
    · rintro ⟨h0, ht⟩
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun ht j
  have hdot : s.z ⬝ᵥ b = s.z 0 * b 0 + (Fin.tail s.z ⬝ᵥ Fin.tail b) := by
    simp only [dotProduct, Fin.sum_univ_succ, Fin.tail]
  simp only [toMatrix_apply, dropFirst, qubitXZ, hdot, negOnePow_add]
  by_cases h0 : a 0 = b 0 + s.x 0 <;>
    by_cases ht : Fin.tail a = Fin.tail b + Fin.tail s.x
  · rw [ite_eq_left (heq.mpr ⟨h0, ht⟩), ite_eq_left h0, ite_eq_left ht]
    ring
  · rw [ite_eq_right (fun h => ht (heq.mp h).2), ite_eq_left h0, ite_eq_right ht]
    ring
  · rw [ite_eq_right (fun h => h0 (heq.mp h).1), ite_eq_right h0, ite_eq_left ht]
    ring
  · rw [ite_eq_right (fun h => h0 (heq.mp h).1), ite_eq_right h0, ite_eq_right ht]
    ring

/-- **The matrix model is the phase-corrected tensor product of Pauli matrices.** For every
Pauli string `s`, `toMatrix s` is `i ^ (s.phase - yPhase s.x s.z)` times the Kronecker product
of the one-qubit Pauli matrices of `def:pauli_basis`. The identification of the entrywise model
with a tensor product is thus a theorem, not an assumption. -/
theorem toMatrix_eq_phase_tensor : ∀ {n : ℕ} (s : PauliString n),
    toMatrix s = iPow (s.phase - yPhase s.x s.z) • tensorPauli n s.x s.z := by
  intro n
  induction n with
  | zero =>
      intro s
      ext a b
      have hab : a = b + s.x := Subsingleton.elim _ _
      have hab' : a = b := Subsingleton.elim _ _
      rw [Matrix.smul_apply, smul_eq_mul, toMatrix_apply, ite_eq_left hab]
      simp only [tensorPauli, Matrix.one_apply, ite_eq_left hab', mul_one]
      simp [yPhase, dotProduct]
  | succ n ih =>
      intro s
      ext a b
      rw [toMatrix_split, qubitXZ_eq_phase_qubitPauli]
      rw [ih (dropFirst s)]
      simp only [Matrix.smul_apply, smul_eq_mul, tensorPauli_succ_apply, dropFirst]
      have hphase : iPow (-((s.x 0 * s.z 0).val : ZMod 4)) *
          iPow (s.phase - yPhase (Fin.tail s.x) (Fin.tail s.z)) =
          iPow (s.phase - yPhase s.x s.z) := by
        rw [← iPow_add, yPhase_succ]
        congr 1
        ring
      calc
        (iPow (-((s.x 0 * s.z 0).val : ZMod 4)) * qubitPauli (s.x 0) (s.z 0) (a 0) (b 0)) *
            (iPow (s.phase - yPhase (Fin.tail s.x) (Fin.tail s.z)) *
              tensorPauli n (Fin.tail s.x) (Fin.tail s.z) (Fin.tail a) (Fin.tail b)) =
            (iPow (-((s.x 0 * s.z 0).val : ZMod 4)) *
              iPow (s.phase - yPhase (Fin.tail s.x) (Fin.tail s.z))) *
                (qubitPauli (s.x 0) (s.z 0) (a 0) (b 0) *
                  tensorPauli n (Fin.tail s.x) (Fin.tail s.z) (Fin.tail a) (Fin.tail b)) := by ring
        _ = _ := by rw [hphase]

/-- The positive tensor representative of a signless class, as in `def:pauli_basis`. Unlike
`herm`, its phase is the full count of `Y` sites modulo four, not only the parity. -/
def tensorRepresentative {n : ℕ} (p : PauliIndex n) : PauliString n :=
  ⟨p.1, p.2, yPhase p.1 p.2⟩

/-- The matrix of the positive tensor representative is exactly the tensor product of Pauli
matrices of `def:pauli_basis`, with no residual sign or phase. -/
theorem toMatrix_tensorRepresentative {n : ℕ} (p : PauliIndex n) :
    toMatrix (tensorRepresentative p) = tensorPauli n p.1 p.2 := by
  rw [toMatrix_eq_phase_tensor]
  simp [tensorRepresentative]

/-- Doubling the full Y-count phase gives the symplectic sign. This verifies the
Hermiticity convention for the positive tensor basis of `def:pauli_basis`. -/
theorem two_mul_yPhase : ∀ {n : ℕ} (x z : Bits n),
    2 * yPhase x z = signPhase (z ⬝ᵥ x) := by
  intro n
  induction n with
  | zero => intro x z; simp [yPhase, dotProduct, signPhase]
  | succ n ih =>
      intro x z
      have hdot : z ⬝ᵥ x = z 0 * x 0 + (Fin.tail z ⬝ᵥ Fin.tail x) := by
        simp only [dotProduct, Fin.sum_univ_succ, Fin.tail]
      rw [yPhase_succ, mul_add, ih, hdot, signPhase_add]
      congr 1
      simp only [signPhase, mul_comm (x 0) (z 0)]

/-- Positive tensor representatives are genuine Hermitian Pauli strings, not just tensors
identified up to a freely chosen phase (`def:pauli_basis`). -/
theorem isSelfAdjoint_tensorRepresentative {n : ℕ} (p : PauliIndex n) :
    IsSelfAdjoint (tensorRepresentative p) := by
  apply isSelfAdjoint_iff_phase.2
  exact (two_mul_yPhase p.1 p.2).symm

/-- The positive tensor representative has the intended signless class
(`def:pauli_basis`). -/
@[simp] theorem cls_tensorRepresentative {n : ℕ} (p : PauliIndex n) :
    cls (tensorRepresentative p) = p := rfl

/-- The literal tensor Pauli is self-adjoint, as required by `def:pauli_basis`. -/
theorem isSelfAdjoint_tensorPauli {n : ℕ} (p : PauliIndex n) :
    IsSelfAdjoint (tensorPauli n p.1 p.2) := by
  rw [← toMatrix_tensorRepresentative]
  exact star_toMatrix_of_isSelfAdjoint (isSelfAdjoint_tensorRepresentative p)

/-- Orthogonality of the positive tensor Pauli family, in the unnormalized convention of
`def:pauli_basis`. The normalized statement divides this pairing by `2^n`. -/
theorem trace_star_tensorPauli_mul {n : ℕ} (p q : PauliIndex n) :
    (star (tensorPauli n p.1 p.2) * tensorPauli n q.1 q.2).trace =
      if p = q then (2 : ℂ) ^ n else 0 := by
  rw [← toMatrix_tensorRepresentative, ← toMatrix_tensorRepresentative]
  by_cases h : p = q
  · subst q
    rw [trace_star_toMatrix_mul_self, ite_eq_left rfl]
  · rw [ite_eq_right h]
    apply trace_star_toMatrix_mul_eq_zero
    intro hpq
    exact h (Prod.ext hpq.1 hpq.2)

/-- The Hermitian form of the positive tensor Pauli trace pairing in `def:pauli_basis`. -/
theorem trace_tensorPauli_mul {n : ℕ} (p q : PauliIndex n) :
    (tensorPauli n p.1 p.2 * tensorPauli n q.1 q.2).trace =
      if p = q then (2 : ℂ) ^ n else 0 := by
  have h := trace_star_tensorPauli_mul p q
  rw [show star (tensorPauli n p.1 p.2) = tensorPauli n p.1 p.2 from
    isSelfAdjoint_tensorPauli p] at h
  exact h

/-- A noncomputable numbering of the bit strings by `Fin (2^n)`, matching the matrix dimension
`2^n` of `def:pauli_basis`. The bijection is unspecified: no particular order, such as the
lexicographic one, is asserted. -/
noncomputable def bitsEquivFin (n : ℕ) : Bits n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (card_bits n)

/-- The bit-indexed and dimension-indexed matrix algebras are isomorphic, the type-level
bridge needed by `def:pauli_basis`. -/
noncomputable def bitsMatrixEquiv (n : ℕ) :
    Matrix (Bits n) (Bits n) ℂ ≃ₐ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (bitsEquivFin n)

/-- The change of computational-basis indexing preserves the adjoint as well as the algebra
operations (`def:pauli_basis`). -/
theorem bitsMatrixEquiv_star (n : ℕ) (A : Matrix (Bits n) (Bits n) ℂ) :
    bitsMatrixEquiv n (star A) = star (bitsMatrixEquiv n A) := rfl

end Lean4LPD.PauliString
