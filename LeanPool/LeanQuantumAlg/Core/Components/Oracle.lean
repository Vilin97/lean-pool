/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Tensor

/-!
# Boolean (XOR) oracles

Standard quantum-circuit access to a Boolean function
`f : Fin (2 ^ n) → Bool`: the XOR (bit-flip) oracle on `n + 1` qubits,

`U_f |x⟩|b⟩ = |x⟩|b ⊕ f(x)⟩`,

the unitary query form `O_x : |i, b⟩ ↦ |i, b ⊕ xᵢ⟩` of
[dW19, qcnotes.tex:1151].

## Conventions

- An oracle is **not a new kind of object**: it is just a `Gate (n + 1)`,
  built as a basis permutation (`Gate.ofPerm`), hence unitary for free —
  "in matrix representation [it] is a permutation matrix and hence unitary"
  [dW19, qcnotes.tex:1154].
- Register layout matches `LeanPool.LeanQuantumAlg.prodEquiv` (big-endian): input register
  = qubits `0..n-1` (most significant bits), target qubit = qubit `n` (least
  significant bit); the joint basis label is `prodEquiv (x, b)`.
- The bit flip on the target label `b : Fin (2 ^ 1)` is `Fin.rev`
  (`0 ↦ 1, 1 ↦ 0`), so `if f x then b.rev else b` is exactly `b ⊕ f x`.

## Main definitions

- `LeanPool.LeanQuantumAlg.Gate.xorPerm f` — the basis involution `(x, b) ↦ (x, b ⊕ f x)`.
- `LeanPool.LeanQuantumAlg.Gate.xorOracle f` — the oracle gate `U_f : Gate (n + 1)`;
  `xorOracle_apply_ket` computes its action on basis kets and
  `xorOracle_mem_unitaryGroup` gives unitarity.

Pinned Mathlib API: `Equiv.permCongr` (`permCongr_apply`), `Fin.rev`
(`Fin.rev_rev`), `Equiv.apply_eq_iff_eq`, `Equiv.apply_eq_iff_eq_symm_apply`,
`Equiv.symm_apply_eq`.
-/

@[expose] public section

namespace QuantumAlg

namespace Gate

open PureState

noncomputable section

variable {n : ℕ}

/-- The basis involution underlying the XOR oracle:
`(x, b) ↦ (x, b ⊕ f x)`, with the bit flip written as `Fin.rev`. -/
def xorPerm (f : Fin (2 ^ n) → Bool) :
    Equiv.Perm (Fin (2 ^ n) × Fin (2 ^ 1)) where
  toFun p := (p.1, if f p.1 then p.2.rev else p.2)
  invFun p := (p.1, if f p.1 then p.2.rev else p.2)
  left_inv p := by by_cases h : f p.1 <;> simp [h]
  right_inv p := by by_cases h : f p.1 <;> simp [h]

@[simp]
theorem xorPerm_apply (f : Fin (2 ^ n) → Bool) (p : Fin (2 ^ n) × Fin (2 ^ 1)) :
    xorPerm f p = (p.1, if f p.1 then p.2.rev else p.2) :=
  rfl

/-- The XOR oracle is an involution. -/
@[simp]
theorem xorPerm_symm (f : Fin (2 ^ n) → Bool) : (xorPerm f).symm = xorPerm f :=
  rfl

/-- The XOR (bit-flip) oracle of `f`, as a permutation gate on `n + 1`
qubits: `U_f |x⟩|b⟩ = |x⟩|b ⊕ f(x)⟩` (input register first/most significant,
target qubit last/least significant). -/
def xorOracle (f : Fin (2 ^ n) → Bool) : Gate (n + 1) :=
  ofPerm (prodEquiv.permCongr (xorPerm f))

theorem xorOracle_mem_unitaryGroup (f : Fin (2 ^ n) → Bool) :
    (xorOracle f : HilbertOperator (n + 1))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (n + 1))) ℂ :=
  (xorOracle f).unitary

theorem xorOracle_apply (f : Fin (2 ^ n) → Bool) (ψ : PureState (n + 1))
    (i : Fin (2 ^ (n + 1))) :
    (xorOracle f).apply ψ i = ψ (prodEquiv (xorPerm f (prodEquiv.symm i))) := by
  rw [xorOracle, ofPerm_apply, Equiv.permCongr_apply]

/-- Action on basis kets: `U_f |x⟩|b⟩ = |x⟩|b ⊕ f(x)⟩`. -/
theorem xorOracle_apply_ket (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n))
    (b : Fin (2 ^ 1)) :
    (xorOracle f).apply (ket (prodEquiv (x, b)))
      = ket (prodEquiv (x, if f x then b.rev else b)) := by
  rw [xorOracle, ofPerm_apply_ket]
  congr 1
  change prodEquiv ((xorPerm f).symm (prodEquiv.symm (prodEquiv (x, b))))
      = prodEquiv (x, if f x then b.rev else b)
  rw [Equiv.symm_apply_apply, xorPerm_symm, xorPerm_apply]

end

end Gate

end QuantumAlg
