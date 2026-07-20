/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Index plumbing for `Fin (2 ^ n)` registers (quantum-free)

The big-endian pairing of computational-basis labels used to compose qubit
registers, factored out of the quantum framework so it carries no dependency
on `Gate`/`PureState`.

## Main definition

- `LeanPool.LeanQuantumAlg.prodEquiv` — `Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n))`,
  `(x, y) ↦ y + 2 ^ n * x`, so the first (lower-qubit-index) factor carries
  the most significant bits.

Pinned Mathlib API: `finProdFinEquiv` (`(x, y) ↦ y + n * x`), `finCongr`.
-/

@[expose] public section

namespace QuantumAlg

variable {m n : ℕ}

/-- Big-endian pairing of basis labels: `(x, y) ↦ y + 2 ^ n * x`, so the
first (lower-qubit-index) factor carries the most significant bits. -/
def prodEquiv : Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n)) :=
  finProdFinEquiv.trans (finCongr (pow_add (2 : ℕ) m n).symm)

end QuantumAlg
