/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Proofs.Stafford38Reduction
public import LeanPool.Stafford38.Proofs.WeylSymplectic


/-!
# The universal Stafford 3.8 target

This file owns the exact theorem statement that the end-to-end formalization
must eventually prove. It intentionally declares no theorem with an unproved
hypothesis and introduces no project axiom.
-/

@[expose] public section

namespace Stafford38

/-- The presented `n`th Weyl algebra with its standard symplectic form. -/
abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  Stafford.FreeWeyl k (Fin n ⊕ Fin n) (Matrix.J (Fin n) k)

/-- Exact proposition required for the publication theorem. -/
def UniversalStatement : Prop :=
  ∀ (k : Type*) [Field k] [CharZero k] (n : ℕ) (d : WeylAlg k n),
    d ≠ 0 → ∃ F R S : WeylAlg k n, (1 : WeylAlg k n) = d * R + F * d * S

end Stafford38
