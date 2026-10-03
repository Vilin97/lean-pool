/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CellAtlas
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.PrimeBoundary

/-!
# Fox–Neuwirth prime configuration model

This file records existence of the concrete compact Fox–Neuwirth model
constructed in `CellAtlas`, with its free prime-symmetry action and equivariant
map to labelled configurations.

The signed cellular cycle, orientation comparison, and nonzero orbit count are not postulated here.
They provide the finite model used by the obstruction argument.
-/

public section

namespace NRR

variable {p : ℕ}

/-- Public existence statement for the concrete compact model. -/
theorem primeConfigurationModel_exists_of_prime
    (hp : Nat.Prime p) :
    ∃ M : PrimeConfigurationModel hp,
      M = foxNeuwirthTopCellModel hp :=
  ⟨foxNeuwirthTopCellModel hp, rfl⟩

end NRR
