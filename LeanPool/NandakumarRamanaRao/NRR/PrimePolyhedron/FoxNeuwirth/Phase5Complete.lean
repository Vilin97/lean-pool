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

This file packages finite Fox--Neuwirth combinatorics, a concrete
compact `(p - 1)`-simplex atlas with a free prime-symmetry action, an equivariant map to labelled
configurations, and the first-coordinate zero-sum reference map.

The signed cellular cycle, orientation comparison, and nonzero orbit count are not postulated here.
They provide the finite model used by the obstruction argument.
-/

@[expose] public section

namespace NRR

variable {p : ℕ}

/-- Proof-carrying statement of the Fox–Neuwirth model layer. -/
structure FoxNeuwirthPhase5Data (hp : Nat.Prime p) where
  /-- The prime configuration model realized by the Fox–Neuwirth construction. -/
  model : PrimeConfigurationModel hp
  /-- The finite type of top cells in the model layer. -/
  topCell : Type
  [topCellFintype : Fintype topCell]
  [topCellDecidableEq : DecidableEq topCell]
  /-- The dimension function on the model's top cells. -/
  cellDimension : topCell → ℕ
  top_dimension : ∀ c, cellDimension c = p - 1
  hasConcreteModel : model = foxNeuwirthTopCellModel hp

attribute [instance]
  FoxNeuwirthPhase5Data.topCellFintype
  FoxNeuwirthPhase5Data.topCellDecidableEq

/-- Canonical Fox–Neuwirth data for every prime. -/
noncomputable def foxNeuwirthPhase5Data
    (hp : Nat.Prime p) : FoxNeuwirthPhase5Data hp where
  model := foxNeuwirthTopCellModel hp
  topCell := FoxNeuwirthTopCell p
  cellDimension := fun _ => p - 1
  top_dimension := fun _ => rfl
  hasConcreteModel := rfl

/-- The Fox–Neuwirth construction exists for every prime. -/
theorem foxNeuwirthPhase5_complete
    (hp : Nat.Prime p) :
    Nonempty (FoxNeuwirthPhase5Data hp) :=
  ⟨foxNeuwirthPhase5Data hp⟩

/-- Public existence statement for the concrete compact model. -/
theorem primeConfigurationModel_exists_of_prime
    (hp : Nat.Prime p) :
    ∃ M : PrimeConfigurationModel hp,
      M = foxNeuwirthTopCellModel hp :=
  ⟨foxNeuwirthTopCellModel hp, rfl⟩

end NRR
