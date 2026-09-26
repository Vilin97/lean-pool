/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.HilbertPairingPerfect
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.LocalHilbertPairingExists
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.PowerClassGroupFinite
public import Mathlib.NumberTheory.LocalField.Basic
/-!
# A perfect local Hilbert pairing

For a nonarchimedean local field in which `n` is nonzero and the `n`-th
roots of unity are present, the Hilbert pairing identifies power classes
with all `μₙ`-valued characters of the power-class group.
-/

@[expose] public section

namespace ClassFieldTheory

universe u

/-- There is a local Hilbert pairing whose adjoint map to the full
`μₙ`-valued character group is bijective. -/
theorem exists_perfectLocalHilbertPairing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ B : HilbertPairing K n,
      B.IsLocalHilbertPairing ∧ Function.Bijective B := by
  let : Finite (PowerClassGroup K n) :=
    powerClassGroup_finite K n hnK
  obtain ⟨B, hB⟩ := exists_localHilbertPairing K n hnK hmu
  refine ⟨B, hB, ?_⟩
  exact hB.2.2.1.bijective hmu

end ClassFieldTheory
