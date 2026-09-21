/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismStableRelativeBoundary
/-!
# Stable collar comparison

This module isolates the exact finite theorem needed to compare two externally supplied
`StableRegularApproximation`s.  A stable collar is a compatible prime-equivariant generic prism
whose horizontal samples are fixed to the two supplied endpoint approximations.  The global signed
prism-facet cancellation already proved for `RelativeResult` then identifies their positive-ray
counts.

The theorem proved here is the finite Stokes statement for such a collar.  Existence of a stable
collar for arbitrary endpoint triangulations is deliberately separated as
`StableCollarExistenceTheorem`; constructing it requires a relative triangulation/perturbation which
leaves both endpoint triangulations unchanged.
-/

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary

open EquivariantCoordinateHomotopy
open EquivariantPrismGenericPerturbation
open RefinedAffineMap

variable {p : Nat}

/-- A finite generic prism collar whose two horizontal boundaries are prescribed stable
approximations.  The boundary-fixing field includes the necessary equality of endpoint levels with
the horizontal triangulation level `N + L`. -/
structure StableCollar
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  N : Nat
  L : Nat
  m : Real
  positive : 0 < m
  prism : Result hp N L H m
  boundaryFixed : BoundaryFixed hp N L A₀ A₁ prism.assignment

namespace StableCollar

/-- Regard a stable collar as a boundary-relative prism result. -/
noncomputable def toRelativeResult
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁) :
    RelativeResult hp C.N C.L H C.m where
  prism := C.prism
  lower := A₀
  upper := A₁
  boundaryFixed := C.boundaryFixed

/-- Finite stable-collar Stokes theorem: the two prescribed transverse horizontal boundaries have
the same positive-ray count. -/
theorem zeroCount_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁) :
    A₀.zeroCount = A₁.zeroCount := by
  exact (C.toRelativeResult).stable_zeroCount_eq hp C.N C.L H C.m

end StableCollar

/-- Proposition asserting that every pair of stable endpoint approximations admits a finite
boundary-fixed generic collar.  This is the relative-triangulation existence statement used with the finite Stokes theorem. -/
def StableCollarExistenceTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (StableCollar hp H A₀ A₁)

/-- The finite collar comparison theorem, packaged as a reusable proposition. -/
def StableCollarComparisonTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (C : StableCollar hp H A₀ A₁),
      A₀.zeroCount = A₁.zeroCount

/-- The stable collar comparison proposition is proved by global signed prism cancellation. -/
theorem stableCollarComparisonTheorem : StableCollarComparisonTheorem := by
  intro p hp F₀ F₁ H A₀ A₁ C
  exact C.zeroCount_eq

/-- Existence of stable collars implies the stable homotopy-invariance theorem. -/
theorem stableHomotopyInvariance_of_collarExistence
    (HC : StableCollarExistenceTheorem) :
    StableHomotopyInvarianceTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact (Classical.choice (HC hp F₀ F₁ H A₀ A₁)).zeroCount_eq

/-- Every canonical boundary-relative result constructed from a generic prism is itself a stable
collar between its two induced stable endpoint approximations. -/
noncomputable def RelativeResult.toStableCollar
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    {m : Real} (hm : 0 < m)
    (R : RelativeResult hp N L H m) :
    StableCollar hp H R.lower R.upper where
  N := N
  L := L
  m := m
  positive := hm
  prism := R.prism
  boundaryFixed := R.boundaryFixed

/-- The existing generic-prism construction produces at least one pair of stable approximations
connected by a stable collar for every zero-free equivariant homotopy. -/
theorem exists_canonical_stable_collar
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁) :
    ∃ (A₀ : StableRegularApproximation hp F₀.map)
      (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (StableCollar hp H A₀ A₁) := by
  obtain ⟨N, L, m, hm, hR⟩ := exists_stable_relative_result hp H
  let R : RelativeResult hp N L H m := Classical.choice hR
  exact ⟨R.lower, R.upper, ⟨R.toStableCollar hp N L H hm⟩⟩

end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
