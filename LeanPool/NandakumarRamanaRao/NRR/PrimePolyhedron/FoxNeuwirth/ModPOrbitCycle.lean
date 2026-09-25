/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Data.ZMod.Basic
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrientedBoundary
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.PrimeBoundary

/-!
# The Fox--Neuwirth top chain modulo a prime, at the cell-orbit level

A codimension-one orbit is determined by a proper split `0 < k < p`.  Its coefficient in the
boundary of the oriented top chain is the orientation of the lower-dimensional cell multiplied by
the number `p.choose k` of order-preserving shuffles.  For prime `p` this multiplicity is divisible
by `p`, so every orbit boundary coefficient vanishes in `ZMod p`.

The module deliberately records the orbit-summed coefficient used in the pseudomanifold argument.
It does not identify the disjoint simplex atlas with the glued Blagojevic--Ziegler polyhedron; that
regular-cell realization and the subsequent separator construction are separate topological steps.
-/

@[expose] public section

namespace NRR

variable {p : Nat}

namespace FoxNeuwirth

/-- A proper split of `p` labels into two nonempty consecutive blocks. -/
def ProperSplit (p : Nat) := {k : Nat // 0 < k ∧ k < p}

namespace ProperSplit

@[simp] theorem positive (s : ProperSplit p) : 0 < s.1 := s.2.1
@[simp] theorem lt_total (s : ProperSplit p) : s.1 < p := s.2.2

end ProperSplit

/-- Coefficient assigned to an oriented top cell.  Multiplying by the signed facet incidence
removes the top-cell orientation, leaving one copy of the facet orientation per shuffle. -/
def orientedTopCoefficient (b : BarredPermutation p) : ZMod p :=
  if b.IsTop then (b.orientationSign : ZMod p) else 0

/-- The oriented top coefficient is supported exactly on top cells. -/
theorem orientedTopCoefficient_ne_zero_iff
    (hp : Nat.Prime p) (b : BarredPermutation p) :
    orientedTopCoefficient b ≠ 0 ↔ b.IsTop := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hb : b.IsTop
  · rcases b.orientationSign_eq_one_or_neg_one with hsign | hsign
    · simp [orientedTopCoefficient, hb, hsign]
    · simp [orientedTopCoefficient, hb, hsign]
  · simp [orientedTopCoefficient, hb]

/-- A supported top cell contributes precisely the chosen orientation of its facet. -/
theorem signedIncidence_mul_orientedTopCoefficient
    (hp : Nat.Prime p)
    {a b : BarredPermutation p}
    (hab : a.IsFacet b) (hb : b.IsTop) :
    (signedIncidence a b : ZMod p) * orientedTopCoefficient b =
      (a.orientationSign : ZMod p) := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  rw [signedIncidence_of_facet hab]
  rw [orientedTopCoefficient, ite_eq_left hb]
  push_cast
  rw [mul_assoc, ← Int.cast_mul,
    BarredPermutation.orientationSign_sq]
  simp

/-- Unsigned orbit-summed boundary coefficient for a proper split. -/
def orbitBoundaryCoefficient
    (p : Nat) (s : ProperSplit p) : ZMod p :=
  ((unsignedFacetCoefficient p s.1 : Int) : ZMod p)

/-- Every proper-split orbit coefficient vanishes modulo a prime. -/
theorem orbitBoundaryCoefficient_eq_zero
    (hp : Nat.Prime p) (s : ProperSplit p) :
    orbitBoundaryCoefficient p s = 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd
    (unsignedFacetCoefficient p s.1) p).2
  exact prime_dvd_unsignedFacetCoefficient hp s.positive s.lt_total

/-- Oriented orbit-summed boundary coefficient at a codimension-one cell. -/
def orientedOrbitBoundaryCoefficient
    (a : BarredPermutation p) (s : ProperSplit p) : ZMod p :=
  (a.orientationSign : ZMod p) * orbitBoundaryCoefficient p s

/-- The oriented coefficient also vanishes modulo `p`. -/
theorem orientedOrbitBoundaryCoefficient_eq_zero
    (hp : Nat.Prime p) (a : BarredPermutation p) (s : ProperSplit p) :
    orientedOrbitBoundaryCoefficient a s = 0 := by
  simp [orientedOrbitBoundaryCoefficient,
    orbitBoundaryCoefficient_eq_zero hp s]

/-- Proof-carrying orbit-level top-cycle data. -/
structure ModPOrbitCycleData (hp : Nat.Prime p) where
  /-- The top dimension, identified with one less than the number of labels. -/
  topDimensionData : {d : Nat // d = p - 1}
  /-- The coefficient function, identified with the canonical oriented coefficient. -/
  coefficientData : {f : BarredPermutation p → ZMod p // f = orientedTopCoefficient}
  support_iff_top : ∀ b, coefficientData.1 b ≠ 0 ↔ b.IsTop
  /-- The boundary coefficient and its canonical orbit-summed formula. -/
  boundaryCoefficientData : {f : BarredPermutation p → ProperSplit p → ZMod p //
    f = orientedOrbitBoundaryCoefficient}
  boundary_zero : ∀ a s, boundaryCoefficientData.1 a s = 0

namespace ModPOrbitCycleData

variable {hp : Nat.Prime p}

/-- The top dimension of the orbit cycle. -/
def topDimension (D : ModPOrbitCycleData hp) : Nat := D.topDimensionData.1

theorem topDimension_eq (D : ModPOrbitCycleData hp) : D.topDimension = p - 1 :=
  D.topDimensionData.2

/-- The oriented coefficient of a barred permutation. -/
def coefficient (D : ModPOrbitCycleData hp) : BarredPermutation p → ZMod p :=
  D.coefficientData.1

theorem coefficient_eq (D : ModPOrbitCycleData hp) : D.coefficient = orientedTopCoefficient :=
  D.coefficientData.2

/-- The boundary coefficient indexed by a barred permutation and a proper split. -/
def boundaryCoefficient (D : ModPOrbitCycleData hp) :
    BarredPermutation p → ProperSplit p → ZMod p :=
  D.boundaryCoefficientData.1

theorem boundaryCoefficient_eq (D : ModPOrbitCycleData hp) :
    D.boundaryCoefficient = orientedOrbitBoundaryCoefficient :=
  D.boundaryCoefficientData.2

end ModPOrbitCycleData

/-- Canonical modulo-prime Fox--Neuwirth orbit cycle. -/
noncomputable def modPOrbitCycleData
    (hp : Nat.Prime p) : ModPOrbitCycleData hp where
  topDimensionData := ⟨p - 1, rfl⟩
  coefficientData := ⟨orientedTopCoefficient, rfl⟩
  support_iff_top := orientedTopCoefficient_ne_zero_iff hp
  boundaryCoefficientData := ⟨orientedOrbitBoundaryCoefficient, rfl⟩
  boundary_zero := orientedOrbitBoundaryCoefficient_eq_zero hp

/-- The orbit-level top chain is a cycle modulo every prime. -/
theorem modP_orbit_top_cycle
    (hp : Nat.Prime p) :
    ∀ a : BarredPermutation p, ∀ s : ProperSplit p,
      (modPOrbitCycleData hp).boundaryCoefficient a s = 0 :=
  (modPOrbitCycleData hp).boundary_zero

end FoxNeuwirth

end NRR
