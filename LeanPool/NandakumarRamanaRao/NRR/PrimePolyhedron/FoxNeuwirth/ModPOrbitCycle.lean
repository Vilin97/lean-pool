/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Data.ZMod.Basic
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrientedBoundary
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.PrimeBoundary

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
  letI : Fact (Nat.Prime p) := ⟨hp⟩
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
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [signedIncidence_of_facet hab]
  rw [orientedTopCoefficient, if_pos hb]
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
  /-- The dimension of the top cells in the modulo-prime orbit cycle. -/
  topDimension : Nat
  topDimension_eq : topDimension = p - 1
  /-- The oriented top-cell coefficient as a function of barred permutations. -/
  coefficient : BarredPermutation p → ZMod p
  coefficient_eq : coefficient = orientedTopCoefficient
  support_iff_top : ∀ b, coefficient b ≠ 0 ↔ b.IsTop
  /-- The boundary coefficient indexed by a barred permutation and a proper split. -/
  boundaryCoefficient :
    BarredPermutation p → ProperSplit p → ZMod p
  boundaryCoefficient_eq :
    boundaryCoefficient = orientedOrbitBoundaryCoefficient
  boundary_zero : ∀ a s, boundaryCoefficient a s = 0

attribute [-simp] ModPOrbitCycleData.mk.injEq

/-- Canonical modulo-prime Fox--Neuwirth orbit cycle. -/
noncomputable def modPOrbitCycleData
    (hp : Nat.Prime p) : ModPOrbitCycleData hp where
  topDimension := p - 1
  topDimension_eq := rfl
  coefficient := orientedTopCoefficient
  coefficient_eq := rfl
  support_iff_top := orientedTopCoefficient_ne_zero_iff hp
  boundaryCoefficient := orientedOrbitBoundaryCoefficient
  boundaryCoefficient_eq := rfl
  boundary_zero := orientedOrbitBoundaryCoefficient_eq_zero hp

/-- The orbit-level top chain is a cycle modulo every prime. -/
theorem modP_orbit_top_cycle
    (hp : Nat.Prime p) :
    ∀ a : BarredPermutation p, ∀ s : ProperSplit p,
      (modPOrbitCycleData hp).boundaryCoefficient a s = 0 :=
  (modPOrbitCycleData hp).boundary_zero

end FoxNeuwirth

end NRR
