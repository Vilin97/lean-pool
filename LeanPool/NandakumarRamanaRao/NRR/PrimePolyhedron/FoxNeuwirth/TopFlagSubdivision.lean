/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopIncidenceComplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexChain
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Top-flag subdivision of the Fox--Neuwirth cellular cycle

This module implements the concrete simplicial chain required by Step S3 of the simplest route.
A maximal order-complex flag has `p` vertices and `p - 1` successive transitions.  For each
transition we record the change of the bar-indicator vector.  The determinant of the resulting
square matrix is the sign of the order in which the initial bars are removed.  Multiplying by the
orientation of the bottom vertex gives the canonical orientation of the subdivided top cell.

The construction has two advantages over the earlier affine block determinant:

* it depends only on the finite barred-permutation data;
* its coefficient is independent of the final top-cell permutation once the preceding flag is
  fixed, so the terminal boundary is governed directly by the top-extension multiplicity proved
  in `FacetShuffleEquiv`.

The local boundary theorem is rank-two internal cancellation.  It is isolated below as an
explicit finite statement about the actual chain, rather than hidden in a geometric certificate.
-/

@[expose] public section

namespace NRR

open scoped BigOperators

variable {p : Nat}

namespace FoxNeuwirthOrderComplex
namespace TopFlagSubdivision

/-- Integer indicator of a bar position. -/
def barIndicator (c : BarredPermutation p) (r : Fin (p - 1)) : Int :=
  if r ∈ c.bars then 1 else 0

@[simp] theorem barIndicator_of_mem
    (c : BarredPermutation p) (r : Fin (p - 1)) (hr : r ∈ c.bars) :
    barIndicator c r = 1 := by
  simp [barIndicator, hr]

@[simp] theorem barIndicator_of_not_mem
    (c : BarredPermutation p) (r : Fin (p - 1)) (hr : r ∉ c.bars) :
    barIndicator c r = 0 := by
  simp [barIndicator, hr]

/-- Matrix of successive bar-removal vectors along a maximal strict flag. -/
def barDifferenceMatrix (s : Simplex p (p - 1)) :
    Matrix (Fin (p - 1)) (Fin (p - 1)) Int :=
  fun r k => barIndicator (s k.castSucc) r - barIndicator (s k.succ) r

/-- Orientation of the order in which bars disappear along a maximal flag. -/
def barRemovalDeterminant (s : Simplex p (p - 1)) : Int :=
  Matrix.det (barDifferenceMatrix s)

/-- Canonical permutation orientation of a Fox--Neuwirth cell.

This is the Mathlib permutation sign of the displayed rank.  It is the same parity orientation
used by `BarredPermutation.orientationSign`, but using the library sign directly avoids carrying
a second inversion-parity implementation into the subdivision determinant calculation. -/
def permutationOrientationSign (c : BarredPermutation p) : Int :=
  ((Equiv.Perm.sign c.rank : ℤˣ) : ℤ)

/-- Integral coefficient of a maximal flag in the subdivision chain. -/
def integralCoefficient (s : Simplex p (p - 1)) : Int :=
  permutationOrientationSign (s 0) * barRemovalDeterminant s

/-- The concrete top-flag subdivision chain over `ZMod p`. -/
def chain : SimplicialChain (ZMod p) p (p - 1) :=
  fun s => (integralCoefficient s : ZMod p)

@[simp] theorem chain_apply (s : Simplex p (p - 1)) :
    chain s = (integralCoefficient s : ZMod p) :=
  rfl

/-- The actual simplicial boundary of the top-flag subdivision chain. -/
noncomputable def boundary (hp : Nat.Prime p) :
    SimplicialChain (ZMod p) p (p - 2) := by
  have hdim : p - 1 = (p - 2) + 1 := by
    have := hp.two_le
    omega
  exact SimplicialChain.boundary (d := p - 2) (hdim ▸ chain)

/-- Contribution obtained by deleting one fixed position from a maximal flag. -/
noncomputable def deletionCoefficient
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (k : Fin ((p - 2) + 2)) : ZMod p := by
  have hdim : p - 1 = (p - 2) + 1 := by
    have := hp.two_le
    omega
  exact ∑ source : Simplex p ((p - 2) + 1),
    SimplicialChain.faceContribution
      (hdim ▸ chain) target source k

/-- Boundary coefficients split as the sum over deleted positions. -/
theorem boundary_apply_eq_sum_deletionCoefficient
    (hp : Nat.Prime p) (target : Simplex p (p - 2)) :
    boundary hp target =
      ∑ k : Fin ((p - 2) + 2), deletionCoefficient hp target k := by
  simp only [boundary, SimplicialChain.boundary_apply, deletionCoefficient]
  rw [Finset.sum_comm]

/-- Internal deletion positions, including deletion of the bottom vertex, cancel locally. -/
def InternalCancellation (hp : Nat.Prime p) : Prop :=
  ∀ (target : Simplex p (p - 2)) (k : Fin ((p - 2) + 2)),
    k.1 < p - 1 → deletionCoefficient hp target k = 0

/-- The terminal deletion removes the final top-dimensional cell. -/
def TerminalCancellation (hp : Nat.Prime p) : Prop :=
  ∀ (target : Simplex p (p - 2)) (k : Fin ((p - 2) + 2)),
    k.1 = p - 1 → deletionCoefficient hp target k = 0

/-- Internal and terminal cancellation imply that the concrete flag chain is a cycle. -/
theorem boundary_eq_zero_of_internal_terminal
    (hp : Nat.Prime p)
    (hint : InternalCancellation hp)
    (hterminal : TerminalCancellation hp) :
    boundary hp = 0 := by
  funext target
  rw [boundary_apply_eq_sum_deletionCoefficient hp target]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hlast : k.1 = p - 1
  · exact hterminal target k hlast
  · exact hint target k (by
      have hklt : k.1 < (p - 2) + 2 := k.2
      have := hp.two_le
      omega)

/-- A maximal flag's coefficient only depends on its bottom cell and its sequence of bar sets.
In particular, changing only the final top cell does not change the coefficient. -/
theorem integralCoefficient_eq_of_initial_and_bars_eq
    (s t : Simplex p (p - 1))
    (hzero : s 0 = t 0)
    (hbars : ∀ i : Fin (p - 1 + 1), (s i).bars = (t i).bars) :
    integralCoefficient s = integralCoefficient t := by
  unfold integralCoefficient
  rw [hzero]
  congr 1
  unfold barRemovalDeterminant
  congr 1
  funext r k
  unfold barDifferenceMatrix barIndicator
  rw [hbars k.castSucc, hbars k.succ]

/-- Special case used for terminal faces: once all preceding vertices agree and both final
vertices are top cells, the flag coefficients agree. -/
theorem integralCoefficient_eq_of_init_eq_of_final_top
    (hp : Nat.Prime p)
    (s t : Simplex p (p - 1))
    (hinit : ∀ i : Fin (p - 1), s i.castSucc = t i.castSucc)
    (hs : (s (Fin.last (p - 1))).IsTop)
    (ht : (t (Fin.last (p - 1))).IsTop) :
    integralCoefficient s = integralCoefficient t := by
  apply integralCoefficient_eq_of_initial_and_bars_eq s t
  · have hp1 : 0 < p - 1 := by
      have := hp.two_le
      omega
    simpa using hinit ⟨0, hp1⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · unfold BarredPermutation.IsTop at hs ht
      exact hs.trans ht.symm
    · intro j
      simpa using congrArg BarredPermutation.bars (hinit j)

/-- The exact internal combinatorics: every nonterminal deleted face has total signed
extension coefficient zero.  This is a finite rank-two interval statement for ordered partitions. -/
def RankTwoCancellationTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p), InternalCancellation hp

/-- The exact terminal reindexing statement.  The coefficient independence theorem above
reduces this to the already proved facet--shuffle multiplicity. -/
def TerminalMultiplicityTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p), TerminalCancellation hp

/-- If the two finite local cancellation theorems are proved, the concrete chain is an
unconditional simplicial cycle. -/
theorem cycle_of_rankTwo_and_terminal
    (hrank : RankTwoCancellationTheorem)
    (hterminal : TerminalMultiplicityTheorem) :
    ∀ {p : Nat} (hp : Nat.Prime p), boundary hp = 0 := by
  intro p hp
  exact boundary_eq_zero_of_internal_terminal hp (hrank hp) (hterminal hp)

end TopFlagSubdivision
end FoxNeuwirthOrderComplex

namespace AAK

/-- Step S3 now has a concrete maximal-flag chain on the glued order complex. -/
theorem simplestRoute_topFlagSubdivision_defined :
    Nonempty (FoxNeuwirthOrderComplex.SimplicialChain (ZMod 2) 2 1) :=
  ⟨FoxNeuwirthOrderComplex.TopFlagSubdivision.chain⟩

end AAK

end NRR
