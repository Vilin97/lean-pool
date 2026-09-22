/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexRealization
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrientedBoundary
/-!
# Simplicial chains on the Fox--Neuwirth order complex

This module defines simplicial chains on the order complex.  Chains are finite coefficient functions on the strict-chain
simplices from `OrderComplex`.  The simplicial boundary is defined by deleting one vertex with the
usual alternating sign.  The construction is deliberately concrete: all sums are over finite
`Fintype` indices, so later cancellation arguments reduce to finite algebra.

The file also defines the first genuine Fox--Neuwirth top chain on maximal flags.  Its coefficient
is the product of the signed cellular incidences along consecutive vertices of the flag, reduced
modulo the prime.  Its simplicial boundary is expressed as an actual chain on the glued realization and is handled
by the boundary-cancellation theorems.
-/

noncomputable section

namespace NRR

open scoped BigOperators

variable {p d : Nat}

namespace FoxNeuwirthOrderComplex

namespace FaceMap

/-- The coface map that omits vertex `k`. -/
def delete (k : Fin (d + 2)) : FaceMap d (d + 1) where
  toFun := k.succAbove
  strictMono := (Fin.succAboveOrderEmb k).strictMono

@[simp] theorem delete_apply (k : Fin (d + 2)) (i : Fin (d + 1)) :
    delete k i = k.succAbove i :=
  rfl

end FaceMap

/-- Degree-`d` simplicial chains with coefficients in `R`.  Since the simplex type is finite, an
ordinary function is already finitely supported. -/
abbrev SimplicialChain (R : Type*) (p d : Nat) :=
  Simplex p d → R

namespace SimplicialChain

section

variable {R : Type*} [CommRing R]

/-- The alternating sign of the face obtained by deleting vertex `k`. -/
def faceSign (k : Fin (d + 2)) : R :=
  (-1 : R) ^ k.1

/-- Coefficient contributed by one simplex and one deleted vertex. -/
def faceContribution
    (chain : SimplicialChain R p (d + 1))
    (target : Simplex p d)
    (source : Simplex p (d + 1))
    (k : Fin (d + 2)) : R :=
  if source.restrict (FaceMap.delete k) = target then
    faceSign k * chain source
  else 0

/-- Simplicial boundary, written as a finite double sum over source simplices and deleted
vertices. -/
def boundary (chain : SimplicialChain R p (d + 1)) :
    SimplicialChain R p d :=
  fun target =>
    ∑ source : Simplex p (d + 1),
      ∑ k : Fin (d + 2), faceContribution chain target source k

@[simp] theorem boundary_apply
    (chain : SimplicialChain R p (d + 1)) (target : Simplex p d) :
    boundary chain target =
      ∑ source : Simplex p (d + 1),
        ∑ k : Fin (d + 2), faceContribution chain target source k :=
  rfl

@[simp] theorem boundary_zero :
    boundary (0 : SimplicialChain R p (d + 1)) = 0 := by
  funext target
  simp [boundary, faceContribution]

@[simp] theorem boundary_add
    (a b : SimplicialChain R p (d + 1)) :
    boundary (a + b) = boundary a + boundary b := by
  funext target
  simp only [boundary, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : source.restrict (FaceMap.delete k) = target
  · simp [faceContribution, h, mul_add]
  · simp [faceContribution, h]

@[simp] theorem boundary_smul
    (r : R) (a : SimplicialChain R p (d + 1)) :
    boundary (r • a) = r • boundary a := by
  funext target
  simp only [boundary, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : source.restrict (FaceMap.delete k) = target
  · simp [faceContribution, h,  mul_left_comm]
  · simp [faceContribution, h]

/-- Boundary as an `R`-linear map. -/
def boundaryLinearMap :
    SimplicialChain R p (d + 1) →ₗ[R] SimplicialChain R p d where
  toFun := boundary
  map_add' := boundary_add
  map_smul' := boundary_smul

/-- Basis chain supported on one simplex. -/
def single (s : Simplex p d) : SimplicialChain R p d :=
  fun t => if t = s then 1 else 0

@[simp] theorem single_self (s : Simplex p d) :
    single (R := R) s s = 1 := by
  simp [single]

@[simp] theorem single_apply_of_ne
    {s t : Simplex p d} (h : t ≠ s) :
    single (R := R) s t = 0 := by
  simp [single, h]

/-- Relabel a simplicial chain by precomposition with the inverse vertex action. -/
def relabel (sigma : Equiv.Perm (Fin p))
    (chain : SimplicialChain R p d) : SimplicialChain R p d :=
  fun s => chain (s.relabel sigma.symm)

omit [CommRing R] in
@[simp] theorem relabel_apply
    (sigma : Equiv.Perm (Fin p))
    (chain : SimplicialChain R p d) (s : Simplex p d) :
    relabel sigma chain s = chain (s.relabel sigma.symm) :=
  rfl

omit [CommRing R] in
@[simp] theorem relabel_one (chain : SimplicialChain R p d) :
    relabel 1 chain = chain := by
  funext s
  change chain (s.relabel (1 : Equiv.Perm (Fin p)).symm) = chain s
  rw [show (1 : Equiv.Perm (Fin p)).symm = 1 by
    apply Equiv.ext
    intro i
    exact (1 : Equiv.Perm (Fin p)).symm_apply_apply i]
  rw [Simplex.relabel_one]

omit [CommRing R] in
/-- Relabelling is a left action on chains. -/
theorem relabel_mul
    (sigma tau : Equiv.Perm (Fin p))
    (chain : SimplicialChain R p d) :
    relabel (sigma * tau) chain = relabel sigma (relabel tau chain) := by
  funext s
  simp only [relabel_apply]
  congr 1

end

end SimplicialChain

namespace FoxNeuwirthChain

section

/-- Auxiliary incidence-product coefficient for comparison with the determinant orientation.

The signed cellular incidence currently available in `OrientedBoundary` records only the product
of independently chosen cell orientations.  It is sufficient for the orbit-level top-facet count,
but it is not the full incidence function of the barycentric subdivision.  Consequently this
coefficient must not be used as the simplicial fundamental chain. -/
def incidenceProductCoefficient
    (s : Simplex p (p - 1)) : ZMod p :=
  ∏ k : Fin (p - 1),
    ((FoxNeuwirth.signedIncidence (s k.castSucc) (s k.succ) : Int) : ZMod p)

/-- Auxiliary incidence-product chain used to compare the two orientation formulas. -/
def incidenceProductChain :
    SimplicialChain (ZMod p) p (p - 1) :=
  incidenceProductCoefficient

/-- Arithmetic equality identifying the maximal-simplex vertex index with `Fin p`. -/
theorem maximalIndex_eq (hp : Nat.Prime p) : p - 1 + 1 = p := by
  have hp0 : 0 < p := hp.pos
  omega

/-- Cast a maximal-simplex index to a label index. -/
def maximalIndexCast (hp : Nat.Prime p)
    (i : Fin (p - 1 + 1)) : Fin p :=
  Fin.cast (maximalIndex_eq hp) i

/-- Reduced block coordinate modulo the diagonal translation direction.

The first `p - 1` labels are measured relative to the last label.  This realizes the quotient
`ℤ^p / ℤ·(1,…,1)` in explicit coordinates. -/
def reducedBlockCoordinate
    (hp : Nat.Prime p) (c : BarredPermutation p) (i : Fin (p - 1)) : Int :=
  (c.blockIndex (maximalIndexCast hp i.castSucc) : Int) -
    (c.blockIndex (maximalIndexCast hp (Fin.last (p - 1))) : Int)

/-- Affine coordinate matrix of a maximal strict flag.

Columns are the reduced block vectors of the `p` flag vertices; the final row consists of ones.
Its determinant is the canonical affine orientation of that barycentric simplex. -/
def affineBlockMatrix
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    Matrix (Fin (p - 1 + 1)) (Fin (p - 1 + 1)) Int :=
  fun i j =>
    Fin.lastCases (1 : Int)
      (fun r => reducedBlockCoordinate hp (s j) r) i

/-- Integral affine orientation of a maximal flag.  For genuine maximal Fox--Neuwirth flags this
is expected to be `1` or `-1`; only its determinant algebra is needed for the cycle equation. -/
def affineBlockDeterminant
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) : Int :=
  Matrix.det (affineBlockMatrix hp s)

/-- Fox--Neuwirth top chain on maximal flags.

The coefficient orients each barycentric simplex by its affine block-coordinate determinant. -/
def topChain (hp : Nat.Prime p) :
    SimplicialChain (ZMod p) p (p - 1) :=
  fun s => (affineBlockDeterminant hp s : ZMod p)

@[simp] theorem topChain_apply
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    topChain hp s = (affineBlockDeterminant hp s : ZMod p) :=
  rfl

/-- Consecutive vertices of a maximal flag are properly comparable. -/
theorem consecutive_properFace
    (s : Simplex p (p - 1)) (k : Fin (p - 1)) :
    ProperFace (s k.castSucc) (s k.succ) := by
  exact s.properFace (@Fin.castSucc_lt_succ _ k)

/-- The actual determinant-chain boundary. -/
def topBoundary (hp : Nat.Prime p) :
    SimplicialChain (ZMod p) p (p - 2) := by
  have hdim : p - 1 = (p - 2) + 1 := by
    have := hp.two_le
    omega
  exact SimplicialChain.boundary (d := p - 2) (hdim ▸ topChain hp)

/-- Being a cycle is the ordinary simplicial boundary equation. -/
def IsTopCycle (hp : Nat.Prime p) : Prop :=
  topBoundary hp = 0

/-- Contribution to a fixed codimension-one flag from deleting one fixed vertex position. -/
def extensionCoefficient
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (k : Fin ((p - 2) + 2)) : ZMod p := by
  have hdim : p - 1 = (p - 2) + 1 := by
    have := hp.two_le
    omega
  exact ∑ source : Simplex p ((p - 2) + 1),
    SimplicialChain.faceContribution
      (hdim ▸ topChain hp) target source k

/-- The boundary coefficient is the sum of the fixed-deletion extension coefficients. -/
theorem topBoundary_apply_eq_sum_extensionCoefficient
    (hp : Nat.Prime p) (target : Simplex p (p - 2)) :
    topBoundary hp target =
      ∑ k : Fin ((p - 2) + 2), extensionCoefficient hp target k := by
  simp only [topBoundary, SimplicialChain.boundary_apply, extensionCoefficient]
  rw [Finset.sum_comm]

/-- Internal deletion positions are all positions below the terminal top-cell vertex. -/
def InternalExtensionCancellation (hp : Nat.Prime p) : Prop :=
  ∀ (target : Simplex p (p - 2)) (k : Fin ((p - 2) + 2)),
    k.1 < p - 1 → extensionCoefficient hp target k = 0

/-- Terminal deletion is the unique position that removes the top-dimensional cell. -/
def TerminalExtensionCancellation (hp : Nat.Prime p) : Prop :=
  ∀ (target : Simplex p (p - 2)) (k : Fin ((p - 2) + 2)),
    k.1 = p - 1 → extensionCoefficient hp target k = 0

/-- The two local cancellation statements cover every deletion position. -/
theorem extensionCancellation_of_internal_terminal
    (hp : Nat.Prime p)
    (hint : InternalExtensionCancellation hp)
    (hterminal : TerminalExtensionCancellation hp) :
    ∀ (target : Simplex p (p - 2)) (k : Fin ((p - 2) + 2)),
      extensionCoefficient hp target k = 0 := by
  intro target k
  have hp2 : 2 ≤ p := hp.two_le
  by_cases hk : k.1 < p - 1
  · exact hint target k hk
  · apply hterminal target k
    omega

/-- Local internal-diamond cancellation plus terminal prime-orbit cancellation imply that the
determinant chain is a genuine cycle. -/
theorem isTopCycle_of_internal_terminal
    (hp : Nat.Prime p)
    (hint : InternalExtensionCancellation hp)
    (hterminal : TerminalExtensionCancellation hp) :
    IsTopCycle hp := by
  unfold IsTopCycle
  funext target
  rw [topBoundary_apply_eq_sum_extensionCoefficient hp target]
  have hzero := extensionCancellation_of_internal_terminal hp hint hterminal
  simp [hzero]

end

end FoxNeuwirthChain

end FoxNeuwirthOrderComplex

end NRR
