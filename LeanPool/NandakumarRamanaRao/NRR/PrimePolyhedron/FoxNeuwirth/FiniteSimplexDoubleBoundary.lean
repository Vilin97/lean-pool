/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismNonhorizontalCancellation
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricFiniteCancellation
/-!
# Finite cancellation for the boundary of a boundary

This module packages the elementary codimension-two cancellation used by the recursive relative
subdivision cylinder. A sequential deletion is indexed by a first omitted vertex and a second
vertex in the remaining ordered set. Reindexing by the corresponding ordered pair of distinct
original vertices makes the cancellation involution simply swap the two vertices.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace FiniteSimplexDoubleBoundary

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open EquivariantPrismNonhorizontalCancellation

/-- Ordered pairs of distinct vertices of an `(n+2)`-simplex. -/
def DeletedVertexPair (n : Nat) :=
  {z : Fin (n + 3) × Fin (n + 3) // z.1 ≠ z.2}

/-- The index of `b` after deleting the distinct index `a`. This is the total inverse of
`a.succAbove` on the complement of `a`, expressed without the newer partial `Fin.predAbove` API. -/
def deletedIndex {m : Nat} (a b : Fin (m + 1)) (hab : a ≠ b) : Fin m := by
  have habv : a.1 ≠ b.1 := by
    intro h
    exact hab (Fin.ext h)
  by_cases hba : b.1 < a.1
  · exact ⟨b.1, by omega⟩
  · exact ⟨b.1 - 1, by omega⟩

@[simp] theorem deletedIndex_val {m : Nat} (a b : Fin (m + 1)) (hab : a ≠ b) :
    (deletedIndex a b hab).1 = if b.1 < a.1 then b.1 else b.1 - 1 := by
  unfold deletedIndex
  split <;> rfl

@[simp] theorem succAbove_deletedIndex {m : Nat}
    (a b : Fin (m + 1)) (hab : a ≠ b) :
    a.succAbove (deletedIndex a b hab) = b := by
  apply Fin.ext
  rw [fin_succAbove_val]
  simp only [deletedIndex_val]
  have habv : a.1 ≠ b.1 := by
    intro h
    exact hab (Fin.ext h)
  split_ifs <;> omega

@[simp] theorem deletedIndex_succAbove {m : Nat}
    (a : Fin (m + 1)) (k : Fin m) :
    deletedIndex a (a.succAbove k) (Fin.succAbove_ne a k).symm = k := by
  apply Fin.ext
  simp only [deletedIndex_val, fin_succAbove_val]
  split_ifs <;> omega

/-- A sequential deletion determines the two distinct vertices deleted from the original
simplex. -/
def sequentialDeletionEquiv (n : Nat) :
    (Sigma fun _ : Fin (n + 3) => Fin (n + 2)) ≃ DeletedVertexPair n where
  toFun z :=
    ⟨(z.1, z.1.succAbove z.2), (Fin.succAbove_ne z.1 z.2).symm⟩
  invFun z :=
    ⟨z.1.1, deletedIndex z.1.1 z.1.2 z.2⟩
  left_inv := by
    rintro ⟨j, k⟩
    simp
  right_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact succAbove_deletedIndex a b hab

noncomputable instance deletedVertexPairFintype (n : Nat) :
    Fintype (DeletedVertexPair n) :=
  Fintype.ofEquiv (Sigma fun _ : Fin (n + 3) => Fin (n + 2))
    (sequentialDeletionEquiv n)

noncomputable instance deletedVertexPairDecidableEq (n : Nat) :
    DecidableEq (DeletedVertexPair n) := Classical.decEq _

/-- Swap the two deleted original vertices. -/
def swapDeletedVertexPair (n : Nat) : DeletedVertexPair n → DeletedVertexPair n :=
  fun z => ⟨(z.1.2, z.1.1), Ne.symm z.2⟩

/-- Swapping deleted vertices is an involution. -/
theorem swapDeletedVertexPair_involutive (n : Nat) :
    Function.Involutive (swapDeletedVertexPair n) := by
  intro z
  apply Subtype.ext
  rfl

/-- No ordered pair of distinct vertices is fixed by swapping. -/
theorem swapDeletedVertexPair_ne (n : Nat) (z : DeletedVertexPair n) :
    swapDeletedVertexPair n z ≠ z := by
  intro h
  have hfirst := congrArg (fun w : DeletedVertexPair n => w.1.1) h
  exact z.2 hfirst.symm

/-- The two orders of deleting distinct vertices induce the same ordered codimension-two face. -/
theorem double_succAbove_eq
    (n : Nat) (a b : Fin (n + 3)) (hab : a ≠ b) :
    (fun i : Fin (n + 1) =>
      a.succAbove ((deletedIndex a b hab).succAbove i)) =
      fun i : Fin (n + 1) =>
        b.succAbove ((deletedIndex b a hab.symm).succAbove i) := by
  funext i
  apply Fin.ext
  simp only [fin_succAbove_val, deletedIndex_val]
  have habv : a.1 ≠ b.1 := by
    intro h
    exact hab (Fin.ext h)
  split_ifs <;> omega

/-- Geometric coface maps are independent of the order in which two distinct vertices are
deleted. -/
theorem doubleCofacePoint_eq
    (n : Nat) (a b : Fin (n + 3)) (hab : a ≠ b) :
    (fun x : Delta n =>
      cofacePoint (n + 1) a (cofacePoint n (deletedIndex a b hab) x)) =
    fun x : Delta n =>
      cofacePoint (n + 1) b (cofacePoint n (deletedIndex b a hab.symm) x) := by
  funext x
  unfold cofacePoint
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have hcomp :
      a.succAbove ∘ (deletedIndex a b hab).succAbove =
        b.succAbove ∘ (deletedIndex b a hab.symm).succAbove := by
    funext i
    exact congrFun (double_succAbove_eq n a b hab) i
  rw [hcomp]

/-- The alternating signs of the two deletion orders are opposite. -/
theorem double_faceSign_swap
    {R : Type} [CommRing R]
    (n : Nat) (a b : Fin (n + 3)) (hab : a ≠ b) :
    SimplicialChain.faceSign a *
        SimplicialChain.faceSign (deletedIndex a b hab) =
      -(SimplicialChain.faceSign b *
        SimplicialChain.faceSign (deletedIndex b a hab.symm) : R) := by
  simp only [SimplicialChain.faceSign]
  by_cases h : a.1 < b.1
  · have habv : (deletedIndex a b hab).1 = b.1 - 1 := by
      rw [deletedIndex_val]
      simp [Nat.not_lt.mpr (Nat.le_of_lt h)]
    have hbav : (deletedIndex b a hab.symm).1 = a.1 := by
      rw [deletedIndex_val]
      simp [h]
    rw [habv, hbav]
    rw [← pow_add, ← pow_add]
    have hexp : a.1 + (b.1 - 1) + 1 = b.1 + a.1 := by omega
    calc
      (-1 : R) ^ (a.1 + (b.1 - 1)) =
          -((-1 : R) ^ (a.1 + (b.1 - 1) + 1)) := by ring
      _ = -((-1 : R) ^ (b.1 + a.1)) := by rw [hexp]
  · have hba : b.1 < a.1 := lt_of_le_of_ne (Nat.le_of_not_gt h) (by
      intro heq
      exact hab (Fin.ext heq.symm))
    have habv : (deletedIndex a b hab).1 = b.1 := by
      rw [deletedIndex_val]
      simp [hba]
    have hbav : (deletedIndex b a hab.symm).1 = a.1 - 1 := by
      rw [deletedIndex_val]
      simp [Nat.not_lt.mpr (Nat.le_of_lt hba)]
    rw [habv, hbav]
    rw [← pow_add, ← pow_add]
    have hexp : a.1 + b.1 = b.1 + (a.1 - 1) + 1 := by omega
    calc
      (-1 : R) ^ (a.1 + b.1) =
          -((-1 : R) ^ (a.1 + b.1 + 1)) := by ring
      _ = -((-1 : R) ^ (b.1 + (a.1 - 1))) := by
        have : a.1 + b.1 + 1 = b.1 + (a.1 - 1) + 2 := by omega
        rw [this, pow_add]
        ring

/-- Weighted finite form of `boundary ∘ boundary = 0`. -/
theorem double_boundary_weighted_zero
    {R X : Type} [CommRing R]
    (n : Nat) (sigma : Delta (n + 2) → X)
    (W : (Delta n → X) → R) :
    (∑ a : Fin (n + 3),
      SimplicialChain.faceSign a *
        ∑ k : Fin (n + 2),
          SimplicialChain.faceSign k *
            W (fun x => sigma
              (cofacePoint (n + 1) a (cofacePoint n k x)))) = 0 := by
  classical
  simp_rw [Finset.mul_sum]
  let f : (Sigma fun _ : Fin (n + 3) => Fin (n + 2)) → R := fun z =>
    SimplicialChain.faceSign z.1 *
      (SimplicialChain.faceSign z.2 *
        W (fun x => sigma
          (cofacePoint (n + 1) z.1 (cofacePoint n z.2 x))))
  have hreindex :
      (∑ a : Fin (n + 3), ∑ k : Fin (n + 2),
        SimplicialChain.faceSign a *
          (SimplicialChain.faceSign k *
            W (fun x => sigma
              (cofacePoint (n + 1) a (cofacePoint n k x))))) =
        ∑ z, f z := by
    rw [Fintype.sum_sigma]
  rw [hreindex]
  rw [← Equiv.sum_comp (sequentialDeletionEquiv n).symm]
  apply finite_sum_cancel_of_fixedPointFree_involution
    (swapDeletedVertexPair n)
    (swapDeletedVertexPair_involutive n)
    (swapDeletedVertexPair_ne n)
  intro z
  rcases z with ⟨⟨a, b⟩, hab⟩
  simp only [swapDeletedVertexPair]
  dsimp [f, sequentialDeletionEquiv]
  have hW :
      W (fun x => sigma
        (cofacePoint (n + 1) a (cofacePoint n (deletedIndex a b hab) x))) =
      W (fun x => sigma
        (cofacePoint (n + 1) b (cofacePoint n (deletedIndex b a hab.symm) x))) := by
    exact congrArg W (congrArg (Function.comp sigma)
      (doubleCofacePoint_eq n a b hab))
  rw [← hW]
  have hsign :
      (SimplicialChain.faceSign b *
        SimplicialChain.faceSign (deletedIndex b a hab.symm) : R) =
      -(SimplicialChain.faceSign a *
        SimplicialChain.faceSign (deletedIndex a b hab) : R) := by
    have h := double_faceSign_swap (R := R) n a b hab
    rw [h]
    ring
  calc
    SimplicialChain.faceSign b *
        (SimplicialChain.faceSign (deletedIndex b a hab.symm) *
          W (fun x => sigma
            (cofacePoint (n + 1) a
              (cofacePoint n (deletedIndex a b hab) x)))) =
      (SimplicialChain.faceSign b *
        SimplicialChain.faceSign (deletedIndex b a hab.symm)) *
          W (fun x => sigma
            (cofacePoint (n + 1) a
              (cofacePoint n (deletedIndex a b hab) x))) := by ring
    _ = _ := by rw [hsign]; ring

end FiniteSimplexDoubleBoundary
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
