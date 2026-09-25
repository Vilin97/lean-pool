/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopFlagTerminalCancellation
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.PermSignAdjacentSwap

/-!
# Explicit codes and internal pairings for maximal Fox--Neuwirth flags

A maximal flag is combinatorially controlled by three permutations:

* the bottom singleton order;
* the order in which the `p - 1` bars are removed;
* the final top-cell order.

This module implements the sign-reversing part of that description.  Deleting the bottom vertex
is paired by swapping the two bottom labels separated by the first removed bar.  Deleting any
other internal vertex is paired by swapping the two adjacent removal steps around that vertex.
Both operations are fixed-point-free involutions and negate the canonical product sign.

The geometric/combinatorial bridge constructs the associated strict flag and proves that paired
codes have the same deleted face. The finite involution lemma then proves
`RankTwoCancellationTheorem`.

Index conventions.  The bar-removal permutation lives on `Fin (p - 1)`.  Because Lean's natural
subtraction does not make `p - 2 + 1` and `p - 1` definitionally equal, the removal-step pairing
uses the explicit reindexing equivalence `eQ hp : Fin (p - 2 + 1) ≃ Fin (p - 1)`, and the
first-cut labels use `ePp hp : Fin (p - 1 + 1) ≃ Fin p`.
-/

@[expose] public section

namespace NRR

open SphereOddDegree.AffineBarycentricSubdivision

variable {p : Nat}

namespace FoxNeuwirthOrderComplex
namespace MaximalFlagCode

/-- Finite code for a maximal flag. -/
@[ext]
structure Code (p : Nat) where
  /-- The label permutation at the bottom of the encoded maximal flag. -/
  bottom : Equiv.Perm (Fin p)
  /-- The order in which the bars are removed along the maximal flag. -/
  removal : Equiv.Perm (Fin (p - 1))
  /-- The label permutation at the top of the encoded maximal flag. -/
  top : Equiv.Perm (Fin p)
  deriving Fintype, DecidableEq

/-- Integer sign of a finite permutation. -/
noncomputable def permSignInt {n : Nat} (sigma : Equiv.Perm (Fin n)) : Int :=
  ((Equiv.Perm.sign sigma : ℤˣ) : ℤ)

/-- Canonical sign of a maximal-flag code. -/
noncomputable def coefficient (z : Code p) : Int :=
  permSignInt z.bottom * permSignInt z.removal

/-- First bar-removal step; prime cardinality guarantees that `Fin (p - 1)` is nonempty. -/
def firstRemovalStep (hp : Nat.Prime p) : Fin (p - 1) :=
  ⟨0, by
    have := hp.two_le
    omega⟩

/-- Bottom vertex index in a maximal flag. -/
def bottomDeletionIndex (hp : Nat.Prime p) : Fin p :=
  ⟨0, hp.pos⟩

/-- Reindexing equivalence `Fin (p - 1 + 1) ≃ Fin p`, used to view a bar-adjacent position as a
bottom label position. -/
def ePp (hp : Nat.Prime p) : Fin (p - 1 + 1) ≃ Fin p :=
  finCongr (by have := hp.two_le; omega)

/-- Reindexing equivalence `Fin (p - 2 + 1) ≃ Fin (p - 1)`, used to view an internal removal-step
index as a bar position. -/
def eQ (hp : Nat.Prime p) : Fin (p - 2 + 1) ≃ Fin (p - 1) :=
  finCongr (by have := hp.two_le; omega)

/-- Label occupying the position immediately before the first removed bar. -/
def firstCutLeftLabel (hp : Nat.Prime p) (z : Code p) : Fin p :=
  z.bottom.symm (ePp hp (z.removal (firstRemovalStep hp)).castSucc)

/-- Label occupying the position immediately after the first removed bar. -/
def firstCutRightLabel (hp : Nat.Prime p) (z : Code p) : Fin p :=
  z.bottom.symm (ePp hp (z.removal (firstRemovalStep hp)).succ)

/-- The two labels around the first removed bar are distinct. -/
theorem firstCutLabels_ne
    (hp : Nat.Prime p) (z : Code p) :
    firstCutLeftLabel hp z ≠ firstCutRightLabel hp z := by
  intro h
  unfold firstCutLeftLabel firstCutRightLabel at h
  exact (ne_of_lt Fin.castSucc_lt_succ)
    ((ePp hp).injective (z.bottom.symm.injective h))

/-- Pairing for deletion of the bottom vertex: swap the two labels which become identified after
removing the first bar. -/
def bottomPartner (hp : Nat.Prime p) (z : Code p) : Code p where
  bottom :=
    (Equiv.swap (firstCutLeftLabel hp z) (firstCutRightLabel hp z)).trans z.bottom
  removal := z.removal
  top := z.top

@[simp] theorem bottomPartner_removal
    (hp : Nat.Prime p) (z : Code p) :
    (bottomPartner hp z).removal = z.removal :=
  rfl

@[simp] theorem bottomPartner_top
    (hp : Nat.Prime p) (z : Code p) :
    (bottomPartner hp z).top = z.top :=
  rfl

/-- The bottom pairing swaps the ranks of the two labels and fixes every other rank. -/
theorem bottomPartner_bottom_apply
    (hp : Nat.Prime p) (z : Code p) (i : Fin p) :
    (bottomPartner hp z).bottom i =
      z.bottom ((Equiv.swap (firstCutLeftLabel hp z)
        (firstCutRightLabel hp z)) i) :=
  rfl

/-- After the swap, the labels occupying the two first-cut positions are exchanged. -/
@[simp] theorem bottomPartner_leftLabel
    (hp : Nat.Prime p) (z : Code p) :
    firstCutLeftLabel hp (bottomPartner hp z) = firstCutRightLabel hp z := by
  unfold firstCutLeftLabel bottomPartner
  apply z.bottom.injective
  simp [firstCutLeftLabel, firstCutRightLabel]

@[simp] theorem bottomPartner_rightLabel
    (hp : Nat.Prime p) (z : Code p) :
    firstCutRightLabel hp (bottomPartner hp z) = firstCutLeftLabel hp z := by
  unfold firstCutRightLabel bottomPartner
  apply z.bottom.injective
  simp [firstCutLeftLabel, firstCutRightLabel]

/-- Bottom pairing is an involution. -/
theorem bottomPartner_involutive (hp : Nat.Prime p) :
    Function.Involutive (bottomPartner hp : Code p → Code p) := by
  intro z
  apply Code.ext
  · change (Equiv.swap (firstCutLeftLabel hp (bottomPartner hp z))
        (firstCutRightLabel hp (bottomPartner hp z))).trans
        (bottomPartner hp z).bottom = z.bottom
    rw [bottomPartner_leftLabel, bottomPartner_rightLabel]
    change (Equiv.swap (firstCutRightLabel hp z) (firstCutLeftLabel hp z)).trans
      ((Equiv.swap (firstCutLeftLabel hp z) (firstCutRightLabel hp z)).trans z.bottom)
        = z.bottom
    rw [Equiv.swap_comm (firstCutRightLabel hp z), ← Equiv.trans_assoc,
      Equiv.swap_swap, Equiv.refl_trans]
  · rfl
  · rfl

/-- Bottom pairing has no fixed points. -/
theorem bottomPartner_ne (hp : Nat.Prime p) (z : Code p) :
    bottomPartner hp z ≠ z := by
  intro h
  have hbottom := congrArg Code.bottom h
  have happ := congrArg (fun sigma : Equiv.Perm (Fin p) =>
    sigma (firstCutLeftLabel hp z)) hbottom
  simp only [bottomPartner_bottom_apply] at happ
  rw [Equiv.swap_apply_left] at happ
  exact (firstCutLabels_ne hp z) (z.bottom.injective happ).symm

/-- Any nontrivial transposition negates the integer permutation sign. -/
theorem permSignInt_swap_trans
    {n : Nat} (sigma : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    permSignInt ((Equiv.swap i j).trans sigma) = - permSignInt sigma := by
  unfold permSignInt
  have hswap : Equiv.Perm.sign (Equiv.swap i j) = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap hij
  rw [Equiv.Perm.sign_trans, hswap]
  simp

/-- Bottom pairing reverses the code orientation. -/
theorem coefficient_bottomPartner
    (hp : Nat.Prime p) (z : Code p) :
    coefficient (bottomPartner hp z) = - coefficient z := by
  unfold coefficient bottomPartner
  rw [permSignInt_swap_trans z.bottom _ _ (firstCutLabels_ne hp z)]
  ring

/-- Pairing for a positive internal deleted position: swap the adjacent bar-removal steps on the
left and right of that position. -/
def removalPartner
    (hp : Nat.Prime p) (i : Fin (p - 2)) (z : Code p) : Code p where
  bottom := z.bottom
  removal :=
    (Equiv.swap (eQ hp i.castSucc) (eQ hp i.succ)).trans z.removal
  top := z.top

@[simp] theorem removalPartner_bottom
    (hp : Nat.Prime p) (i : Fin (p - 2)) (z : Code p) :
    (removalPartner hp i z).bottom = z.bottom :=
  rfl

@[simp] theorem removalPartner_top
    (hp : Nat.Prime p) (i : Fin (p - 2)) (z : Code p) :
    (removalPartner hp i z).top = z.top :=
  rfl

/-- The two removal steps around an internal position are distinct after reindexing. -/
theorem eQ_castSucc_ne_succ (hp : Nat.Prime p) (i : Fin (p - 2)) :
    eQ hp i.castSucc ≠ eQ hp i.succ :=
  fun h => (ne_of_lt Fin.castSucc_lt_succ) ((eQ hp).injective h)

/-- Removal-step pairing is an involution. -/
theorem removalPartner_involutive
    (hp : Nat.Prime p) (i : Fin (p - 2)) :
    Function.Involutive (removalPartner hp i : Code p → Code p) := by
  intro z
  apply Code.ext
  · rfl
  · change (Equiv.swap (eQ hp i.castSucc) (eQ hp i.succ)).trans
      ((Equiv.swap (eQ hp i.castSucc) (eQ hp i.succ)).trans z.removal) = z.removal
    rw [← Equiv.trans_assoc, Equiv.swap_swap, Equiv.refl_trans]
  · rfl

/-- Removal-step pairing has no fixed points. -/
theorem removalPartner_ne
    (hp : Nat.Prime p) (i : Fin (p - 2)) (z : Code p) :
    removalPartner hp i z ≠ z := by
  intro h
  have hremoval := congrArg Code.removal h
  have happ := congrArg
    (fun sigma : Equiv.Perm (Fin (p - 1)) => sigma (eQ hp i.castSucc)) hremoval
  simp only [removalPartner, Equiv.trans_apply, Equiv.swap_apply_left] at happ
  exact (eQ_castSucc_ne_succ hp i) (z.removal.injective happ).symm

/-- Removal-step pairing reverses the code orientation. -/
theorem coefficient_removalPartner
    (hp : Nat.Prime p) (i : Fin (p - 2)) (z : Code p) :
    coefficient (removalPartner hp i z) = - coefficient z := by
  unfold coefficient removalPartner
  rw [permSignInt_swap_trans z.removal _ _ (eQ_castSucc_ne_succ hp i)]
  ring

/- The face-compatibility bridge predicates below use `deleteFace`, a coface map whose built-in
`Fin.cast` avoids the `p - 2 + 1` vs `p - 1` face-dimension mismatch.  They are consumed by
`MaximalFlagSourceCancellation`. -/

/-- The order-preserving face map that deletes a chosen maximal-flag vertex. -/
def deleteFace (hp : Nat.Prime p) (k : Fin (p - 1 + 1)) :
    FaceMap (p - 2) (p - 1) where
  toFun i := k.succAbove (Fin.cast (by have := hp.two_le; omega) i)
  strictMono := by
    intro a b hab
    apply Fin.strictMono_succAbove k
    simpa using hab

/-- Bottom-partner flag codes represent the same simplex face after the bottom deletion. -/
def BottomFaceCompatibility (hp : Nat.Prime p)
    (toSimplex : Code p → Simplex p (p - 1)) : Prop :=
  ∀ z,
    (toSimplex (bottomPartner hp z)).restrict
      (deleteFace hp (Fin.cast (by have := hp.two_le; omega) (bottomDeletionIndex hp))) =
    (toSimplex z).restrict
      (deleteFace hp (Fin.cast (by have := hp.two_le; omega) (bottomDeletionIndex hp)))

/-- Removal-partner flag codes represent the same simplex face at the chosen internal deletion. -/
def RemovalFaceCompatibility (hp : Nat.Prime p)
    (toSimplex : Code p → Simplex p (p - 1)) : Prop :=
  ∀ (i : Fin (p - 2)) (z : Code p),
    (toSimplex (removalPartner hp i z)).restrict
      (deleteFace hp (Fin.cast (by have := hp.two_le; omega) i.succ.castSucc)) =
    (toSimplex z).restrict
      (deleteFace hp (Fin.cast (by have := hp.two_le; omega) i.succ.castSucc))

end MaximalFlagCode
end FoxNeuwirthOrderComplex

namespace AAK

/-- The explicit sign-reversing internal pairing kernel is available. -/
theorem simplestRoute_internalPairingKernel :
    ∀ {p : Nat} (hp : Nat.Prime p),
      Function.Involutive
        (FoxNeuwirthOrderComplex.MaximalFlagCode.bottomPartner hp) :=
  fun hp => FoxNeuwirthOrderComplex.MaximalFlagCode.bottomPartner_involutive hp

end AAK

end NRR
