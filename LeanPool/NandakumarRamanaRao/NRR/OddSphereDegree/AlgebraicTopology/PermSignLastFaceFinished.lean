/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionOperator
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic

/-!
# Last-face sign identity for barycentric subdivision

This file supplies the sign lemma needed for the last-face part of the proof
that barycentric subdivision commutes with the singular boundary.

The theorem is deliberately stated in the same flexible `face-data` form as the
last-face affine identity: instead of first choosing a canonical deletion
permutation, it assumes the data

* `j : Fin (n+2)`, the deleted target vertex;
* `ρ : Perm (Fin (n+1))`, the induced permutation on the remaining vertices;
* `hj : j = π last`;
* `hρ : ∀ t, j.succAbove (ρ t) = π (Fin.castSucc t)`.

This is exactly the data consumed by the affine last-face lemma. The theorem
then proves

`(-1)^(n+1) sign(π) = (-1)^j sign(ρ)`.

This module proves the permutation-sign identity used by the boundary-chain theorem.
-/

@[expose] public section

open scoped BigOperators
open Equiv Equiv.Perm

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The last vertex of `Fin (n+2)`. -/
def lastVertex (n : ℕ) : Fin (n + 2) :=
  ⟨n + 1, by omega⟩

@[simp] theorem lastVertex_val (n : ℕ) : (lastVertex n).val = n + 1 := rfl

/-- Extend a permutation of the first `n+1` indices to a permutation of
`Fin (n+2)` fixing the last index.

This uses Mathlib's `viaFintypeEmbedding`, so its sign is exactly the sign of
`ρ`. -/
noncomputable def extendLastPerm {n : ℕ}
    (ρ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  ρ.viaFintypeEmbedding (Fin.castSuccOrderEmb.toEmbedding)

@[simp] theorem sign_extendLastPerm {n : ℕ}
    (ρ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm.sign (extendLastPerm ρ) = Equiv.Perm.sign ρ := by
  classical
  unfold extendLastPerm
  exact Equiv.Perm.viaFintypeEmbedding_sign ρ (Fin.castSuccOrderEmb.toEmbedding)

/-- The order-preserving insertion permutation that sends the last domain vertex
to `j` and sends the first `n+1` domain vertices to the remaining target vertices
in increasing order.

It is implemented as:

1. `finRotate (n+2)`, sending the last input position to `0` and shifting the
 other positions to successors;
2. `j.cycleRange.symm`, sending `0` to `j` and successors to `j.succAbove _`.
-/
noncomputable def insertLastPerm {n : ℕ} (j : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  (finRotate (n + 2)).trans j.cycleRange.symm

@[simp] theorem insertLastPerm_last {n : ℕ} (j : Fin (n + 2)) :
    insertLastPerm j (lastVertex n) = j := by
  classical
  unfold insertLastPerm lastVertex
  have hrot : finRotate (n + 2) ⟨n + 1, by omega⟩ = 0 := by
    simp [finRotate]
  have h_symm : (j.cycleRange.symm : Equiv.Perm (Fin (n + 2))) 0 = j := Fin.cycleRange_symm_zero j
  change (j.cycleRange.symm : Equiv.Perm (Fin (n + 2))) (finRotate (n + 2) ⟨n + 1, by omega⟩) = j
  rw [hrot, h_symm]

@[simp] theorem insertLastPerm_castSucc {n : ℕ} (j : Fin (n + 2))
    (t : Fin (n + 1)) :
    insertLastPerm j (Fin.castSucc t) = j.succAbove t := by
  classical
  unfold insertLastPerm
  simp

/-- Sign of the insertion permutation. -/
theorem sign_insertLastPerm {n : ℕ} (j : Fin (n + 2)) :
    Equiv.Perm.sign (insertLastPerm j)
      = (-1 : ℤˣ) ^ (n + 1) * (-1 : ℤˣ) ^ j.val := by
  classical
  unfold insertLastPerm
  calc
    Equiv.Perm.sign ((finRotate (n + 2)).trans j.cycleRange.symm)
        = Equiv.Perm.sign j.cycleRange.symm
            * Equiv.Perm.sign (finRotate (n + 2)) := by
          exact Equiv.Perm.sign_trans (finRotate (n + 2)) j.cycleRange.symm
    _ = Equiv.Perm.sign j.cycleRange
            * Equiv.Perm.sign (finRotate (n + 2)) := by
          simp
    _ = (-1 : ℤˣ) ^ j.val * (-1 : ℤˣ) ^ (n + 1) := by
          simp [sign_finRotate]
    _ = (-1 : ℤˣ) ^ (n + 1) * (-1 : ℤˣ) ^ j.val := by
          ac_rfl

/-
Factorization of a permutation from last-face data.

If `π last = j` and, on the remaining first `n+1` domain vertices,
`π` is `j.succAbove ∘ ρ`, then `π` factors as the extension of `ρ` followed by
insertion of `j` in the last position.
-/
theorem factor_lastFace_of_faceData {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hj : j = π (lastVertex n))
    (hρ : ∀ t : Fin (n + 1), j.succAbove (ρ t) = π (Fin.castSucc t)) :
    π = (extendLastPerm ρ).trans (insertLastPerm j) := by
  classical
  ext x
  obtain ⟨t, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · have h_emb : (extendLastPerm ρ) (Fin.castSucc t) = Fin.castSucc (ρ t) :=
      Equiv.Perm.viaFintypeEmbedding_apply_image ρ Fin.castSuccOrderEmb.toEmbedding t
    rw [Equiv.trans_apply, h_emb, insertLastPerm_castSucc, hρ]
  · have h_not : (Fin.last (n + 1) : Fin (n + 2)) ∉ Set.range (Fin.castSuccOrderEmb.toEmbedding)
      := by
      simp [Fin.castSuccOrderEmb]
    have h_fix : (extendLastPerm ρ) (Fin.last (n + 1)) = Fin.last (n + 1) :=
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range ρ Fin.castSuccOrderEmb.toEmbedding h_not
    have h_last : (Fin.last (n + 1) : Fin (n + 2)) = lastVertex n := rfl
    rw [Equiv.trans_apply, h_fix, h_last, insertLastPerm_last, hj]

/-- Unit-valued last-face sign identity, in the face-data form used by the
last-face affine identity. -/
theorem permSign_units_last_face_of_faceData {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hj : j = π (lastVertex n))
    (hρ : ∀ t : Fin (n + 1), j.succAbove (ρ t) = π (Fin.castSucc t)) :
    ((-1 : ℤˣ) ^ (n + 1)) * Equiv.Perm.sign π
      = ((-1 : ℤˣ) ^ j.val) * Equiv.Perm.sign ρ := by
  classical
  have hfac := factor_lastFace_of_faceData π j ρ hj hρ
  calc
    ((-1 : ℤˣ) ^ (n + 1)) * Equiv.Perm.sign π
        = ((-1 : ℤˣ) ^ (n + 1))
            * Equiv.Perm.sign ((extendLastPerm ρ).trans (insertLastPerm j)) := by
          rw [hfac]
    _ = ((-1 : ℤˣ) ^ (n + 1))
            * (Equiv.Perm.sign (insertLastPerm j) * Equiv.Perm.sign (extendLastPerm ρ)) := by
          rw [Equiv.Perm.sign_trans]
    _ = ((-1 : ℤˣ) ^ (n + 1))
            * (((-1 : ℤˣ) ^ (n + 1) * (-1 : ℤˣ) ^ j.val) * Equiv.Perm.sign ρ) := by
          rw [sign_insertLastPerm, sign_extendLastPerm]
    _ = ((-1 : ℤˣ) ^ j.val) * Equiv.Perm.sign ρ := by
          -- `(-1)^(n+1) * (-1)^(n+1) = 1` in `ℤˣ`.
          have hsq : ((-1 : ℤˣ) ^ (n + 1)) * ((-1 : ℤˣ) ^ (n + 1)) = 1 := by
            rw [← pow_add]
            have : (n + 1) + (n + 1) = 2 * (n + 1) := by omega
            rw [this, pow_mul]
            norm_num
          rw [← mul_assoc, ← mul_assoc, hsq, one_mul]

/-- Integer-valued last-face sign identity. -/
theorem permSign_int_last_face_of_faceData {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hj : j = π (lastVertex n))
    (hρ : ∀ t : Fin (n + 1), j.succAbove (ρ t) = π (Fin.castSucc t)) :
    (((-1 : ℤˣ) ^ (n + 1)) * Equiv.Perm.sign π : ℤˣ) =
      (((-1 : ℤˣ) ^ j.val) * Equiv.Perm.sign ρ : ℤˣ) := by
  exact permSign_units_last_face_of_faceData π j ρ hj hρ

/-- Coefficient-ring last-face sign identity. This is the version to use in the
barycentric subdivision boundary computation. -/
theorem permSignCoeff_last_face_of_faceData (R : Type) [CommRing R] {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2))
    (ρ : Equiv.Perm (Fin (n + 1)))
    (hj : j = π (lastVertex n))
    (hρ : ∀ t : Fin (n + 1), j.succAbove (ρ t) = π (Fin.castSucc t)) :
    ((-1 : R) ^ (n + 1)) * permSignCoeff R π
      = ((-1 : R) ^ j.val) * permSignCoeff R ρ := by
  classical
  have h := congrArg (fun u : ℤˣ => ((u : ℤ) : R))
    (permSign_units_last_face_of_faceData π j ρ hj hρ)
  unfold permSignCoeff
  simpa [Int.cast_mul, Int.cast_pow] using h

end AffineBarycentricSubdivision
end SphereOddDegree
