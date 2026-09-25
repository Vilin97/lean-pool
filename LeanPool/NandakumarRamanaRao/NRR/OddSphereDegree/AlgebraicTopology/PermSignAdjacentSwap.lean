/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionOperator
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Adjacent-swap sign lemma for barycentric subdivision

This file proves the sign part of the internal-face cancellation in the
boundary computation for barycentric subdivision.

If `τ` is the adjacent transposition swapping positions `i` and `i+1`, then
`τ.trans π` has the opposite sign from `π`. The final theorem is stated for the
coefficient-ring sign convention used by `permSignCoeff` in
`BarycentricSubdivisionOperator.lean`.
-/

@[expose] public section

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The adjacent entries `i` and `i+1` in `Fin (n+2)` are distinct. -/
theorem castSucc_ne_succ_adjacent {n : ℕ} (i : Fin (n + 1)) :
    Fin.castSucc i ≠ Fin.succ i := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_succ] at this

/-- Unit-valued sign identity for left composition by the adjacent transposition
swapping `i` and `i+1`.

The order is chosen to match the affine internal-swap lemma, where the swapped
permutation is written

`(Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π`.
-/
theorem permSign_units_adjacent_swap {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    Equiv.Perm.sign
        ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π)
      = - Equiv.Perm.sign π := by
  let τ : Equiv.Perm (Fin (n + 2)) :=
    Equiv.swap (Fin.castSucc i) (Fin.succ i)
  have hτ : Equiv.Perm.sign τ = (-1 : ℤˣ) := by
    dsimp [τ]
    exact Equiv.Perm.sign_swap (castSucc_ne_succ_adjacent i)
  calc
    Equiv.Perm.sign (τ.trans π)
        = Equiv.Perm.sign π * Equiv.Perm.sign τ := by
          exact Equiv.Perm.sign_trans τ π
    _ = Equiv.Perm.sign π * (-1 : ℤˣ) := by
          rw [hτ]
    _ = - Equiv.Perm.sign π := by
          ext
          simp

/-- Integer-valued version of `permSign_units_adjacent_swap`. -/
theorem permSign_int_adjacent_swap {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    ((Equiv.Perm.sign
        ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π) : ℤˣ) : ℤ)
      = - ((Equiv.Perm.sign π : ℤˣ) : ℤ) := by
  have h := congrArg (fun u : ℤˣ => (u : ℤ))
    (permSign_units_adjacent_swap π i)
  simpa using h

/-- Coefficient-ring sign identity for the internal adjacent-swap cancellation.

This is the lemma needed to pair the internal boundary face coming from `π` with
that coming from the adjacent-swapped permutation. -/
theorem permSignCoeff_adjacent_swap (R : Type) [CommRing R] {n : ℕ}
    (π : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    permSignCoeff R ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π)
      = - permSignCoeff R π := by
  have h := permSign_int_adjacent_swap π i
  unfold permSignCoeff
  have h2 := congrArg (fun z : ℤ => (z : R)) h
  push_cast at h2
  convert h2 using 2

end AffineBarycentricSubdivision
end SphereOddDegree
