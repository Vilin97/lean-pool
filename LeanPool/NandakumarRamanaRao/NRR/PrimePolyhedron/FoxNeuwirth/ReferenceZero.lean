/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopCellModel

/-!
# The reference zero orbit in the Fox--Neuwirth top-cell model

The reference map is the first-coordinate vector modulo the diagonal.  On the standard simplex it
vanishes exactly at the uniform weight vector.  Consequently the full permutation group acts
transitively on its zeros: there is one zero in every top cell, and all of them are relabelings of
the identity-cell zero.

Restricting that full permutation torsor to the prime symmetry group gives one orbit for `p = 2`
and two orbits for odd primes, because the chosen group is respectively `S_2` and `A_p`.  Giving
each orbit local coefficient `1` produces the nonzero reference count used in the prime argument.
-/

namespace NRR

open scoped BigOperators

variable {p : Nat}

namespace FoxNeuwirth

/-- Uniform barycentric weights on the `p` labels. -/
noncomputable def uniformWeights (hp : Nat.Prime p) : FoxNeuwirthWeights p where
  val := fun _ => 1 / (p : Real)
  property := by
    constructor
    · intro i
      positivity
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      have hp0 : (p : Real) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      simp [nsmul_eq_mul, hp0]

@[simp] theorem uniformWeights_apply
    (hp : Nat.Prime p) (i : Fin p) :
    uniformWeights hp i = 1 / (p : Real) :=
  rfl

/-- Uniform weights are fixed by every relabeling. -/
theorem uniformWeights_relabel
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) :
    FoxNeuwirthWeights.relabel sigma (uniformWeights hp) =
      uniformWeights hp := by
  apply Subtype.ext
  funext i
  rfl

/-- Mean of any point of the standard simplex. -/
theorem coordinateMean_weights
    (hp : Nat.Prime p) (w : FoxNeuwirthWeights p) :
    coordinateMean hp.pos w.1 = 1 / (p : Real) := by
  simp [coordinateMean, w.sum_eq_one]

/-- Distinguished reference zero in the identity top cell. -/
noncomputable def referenceZeroRepresentative
    (hp : Nat.Prime p) : FoxNeuwirthTopCellModelPoint p :=
  (FoxNeuwirthTopCell.identity p, uniformWeights hp)

/-- The reference map vanishes exactly at uniform weights. -/
theorem reference_eq_zero_iff_weights_eq_uniform
    (hp : Nat.Prime p) (z : FoxNeuwirthTopCellModelPoint p) :
    FoxNeuwirthTopCellModelPoint.reference hp z = 0 ↔
      z.2 = uniformWeights hp := by
  constructor
  · intro hz
    apply Subtype.ext
    funext i
    have hi := congrArg
      (fun v : ZeroSum p => v i) hz
    change z.2 i - coordinateMean hp.pos z.2.1 = 0 at hi
    rw [coordinateMean_weights hp z.2] at hi
    have hi' : z.2 i = 1 / (p : Real) := sub_eq_zero.mp hi
    simpa only [uniformWeights_apply] using hi'
  · intro hz
    apply ZeroSum.ext
    intro i
    change z.2 i - coordinateMean hp.pos z.2.1 = 0
    rw [coordinateMean_weights hp z.2]
    have hi := congrArg (fun w : FoxNeuwirthWeights p => w i) hz
    simpa only [uniformWeights_apply, sub_eq_zero] using hi

/-- Relabel a top-cell model point by an arbitrary permutation. -/
def relabelPoint
    (sigma : Equiv.Perm (Fin p))
    (z : FoxNeuwirthTopCellModelPoint p) :
    FoxNeuwirthTopCellModelPoint p :=
  (FoxNeuwirthTopCell.relabel sigma z.1,
    FoxNeuwirthWeights.relabel sigma z.2)

/-- The distinguished zero remains a zero after arbitrary relabeling. -/
theorem reference_relabelPoint_zero
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) :
    FoxNeuwirthTopCellModelPoint.reference hp
      (relabelPoint sigma (referenceZeroRepresentative hp)) = 0 := by
  rw [reference_eq_zero_iff_weights_eq_uniform]
  exact uniformWeights_relabel hp sigma

/-- Every reference zero is in the full-permutation orbit of the distinguished zero. -/
theorem reference_zero_in_full_permutation_orbit
    (hp : Nat.Prime p) (z : FoxNeuwirthTopCellModelPoint p)
    (hz : FoxNeuwirthTopCellModelPoint.reference hp z = 0) :
    ∃ sigma : Equiv.Perm (Fin p),
      z = relabelPoint sigma (referenceZeroRepresentative hp) := by
  let sigma : Equiv.Perm (Fin p) := z.1.1.rank.symm
  refine ⟨sigma, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    apply BarredPermutation.ext
    · change z.1.1.rank = z.1.1.rank.trans (1 : Equiv.Perm (Fin p))
      apply Equiv.ext
      intro i
      rfl
    · change z.1.1.bars = ∅
      have htop := z.1.2
      change z.1.1.bars = ∅ at htop
      exact htop
  · have hw := (reference_eq_zero_iff_weights_eq_uniform hp z).1 hz
    simpa [relabelPoint, referenceZeroRepresentative,
      uniformWeights_relabel hp sigma] using hw

/-- Number of prime-symmetry orbits obtained by restricting a full permutation torsor. -/
noncomputable def referenceOrbitMultiplicity (hp : Nat.Prime p) : Nat :=
  (primeSymmetrySubgroup hp).index

/-- For two labels the selected symmetry group is the full group, so the reference zero set has one
orbit. -/
theorem referenceOrbitMultiplicity_eq_one
    (hp : Nat.Prime p) (h2 : p = 2) :
    referenceOrbitMultiplicity hp = 1 := by
  rw [referenceOrbitMultiplicity, primeSymmetrySubgroup_eq_top hp h2]
  simp

/-- For an odd prime the selected symmetry group is alternating, hence has index two. -/
theorem referenceOrbitMultiplicity_eq_two
    (hp : Nat.Prime p) (h2 : p ≠ 2) :
    referenceOrbitMultiplicity hp = 2 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  let i : Fin p := ⟨0, hp.pos⟩
  let j : Fin p := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp [i, j] at hval
  letI : Nontrivial (Fin p) := ⟨⟨i, j, hij⟩⟩
  rw [referenceOrbitMultiplicity,
    primeSymmetrySubgroup_eq_alternating hp h2]
  exact alternatingGroup.index_eq_two

/-- Signed reference orbit count with local coefficient `1` on each restricted orbit. -/
noncomputable def referenceSignedOrbitCount
    (hp : Nat.Prime p) : ZMod p :=
  (referenceOrbitMultiplicity hp : ZMod p)

private theorem two_ne_zero_zmod
    (hp : Nat.Prime p) (h2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hint : ((2 : Int) : ZMod p) = 0 := by
    norm_num at hzero ⊢
    exact hzero
  have hdInt : (p : Int) ∣ 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : Int) p).mp hint
  have hdNat : p ∣ 2 := by
    exact_mod_cast hdInt
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdNat
  exact h2 (Nat.le_antisymm hle hp.two_le)

/-- The signed reference orbit count is nonzero modulo `p`. -/
theorem referenceSignedOrbitCount_ne_zero
    (hp : Nat.Prime p) :
    referenceSignedOrbitCount hp ≠ 0 := by
  by_cases h2 : p = 2
  · subst p
    simp [referenceSignedOrbitCount, referenceOrbitMultiplicity,
      primeSymmetrySubgroup]
  · rw [referenceSignedOrbitCount,
      referenceOrbitMultiplicity_eq_two hp h2]
    exact two_ne_zero_zmod hp h2

end FoxNeuwirth

end NRR
