/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.NatCard
/-!
# The finite-group count in the global cyclotomic inertia argument

The global Kronecker--Weber proof generates the full Galois group by the
inertia groups at the finitely many ramified primes.  Since the group is
abelian, the cardinality of the subgroup that they generate is at most the
product of their cardinalities.  This file isolates that elementary count
from the arithmetic part of the proof.
-/

@[expose] public section

noncomputable
section

namespace RamificationTheory

open scoped BigOperators

variable {G ι : Type*} [CommGroup G] [Finite G]

/-- In a finite abelian group, the supremum of two subgroups has cardinality
at most the product of their cardinalities. -/
theorem natCard_sup_le_mul_natCard (H J : Subgroup G) :
    Nat.card ↥(H ⊔ J : Subgroup G) ≤ Nat.card H * Nat.card J := by
  let : Finite H := Finite.of_injective (fun x : H ↦ (x : G))
    (fun _ _ h ↦ Subtype.ext h)
  let : Finite J := Finite.of_injective (fun x : J ↦ (x : G))
    (fun _ _ h ↦ Subtype.ext h)
  let : Fintype H := Fintype.ofFinite H
  let : Fintype J := Fintype.ofFinite J
  let f : H × J → ↥(H ⊔ J : Subgroup G) := fun x ↦
    ⟨x.1.1 * x.2.1, (H ⊔ J).mul_mem (show x.1.1 ∈ H ⊔ J from
      (show H ≤ H ⊔ J from le_sup_left) x.1.2)
      (show x.2.1 ∈ H ⊔ J from
        (show J ≤ H ⊔ J from le_sup_right) x.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases Subgroup.mem_sup.mp hx with ⟨h, hh, j, hj, rfl⟩
    exact ⟨(⟨h, hh⟩, ⟨j, hj⟩), rfl⟩
  simpa [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

/-- Finite-family form of the inertia-group cardinality bound used in the
proof of the global cyclotomic inertia argument. -/
theorem natCard_finsetSup_le_prod_natCard
    (s : Finset ι) (I : ι → Subgroup G) :
    Nat.card ↥(s.sup I : Subgroup G) ≤ ∏ i ∈ s, Nat.card (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sup_insert, Finset.prod_insert ha]
      exact (natCard_sup_le_mul_natCard (I a) (s.sup I)).trans
        (Nat.mul_le_mul_left _ ih)

end RamificationTheory

end
