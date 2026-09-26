/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SameCycleQuot

/-!
# The orbit factorization of a fixed-colouring sum

For a permutation `π` of `Fin n`, the sum of colouring weights
over the colourings fixed by `π` factorizes over the orbit space:
each orbit is coloured uniformly, contributing a power sum in its
size.
-/

@[expose] public section

namespace RS

open Finset Equiv Equiv.Perm

/-- The completed cycle-type product of a prospective power-sum
sequence: the product over the full cycle type, fixed points
included. -/
noncomputable def cycleProd (t : ℕ → ℂ) {n : ℕ}
    (π : Equiv.Perm (Fin n)) : ℂ :=
  (π.cycleType.map t).prod * t 1 ^ (n - π.cycleType.sum)

variable {n N : ℕ}

/-- **The orbit factorization**: the fixed-colouring weight sum of
a permutation is the product of the power sums of its orbit
sizes. -/
theorem sum_fixedFun_eq_prod_orbits (x : Fin N → ℂ)
    (π : Equiv.Perm (Fin n)) :
    (∑ f : {f : Fin n → Fin N // f ∘ π = f}, ∏ i, x (f.1 i)) =
      ∏ O : OrbitSpace π, pVal x (orbCard π O) := by
  classical
  rw [Fintype.sum_equiv (fixedFunEquiv π (Fin N))
    (fun f => ∏ i, x (f.1 i))
    (fun g => ∏ O, x (g O) ^ orbCard π O) ?_]
  · -- the coloured-orbit sum is the product of power sums
    rw [show (∏ O : OrbitSpace π, pVal x (orbCard π O)) =
      ∏ O : OrbitSpace π, ∑ j ∈ (Finset.univ : Finset (Fin N)),
        x j ^ orbCard π O from Finset.prod_congr rfl fun O _ => rfl]
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  · -- pointwise: group the weight product by orbits
    intro f
    rw [← Finset.prod_fiberwise_of_maps_to
      (g := orbitOf π) (t := (Finset.univ : Finset (OrbitSpace π)))
      (fun i _ => Finset.mem_univ _) (fun i => x (f.1 i))]
    refine Finset.prod_congr rfl fun O _ => ?_
    have hfib : Finset.univ.filter (fun i => orbitOf π i = O) =
        orbFibre π O := by
      rw [orbFibre]
    rw [hfib]
    rw [Finset.prod_congr rfl (fun i hi =>
      show x (f.1 i) = x (fixedFunEquiv π (Fin N) f O) from by
        rw [← (mem_orbFibre π).mp hi]
        exact (congrArg x
          (fixedFunEquiv_apply_orbitOf π f i)).symm)]
    rw [Finset.prod_const, orbCard]

end RS
