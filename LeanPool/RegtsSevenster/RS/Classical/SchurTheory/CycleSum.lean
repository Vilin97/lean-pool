/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CycleSumPrep
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.OrbitBridge
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.StabCount
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ContentCount

/-!
# The cycle-sum identity (assembly)

The fixed-colouring sum of a permutation is its completed
cycle-type product in the power sums of the colours; summed over
the symmetric group this yields `n! · h_n`.
-/

namespace RS

open Finset Equiv Equiv.Perm

variable {n N : ℕ}

/-- The fixed-colouring sum of a permutation is its completed
cycle-type product. -/
theorem sum_fixedFun_eq_cycleProd (x : Fin N → ℂ)
    (π : Equiv.Perm (Fin n)) :
    (∑ f : {f : Fin n → Fin N // f ∘ π = f}, ∏ i, x (f.1 i)) =
      cycleProd (pVal x) π := by
  rw [sum_fixedFun_eq_prod_orbits]
  rw [show (∏ O : OrbitSpace π, pVal x (orbCard π O)) =
    (((Finset.univ : Finset (OrbitSpace π)).val.map
      (orbCard π)).map (pVal x)).prod from by
    rw [Multiset.map_map]
    rfl]
  rw [orbCard_multiset]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
    Multiset.prod_replicate]
  rfl

/-- The cycle sum at a realized specialization. -/
theorem cycleSum_spec (x : Fin N → ℂ) :
    (∑ π : Equiv.Perm (Fin n), cycleProd (pVal x) π) =
      (n.factorial : ℂ) * hVal x n := by
  classical
  rw [Finset.sum_congr rfl (fun π (_ : π ∈ Finset.univ) =>
    (sum_fixedFun_eq_cycleProd x π).symm)]
  rw [sum_perm_fixed_weight (fun f => ∏ i, x (f i))]
  rw [Finset.sum_congr rfl (fun f (_ : f ∈ Finset.univ) => by
    rw [card_fixing_perms f])]
  exact sum_fibreFactorial_weight' x card_fixing_perms

/-- **The cycle-sum identity**: over any prospective power-sum
sequence, the completed cycle-type products of all permutations
sum to `n! · h_n`. -/
theorem cycleSum_eq (t : ℕ → ℂ) (n : ℕ) :
    (∑ π : Equiv.Perm (Fin n), cycleProd t π) =
      (n.factorial : ℂ) * newtonH t n := by
  classical
  obtain ⟨N, x, hx⟩ := exists_pVal_eq n t
  rw [Finset.sum_congr rfl (fun π (_ : π ∈ Finset.univ) =>
    cycleProd_congr π (fun c h1 h2 => (hx c h1 h2).symm))]
  rw [cycleSum_spec, ← newtonH_pVal x n,
    newtonH_congr n (fun c hc1 hc2 => hx c hc1 hc2)]

end RS
