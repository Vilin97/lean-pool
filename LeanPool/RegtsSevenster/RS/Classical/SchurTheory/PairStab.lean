/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ColourWeight

/-!
# Stabilizer counts for pair colourings

The stabilizer count for colourings by pairs, transported along
`finProdFinEquiv` from the `Fin`-codomain machinery.
-/

@[expose] public section

namespace RS

open Finset Equiv

variable {n k : ℕ}

open scoped Classical in
/-- The fibre size of a pair colouring over a pair colour. -/
noncomputable def pairFibre (p : Fin n → Fin k × Fin k)
    (c : Fin k × Fin k) : ℕ :=
  (Finset.univ.filter (fun i => p i = c)).card

open scoped Classical in
/-- **The pair stabilizer count**: permutations fixing a pair
colouring number the product of its fibre factorials. -/
theorem card_fixing_pairs (p : Fin n → Fin k × Fin k) :
    (Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => p ∘ π = p)).card =
      ∏ c : Fin k × Fin k, (pairFibre p c).factorial := by
  classical
  have hcond : ∀ π : Equiv.Perm (Fin n),
      ((finProdFinEquiv ∘ p) ∘ π = finProdFinEquiv ∘ p) ↔
      (p ∘ π = p) := by
    intro π
    constructor
    · intro h
      funext i
      have h1 := congrFun h i
      exact finProdFinEquiv.injective h1
    · intro h
      funext i
      have h1 := congrFun h i
      change finProdFinEquiv (p (π i)) = finProdFinEquiv (p i)
      rw [show p (π i) = p i from h1]
  have h1 : (Finset.univ.filter
      (fun π : Equiv.Perm (Fin n) => p ∘ π = p)).card =
      (Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) =>
          (finProdFinEquiv ∘ p) ∘ π = finProdFinEquiv ∘ p)).card := by
    congr 1
    exact Finset.filter_congr fun π _ => (hcond π).symm
  rw [h1, card_fixing_perms (finProdFinEquiv ∘ p)]
  have h2 : ∀ j : Fin (k * k),
      fibreCard (finProdFinEquiv ∘ p) j =
        pairFibre p (finProdFinEquiv.symm j) := by
    intro j
    rw [fibreCard, pairFibre]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    change finProdFinEquiv (p i) = j ↔ p i = finProdFinEquiv.symm j
    exact (Equiv.eq_symm_apply finProdFinEquiv).symm
  rw [Finset.prod_congr rfl (fun j _ => by rw [h2 j])]
  exact Equiv.prod_comp finProdFinEquiv.symm
    (fun c => (pairFibre p c).factorial)

end RS
