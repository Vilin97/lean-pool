/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairStab

/-!
# Orbit–stabilizer for pair colourings

Pair contents, the orbit–stabilizer identity for pair-colouring
classes (transported along `finProdFinEquiv`), and the
fibre-margin partition.
-/

namespace RS

open Finset Equiv

variable {n k : ℕ}

/-- The content multiset of a pair colouring. -/
def pairContent (p : Fin n → Fin k × Fin k) :
    Multiset (Fin k × Fin k) :=
  Finset.univ.val.map p

/-- A pair-colouring's fibre size is the pair's multiplicity in its
content. -/
theorem pairFibre_eq_count (p : Fin n → Fin k × Fin k)
    (c : Fin k × Fin k) :
    pairFibre p c = (pairContent p).count c := by
  classical
  rw [pairFibre, pairContent, Multiset.count_map]
  rw [Multiset.filter_congr
    (fun x _ => (eq_comm : c = p x ↔ p x = c))]
  rfl

/-- Content of the transported colouring. -/
theorem content_comp_equiv (p : Fin n → Fin k × Fin k) :
    (content (finProdFinEquiv ∘ p)).1 =
      (pairContent p).map finProdFinEquiv := by
  rw [content, pairContent]
  change Finset.univ.val.map (finProdFinEquiv ∘ p) = _
  rw [← Multiset.map_map]

open scoped Classical in
/-- **Orbit–stabilizer for pair classes**: the class size times the
content factorial product is `n!`. -/
theorem pair_orbit_stab (p₀ : Fin n → Fin k × Fin k) :
    Fintype.card {p : Fin n → Fin k × Fin k //
        pairContent p = pairContent p₀} *
      ∏ c : Fin k × Fin k,
        ((pairContent p₀).count c).factorial = n.factorial := by
  classical
  have h := orbit_stab (finProdFinEquiv ∘ p₀)
    (card_fixing_perms (finProdFinEquiv ∘ p₀))
  have hkey : ∀ g : Fin n → Fin (k * k),
      (content g).1 =
        (pairContent (fun i => finProdFinEquiv.symm (g i))).map
          finProdFinEquiv := by
    intro g
    have h1 := content_comp_equiv
      (fun i => finProdFinEquiv.symm (g i))
    rw [show (finProdFinEquiv ∘ fun i =>
        finProdFinEquiv.symm (g i)) = g from
      funext fun i => Equiv.apply_symm_apply _ _] at h1
    exact h1
  have hcardeq :
      Fintype.card {g : Fin n → Fin (k * k) //
        content g = content (finProdFinEquiv ∘ p₀)} =
      Fintype.card {p : Fin n → Fin k × Fin k //
        pairContent p = pairContent p₀} := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquiv
      (Equiv.arrowCongr (Equiv.refl (Fin n))
        finProdFinEquiv).symm (fun g => ?_)
    rw [show ((Equiv.arrowCongr (Equiv.refl (Fin n))
        finProdFinEquiv).symm g : Fin n → Fin k × Fin k) =
      fun i => finProdFinEquiv.symm (g i) from rfl]
    constructor
    · intro hc
      apply Multiset.map_injective finProdFinEquiv.injective
      rw [← hkey g, ← content_comp_equiv p₀]
      exact congrArg Subtype.val hc
    · intro hc
      apply Subtype.ext
      rw [hkey g, content_comp_equiv p₀, hc]
  have hcnt : ∀ j : Fin (k * k),
      ((pairContent p₀).map finProdFinEquiv).count j =
        (pairContent p₀).count (finProdFinEquiv.symm j) := by
    intro j
    conv_lhs => rw [show j =
      finProdFinEquiv (finProdFinEquiv.symm j) from
      (Equiv.apply_symm_apply _ _).symm]
    exact Multiset.count_map_eq_count' _ _
      finProdFinEquiv.injective _
  have hprodeq :
      (∏ j : Fin (k * k),
        ((content (finProdFinEquiv ∘ p₀)).1.count j).factorial) =
      ∏ c : Fin k × Fin k,
        ((pairContent p₀).count c).factorial := by
    rw [show (∏ j : Fin (k * k),
        ((content (finProdFinEquiv ∘ p₀)).1.count j).factorial) =
      ∏ j : Fin (k * k),
        (((pairContent p₀).map finProdFinEquiv).count
          j).factorial from by rw [content_comp_equiv]]
    rw [Finset.prod_congr rfl
      (fun j (_ : j ∈ Finset.univ) => by rw [hcnt j])]
    exact Equiv.prod_comp finProdFinEquiv.symm
      (fun c => ((pairContent p₀).count c).factorial)
  rw [hcardeq, hprodeq] at h
  exact h

open scoped Classical in
/-- **The fibre-margin partition**: a first-coordinate fibre size
is the row sum of the pair fibres. -/
theorem fibreCard_fst_eq_sum (p : Fin n → Fin k × Fin k)
    (a : Fin k) :
    fibreCard (fun i => (p i).1) a =
      ∑ b : Fin k, pairFibre p (a, b) := by
  classical
  rw [fibreCard]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun i => (p i).2) (t := Finset.univ)
    (fun i _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pairFibre, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  constructor
  · intro hi
    exact Prod.ext hi.1 hi.2
  · intro hi
    exact ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩

open scoped Classical in
/-- The second-coordinate analogue. -/
theorem fibreCard_snd_eq_sum (p : Fin n → Fin k × Fin k)
    (b : Fin k) :
    fibreCard (fun i => (p i).2) b =
      ∑ a : Fin k, pairFibre p (a, b) := by
  classical
  rw [fibreCard]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun i => (p i).1) (t := Finset.univ)
    (fun i _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pairFibre, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  constructor
  · intro hi
    exact Prod.ext hi.2 hi.1
  · intro hi
    exact ⟨congrArg Prod.snd hi, congrArg Prod.fst hi⟩

end RS
