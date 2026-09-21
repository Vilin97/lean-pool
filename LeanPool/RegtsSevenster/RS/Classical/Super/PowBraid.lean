/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPower

/-!
# Adjacent braidings on monoidal powers

The braiding of two adjacent factors of a monoidal power: the top
case conjugates the braiding through one associator, and lower
positions whisker the smaller power's braiding.  On the colouring
model the intended action is the Koszul-signed position swap,
defined here; the identification is the coordinate workhorse of
the extraction.
-/

namespace RS

open CategoryTheory MonoidalCategory

/-- The top adjacent braiding on a monoidal power: braid the last
two factors through the associator. -/
noncomputable def topBraid (V : SuperVect) (m : ℕ) :
    superPow V (m + 2) ⟶ superPow V (m + 2) :=
  (α_ (superPow V m) V V).hom ≫
    (superPow V m ◁ (β_ V V).hom) ≫
    (α_ (superPow V m) V V).inv

/-- The adjacent braiding at position `i`: swap the factors at
zero-based positions `i` and `i + 1`. -/
noncomputable def powBraid (V : SuperVect) :
    (n : ℕ) → (i : ℕ) → i + 2 ≤ n →
      (superPow V n ⟶ superPow V n)
  | 0, _, h => absurd h (by omega)
  | 1, _, h => absurd h (by omega)
  | n + 2, i, h =>
    if hi : i = n then topBraid V n
    else (powBraid V (n + 1) i (by omega)) ▷ V

/-- Reindexing a colouring along a permutation preserves the odd
count. -/
theorem MixedColouring.oddSet_comp_card {k ℓ d : ℕ}
    (c : MixedColouring k ℓ d) (σ : _root_.Equiv.Perm (Fin d)) :
    (MixedColouring.oddSet (c ∘ σ)).card =
      c.oddSet.card := by
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro i hi
    simp only [MixedColouring.oddSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · intro a _ b _ hab
    exact σ.injective hab
  · intro j hj
    refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
    simp only [MixedColouring.oddSet, Finset.mem_filter,
      Finset.mem_univ, true_and,
      Function.comp_apply, σ.apply_symm_apply] at hj ⊢
    exact hj

/-- Reindexing preserves evenness. -/
theorem MixedColouring.IsEven.comp {k ℓ d : ℕ}
    {c : MixedColouring k ℓ d}
    (hc : c.IsEven) (σ : _root_.Equiv.Perm (Fin d)) :
    MixedColouring.IsEven (c ∘ σ) := by
  unfold MixedColouring.IsEven
  rw [MixedColouring.oddSet_comp_card c σ]
  exact hc

/-- Reindexing preserves oddness. -/
theorem MixedColouring.not_isEven_comp {k ℓ d : ℕ}
    {c : MixedColouring k ℓ d}
    (hc : ¬ c.IsEven) (σ : _root_.Equiv.Perm (Fin d)) :
    ¬ MixedColouring.IsEven (c ∘ σ) := by
  intro hcontra
  apply hc
  unfold MixedColouring.IsEven at hcontra ⊢
  rw [MixedColouring.oddSet_comp_card c σ] at hcontra
  exact hcontra

/-- The Koszul sign of swapping two positions of a colouring:
`−1` when both are odd. -/
def adjSign {k ℓ d : ℕ} (c : MixedColouring k ℓ d)
    (a b : Fin d) : ℂ :=
  if (c a).isRight ∧ (c b).isRight then -1 else 1

/-- The Koszul-signed adjacent position swap on the colouring
model. -/
noncomputable def colourSwap (k ℓ : ℕ) :
    (n : ℕ) → (i : ℕ) → i + 2 ≤ n →
      (colourPower k ℓ n ⟶ colourPower k ℓ n) :=
  fun n i h =>
  { evenMap :=
    { toFun := fun F c =>
        adjSign c.val ⟨i, by omega⟩ ⟨i + 1, by omega⟩ *
          F ⟨c.val ∘ _root_.Equiv.swap
              (⟨i, by omega⟩ : Fin n) ⟨i + 1, by omega⟩,
            c.prop.comp _⟩
      map_add' := fun F G => by
        funext c
        exact mul_add _ (F _) (G _)
      map_smul' := fun r F => by
        funext c
        exact mul_left_comm _ r (F _) }
    oddMap :=
    { toFun := fun F c =>
        adjSign c.val ⟨i, by omega⟩ ⟨i + 1, by omega⟩ *
          F ⟨c.val ∘ _root_.Equiv.swap
              (⟨i, by omega⟩ : Fin n) ⟨i + 1, by omega⟩,
            MixedColouring.not_isEven_comp c.prop _⟩
      map_add' := fun F G => by
        funext c
        exact mul_add _ (F _) (G _)
      map_smul' := fun r F => by
        funext c
        exact mul_left_comm _ r (F _) } }

end RS
