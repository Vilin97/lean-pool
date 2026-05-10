/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.Sensitivity.Defs
import LeanPool.Sensitivity.Multilinear

/-!
# Subcube Restriction

We define the restriction of a Boolean function to a subcube by fixing some
coordinates to a base assignment, and prove that this operation can only
decrease sensitivity and preserves Möbius coefficients on subsets of the
"free" coordinates.

## Main definitions

* `LeanPoolSensitivity.embed` — embed a free-coordinate assignment into a
  full input by reading the remaining coordinates from a base assignment.
* `LeanPoolSensitivity.BoolFun.restrictTo` — restrict `f` by fixing the
  coordinates outside `free` to `base`.

## Main results

* `LeanPoolSensitivity.BoolFun.restrictTo_sensitivity_le` — restriction
  cannot increase sensitivity.
* `LeanPoolSensitivity.BoolFun.exists_fullDegree_restriction` — if `f` has
  positive degree `d`, there is a subcube of dimension `d` on which the
  restriction has full degree `d`.
-/

namespace LeanPoolSensitivity

variable {n : ℕ}

/-- Embed an assignment of the "free" coordinates into the full hypercube by
copying values from `base` on the non-free coordinates. -/
def embed (free : Finset (Fin n)) (base : Fin n → Bool)
    (x : Fin n → Bool) : Fin n → Bool :=
  fun j => if j ∈ free then x j else base j

/-- For a free coordinate `i`, embedding commutes with flipping bit `i`. -/
theorem embed_flipBit_free (free : Finset (Fin n)) (base x : Fin n → Bool)
    (i : Fin n) (hi : i ∈ free) :
    embed free base (flipBit x i) = flipBit (embed free base x) i := by
  funext j
  by_cases hji : j = i
  · subst hji; simp [embed, flipBit, hi]
  · by_cases hj : j ∈ free
    · simp [embed, hj, flipBit, Function.update_of_ne hji]
    · simp only [embed, hj, ↓reduceIte, flipBit]
      rw [Function.update_of_ne hji]
      simp [embed, hj]

/-- For a non-free coordinate `i`, embedding ignores flips at `i`. -/
theorem embed_flipBit_nonfree (free : Finset (Fin n)) (base x : Fin n → Bool)
    (i : Fin n) (hi : i ∉ free) :
    embed free base (flipBit x i) = embed free base x := by
  funext j
  simp only [embed, flipBit]
  by_cases hj : j ∈ free
  · simp [hj, Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
  · simp [hj]

/-- Embedding the indicator of `T ⊆ S ⊆ free` with `base = false` recovers
the original indicator of `T`. -/
theorem embed_indicator_subset (free S T : Finset (Fin n))
    (hS : S ⊆ free) (hT : T ⊆ S) :
    embed free (fun _ => false) (indicator T) = indicator T := by
  funext j
  simp only [embed]
  by_cases hj : j ∈ free
  · simp only [if_pos hj]
  · simp only [if_neg hj, indicator]
    have : j ∉ T := fun hjT => absurd (hS (hT hjT)) hj
    simp only [decide_eq_false this]

namespace BoolFun

/-- Restriction of `f` to the subcube parametrised by the free coordinates
`free` and the fixed assignment `base` on the remaining coordinates. -/
def restrictTo (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) : BoolFun n :=
  fun x => f (embed free base x)

/-- Flipping a coordinate outside `free` does not change the restriction. -/
theorem restrictTo_flipBit_nonfree (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    f.restrictTo free base (flipBit x i) = f.restrictTo free base x := by
  unfold restrictTo
  rw [embed_flipBit_nonfree free base x i hi]

/-- The restriction is never sensitive in a coordinate outside `free`. -/
theorem restrictTo_not_sensitiveAt_nonfree (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) (x : Fin n → Bool) (i : Fin n) (hi : i ∉ free) :
    ¬(f.restrictTo free base).sensitiveAt x i := by
  unfold sensitiveAt
  intro hcontra
  exact hcontra (f.restrictTo_flipBit_nonfree free base x i hi)

/-- Restriction cannot increase sensitivity. -/
theorem restrictTo_sensitivity_le (f : BoolFun n) (free : Finset (Fin n))
    (base : Fin n → Bool) :
    (f.restrictTo free base).sensitivity ≤ f.sensitivity := by
  apply Finset.sup_le
  intro x _
  apply le_trans _ (f.localSensitivity_le_sensitivity (embed free base x))
  unfold localSensitivity
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hi
  unfold sensitiveAt at hi ⊢
  by_cases him : i ∈ free
  · unfold restrictTo at hi
    rw [embed_flipBit_free free base x i him] at hi
    exact hi
  · exfalso
    exact f.restrictTo_not_sensitiveAt_nonfree free base x i him hi

/-- Restricting with `base = false` preserves Möbius coefficients on subsets
of the free coordinates. -/
theorem restrictTo_moebius_subset (f : BoolFun n) (free : Finset (Fin n))
    (S : Finset (Fin n)) (hS : S ⊆ free) :
    (f.restrictTo free (fun _ => false)).moebius S = f.moebius S := by
  unfold moebius restrictTo
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  congr 1
  rw [embed_indicator_subset free S T hS hT]

/-- Key lemma: if `f` has degree `d ≥ 1`, there is a subcube of dimension `d`
on which the restriction has full degree `d` (its top Möbius coefficient is
nonzero). -/
theorem exists_fullDegree_restriction (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n),
      S.card = f.degree ∧
      f.moebius S ≠ 0 ∧
      (f.restrictTo S (fun _ => false)).moebius S ≠ 0 := by
  obtain ⟨S, hcard, hne⟩ := f.exists_degree_witness hd
  exact ⟨S, hcard, hne, by rwa [f.restrictTo_moebius_subset S S Finset.Subset.rfl]⟩

end BoolFun

end LeanPoolSensitivity
