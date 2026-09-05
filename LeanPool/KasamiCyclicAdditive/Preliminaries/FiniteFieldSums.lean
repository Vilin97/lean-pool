/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude

/-!
# Finite-field sum decompositions

Elementary identities relating sums over the units of a finite field to sums
over the whole field. This module is deliberately below the character-sum
and MCM layers so that both can use the same finite-field infrastructure.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- A sum over the unit group equals the sum over the whole field, for a function
vanishing at `0`. -/
lemma sum_units_eq_sum {M : Type*} [AddCommMonoid M] (f : K → M) (hf : f 0 = 0) :
    ∑ b : Kˣ, f (b : K) = ∑ a : K, f a := by
  have h0 : ∀ x ∈ (Finset.univ : Finset K), x ∉ ({0}ᶜ : Finset K) → f x = 0 := by
    intro x _ hx
    simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at hx
    simp [hx, hf]
  rw [← Finset.sum_subset (Finset.subset_univ ({0}ᶜ : Finset K)) h0]
  refine Finset.sum_nbij' (fun b => (b : K)) (fun a => if h : a = 0 then 1 else Units.mk0 a h)
    ?_ ?_ ?_ ?_ ?_ <;> intro a ha <;> simp_all

/-- Splitting off the value at `0` from a sum over the whole field. -/
lemma sum_units_add {M : Type*} [AddCommMonoid M] (f : K → M) :
    f 0 + ∑ b : Kˣ, f (b : K) = ∑ a : K, f a := by
  have h1 : ∑ b : Kˣ, f (b : K) = ∑ a ∈ ({0} : Finset K)ᶜ, f a := by
    refine Finset.sum_nbij' (fun b : Kˣ => (b : K))
      (fun a : K => if h : a = 0 then 1 else Units.mk0 a h) ?_ ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp_all
  rw [h1, ← Finset.sum_add_sum_compl ({0} : Finset K) f, Finset.sum_singleton]

end KasamiCyclicAdditive
