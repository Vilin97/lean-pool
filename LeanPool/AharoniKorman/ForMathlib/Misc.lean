/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Attr.Core

/-!
# Results for mathlib

A collection of results for the disproof of the Aharoni–Korman conjecture which should be in
mathlib.
-/

@[expose] public section

namespace LeanPool.AharoniKorman

lemma chain_intersect_antichain {α : Type*} [PartialOrder α] {s t : Set α}
    (hs : IsChain (· ≤ ·) s) (ht : IsAntichain (· ≤ ·) t) :
    (s ∩ t).Subsingleton := by
  simp only [Set.Subsingleton, Set.mem_inter_iff, and_imp]
  intro x hxs hxt y hys hyt
  by_contra! hne
  cases hs.total hxs hys
  case inl h => exact ht hxt hyt hne h
  case inr h => exact ht hyt hxt hne.symm h

end LeanPool.AharoniKorman
