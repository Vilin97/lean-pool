/-
Copyright (c) 2026 Rémy Degenne, Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

import Mathlib.MeasureTheory.SetSemiring

/-! # Semirings of sets

A semi-ring of sets `C` is a family of sets containing `∅`, stable by intersection and such that
for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of finitely many sets in `C`.

THIS FILE IS NOT USED FOR THE MAIN RESULT
-/


variable {α : Type*} {C : Set (Set α)} {s t : Set α} {J : Finset (Set α)}

open Finset Set

namespace MeasureTheory

/-- A field of sets is a family of sets which is stable under union, difference, and contains
the empty set and the whole space.
-/
structure IsSetField (C : Set (Set α)) : Prop extends IsSetRing C where
  univ_mem : Set.univ ∈ C

namespace IsSetField

theorem inter_mem (hC : IsSetField C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C :=
  hC.toIsSetRing.inter_mem hs ht

theorem compl_mem (hC : IsSetField C) (hs : s ∈ C) : sᶜ ∈ C := by
  rw [compl_eq_univ_sdiff]; exact hC.sdiff_mem hC.univ_mem hs

theorem toIsSetSemiring (hC : IsSetField C) : IsSetSemiring C :=
  hC.toIsSetRing.isSetSemiring

theorem iUnion_le_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C :=
  hC.toIsSetRing.iUnion_le_mem hs n

theorem iInter_le_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C :=
  hC.toIsSetRing.iInter_le_mem hs n

theorem partialSups_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    partialSups s n ∈ C :=
  hC.toIsSetRing.partialSups_mem hs n

theorem disjointed_mem (hC : IsSetField C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    disjointed s n ∈ C :=
  hC.toIsSetRing.disjointed_mem hs n

end IsSetField

end MeasureTheory
