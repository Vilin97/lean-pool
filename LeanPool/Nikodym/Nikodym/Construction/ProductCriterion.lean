/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Definition

/-!
# Product-complement criterion

Blueprint node P01: if a product set `P = ∏ Pⱼ ⊆ F^h` (`h ≥ 2`) has a tangent line at every
point of `P`, then the complement `univ \ P` is a Nikodym set. The file also records the
cardinality identity `|univ \ P| = q^h - |P|` in `ℕ` and in `ℝ`.
-/

namespace Nikodym

open scoped Classical in
/-- Blueprint P01: if every point of the product `Fintype.piFinset P` has a direction whose
punctured line misses the product, then the complement is a Nikodym set. Points already outside
the product are handled by a coordinate-preserving direction `Pi.single k 1`. -/
theorem isNikodym_univ_sdiff_piFinset {F : Type*} [Field F] [Fintype F] {h : ℕ} (hh : 2 ≤ h)
    (P : Fin h → Finset F)
    (hP : ∀ u ∈ Fintype.piFinset P, ∃ v : Fin h → F, v ≠ 0 ∧
      ∀ t : F, t ≠ 0 → u + t • v ∉ Fintype.piFinset P) :
    IsNikodym (Finset.univ \ Fintype.piFinset P) := by
  intro u
  by_cases hu : u ∈ Fintype.piFinset P
  · obtain ⟨v, hv0, hv⟩ := hP u hu
    exact ⟨v, hv0, fun t ht ↦ Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hv t ht⟩⟩
  · have : ∃ j, u j ∉ P j := by
      simpa [Fintype.mem_piFinset] using hu
    obtain ⟨j, hj⟩ := this
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by
      rw [Fintype.card_fin]
      exact Nat.succ_le_iff.mp hh) j
    refine ⟨Pi.single k 1, Pi.single_ne_zero_iff.2 one_ne_zero, fun t _ht ↦ ?_⟩
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    refine not_forall.2 ⟨j, ?_⟩
    convert hj
    simp [Pi.single_eq_of_ne' hk]

open scoped Classical in
/-- Blueprint P01: `|univ \ P| = q^h - |P|`. -/
theorem card_univ_sdiff {F : Type*} [Fintype F] {h : ℕ} (P : Finset (Fin h → F)) :
    (Finset.univ \ P).card = Fintype.card F ^ h - P.card := by
  rw [Finset.card_univ_sdiff, Fintype.card_fun, Fintype.card_fin]

open scoped Classical in
/-- Blueprint P01: the same identity after coercion to `ℝ`. -/
theorem card_univ_sdiff_real {F : Type*} [Fintype F] {h : ℕ} (P : Finset (Fin h → F)) :
    ((Finset.univ \ P).card : ℝ) = (Fintype.card F : ℝ) ^ h - P.card := by
  have hle : P.card ≤ Fintype.card F ^ h := by
    simpa [Fintype.card_fun, Fintype.card_fin] using P.card_le_univ
  rw [card_univ_sdiff, Nat.cast_sub hle, Nat.cast_pow]

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
