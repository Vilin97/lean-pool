/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiniteRows
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality

/-!
# The length-two part of the corrected cross-one-off finite count

For strand length two, every unordered pair of indices in `Fin (g - 1)`
selects a distinct inversion: its smaller index selects an odd row and its
larger index selects a later even row.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- The explicit length-two forced inversion attached to an unordered pair. -/
noncomputable def crossOneOffLengthTwoPair (g : ℕ) :
    Sym2 (Fin (g - 1)) → ℕ × ℕ :=
  Sym2.lift ⟨fun a b =>
    (2 * min a.val b.val + 3, 2 * max a.val b.val + 4), by
      intro a b
      simp [min_comm, max_comm]⟩

theorem crossOneOffLengthTwoPair_injective (g : ℕ) :
    Function.Injective (crossOneOffLengthTwoPair g) := by
  intro x y hxy
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [crossOneOffLengthTwoPair, Sym2.lift_mk,
        Prod.mk.injEq] at hxy
      have hMin : min a.val b.val = min c.val d.val := by omega
      have hMax : max a.val b.val = max c.val d.val := by omega
      apply endpointPairEmbedding_injective (g - 1)
      simp only [endpointPairEmbedding, Sym2.lift_mk, Prod.mk.injEq]
      exact ⟨by exact_mod_cast hMin, by exact_mod_cast congrArg Nat.succ hMax⟩

private theorem crossOneOffLengthTwoPair_mem
    {g : ℕ} (hg : 2 ≤ g) (x : Sym2 (Fin (g - 1))) :
    crossOneOffLengthTwoPair g x ∈ crossOneOffForcedInversionPairs g 2 := by
  induction x using Sym2.ind with
  | _ a b =>
    let m := min a.val b.val
    let M := max a.val b.val
    change (2 * m + 3, 2 * M + 4) ∈
      crossOneOffForcedInversionPairs g 2
    have hm : m ≤ M := min_le_max
    have hM : M < g - 1 := max_lt a.isLt b.isLt
    have hOddRow : crossOneOffRow g 2 (2 * m + 3) = g + m + 2 := by
      have hMod : (2 * m + 3) % 2 = 1 := by omega
      have hDiv : (2 * m + 3) / 2 = m + 1 := by omega
      simp [crossOneOffRow, hMod, hDiv]
      omega
    have hEvenRow : crossOneOffRow g 2 (2 * M + 4) = M + 3 := by
      have hMod : (2 * M + 4) % 2 = 0 := by omega
      have hDiv : (2 * M + 4) / 2 = M + 2 := by omega
      simp [crossOneOffRow, hMod, hDiv]
    rw [crossOneOffForcedInversionPairs, finiteRowInversionPairs,
      Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
      Finset.mem_Icc.mpr ?_⟩, ?_⟩
    · constructor
      · omega
      · simp [crossOneOffCutoff]
        omega
    · constructor
      · omega
      · simp [crossOneOffCutoff]
        omega
    · constructor
      · omega
      · rw [hOddRow, hEvenRow]
        omega

/-- The corrected `n = 2` target is certified by the finite forced block. -/
theorem correctedCrossOneOffForcedCount_le_card_length_two
    {g : ℕ} (hg : 2 ≤ g) :
    correctedCrossOneOffForcedCount g 2 ≤
      (crossOneOffForcedInversionPairs g 2).card := by
  have hmap : ∀ x : Sym2 (Fin (g - 1)), x ∈ Set.univ →
      crossOneOffLengthTwoPair g x ∈
        (crossOneOffForcedInversionPairs g 2 : Set (ℕ × ℕ)) := by
    intro x _
    exact crossOneOffLengthTwoPair_mem hg x
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (Set.univ : Set (Sym2 (Fin (g - 1)))))
    (t := (crossOneOffForcedInversionPairs g 2 : Set (ℕ × ℕ)))
    (crossOneOffLengthTwoPair g) hmap
    (crossOneOffLengthTwoPair_injective g).injOn
    (crossOneOffForcedInversionPairs g 2).finite_toSet
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  change (Finset.univ : Finset (Sym2 (Fin (g - 1)))).card ≤ _ at hle
  rw [← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ] at hle
  simpa [correctedCrossOneOffForcedCount,
    Nat.sub_add_cancel (by omega : 1 ≤ g)] using hle

end Bananas
