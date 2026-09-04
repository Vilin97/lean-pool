/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.WORealization
import Mathlib.Order.Interval.Finset.Fin

/-!
# Marking extension: the range-based constant split (issue #12, commit 4b part 2)

The constant-sensitive closure rules split an arbitrary constant `c` by
**`c ∈ Set.range ratConstIdx`** — not by parity coding (per review: `ratConstIdx` is
injective but not proved surjective onto the evens; unused even indices are treated exactly
like Henkin constants, as ordinary auxiliary constants with no rank insertion).

* `henkinConstIdx_notMem_range_ratConstIdx` — fresh existential witnesses chosen odd are
  automatically outside the rational range.
* `add_lt_omega1` / `add_one_lt_omega1` — `ω₁` is closed under the (*)-level arithmetic the
  fields need (`β := α + α + 1`).
* `exists_insertNth_slot` — an unmarked rational has a slot at which inserting it keeps the
  marking enumeration strictly monotone (via the initial-segment characterization of the
  below-`q₀` marks).
* `StarWitness.add_sentence` — the generic closure step: a sentence realized by the witness
  whose rationals are already marked extends the remainder.
* `StarWitness.mark_rat` — the composite rational-marking operation: an unmarked rational is
  re-pointed to an engine-provided chain point (`GapWitness.exists_insertNth`) at the strict-
  monotonicity slot; freshness for the remainder is automatic (an unmarked rational cannot be
  mentioned, by `mark_cover`), so remainder realization transports by the repointing
  invariant.  Already-marked rationals need only downward closure.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## The range split -/

/-- Odd (Henkin) constants lie outside the rational range — parity. -/
theorem henkinConstIdx_notMem_range_ratConstIdx (n : ℕ) :
    henkinConstIdx n ∉ Set.range ratConstIdx := by
  rintro ⟨q, hq⟩
  exact ratConstIdx_ne_henkinConstIdx q n hq

/-! ## `ω₁` arithmetic -/

/-- `ω₁` is closed under addition. -/
theorem add_lt_omega1 {α β : Ordinal.{0}} (hα : α < (Cardinal.aleph 1).ord)
    (hβ : β < (Cardinal.aleph 1).ord) : α + β < (Cardinal.aleph 1).ord := by
  rw [Cardinal.lt_ord] at hα hβ ⊢
  calc (α + β).card ≤ α.card + β.card := le_of_eq (Ordinal.card_add α β)
    _ < Cardinal.aleph 1 :=
      Cardinal.add_lt_of_lt (le_of_lt Cardinal.aleph0_lt_aleph_one) hα hβ

/-- `ω₁` is closed under successor. -/
theorem add_one_lt_omega1 {α : Ordinal.{0}} (hα : α < (Cardinal.aleph 1).ord) :
    α + 1 < (Cardinal.aleph 1).ord := by
  have hlim : Order.IsSuccLimit ((Cardinal.aleph 1).ord) :=
    Cardinal.isSuccLimit_ord (le_of_lt Cardinal.aleph0_lt_aleph_one)
  exact hlim.add_one_lt hα

/-! ## The strict-monotonicity slot -/

/-- The range of an inserted tuple. -/
theorem range_insertNth {m : ℕ} {γ : Type*} (s : Fin (m + 1)) (x : γ) (f : Fin m → γ) :
    Set.range (Fin.insertNth s x f) = insert x (Set.range f) := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i = s
    · rw [hi, Fin.insertNth_apply_same]
      exact Set.mem_insert _ _
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [Fin.insertNth_apply_succAbove]
      exact Set.mem_insert_of_mem _ ⟨k, rfl⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨s, Fin.insertNth_apply_same ..⟩
    · exact ⟨s.succAbove k, Fin.insertNth_apply_succAbove ..⟩

/-- **The slot lemma**: an unmarked rational has a slot at which insertion keeps the
enumeration strictly monotone. -/
theorem exists_insertNth_slot {m : ℕ} {mark : Fin m → ℚ} (hm : StrictMono mark)
    {q₀ : ℚ} (hq : q₀ ∉ Set.range mark) :
    ∃ s : Fin (m + 1), StrictMono (Fin.insertNth s q₀ mark) := by
  set c := (Finset.univ.filter fun k : Fin m => mark k < q₀).card with hc
  have hcle : c ≤ m := le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_fin m))
  refine ⟨⟨c, Nat.lt_succ_of_le hcle⟩, ?_⟩
  -- the below-`q₀` marks form the initial segment `[0, c)`
  have hmem : ∀ k : Fin m, mark k < q₀ ↔ (k : ℕ) < c := by
    intro k
    constructor
    · intro hk
      have hsub : Finset.Iic k ⊆ Finset.univ.filter fun j : Fin m => mark j < q₀ := by
        intro j hj
        rw [Finset.mem_Iic] at hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt (hm.monotone hj) hk⟩
      have := Finset.card_le_card hsub
      rw [Fin.card_Iic] at this
      omega
    · intro hk
      by_contra hnot
      have hgt : q₀ < mark k := by
        rcases lt_trichotomy (mark k) q₀ with h | h | h
        · exact absurd h hnot
        · exact absurd ⟨k, h⟩ hq
        · exact h
      have hsub : (Finset.univ.filter fun j : Fin m => mark j < q₀) ⊆ Finset.Iio k := by
        intro j hj
        rw [Finset.mem_Iio]
        exact hm.lt_iff_lt.mp (lt_trans (Finset.mem_filter.mp hj).2 hgt)
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio] at this
      omega
  -- strict monotonicity by the engine's case split
  set s : Fin (m + 1) := ⟨c, Nat.lt_succ_of_le hcle⟩ with hs
  intro i j hij
  by_cases hi : i = s
  · have hij' : s < j := hi ▸ hij
    rw [hi]
    by_cases hj : j = s
    · exact absurd (hj ▸ hij') (lt_irrefl _)
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
      have hl : s ≤ l.castSucc := (Fin.lt_succAbove_iff_le_castSucc s l).mp hij'
      rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      have : ¬ ((l : ℕ) < c) := by
        have hle := Fin.le_def.mp hl
        have hcs : (s : ℕ) = c := rfl
        simp only [Fin.val_castSucc, hcs] at hle
        omega
      rcases lt_trichotomy (mark l) q₀ with h | h | h
      · exact absurd ((hmem l).mp h) this
      · exact absurd ⟨l, h⟩ hq
      · exact h
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    by_cases hj : j = s
    · have hij' : s.succAbove k < s := hj ▸ hij
      rw [hj]
      have hk : k.castSucc < s := (Fin.succAbove_lt_iff_castSucc_lt s k).mp hij'
      rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      refine (hmem k).mpr ?_
      have hlt := Fin.lt_def.mp hk
      have hcs : (s : ℕ) = c := rfl
      simp only [Fin.val_castSucc, hcs] at hlt
      omega
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      exact hm (Fin.succAbove_lt_succAbove_iff.mp hij)

/-! ## The generic closure step -/

/-- **Adding a realized, already-covered sentence**: a sentence realized by the witness whose
mentioned rationals are all marked extends the remainder without touching the marking. -/
def StarWitness.add_sentence {φ : L.Sentenceω} {lt : L.Relations 2}
    {Γ : Set L[[ℕ]].Sentenceω} {α : Ordinal.{0}} (W : StarWitness φ lt Γ α)
    {χ : L[[ℕ]].Sentenceω}
    (hreal : @Sentenceω.Realize L[[ℕ]] χ W.M (wc W.inst W.h))
    (hsupp : ∀ q : ℚ, ratConstIdx q ∈ sentenceJConsts (L' := L) (J := ℕ) χ →
      q ∈ Set.range W.mark) :
    StarWitness φ lt (Γ ∪ {χ}) α where
  M := W.M
  inst := W.inst
  ne := W.ne
  h := W.h
  base_realize := W.base_realize
  rem_realize := by
    intro ψ hψ
    rcases hψ with hψ | hψ
    · exact W.rem_realize ψ hψ
    · rw [Set.mem_singleton_iff] at hψ
      exact hψ ▸ hreal
  m := W.m
  mark := W.mark
  mark_mono := W.mark_mono
  mark_cover := by
    rintro q ⟨ψ, hψ, hmem⟩
    rcases hψ with hψ | hψ
    · exact W.mark_cover ⟨ψ, hψ, hmem⟩
    · rw [Set.mem_singleton_iff] at hψ
      exact hsupp q (hψ ▸ hmem)
  witness := W.witness

/-! ## The composite rational-marking operation -/

/-- **Marking a rational** (the range-split case 1): from a witness at `β` with `α + α < β`,
produce a witness at `α` whose marking covers `q₀`.  Already-marked rationals need only
downward closure; an unmarked rational is automatically fresh for the remainder
(`mark_cover`), so its constant re-points to the engine's chain point at the
strict-monotonicity slot. -/
theorem StarWitness.mark_rat {φ : L.Sentenceω} {lt : L.Relations 2}
    {Γ : Set L[[ℕ]].Sentenceω} {α β : Ordinal.{0}} (W : StarWitness φ lt Γ β)
    (hβ : α + α < β) (q₀ : ℚ) :
    ∃ W' : StarWitness φ lt Γ α, q₀ ∈ Set.range W'.mark ∧
      Set.range W.mark ⊆ Set.range W'.mark := by
  have hαβ : α ≤ β := le_of_lt (lt_of_le_of_lt le_self_add hβ)
  by_cases hmarked : q₀ ∈ Set.range W.mark
  · -- already marked: downward closure only
    obtain ⟨W'⟩ := StarCondition.mono hαβ ⟨W⟩
    -- `mono` preserves the marking data definitionally, but re-establish via the witness
    exact ⟨{ W with witness := @GapWitness.mono L W.M W.inst lt β α hαβ _ _ W.witness },
      hmarked, subset_rfl⟩
  · -- unmarked: automatically fresh for the remainder
    have hfresh : ∀ χ ∈ Γ, ratConstIdx q₀ ∉ sentenceJConsts (L' := L) (J := ℕ) χ :=
      fun χ hχ hc => hmarked (W.mark_cover ⟨χ, hχ, hc⟩)
    let := W.inst
    obtain ⟨s, hs⟩ := exists_insertNth_slot W.mark_mono hmarked
    obtain ⟨x, ⟨Wg⟩⟩ := W.witness.exists_insertNth hβ s
    -- the re-pointed constant map and extended marking
    refine ⟨{
      M := W.M
      inst := W.inst
      ne := W.ne
      h := Function.update W.h (ratConstIdx q₀) x
      base_realize := W.base_realize
      rem_realize := W.rem_realize_update hfresh x
      m := W.m + 1
      mark := Fin.insertNth s q₀ W.mark
      mark_mono := hs
      mark_cover := ?_
      witness := ?_ }, ?_, ?_⟩
    · refine le_trans W.mark_cover ?_
      rw [range_insertNth]
      exact Set.subset_insert _ _
    · -- align the marked-value tuple with the engine's inserted tuple
      have htup : (fun i => Function.update W.h (ratConstIdx q₀) x
          (ratConstIdx ((Fin.insertNth s q₀ W.mark : Fin (W.m + 1) → ℚ) i))) =
          (Fin.insertNth s x (fun i => W.h (ratConstIdx (W.mark i))) :
            Fin (W.m + 1) → W.M) := by
        funext i
        by_cases hi : i = s
        · rw [hi, Fin.insertNth_apply_same, Fin.insertNth_apply_same,
            Function.update_self]
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
          rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
          have hne : ratConstIdx (W.mark k) ≠ ratConstIdx q₀ :=
            fun hc => hmarked ⟨k, ratConstIdx_injective hc⟩
          rw [Function.update_of_ne hne]
      rw [htup]
      exact Wg
    · rw [range_insertNth]
      exact Set.mem_insert _ _
    · rw [range_insertNth]
      exact Set.subset_insert _ _

end FirstOrder.Language
