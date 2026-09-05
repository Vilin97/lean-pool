/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.GapWitness
import Mathlib.Data.Fin.SuccPred

/-!
# The four-case gap insertion engine (issue #12, risky engine 2)

**One uniform insertion lemma**: a gap witness at `β` with `α + α < β` admits, at every slot
`s : Fin (m + 1)` — below everything, between any two neighbours, above everything, or into
empty support — a chain point whose insertion yields a gap witness at `α` for the extended
tuple.  This is Marker's C7c move ("pick `β > α + α` and place the fresh constant inside a
gap"), made slot-uniform by the terminal and bottom margins (audit v2, D6).

The inserted rank is `α` at slot `0` and `rank (s-1) + α` otherwise (`insertGapRank`); every
margin obligation is ordinal-rank arithmetic, and the four cases collapse into a single
`Fin.succAbove` case analysis.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {M : Type} [L.Structure M] {lt : L.Relations 2}

/-- The rank of the point inserted at slot `s`: `α` below everything (slot `0`), the
predecessor's rank plus `α` otherwise. -/
private def insertGapRank {m : ℕ} (rank : Fin m → Ordinal.{0}) (α : Ordinal.{0})
    (s : Fin (m + 1)) : Ordinal.{0} :=
  Fin.cases α (fun k => rank k + α) s

/-- **The uniform insertion engine**: given a gap witness at `β` with `α + α < β`, every slot
admits a chain point whose insertion is a gap witness at `α`. -/
theorem GapWitness.exists_insertNth {α β : Ordinal.{0}} {m : ℕ} {b : Fin m → M}
    (W : GapWitness lt β b) (hβ : α + α < β) (s : Fin (m + 1)) :
    ∃ x : M, Nonempty (GapWitness lt α (Fin.insertNth s x b)) := by
  have hαβ : α < β := lt_of_le_of_lt le_self_add hβ
  have hαβle : α ≤ β := le_of_lt hαβ
  have hααβle : α + α ≤ β := le_of_lt hβ
  -- the new rank satisfies all one-sided margins, uniformly in the slot
  have hnew_initial : α ≤ insertGapRank W.rank α s := by
    induction s using Fin.cases with
    | zero => simp [insertGapRank]
    | succ t => simp only [insertGapRank, Fin.cases_succ]; exact le_add_self
  have hnew_terminal : insertGapRank W.rank α s + α ≤ W.γ := by
    induction s using Fin.cases with
    | zero =>
      simp only [insertGapRank, Fin.cases_zero]
      exact le_of_lt (lt_of_le_of_lt hααβle W.lt_gamma)
    | succ t =>
      simp only [insertGapRank, Fin.cases_succ]
      calc W.rank t + α + α = W.rank t + (α + α) := by rw [add_assoc]
        _ ≤ W.rank t + β := add_le_add_right hααβle _
        _ ≤ W.γ := W.terminal t
  have hnew_lt : insertGapRank W.rank α s < W.γ := by
    induction s using Fin.cases with
    | zero =>
      simp only [insertGapRank, Fin.cases_zero]
      exact lt_trans hαβ W.lt_gamma
    | succ t =>
      simp only [insertGapRank, Fin.cases_succ]
      exact lt_of_lt_of_le ((add_lt_add_iff_left _).mpr hαβ) (W.terminal t)
  -- gap from an old rank strictly before the slot up to the new rank
  have hold_new : ∀ k : Fin m, k.castSucc < s →
      W.rank k + α ≤ insertGapRank W.rank α s := by
    intro k hk
    rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨t, rfl⟩
    · exact absurd hk (Fin.not_lt_zero _)
    · simp only [insertGapRank, Fin.cases_succ]
      rcases eq_or_lt_of_le (Fin.castSucc_lt_succ_iff.mp hk) with rfl | hkt
      · exact le_rfl
      · exact le_trans (le_trans (add_le_add_right hαβle _) (W.gaps k t hkt)) le_self_add
  -- gap from the new rank up to an old rank at or after the slot
  have hnew_old : ∀ k : Fin m, s ≤ k.castSucc →
      insertGapRank W.rank α s + α ≤ W.rank k := by
    intro k hk
    induction s using Fin.cases with
    | zero =>
      simp only [insertGapRank, Fin.cases_zero]
      exact le_trans hααβle (W.initial k)
    | succ t =>
      simp only [insertGapRank, Fin.cases_succ]
      have htk : t < k := Fin.succ_le_castSucc_iff.mp hk
      calc W.rank t + α + α = W.rank t + (α + α) := by rw [add_assoc]
        _ ≤ W.rank t + β := add_le_add_right hααβle _
        _ ≤ W.rank k := W.gaps t k htk
  refine ⟨W.w (Ordinal.ToType.mk ⟨insertGapRank W.rank α s, hnew_lt⟩), ⟨{
    γ := W.γ
    w := W.w
    chain := W.chain
    rank := Fin.insertNth s (insertGapRank W.rank α s) W.rank
    rank_lt := ?_
    initial := ?_
    gaps := ?_
    terminal := ?_
    lt_gamma := lt_trans hαβ W.lt_gamma
    marks := ?_ }⟩⟩
  · -- rank_lt
    intro i
    by_cases hi : i = s
    · rw [hi]
      simpa [Fin.insertNth_apply_same] using hnew_lt
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa [Fin.insertNth_apply_succAbove] using W.rank_lt k
  · -- initial
    intro i
    by_cases hi : i = s
    · rw [hi]
      simpa [Fin.insertNth_apply_same] using hnew_initial
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa [Fin.insertNth_apply_succAbove] using le_trans hαβle (W.initial k)
  · -- gaps
    intro i j hij
    by_cases hi : i = s
    · have hij' : s < j := hi ▸ hij
      rw [hi]
      by_cases hj : j = s
      · exact absurd (hj ▸ hij') (lt_irrefl _)
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        have hk : s ≤ k.castSucc := (Fin.lt_succAbove_iff_le_castSucc s k).mp hij'
        simpa [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using hnew_old k hk
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      by_cases hj : j = s
      · have hij' : s.succAbove k < s := hj ▸ hij
        rw [hj]
        have hk : k.castSucc < s := (Fin.succAbove_lt_iff_castSucc_lt s k).mp hij'
        simpa [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] using hold_new k hk
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
        have hkl : k < l := Fin.succAbove_lt_succAbove_iff.mp hij
        simpa [Fin.insertNth_apply_succAbove]
          using le_trans (add_le_add_right hαβle _) (W.gaps k l hkl)
  · -- terminal
    intro i
    by_cases hi : i = s
    · rw [hi]
      simpa [Fin.insertNth_apply_same] using hnew_terminal
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa [Fin.insertNth_apply_succAbove]
        using le_trans (add_le_add_right hαβle _) (W.terminal k)
  · -- marks
    intro i
    by_cases hi : i = s
    · rw [hi]
      simp [Fin.insertNth_apply_same]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      simp only [Fin.insertNth_apply_succAbove]
      rw [W.marks k]

end FirstOrder.Language
