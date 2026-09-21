/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.MixedTorsionChainBalance

/-!
# Arithmetic balancing cuts for mixed-torsion chains

The prefix genus of a chain is nondecreasing and its suffix genus is
nonincreasing.  For a chain with at least two positive-genus factors, the
prefix is strictly smaller than the suffix at the first factor, while the
reverse strict inequality holds at the last factor.  The first crossing
therefore gives a nonempty split satisfying `ChainDominatesAtSplit`.

This is the finite arithmetic step used in the proof of Corollary 6.16(2).
Genus-zero factors are deliberately handled separately by
`ZeroGenusWedge`: strict positivity is used here only to keep both sides of
the balancing cut nonempty.
-/

namespace Bananas

open Utilities

/-! ## Monotonicity of prefix and suffix genus -/

theorem chainFactorGenus_nonneg (L : List KGeneralChainFactor) :
    0 ≤ chainFactorGenus L := by
  induction L with
  | nil => simp
  | cons F rest ih =>
      rw [chainFactorGenus_cons]
      exact add_nonneg
        (genus_nonneg_of_graph_connected F.marked.graph F.connected) ih

@[simp] theorem chainFactorGenus_append
    (L R : List KGeneralChainFactor) :
    chainFactorGenus (L ++ R) = chainFactorGenus L + chainFactorGenus R := by
  simp [chainFactorGenus]

/-- Prefix genus is monotone in the prefix length. -/
theorem chainFactorGenus_take_mono
    (L : List KGeneralChainFactor) {i j : ℕ} (hij : i ≤ j) :
    chainFactorGenus (L.take i) ≤ chainFactorGenus (L.take j) := by
  induction L generalizing i j with
  | nil => simp
  | cons F rest ih =>
      cases i with
      | zero => exact chainFactorGenus_nonneg _
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simp only [List.take_succ_cons, chainFactorGenus_cons]
              simpa only [add_comm] using
                add_le_add_left (ih (Nat.le_of_succ_le_succ hij))
                  (genus F.marked.graph)

/-- Suffix genus is antitone in the number of discarded factors. -/
theorem chainFactorGenus_drop_anti
    (L : List KGeneralChainFactor) {i j : ℕ} (hij : i ≤ j) :
    chainFactorGenus (L.drop j) ≤ chainFactorGenus (L.drop i) := by
  induction L generalizing i j with
  | nil => simp
  | cons F rest ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp
          | succ j =>
              simp only [List.drop_succ_cons, List.drop_zero,
                chainFactorGenus_cons]
              exact le_trans (ih (Nat.zero_le j))
                (le_add_of_nonneg_left
                  (genus_nonneg_of_graph_connected F.marked.graph F.connected))
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simpa using ih (Nat.le_of_succ_le_succ hij)

/-! ## The first crossing -/

/-- At the last factor, suffix genus is at most prefix genus. -/
theorem chain_last_suffix_le_prefix
    (L : List KGeneralChainFactor) (hL : L ≠ []) :
    chainFactorGenus (L.drop (L.length - 1)) ≤
      chainFactorGenus (L.take ((L.length - 1) + 1)) := by
  have hLenPos : 0 < L.length := List.length_pos_iff_ne_nil.mpr hL
  have hTake : L.take ((L.length - 1) + 1) = L := by
    have hLength : L.length - 1 + 1 = L.length := by omega
    rw [hLength]
    exact List.take_length
  rw [hTake]
  have hSplit := chainFactorGenus_append (L.take (L.length - 1))
    (L.drop (L.length - 1))
  rw [List.take_append_drop] at hSplit
  rw [hSplit]
  exact le_add_of_nonneg_left (chainFactorGenus_nonneg _)

/-- The first factor's prefix genus is strictly smaller than its suffix genus
when a positive-genus tail is present. -/
theorem first_prefix_lt_suffix_of_positive_tail
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hPositive : ∀ Q ∈ next :: rest, 0 < genus Q.marked.graph) :
    chainFactorGenus ((F :: next :: rest).take 1) <
      chainFactorGenus ((F :: next :: rest).drop 0) := by
  have hTailPositive : 0 < chainFactorGenus (next :: rest) := by
    rw [chainFactorGenus_cons]
    have hNext : 0 < genus next.marked.graph := hPositive next (by simp)
    have hRest : 0 ≤ chainFactorGenus rest := chainFactorGenus_nonneg rest
    exact add_pos_of_pos_of_nonneg hNext hRest
  simpa only [List.take_succ_cons, List.take_zero, List.drop_zero,
    chainFactorGenus_cons, chainFactorGenus_nil, add_zero] using
      (lt_add_of_pos_right (genus F.marked.graph) hTailPositive)

/-- The prefix and suffix genus functions have crossed at `i`. -/
def GenusCrossed (L : List KGeneralChainFactor) (i : ℕ) : Prop :=
  chainFactorGenus (L.drop i) ≤ chainFactorGenus (L.take (i + 1))

theorem exists_genusCrossed (L : List KGeneralChainFactor) (hL : L ≠ []) :
    ∃ i, GenusCrossed L i :=
  ⟨L.length - 1, chain_last_suffix_le_prefix L hL⟩

/-- The first index at which suffix genus is no larger than prefix genus.
It exists for every nonempty chain by the last-factor inequality. -/
noncomputable def firstGenusCrossing
    (L : List KGeneralChainFactor) (hL : L ≠ []) : ℕ :=
  by
    classical
    exact Nat.find (exists_genusCrossed L hL)

theorem firstGenusCrossing_spec
    (L : List KGeneralChainFactor) (hL : L ≠ []) :
    chainFactorGenus (L.drop (firstGenusCrossing L hL)) ≤
      chainFactorGenus (L.take (firstGenusCrossing L hL + 1)) := by
  classical
  unfold firstGenusCrossing
  exact Nat.find_spec (exists_genusCrossed L hL)

theorem firstGenusCrossing_lt_length
    (L : List KGeneralChainFactor) (hL : L ≠ []) :
    firstGenusCrossing L hL < L.length := by
  classical
  have hBound := Nat.find_min'
    (exists_genusCrossed L hL) (chain_last_suffix_le_prefix L hL)
  have hLen : 0 < L.length := List.length_pos_iff_ne_nil.mpr hL
  unfold firstGenusCrossing
  omega

/-- Before the first crossing, prefix genus is no larger than suffix genus. -/
theorem prefix_le_suffix_before_firstGenusCrossing
    (L : List KGeneralChainFactor) (hL : L ≠ [])
    {i : ℕ} (hi : i < firstGenusCrossing L hL) :
    chainFactorGenus (L.take (i + 1)) ≤
      chainFactorGenus (L.drop i) := by
  classical
  unfold firstGenusCrossing at hi
  have hNot := Nat.find_min
    (exists_genusCrossed L hL) hi
  unfold GenusCrossed at hNot
  omega

/-- From the first crossing onward, suffix genus remains no larger than
prefix genus. -/
theorem suffix_le_prefix_from_firstGenusCrossing
    (L : List KGeneralChainFactor) (hL : L ≠ [])
    {i : ℕ} (hi : firstGenusCrossing L hL ≤ i) :
    chainFactorGenus (L.drop i) ≤
      chainFactorGenus (L.take (i + 1)) := by
  exact le_trans (chainFactorGenus_drop_anti L hi)
    (le_trans (firstGenusCrossing_spec L hL)
      (chainFactorGenus_take_mono L (Nat.add_le_add_right hi 1)))

/-- Positivity forces the first crossing to occur after the initial factor. -/
theorem firstGenusCrossing_pos_of_positive_tail
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hPositive : ∀ Q ∈ next :: rest, 0 < genus Q.marked.graph) :
    0 < firstGenusCrossing (F :: next :: rest) (by simp) := by
  by_contra h
  have hZero : firstGenusCrossing (F :: next :: rest) (by simp) = 0 := by omega
  have hSpec := firstGenusCrossing_spec (F :: next :: rest) (by simp)
  rw [hZero] at hSpec
  have hStrict := first_prefix_lt_suffix_of_positive_tail F next rest hPositive
  exact (not_le_of_gt hStrict) (by simpa using hSpec)

/-! ## A nonempty dominating split -/

/-- Every chain of at least two positive-genus factors admits a nonempty
crossing split.  The split is canonical: take the first genus crossing. -/
theorem exists_chainDominatesAtSplit_of_positive
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hPositive : ∀ Q ∈ F :: next :: rest, 0 < genus Q.marked.graph) :
    ∃ (leftHead : KGeneralChainFactor)
      (leftTail : List KGeneralChainFactor)
      (rightHead : KGeneralChainFactor)
      (rightTail : List KGeneralChainFactor),
      F :: next :: rest =
        (leftHead :: leftTail) ++ (rightHead :: rightTail) ∧
      ChainDominatesAtSplit
        (leftHead :: leftTail) (rightHead :: rightTail) := by
  let L := F :: next :: rest
  have hL : L ≠ [] := by simp [L]
  let cut := firstGenusCrossing L hL
  have hCutPos : 0 < cut := by
    dsimp [cut, L]
    apply firstGenusCrossing_pos_of_positive_tail F next rest
    intro Q hQ
    exact hPositive Q (by simp [hQ])
  have hCutLt : cut < L.length := firstGenusCrossing_lt_length L hL
  have hTakeNe : L.take cut ≠ [] := by
    intro hEq
    have hLength := congrArg List.length hEq
    simp [List.length_take, Nat.min_eq_left hCutLt.le] at hLength
    omega
  obtain ⟨leftHead, leftTail, hLeft⟩ := List.exists_cons_of_ne_nil hTakeNe
  have hDropNe : L.drop cut ≠ [] := by
    intro hEq
    have hLength := congrArg List.length hEq
    simp [List.length_drop] at hLength
    omega
  obtain ⟨rightHead, rightTail, hRight⟩ := List.exists_cons_of_ne_nil hDropNe
  refine ⟨leftHead, leftTail, rightHead, rightTail, ?_, ?_⟩
  · rw [← hLeft, ← hRight]
    exact (List.take_append_drop cut L).symm
  · rw [← hLeft, ← hRight]
    unfold ChainDominatesAtSplit
    rw [List.take_append_drop]
    constructor
    · intro i hi
      have hiCut : i < cut := by
        simpa [List.length_take, Nat.min_eq_left hCutLt.le] using hi
      have hBefore := prefix_le_suffix_before_firstGenusCrossing L hL
        (i := i) (by simpa [cut] using hiCut)
      have hTake : (L.take cut).take (i + 1) = L.take (i + 1) := by
        rw [List.take_take, min_eq_left (Nat.succ_le_iff.mpr hiCut)]
      simpa only [hTake] using hBefore
    · intro i hi
      have hiRight : cut + i < L.length := by
        simp only [List.length_drop] at hi
        have hDecomp : cut + (L.length - cut) = L.length :=
          Nat.add_sub_of_le hCutLt.le
        omega
      have hFrom := suffix_le_prefix_from_firstGenusCrossing L hL
        (i := cut + i) (by dsimp [cut]; omega)
      have hDrop : (L.drop cut).drop i = L.drop (cut + i) := by
        rw [List.drop_drop, add_comm]
      rw [hDrop]
      have hLength : (L.take cut).length = cut := by
        simp [List.length_take, Nat.min_eq_left hCutLt.le]
      rw [hLength]
      simpa [Nat.add_assoc] using hFrom

/-- If the canonical first crossing is nonzero, it gives a nonempty
dominating split without any positivity assumption on the individual
factors.  Positivity above is only one sufficient condition for the crossing
to be nonzero; the zero-crossing case is handled separately in the final
form of Corollary 6.16(2). -/
theorem exists_chainDominatesAtSplit_of_firstCrossing_pos
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hCrossingPos :
      0 < firstGenusCrossing (F :: next :: rest) (by simp)) :
    ∃ (leftHead : KGeneralChainFactor)
      (leftTail : List KGeneralChainFactor)
      (rightHead : KGeneralChainFactor)
      (rightTail : List KGeneralChainFactor),
      F :: next :: rest =
        (leftHead :: leftTail) ++ (rightHead :: rightTail) ∧
      ChainDominatesAtSplit
        (leftHead :: leftTail) (rightHead :: rightTail) := by
  let L := F :: next :: rest
  have hL : L ≠ [] := by simp [L]
  let cut := firstGenusCrossing L hL
  have hCutPos : 0 < cut := by
    simpa only [L, cut] using hCrossingPos
  have hCutLt : cut < L.length := firstGenusCrossing_lt_length L hL
  have hTakeNe : L.take cut ≠ [] := by
    intro hEq
    have hLength := congrArg List.length hEq
    simp [List.length_take, Nat.min_eq_left hCutLt.le] at hLength
    omega
  obtain ⟨leftHead, leftTail, hLeft⟩ := List.exists_cons_of_ne_nil hTakeNe
  have hDropNe : L.drop cut ≠ [] := by
    intro hEq
    have hLength := congrArg List.length hEq
    simp [List.length_drop] at hLength
    omega
  obtain ⟨rightHead, rightTail, hRight⟩ := List.exists_cons_of_ne_nil hDropNe
  refine ⟨leftHead, leftTail, rightHead, rightTail, ?_, ?_⟩
  · rw [← hLeft, ← hRight]
    exact (List.take_append_drop cut L).symm
  · rw [← hLeft, ← hRight]
    unfold ChainDominatesAtSplit
    rw [List.take_append_drop]
    constructor
    · intro i hi
      have hiCut : i < cut := by
        simpa [List.length_take, Nat.min_eq_left hCutLt.le] using hi
      have hBefore := prefix_le_suffix_before_firstGenusCrossing L hL
        (i := i) (by simpa [cut] using hiCut)
      have hTake : (L.take cut).take (i + 1) = L.take (i + 1) := by
        rw [List.take_take, min_eq_left (Nat.succ_le_iff.mpr hiCut)]
      simpa only [hTake] using hBefore
    · intro i hi
      have hiRight : cut + i < L.length := by
        simp only [List.length_drop] at hi
        have hDecomp : cut + (L.length - cut) = L.length :=
          Nat.add_sub_of_le hCutLt.le
        omega
      have hFrom := suffix_le_prefix_from_firstGenusCrossing L hL
        (i := cut + i) (by dsimp [cut]; omega)
      have hDrop : (L.drop cut).drop i = L.drop (cut + i) := by
        rw [List.drop_drop, add_comm]
      rw [hDrop]
      have hLength : (L.take cut).length = cut := by
        simp [List.length_take, Nat.min_eq_left hCutLt.le]
      rw [hLength]
      simpa [Nat.add_assoc] using hFrom

/-- The paper's minimum budget therefore yields a nonempty balanced split
for every chain of at least two positive-genus factors. -/
theorem exists_chainBalancedAtSplit_of_minBudget_of_positive
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hPositive : ∀ Q ∈ F :: next :: rest, 0 < genus Q.marked.graph)
    (hMin : ChainMinBudget (F :: next :: rest)) :
    ∃ (leftHead : KGeneralChainFactor)
      (leftTail : List KGeneralChainFactor)
      (rightHead : KGeneralChainFactor)
      (rightTail : List KGeneralChainFactor),
      F :: next :: rest =
        (leftHead :: leftTail) ++ (rightHead :: rightTail) ∧
      ChainBalancedAtSplit
        (leftHead :: leftTail) (rightHead :: rightTail) := by
  obtain ⟨leftHead, leftTail, rightHead, rightTail, hDecomp, hCross⟩ :=
    exists_chainDominatesAtSplit_of_positive F next rest hPositive
  refine ⟨leftHead, leftTail, rightHead, rightTail, hDecomp, ?_⟩
  apply chainBalancedAtSplit_of_minBudget
  · rwa [← hDecomp]
  · exact hCross

/-! ## Removing a zero-genus leading factor -/

/-- If the first factor has genus zero, the paper's minimum-budget condition
restricts to the remaining nonempty tail without change. -/
theorem chainMinBudget_tail_of_head_genus_zero
    (F next : KGeneralChainFactor) (rest : List KGeneralChainFactor)
    (hZero : genus F.marked.graph = 0)
    (hMin : ChainMinBudget (F :: next :: rest)) :
    ChainMinBudget (next :: rest) := by
  intro i hi
  have hi' : i + 1 < (F :: next :: rest).length := by
    simpa using hi
  have h := hMin (i + 1) hi'
  have hTake :
      chainFactorGenus ((F :: next :: rest).take (i + 1 + 1)) =
        chainFactorGenus ((next :: rest).take (i + 1)) := by
    simp only [List.take_succ_cons, chainFactorGenus_cons]
    rw [hZero]
    ring
  have hDrop :
      chainFactorGenus ((F :: next :: rest).drop (i + 1)) =
        chainFactorGenus ((next :: rest).drop i) := by
    simp only [List.drop_succ_cons]
  have hGet : (F :: next :: rest).get ⟨i + 1, hi'⟩ =
      (next :: rest).get ⟨i, hi⟩ := by
    change (F :: next :: rest)[i + 1] = (next :: rest)[i]
    rfl
  rw [hTake, hDrop, hGet] at h
  exact h

/-- If the total genus of a factor list is zero, every member has genus zero.
Connectivity of each bundled factor supplies nonnegativity. -/
theorem genus_eq_zero_of_mem_of_chainFactorGenus_eq_zero
    (L : List KGeneralChainFactor) (hSum : chainFactorGenus L = 0)
    (F : KGeneralChainFactor) (hMem : F ∈ L) :
    genus F.marked.graph = 0 := by
  induction L with
  | nil => simp at hMem
  | cons head rest ih =>
      rw [chainFactorGenus_cons] at hSum
      have hHeadNonneg : 0 ≤ genus head.marked.graph :=
        genus_nonneg_of_graph_connected head.marked.graph head.connected
      have hRestNonneg : 0 ≤ chainFactorGenus rest :=
        chainFactorGenus_nonneg rest
      have hHeadZero : genus head.marked.graph = 0 := by omega
      have hRestZero : chainFactorGenus rest = 0 := by omega
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact hHeadZero
      · exact ih hRestZero hMem

end Bananas
