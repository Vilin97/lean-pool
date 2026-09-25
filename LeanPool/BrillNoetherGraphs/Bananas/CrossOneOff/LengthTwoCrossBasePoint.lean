/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.LengthTwoCross

/-!
# Base-point calculations for the length-two cross exception

This file develops the low-degree base-point criterion used in the corrected
distinct-strand theorem.  It is kept separate from the dependent semibreak
update API in `LengthTwoCross`.
-/

@[expose] public section

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- In the low-degree range, a length-two midpoint already present in the
semibreak part is a base point of the corresponding banana normal form. -/
theorem basePointDrop_bananaNormalForm_eq_zero_of_midpoint_mem
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (v : B.graph.V)
    (a b : ℤ) (E : CFDiv B.graph)
    (hα : B.length α = 2) (hi : i.val = 1)
    (hE : IsSemibreak B E)
    (hmem : E (strandVertex B α i) = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ)) :
    basePointDrop
      (mark B.graph (strandVertex B α i) v)
      (bananaNormalForm B a b E) = 0 := by
  change rank B.graph (bananaNormalForm B a b E) -
      rank B.graph (bananaNormalForm B a b E -
        oneChip (strandVertex B α i)) = 0
  rw [rank_bananaNormalForm_remove_midpoint_chip B E hE α i hα hi
    a b ha hb hLowDeg hmem]
  ring

/-- Adding a chip to a strand explicitly known to be empty is the inverse of
`semibreakDivisor_remove_chip`. -/
theorem semibreakDivisor_add_chip {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (β : Fin (g + 1)) (newChip : Fin (B.length β - 1)) :
    semibreakDivisor B (replaceSemibreakChip B chips β (some newChip)) =
      semibreakDivisor B (replaceSemibreakChip B chips β none) +
        oneChip (B.interiorVertex β newChip) := by
  rw [semibreakDivisor_remove_chip B chips β newChip]
  abel

/-- On a length-two strand, vanishing at the midpoint means that the strand
slot is empty, so adding the midpoint chip preserves semibreakness. -/
theorem isSemibreak_add_midpoint_chip_of_eq_zero
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph)
    (hE : IsSemibreak B E) (α : Fin (g + 1))
    (i : B.PathPosition α) (hα : B.length α = 2) (hi : i.val = 1)
    (hzero : E (strandVertex B α i) = 0) :
    IsSemibreak (B := B) (E + oneChip (strandVertex B α i)) := by
  rcases hE with ⟨chips, rfl⟩
  have hmid : strandVertex B α i = B.interiorVertex α ⟨0, by omega⟩ := by
    unfold strandVertex
    split_ifs with htail
    · rw [B.pathVertex_eq_interiorVertex α i ⟨by omega, by omega⟩]
      congr 2
      apply Fin.ext
      omega
    · let j : B.PathPosition α := ⟨B.length α - i.val, by omega⟩
      rw [B.pathVertex_eq_interiorVertex α j ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩]
      congr 2
      apply Fin.ext
      dsimp [j]
      omega
  rw [hmid] at hzero ⊢
  have hnone : chips α = none := by
    cases hchip : chips α with
    | none => simp []
    | some chip =>
        have hchipEq : chip = ⟨0, by omega⟩ := by
          apply Fin.ext
          omega
        subst chip
        simp [semibreakDivisor_interiorVertex, hchip] at hzero
  have hreplaceNone : replaceSemibreakChip B chips α none = chips := by
    funext γ
    by_cases hγα : γ = α
    · subst γ
      simp [hnone]
    · exact replaceSemibreakChip_other B chips α γ none hγα
  refine ⟨replaceSemibreakChip B chips α (some ⟨0, by omega⟩), ?_⟩
  rw [semibreakDivisor_add_chip B chips α ⟨0, by omega⟩, hreplaceNone]

/-! The complementary rank computation: when the midpoint is absent from the
semibreak part, the endpoint relation converts its subtraction into a normal
form with both endpoint coefficients lowered. -/

theorem bananaNormalForm_sub_midpoint_linearEquiv
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (a b : ℤ) (E : CFDiv B.graph)
    (hα : B.length α = 2) (hi : i.val = 1) :
    linearEquiv B.graph
      (bananaNormalForm B a b E - oneChip (strandVertex B α i))
      (bananaNormalForm B (a - 1) (b - 1)
        (E + oneChip (strandVertex B α i))) := by
  have hmid :=
    (two_smul_midpoint_linearEquiv_endpoints B α i hα hi).symm
  unfold linearEquiv at hmid ⊢
  convert hmid using 1
  unfold bananaNormalForm
  rw [sub_smul, sub_smul]
  simp only [one_smul]
  abel

theorem basePointDrop_bananaNormalForm_eq_one_of_midpoint_eq_zero
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (v : B.graph.V)
    (a b : ℤ) (E : CFDiv B.graph)
    (hα : B.length α = 2) (hi : i.val = 1)
    (hE : IsSemibreak B E)
    (hzero : E (strandVertex B α i) = 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ)) :
    basePointDrop
      (mark B.graph (strandVertex B α i) v)
      (bananaNormalForm B a b E) = 1 := by
  let u := strandVertex B α i
  let Eplus : CFDiv B.graph := E + oneChip u
  have hEplus : IsSemibreak B Eplus := by
    dsimp [Eplus, u]
    exact isSemibreak_add_midpoint_chip_of_eq_zero B E hE α i hα hi hzero
  have hdegPlus : deg Eplus = deg E + 1 := by
    dsimp [Eplus]
    rw [deg.map_add, deg_one_chip]
  have hNormalDeg : b + deg E ≤ (g : ℤ) := by omega
  have hRankD : rank B.graph (bananaNormalForm B a b E) = min a b := by
    rw [rank_bananaNormalForm B a b E hE (by omega) hb hNormalDeg]
    rw [max_eq_left (by omega :
      a + b + deg E - (g : ℤ) ≤ min a b)]
  have hEquiv : linearEquiv B.graph
      (bananaNormalForm B a b E - oneChip u)
      (bananaNormalForm B (a - 1) (b - 1) Eplus) := by
    dsimp [u, Eplus]
    exact bananaNormalForm_sub_midpoint_linearEquiv B α i a b E hα hi
  have hRankEquiv := rank_eq_of_linear_equiv B.graph hEquiv
  by_cases hbZero : b = 0
  · subst b
    have hRankDZero : rank B.graph (bananaNormalForm B a 0 E) = 0 := by
      simpa [min_eq_right ha] using hRankD
    by_cases haZero : a = 0
    · subst a
      have hRankSub : rank B.graph
          (bananaNormalForm B 0 0 E - oneChip u) = -1 := by
        have hSupport := rank_semibreak_sub_vertex_eq_neg_one B E hE
          (by omega : deg E ≤ (g : ℤ)) u (by simpa [u] using hzero)
        simpa [bananaNormalForm] using hSupport
      change rank B.graph (bananaNormalForm B 0 0 E) -
          rank B.graph (bananaNormalForm B 0 0 E - oneChip u) = 1
      rw [hRankDZero, hRankSub]
      ring
    · have haPos : 0 < a := by omega
      have hRightDeg : (a - 1) + deg Eplus ≤ (g : ℤ) := by
        rw [hdegPlus]
        omega
      have hReduced := q_reduced_bananaNormalForm_right B
        (a - 1) (-1) Eplus hEplus (by omega) hRightDeg
      have hRankNormal :
          rank B.graph (bananaNormalForm B (a - 1) (-1) Eplus) = -1 := by
        apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
          (bananaNormalForm B (a - 1) (-1) Eplus) hReduced
        rw [bananaNormalForm_rightEndpoint B (a - 1) (-1) Eplus hEplus]
        omega
      have hRankSub : rank B.graph
          (bananaNormalForm B a 0 E - oneChip u) = -1 := by
        exact hRankEquiv.trans hRankNormal
      change rank B.graph (bananaNormalForm B a 0 E) -
          rank B.graph (bananaNormalForm B a 0 E - oneChip u) = 1
      rw [hRankDZero, hRankSub]
      ring
  · have hbPos : 0 < b := by omega
    have hNormalPlus : (b - 1) + deg Eplus ≤ (g : ℤ) := by
      rw [hdegPlus]
      omega
    have hRankNormal : rank B.graph
        (bananaNormalForm B (a - 1) (b - 1) Eplus) = min a b - 1 := by
      rw [rank_bananaNormalForm B (a - 1) (b - 1) Eplus hEplus
        (by omega) (by omega) hNormalPlus]
      have hMinLower : -1 ≤ min (a - 1) (b - 1) := by
        exact le_min (by omega) (by omega)
      have hTop :
          a - 1 + (b - 1) + deg Eplus - (g : ℤ) ≤
            min (a - 1) (b - 1) := by
        rw [hdegPlus]
        omega
      rw [max_eq_left hTop, min_sub_sub_right]
    have hRankSub : rank B.graph
        (bananaNormalForm B a b E - oneChip u) = min a b - 1 :=
      hRankEquiv.trans hRankNormal
    change rank B.graph (bananaNormalForm B a b E) -
        rank B.graph (bananaNormalForm B a b E - oneChip u) = 1
    rw [hRankD, hRankSub]
    ring

/-- A length-two strand has exactly one interior slot, so a semibreak divisor
has either zero or one chip at its normalized midpoint. -/
theorem semibreak_midpoint_eq_zero_or_one
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (α : Fin (g + 1)) (i : B.PathPosition α)
    (hα : B.length α = 2) (hi : i.val = 1) :
    E (strandVertex B α i) = 0 ∨ E (strandVertex B α i) = 1 := by
  rcases hE with ⟨chips, rfl⟩
  have hmid : strandVertex B α i = B.interiorVertex α ⟨0, by omega⟩ := by
    unfold strandVertex
    split_ifs with htail
    · rw [B.pathVertex_eq_interiorVertex α i ⟨by omega, by omega⟩]
      congr 2
      apply Fin.ext
      omega
    · let j : B.PathPosition α := ⟨B.length α - i.val, by omega⟩
      rw [B.pathVertex_eq_interiorVertex α j ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩]
      congr 2
      apply Fin.ext
      dsimp [j]
      omega
  rw [hmid]
  cases hchip : chips α with
  | none => left; simp [semibreakDivisor_interiorVertex, hchip]
  | some offset =>
    right
    have hoffset : offset = ⟨0, by omega⟩ := by
      apply Fin.ext
      omega
    subst offset
    simp [semibreakDivisor_interiorVertex, hchip]

/-- Exact midpoint base-point dichotomy in the low-degree normal-form range.
It is the local input for the corrected length-two cross exception. -/
theorem basePointDrop_bananaNormalForm_eq_one_iff_midpoint_eq_zero
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (v : B.graph.V)
    (a b : ℤ) (E : CFDiv B.graph)
    (hα : B.length α = 2) (hi : i.val = 1)
    (hE : IsSemibreak B E)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ)) :
    basePointDrop
      (mark B.graph (strandVertex B α i) v)
      (bananaNormalForm B a b E) = 1 ↔
      E (strandVertex B α i) = 0 := by
  constructor
  · intro hDrop
    rcases semibreak_midpoint_eq_zero_or_one B E hE α i hα hi with hzero | hmem
    · exact hzero
    · have hZeroDrop := basePointDrop_bananaNormalForm_eq_zero_of_midpoint_mem
        B α i v a b E hα hi hE hmem ha hb hLowDeg
      omega
  · intro hzero
    exact basePointDrop_bananaNormalForm_eq_one_of_midpoint_eq_zero
      B α i v a b E hα hi hE hzero ha hb hLowDeg

end Bananas
