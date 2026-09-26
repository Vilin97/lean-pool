/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffDelta

/-!
# The endpoint residue cases for the cross-one-off marking

This file proves the two rank-difference calculations that complement
`rankDelta_crossOneOff_two_interior_eq_one`.  Together they are the three
corrected residue cases used in Lemma 4.30 of the paper.

The complementary-residue calculation is stated both in its valid range and
at its unique boundary exception.  At the latter boundary the second
difference is zero, not one; arithmetically that boundary is exactly the
paper's `N = 2, b = 1` case.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec


/-- A single chip at a normalized interior position is a semibreak divisor. -/
theorem isSemibreak_one_strand_chip
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (p : B.PathPosition α) (hp : B.IsInteriorPosition α p) :
    IsSemibreak B (oneChip (strandVertex B α p)) := by
  let op := normalizedInteriorOffset B α p hp
  let chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)) :=
    fun γ => if hγα : γ = α then some (hγα ▸ op) else none
  refine ⟨chips, ?_⟩
  rw [strandVertex_eq_interiorVertex_normalizedInteriorOffset B α p hp]
  funext z
  rcases z with core | ⟨γ, offset⟩
  · simp [semibreakDivisor, oneChip,
      SubdivisionGraph.Spec.interiorVertex]
  · by_cases hγα : γ = α
    · subst γ
      simp [semibreakDivisor, chips, oneChip,
        SubdivisionGraph.Spec.interiorVertex]
      aesop
    · simp [semibreakDivisor, chips, hγα, oneChip,
        SubdivisionGraph.Spec.interiorVertex]

private theorem linearEquiv_add {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linearEquiv G A B) (h₂ : linearEquiv G C D) :
    linearEquiv G (A + C) (B + D) := by
  unfold linearEquiv at h₁ h₂ ⊢
  have h := (principalDivisors G).add_mem h₁ h₂
  convert h using 1 ; abel

private theorem linearEquiv_add_common {G : CFGraph} {A B : CFDiv G}
    (h : linearEquiv G A B) (C : CFDiv G) :
    linearEquiv G (C + A) (C + B) := by
  unfold linearEquiv at h ⊢
  convert h using 1 ; abel

/-- The positive-multiple residue case of corrected Lemma 4.30.  The normal
form consists of a right-endpoint coefficient and one interior chip on the
first marked strand. -/
theorem rankDelta_crossOneOff_multiple_normalForm_eq_one
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (p : B.PathPosition α) (c : ℕ)
    (hg : 2 ≤ g) (hαβ : α ≠ β)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length α)
    (hβLength : 2 ≤ B.length β) (hc : c ≤ g - 1) :
    rankDelta
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      ((c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B α p)) = 1 := by
  let pPrev : B.PathPosition α := ⟨p.val - 1, by omega⟩
  let qOne : B.PathPosition β := ⟨1, by omega⟩
  let qMark : B.PathPosition β := ⟨B.length β - 1, by omega⟩
  have hp : B.IsInteriorPosition α p := by
    change 0 < p.val ∧ p.val < B.length α
    omega
  have hpPrev : B.IsInteriorPosition α pPrev := by
    change 0 < p.val - 1 ∧ p.val - 1 < B.length α
    omega
  have hqOne : B.IsInteriorPosition β qOne := by
    change 0 < (1 : ℕ) ∧ 1 < B.length β
    omega
  have hqMark : B.IsInteriorPosition β qMark := by
    change 0 < B.length β - 1 ∧ B.length β - 1 < B.length β
    omega
  let E : CFDiv B.graph := oneChip (strandVertex B α p)
  let EU : CFDiv B.graph := oneChip (strandVertex B α pPrev)
  let EV : CFDiv B.graph :=
    oneChip (strandVertex B α p) + oneChip (strandVertex B β qOne)
  have hE : IsSemibreak B E := by
    dsimp [E]
    exact isSemibreak_one_strand_chip B α p hp
  have hEU : IsSemibreak B EU := by
    dsimp [EU]
    exact isSemibreak_one_strand_chip B α pPrev hpPrev
  have hEV : IsSemibreak B EV := by
    dsimp [EV]
    exact isSemibreak_two_distinct_strand_chips B α β p qOne
      hp hqOne hαβ
  have hdegE : deg E = 1 := by simp [E, deg_one_chip]
  have hdegEU : deg EU = 1 := by simp [EU, deg_one_chip]
  have hdegEV : deg EV = 2 := by
    simp [EV, deg.map_add, deg_one_chip]
  let D : CFDiv B.graph := bananaNormalForm B 0 (c : ℤ) E
  have hDDef : D =
      (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B α p) := by
    dsimp [D, E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  have hShiftU := crossOneOff_sub_first_mark_shift B α p.val
    (by omega) (by omega)
  have hDU : linearEquiv B.graph
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))
      (bananaNormalForm B (-1) (c : ℤ) EU) := by
    have h := linearEquiv_add_common hShiftU
      ((c : ℤ) • oneChip (rightEndpoint B))
    dsimp [D, E, EU, pPrev]
    unfold bananaNormalForm at h ⊢
    convert h using 1 <;>
      ext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  have hShiftV := crossOneOff_sub_second_mark_shift B β 0 (by omega)
  rw [strandVertex_zero B β] at hShiftV
  have hDV : linearEquiv B.graph
      (D - oneChip (strandVertex B β qMark))
      (bananaNormalForm B (-1) ((c : ℤ) - 1) EV) := by
    dsimp [D, E, EV, qOne, qMark]
    unfold bananaNormalForm
    unfold linearEquiv at hShiftV ⊢
    convert hShiftV using 1 ;
      ext z ;
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Nat.zero_add] ;
      ring
  have hRankD : rank B.graph D = 0 := by
    rw [rank_bananaNormalForm B 0 (c : ℤ) E hE (by omega) (by omega)]
    · rw [hdegE]
      simp
      omega
    · rw [hdegE]
      exact_mod_cast (show c + 1 ≤ g by omega)
  have hRankDU : rank B.graph
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)) = -1 := by
    rw [rank_eq_of_linear_equiv B.graph hDU,
      rank_bananaNormalForm B (-1) (c : ℤ) EU hEU (by omega) (by omega)]
    · rw [hdegEU]
      simp
      omega
    · rw [hdegEU]
      exact_mod_cast (show c + 1 ≤ g by omega)
  have hRankDV : rank B.graph
      (D - oneChip (strandVertex B β qMark)) = -1 := by
    by_cases hcZero : c = 0
    · subst c
      have hDistinct : strandVertex B α p ≠ strandVertex B β qMark := by
        intro hEq
        exact hαβ (strand_eq_of_interior_vertex_eq B α β p qMark
          hp hqMark hEq)
      have hSupport : E (strandVertex B β qMark) = 0 := by
        simp [E, hDistinct]
      have hRank := rank_semibreak_sub_vertex_eq_neg_one B E hE (by
        rw [hdegE]
        exact_mod_cast (show 1 ≤ g by omega))
        (strandVertex B β qMark) hSupport
      simpa [D, bananaNormalForm] using hRank
    · rw [rank_eq_of_linear_equiv B.graph hDV,
        rank_bananaNormalForm B (-1) ((c : ℤ) - 1) EV hEV
          (by omega) (by omega)]
      · rw [hdegEV]
        rw [min_eq_left (by omega), max_eq_left (by omega)]
      · rw [hdegEV]
        omega
  have hRankDUV : rank B.graph
      (D - oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        oneChip (strandVertex B β qMark)) = -1 := by
    have hUpper := rank_sub_one_chip_le_rank B.graph
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))
      (strandVertex B β qMark)
    have hLower := rank_geq_neg_one B.graph
      (D - oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        oneChip (strandVertex B β qMark))
    rw [hRankDU] at hUpper
    omega
  rw [← hDDef]
  unfold rankDelta mark
  rw [hRankD, hRankDU, hRankDV, hRankDUV]
  ring

/-- The complementary-residue normal form has second rank difference one
away from its top boundary.  The strict inequality `c < g - 1` is essential:
the next theorem computes the omitted boundary value as zero. -/
theorem rankDelta_crossOneOff_complement_normalForm_eq_one
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (p : B.PathPosition α) (c : ℕ)
    (hg : 2 ≤ g) (hαβ : α ≠ β)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length α)
    (hβLength : 2 ≤ B.length β) (hc : c < g - 1) :
    rankDelta
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B α p) +
        oneChip
          (strandVertex B β ⟨B.length β - 1, by omega⟩)) = 1 := by
  let pPrev : B.PathPosition α := ⟨p.val - 1, by omega⟩
  let qMark : B.PathPosition β := ⟨B.length β - 1, by omega⟩
  have hp : B.IsInteriorPosition α p := by
    change 0 < p.val ∧ p.val < B.length α
    omega
  have hpPrev : B.IsInteriorPosition α pPrev := by
    change 0 < p.val - 1 ∧ p.val - 1 < B.length α
    omega
  have hqMark : B.IsInteriorPosition β qMark := by
    change 0 < B.length β - 1 ∧ B.length β - 1 < B.length β
    omega
  let E : CFDiv B.graph :=
    oneChip (strandVertex B α p) + oneChip (strandVertex B β qMark)
  let EU : CFDiv B.graph :=
    oneChip (strandVertex B α pPrev) + oneChip (strandVertex B β qMark)
  let EV : CFDiv B.graph := oneChip (strandVertex B α p)
  let EUV : CFDiv B.graph := oneChip (strandVertex B α pPrev)
  have hE : IsSemibreak B E := by
    dsimp [E]
    exact isSemibreak_two_distinct_strand_chips B α β p qMark
      hp hqMark hαβ
  have hEU : IsSemibreak B EU := by
    dsimp [EU]
    exact isSemibreak_two_distinct_strand_chips B α β pPrev qMark
      hpPrev hqMark hαβ
  have hEV : IsSemibreak B EV := by
    dsimp [EV]
    exact isSemibreak_one_strand_chip B α p hp
  have hEUV : IsSemibreak B EUV := by
    dsimp [EUV]
    exact isSemibreak_one_strand_chip B α pPrev hpPrev
  have hdegE : deg E = 2 := by simp [E, deg.map_add, deg_one_chip]
  have hdegEU : deg EU = 2 := by simp [EU, deg.map_add, deg_one_chip]
  have hdegEV : deg EV = 1 := by simp [EV, deg_one_chip]
  have hdegEUV : deg EUV = 1 := by simp [EUV, deg_one_chip]
  let D : CFDiv B.graph :=
    bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) E
  have hDDef : D =
      ((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B α p) +
        oneChip (strandVertex B β qMark) := by
    dsimp [D, E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  have hShiftU := crossOneOff_sub_first_mark_shift B α p.val
    (by omega) (by omega)
  have hDU : linearEquiv B.graph
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))
      (bananaNormalForm B ((g : ℤ) - 2) (c : ℤ) EU) := by
    have h := linearEquiv_add_common hShiftU
      (((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B β qMark))
    dsimp [D, E, EU, pPrev]
    unfold bananaNormalForm at h ⊢
    convert h using 1 <;>
      ext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  have hDVDef :
      D - oneChip (strandVertex B β qMark) =
        bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) EV := by
    dsimp [D, E, EV]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hDUV : linearEquiv B.graph
      (D - oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        oneChip (strandVertex B β qMark))
      (bananaNormalForm B ((g : ℤ) - 2) (c : ℤ) EUV) := by
    have h := linearEquiv_add_common hShiftU
      (((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        (c : ℤ) • oneChip (rightEndpoint B))
    dsimp [D, E, EUV, pPrev]
    unfold bananaNormalForm at h ⊢
    convert h using 1 <;>
      ext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  have hRankD : rank B.graph D = (c : ℤ) + 1 := by
    rw [rank_bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) E hE
      (by omega) (by omega)]
    · rw [hdegE, min_eq_right (by omega), max_eq_right (by omega)]
      ring
    · rw [hdegE]
      omega
  have hRankDU : rank B.graph
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)) =
        (c : ℤ) := by
    rw [rank_eq_of_linear_equiv B.graph hDU,
      rank_bananaNormalForm B ((g : ℤ) - 2) (c : ℤ) EU hEU
        (by omega) (by omega)]
    · rw [hdegEU, min_eq_right (by omega), max_eq_left (by omega)]
    · rw [hdegEU]
      omega
  have hRankDV : rank B.graph
      (D - oneChip (strandVertex B β qMark)) = (c : ℤ) := by
    rw [hDVDef,
      rank_bananaNormalForm B ((g : ℤ) - 1) (c : ℤ) EV hEV
        (by omega) (by omega)]
    · rw [hdegEV, min_eq_right (by omega), max_eq_left (by omega)]
    · rw [hdegEV]
      omega
  have hRankDUV : rank B.graph
      (D - oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        oneChip (strandVertex B β qMark)) = (c : ℤ) := by
    rw [rank_eq_of_linear_equiv B.graph hDUV,
      rank_bananaNormalForm B ((g : ℤ) - 2) (c : ℤ) EUV hEUV
        (by omega) (by omega)]
    · rw [hdegEUV, min_eq_right (by omega), max_eq_left (by omega)]
    · rw [hdegEUV]
      omega
  rw [← hDDef]
  unfold rankDelta mark
  rw [hRankD, hRankDU, hRankDV, hRankDUV]
  ring

/-- At the omitted top boundary `c = g - 1`, the complementary-residue
normal form has second rank difference zero.  This is the formal obstruction
behind the false `N = 2, b = 1` instance in the printed Lemma 4.30(2). -/
theorem rankDelta_crossOneOff_complement_boundary_eq_zero
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (p : B.PathPosition α)
    (hg : 2 ≤ g)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length α)
    (hβLength : 2 ≤ B.length β) :
    rankDelta
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        ((g : ℤ) - 1) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B α p) +
        oneChip
          (strandVertex B β ⟨B.length β - 1, by omega⟩)) = 0 := by
  let pPrev : B.PathPosition α := ⟨p.val - 1, by omega⟩
  let qMark : B.PathPosition β := ⟨B.length β - 1, by omega⟩
  have hpPrev : B.IsInteriorPosition α pPrev := by
    change 0 < p.val - 1 ∧ p.val - 1 < B.length α
    omega
  let E : CFDiv B.graph :=
    oneChip (strandVertex B α p) + oneChip (strandVertex B β qMark)
  let EUV : CFDiv B.graph := oneChip (strandVertex B α pPrev)
  have hEUV : IsSemibreak B EUV := by
    dsimp [EUV]
    exact isSemibreak_one_strand_chip B α pPrev hpPrev
  have hdegE : deg E = 2 := by simp [E, deg.map_add, deg_one_chip]
  have hdegEUV : deg EUV = 1 := by simp [EUV, deg_one_chip]
  let D : CFDiv B.graph :=
    bananaNormalForm B ((g : ℤ) - 1) ((g : ℤ) - 1) E
  have hDDef : D =
      ((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        ((g : ℤ) - 1) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B α p) +
        oneChip (strandVertex B β qMark) := by
    dsimp [D, E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  have hShiftU := crossOneOff_sub_first_mark_shift B α p.val
    (by omega) (by omega)
  have hDUV : linearEquiv B.graph
      (D - oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        oneChip (strandVertex B β qMark))
      (bananaNormalForm B ((g : ℤ) - 2) ((g : ℤ) - 1) EUV) := by
    have h := linearEquiv_add_common hShiftU
      (((g : ℤ) - 1) • oneChip (leftEndpoint B) +
        ((g : ℤ) - 1) • oneChip (rightEndpoint B))
    dsimp [D, E, EUV, pPrev]
    unfold bananaNormalForm at h ⊢
    convert h using 1 <;>
      ext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  have hDegreeD : deg D = 2 * (g : ℤ) := by
    rw [degree_bananaNormalForm, hdegE]
    ring
  have hDegreeDU : deg
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)) =
        2 * (g : ℤ) - 1 := by
    rw [deg.map_sub, hDegreeD, deg_one_chip]
  have hDegreeDV : deg
      (D - oneChip (strandVertex B β qMark)) =
        2 * (g : ℤ) - 1 := by
    rw [deg.map_sub, hDegreeD, deg_one_chip]
  have hRankD : rank B.graph D = (g : ℤ) := by
    have h := (rank_nonspecial_range (banana_graph_connected B) D).2.2 (by
      rw [hDegreeD, banana_genus]
      omega)
    rw [hDegreeD, banana_genus] at h
    omega
  have hRankDU : rank B.graph
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)) =
        (g : ℤ) - 1 := by
    have h := (rank_nonspecial_range (banana_graph_connected B)
      (D - oneChip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))).2.2 (by
          rw [hDegreeDU, banana_genus]
          omega)
    rw [hDegreeDU, banana_genus] at h
    omega
  have hRankDV : rank B.graph
      (D - oneChip (strandVertex B β qMark)) = (g : ℤ) - 1 := by
    have h := (rank_nonspecial_range (banana_graph_connected B)
      (D - oneChip (strandVertex B β qMark))).2.2 (by
        rw [hDegreeDV, banana_genus]
        omega)
    rw [hDegreeDV, banana_genus] at h
    omega
  have hRankDUV : rank B.graph
      (D - oneChip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        oneChip (strandVertex B β qMark)) = (g : ℤ) - 2 := by
    rw [rank_eq_of_linear_equiv B.graph hDUV,
      rank_bananaNormalForm B ((g : ℤ) - 2) ((g : ℤ) - 1) EUV hEUV
        (by omega) (by omega)]
    · rw [hdegEUV, min_eq_left (by omega), max_eq_left (by omega)]
    · rw [hdegEUV]
      omega
  rw [← hDDef]
  unfold rankDelta mark
  rw [hRankD, hRankDU, hRankDV, hRankDUV]
  ring

/-- Under the arithmetic hypotheses of the complementary residue case, its
top normal-form coefficient occurs exactly for `N = 2, m = 1`, and then the
paper's row coordinate is `b = 1`. -/
theorem crossOneOff_complement_boundary_iff_length_two
    {g N m b : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m)
    (hProduct : m * (N - 1) ≤ g) (hb : b + 1 = m * N) :
    m * (N - 1) = 1 ↔ N = 2 ∧ m = 1 ∧ b = 1 := by
  constructor
  · intro hProductEq
    have hmLe : m ≤ 1 := by
      nlinarith [show 1 ≤ N - 1 by omega]
    have hmEq : m = 1 := by omega
    have hPredEq : N - 1 = 1 := by simpa [hmEq] using hProductEq
    have hNEq : N = 2 := by omega
    have hbEq : b = 1 := by
      rw [hmEq, hNEq] at hb
      omega
    exact ⟨hNEq, hmEq, hbEq⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

end Bananas
