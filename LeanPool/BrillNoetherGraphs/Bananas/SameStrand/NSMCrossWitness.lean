/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffDelta
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.FarMarkNegativeAPI

/-!
# Rank-zero part of the cross-strand witness in Theorem 3.9

The first divisor in the distinct-strand proof of Theorem 3.9 is reduced,
after a path-pair slide, to a core chip plus a two-strand semibreak.  This file
records the normal-form calculation abstractly, so the eventual case split
does not need to unfold a concrete banana divisor.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Two raw interior path chips on distinct strands form a semibreak divisor.
This is the raw-coordinate companion of
`isSemibreak_two_distinct_strand_chips`, used by the explicit path-firing
witnesses in Theorem 3.9. -/
theorem isSemibreak_two_distinct_path_chips
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (p : B.PathPosition α) (q : B.PathPosition β)
    (hp : B.IsInteriorPosition α p)
    (hq : B.IsInteriorPosition β q) (hαβ : α ≠ β) :
    IsSemibreak B
      (oneChip (B.pathVertex α p) + oneChip (B.pathVertex β q)) := by
  let op := B.interiorOffsetOfPosition α p hp
  let oq := B.interiorOffsetOfPosition β q hq
  let chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)) :=
    fun γ => if hγα : γ = α then some (hγα ▸ op)
      else if hγβ : γ = β then some (hγβ ▸ oq) else none
  refine ⟨chips, ?_⟩
  rw [B.pathVertex_eq_interiorVertex α p hp,
    B.pathVertex_eq_interiorVertex β q hq]
  funext z
  rcases z with core | ⟨γ, offset⟩
  · simp [semibreakDivisor, oneChip,
      SubdivisionGraph.Spec.interiorVertex]
  · by_cases hγα : γ = α
    · subst γ
      simp [semibreakDivisor, chips, hαβ, oneChip,
        SubdivisionGraph.Spec.interiorVertex]
      aesop
    · by_cases hγβ : γ = β
      · subst γ
        simp [semibreakDivisor, chips, hγα, oneChip,
          SubdivisionGraph.Spec.interiorVertex]
        aesop
      · simp [semibreakDivisor, chips, hγα, hγβ, oneChip,
        SubdivisionGraph.Spec.interiorVertex]

/-- Adding the left endpoint to a degree-two semibreak divisor has rank zero
on a banana of genus at least three. -/
theorem rank_leftEndpoint_add_two_chip_semibreak_eq_zero
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E) (hdeg : deg E = 2) :
    rank B.graph (oneChip (leftEndpoint B) + E) = 0 := by
  have hForm : oneChip (leftEndpoint B) + E =
      bananaNormalForm B 1 0 E := by
    unfold bananaNormalForm leftEndpoint
    simp only [one_zsmul, zero_zsmul, add_zero]
  rw [hForm, rank_bananaNormalForm B 1 0 E hE (by omega) (by omega)]
  · rw [hdeg]
    omega
  rw [hdeg]
  omega

/-- Adding the right endpoint to a degree-two semibreak divisor has rank zero
on a banana of genus at least three. -/
theorem rank_rightEndpoint_add_two_chip_semibreak_eq_zero
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E) (hdeg : deg E = 2) :
    rank B.graph (oneChip (rightEndpoint B) + E) = 0 := by
  have hForm : oneChip (rightEndpoint B) + E =
        bananaNormalForm B 0 1 E := by
    unfold bananaNormalForm rightEndpoint
    simp only [zero_zsmul, one_zsmul, zero_add]
  rw [hForm, rank_bananaNormalForm B 0 1 E hE (by omega) (by omega)]
  · rw [hdeg]
    omega
  rw [hdeg]
  omega

private theorem linearEquiv_add_common {G : CFGraph} {A B : CFDiv G}
    (h : linearEquiv G A B) (C : CFDiv G) :
    linearEquiv G (A + C) (B + C) := by
  unfold linearEquiv at h ⊢
  convert h using 1
  abel

/-- The first rank-zero line of the distinct-strand witness in Theorem 3.9.
If two interior chips on one raw path slide to its tail endpoint, adjoining an
interior chip on a distinct strand gives a rank-zero divisor in genus at least
three. -/
theorem rank_tail_slide_add_distinct_path_eq_zero
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g)
    (α β : Fin (g + 1)) (p q : B.PathPosition α)
    (r : B.PathPosition β)
    (hp : B.IsInteriorPosition α p) (hq : B.IsInteriorPosition α q)
    (hr : B.IsInteriorPosition β r) (hαβ : α ≠ β)
    (hsum : p.val + q.val < B.length α) :
    rank B.graph
      (oneChip (B.pathVertex α p) + oneChip (B.pathVertex α q) +
        oneChip (B.pathVertex β r)) = 0 := by
  let s : B.PathPosition α := ⟨p.val + q.val, by omega⟩
  have hs : B.IsInteriorPosition α s := by
    change 0 < p.val + q.val ∧ p.val + q.val < B.length α
    exact ⟨Nat.add_pos_left hp.1 _, hsum⟩
  have hSlide := path_pair_linearEquiv_tail_sum B α p q hp.1 hq.1 hsum
  have hAdd := linearEquiv_add_common hSlide (oneChip (B.pathVertex β r))
  have hRankEq := rank_eq_of_linear_equiv B.graph hAdd
  have hE : IsSemibreak B
      (oneChip (B.pathVertex α s) + oneChip (B.pathVertex β r)) :=
    isSemibreak_two_distinct_path_chips B α β s r hs hr hαβ
  have hdeg : deg ((oneChip (B.pathVertex α s) +
      oneChip (B.pathVertex β r) : CFDiv B.graph)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hTailRank : rank B.graph
      (oneChip (B.coreVertex (B.core.tail α)) +
        (oneChip (B.pathVertex α s) + oneChip (B.pathVertex β r))) = 0 := by
    rcases fin_two_eq_zero_or_one (B.core.tail α) with hTail | hTail
    · rw [hTail]
      simpa [leftEndpoint] using
        rank_leftEndpoint_add_two_chip_semibreak_eq_zero hg B _ hE hdeg
    · rw [hTail]
      simpa [rightEndpoint] using
        rank_rightEndpoint_add_two_chip_semibreak_eq_zero hg B _ hE hdeg
  dsimp [s] at hTailRank
  have hTailRank' : rank B.graph
      (oneChip (B.coreVertex (B.core.tail α)) +
        oneChip (B.pathVertex α ⟨p.val + q.val, by omega⟩) +
        oneChip (B.pathVertex β r)) = 0 := by
    simpa only [add_assoc] using hTailRank
  rw [hTailRank'] at hRankEq
  exact hRankEq

private theorem crossLinearEquiv_add {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linearEquiv G A B) (h₂ : linearEquiv G C D) :
    linearEquiv G (A + C) (B + D) := by
  unfold linearEquiv at h₁ h₂ ⊢
  have h := (principalDivisors G).add_mem h₁ h₂
  convert h using 1
  abel

private theorem crossLinearEquiv_sub {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linearEquiv G A B) (h₂ : linearEquiv G C D) :
    linearEquiv G (A - C) (B - D) := by
  unfold linearEquiv at h₁ h₂ ⊢
  have h := (principalDivisors G).sub_mem h₁ h₂
  convert h using 1
  abel

private theorem crossLinearEquiv_refl {G : CFGraph} (D : CFDiv G) :
    linearEquiv G D D := by
  unfold linearEquiv
  rw [sub_self]
  exact (principalDivisors G).zero_mem

/-- Two normalized chips at positions `1` and `i` slide to the left endpoint
and position `i+1`. -/
theorem strand_one_add_position_linearEquiv_left_succ
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (hi : i.val + 1 ≤ B.length α) :
    linearEquiv B.graph
      (oneChip (strandVertex B α ⟨1, by
          have := B.length_pos α
          omega⟩) + oneChip (strandVertex B α i))
      (oneChip (leftEndpoint B) +
        oneChip (strandVertex B α ⟨i.val + 1, by omega⟩)) := by
  have hᵢ := strand_prefix_linearEquiv B α i
  have hsucc := strand_prefix_linearEquiv B α
    (⟨i.val + 1, by omega⟩ : B.PathPosition α)
  unfold linearEquiv at hᵢ hsucc ⊢
  have h := (principalDivisors B.graph).sub_mem hsucc hᵢ
  convert h using 1
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  push_cast
  ring

/-- The left endpoint plus the difference between positions `n-1` and `j`
is equivalent to the chip in complementary position `n-1-j`. -/
theorem left_add_penultimate_sub_position_linearEquiv_complement
    {g : ℕ} (B : Banana g) (β : Fin (g + 1))
    (j : B.PathPosition β) (hj : j.val + 1 ≤ B.length β) :
    linearEquiv B.graph
      (oneChip (leftEndpoint B) +
        oneChip (strandVertex B β ⟨B.length β - 1, by
          have := B.length_pos β
          omega⟩) - oneChip (strandVertex B β j))
      (oneChip (strandVertex B β
        ⟨B.length β - 1 - j.val, by omega⟩)) := by
  have hlast := strand_prefix_linearEquiv B β
    (⟨B.length β - 1, by omega⟩ : B.PathPosition β)
  have hjPrefix := strand_prefix_linearEquiv B β j
  have hcomp := strand_prefix_linearEquiv B β
    (⟨B.length β - 1 - j.val, by omega⟩ : B.PathPosition β)
  unfold linearEquiv at hlast hjPrefix hcomp ⊢
  have hdiff := (principalDivisors B.graph).sub_mem hlast hjPrefix
  have h := (principalDivisors B.graph).sub_mem hcomp hdiff
  convert h using 1
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  have hcast : ((B.length β - 1 - j.val : ℕ) : ℤ) =
      (B.length β : ℤ) - 1 - (j.val : ℤ) := by
    omega
  have hlastcast : ((B.length β - 1 : ℕ) : ℤ) = (B.length β : ℤ) - 1 := by
    omega
  rw [hcast, hlastcast]
  ring

/-- The first explicit divisor in the distinct-strand proof of corrected
Theorem 3.9 has negative rank difference. -/
theorem rankDelta_first_cross_witness_neg
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α)
    (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i)
    (_hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β)
    (hiFar : i.val + 1 < B.length α)
    (hjFar : j.val + 1 < B.length β) :
    rankDelta
      (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (oneChip (strandVertex B α ⟨1, by omega⟩) +
        oneChip (strandVertex B α i) +
        oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) < 0 := by
  let p : B.PathPosition α := ⟨i.val + 1, by omega⟩
  let q : B.PathPosition β := ⟨B.length β - 1 - j.val, by omega⟩
  have hOne : B.IsInteriorPosition α (⟨1, by omega⟩ : B.PathPosition α) := by
    change 0 < (1 : ℕ) ∧ 1 < B.length α
    omega
  have hPenult : B.IsInteriorPosition β
      (⟨B.length β - 1, by omega⟩ : B.PathPosition β) := by
    change 0 < B.length β - 1 ∧ B.length β - 1 < B.length β
    omega
  have hp : B.IsInteriorPosition α p := by
    change 0 < i.val + 1 ∧ i.val + 1 < B.length α
    omega
  have hq : B.IsInteriorPosition β q := by
    change 0 < B.length β - 1 - j.val ∧
      B.length β - 1 - j.val < B.length β
    omega
  have hPair := strand_one_add_position_linearEquiv_left_succ B α i
    (by omega)
  have hComplement :=
    left_add_penultimate_sub_position_linearEquiv_complement B β j (by omega)
  have hD : linearEquiv B.graph
      (oneChip (strandVertex B α ⟨1, by omega⟩) +
        oneChip (strandVertex B α i) +
        oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (oneChip (leftEndpoint B) +
        (oneChip (strandVertex B α p) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩))) := by
    have h := crossLinearEquiv_add hPair
      (crossLinearEquiv_refl
        (oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)))
    dsimp [p]
    convert h using 1
    abel
  have hDV : linearEquiv B.graph
      ((oneChip (strandVertex B α ⟨1, by omega⟩) +
          oneChip (strandVertex B α i) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) -
        oneChip (strandVertex B β j))
      (oneChip (strandVertex B α p) + oneChip (strandVertex B β q)) := by
    have hSub := crossLinearEquiv_sub hD
      (crossLinearEquiv_refl (oneChip (strandVertex B β j)))
    have hAdd := crossLinearEquiv_add
      (crossLinearEquiv_refl (oneChip (strandVertex B α p))) hComplement
    dsimp [p, q] at hAdd ⊢
    exact hSub.trans (by
      convert hAdd using 1
      abel)
  have hDUV : linearEquiv B.graph
      ((oneChip (strandVertex B α ⟨1, by omega⟩) +
          oneChip (strandVertex B α i) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) -
        oneChip (strandVertex B α i) - oneChip (strandVertex B β j))
      (oneChip (strandVertex B α p) + oneChip (strandVertex B β q) -
        oneChip (strandVertex B α i)) := by
    have hSub := crossLinearEquiv_sub hDV
      (crossLinearEquiv_refl (oneChip (strandVertex B α i)))
    convert hSub using 1
    abel
  have hSemiD : IsSemibreak B
      (oneChip (strandVertex B α p) +
        oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) :=
    isSemibreak_two_distinct_strand_chips B α β p _ hp hPenult hαβ
  have hSemiDU : IsSemibreak B
      (oneChip (strandVertex B α ⟨1, by omega⟩) +
        oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) :=
    isSemibreak_two_distinct_strand_chips B α β _ _ hOne hPenult hαβ
  have hSemiDV : IsSemibreak B
      (oneChip (strandVertex B α p) + oneChip (strandVertex B β q)) :=
    isSemibreak_two_distinct_strand_chips B α β p q hp hq hαβ
  have hdegD : deg (oneChip (strandVertex B α p) +
      oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hdegDU : deg (oneChip (strandVertex B α ⟨1, by omega⟩) +
      oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hdegDV : deg (oneChip (strandVertex B α p) +
      oneChip (strandVertex B β q)) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  have hRankD : rank B.graph
      (oneChip (strandVertex B α ⟨1, by omega⟩) +
        oneChip (strandVertex B α i) +
        oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) = 0 := by
    rw [rank_eq_of_linear_equiv B.graph hD]
    exact rank_leftEndpoint_add_two_chip_semibreak_eq_zero hg B _ hSemiD hdegD
  have hRankDU : rank B.graph
      ((oneChip (strandVertex B α ⟨1, by omega⟩) +
          oneChip (strandVertex B α i) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) -
        oneChip (strandVertex B α i)) = 0 := by
    rw [show (oneChip (strandVertex B α ⟨1, by omega⟩) +
          oneChip (strandVertex B α i) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) -
        oneChip (strandVertex B α i) =
        oneChip (strandVertex B α ⟨1, by omega⟩) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩) by abel]
    exact rank_semibreak_eq_zero B _ hSemiDU (by rw [hdegDU]; omega)
  have hRankDV : rank B.graph
      ((oneChip (strandVertex B α ⟨1, by omega⟩) +
          oneChip (strandVertex B α i) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) -
        oneChip (strandVertex B β j)) = 0 := by
    rw [rank_eq_of_linear_equiv B.graph hDV]
    exact rank_semibreak_eq_zero B _ hSemiDV (by rw [hdegDV]; omega)
  have hpx : strandVertex B α i ≠ strandVertex B α p := by
    intro h
    have hv := congrArg Fin.val (strandVertex_injective B α h)
    dsimp [p] at hv
    omega
  have hpy : strandVertex B α i ≠ strandVertex B β q := by
    intro h
    exact hαβ (strand_eq_of_interior_vertex_eq B α β i q hi hq h)
  have hRankDUV : rank B.graph
      ((oneChip (strandVertex B α ⟨1, by omega⟩) +
          oneChip (strandVertex B α i) +
          oneChip (strandVertex B β ⟨B.length β - 1, by omega⟩)) -
        oneChip (strandVertex B α i) - oneChip (strandVertex B β j)) = -1 := by
    rw [rank_eq_of_linear_equiv B.graph hDUV]
    exact rank_strand_pair_sub_neg_of_distinct_interior (by omega) B α β α
      p q i hp hq hi hαβ hpx hpy
  unfold rankDelta mark
  rw [hRankD, hRankDU, hRankDV, hRankDUV]
  norm_num

end Bananas
