/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiring
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankZeroSupport

/-!
# Rank-difference calculation for the cross-one-off marking

This file proves the first assertion of part (3) of paper Corollary 2.25
(`cor-BananaDeltaComps`).  The marked points lie one step from opposite
endpoints on two distinct strands.  The proof packages the two remaining
interior chips as a semibreak divisor, shifts them after deleting a marked
point, and applies the endpoint/semibreak rank formula four times.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec


/-- The storage-oriented interior offset corresponding to a normalized
interior strand position. -/
def normalizedInteriorOffset {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (p : B.PathPosition α)
    (hp : B.IsInteriorPosition α p) : Fin (B.length α - 1) :=
  if htail : B.core.tail α = 0 then
    ⟨p.val - 1, by
      change 0 < p.val ∧ p.val < B.length α at hp
      omega⟩
  else
    ⟨B.length α - p.val - 1, by
      change 0 < p.val ∧ p.val < B.length α at hp
      omega⟩

theorem strandVertex_eq_interiorVertex_normalizedInteriorOffset
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (p : B.PathPosition α) (hp : B.IsInteriorPosition α p) :
    strandVertex B α p =
      B.interiorVertex α (normalizedInteriorOffset B α p hp) := by
  unfold strandVertex normalizedInteriorOffset
  by_cases htail : B.core.tail α = 0
  · simp only [htail, ↓reduceIte]
    rw [B.pathVertex_eq_interiorVertex α p hp]
    congr 1
  · simp only [htail, ↓reduceIte]
    let raw : B.PathPosition α :=
      ⟨B.length α - p.val, by have := p.isLt; omega⟩
    have hraw : B.IsInteriorPosition α raw := by
      change 0 < p.val ∧ p.val < B.length α at hp
      change 0 < B.length α - p.val ∧
        B.length α - p.val < B.length α
      omega
    change B.pathVertex α raw = _
    rw [B.pathVertex_eq_interiorVertex α raw hraw]
    congr 1

/-- Two normalized interior chips on distinct strands form a semibreak
divisor. -/
theorem isSemibreak_two_distinct_strand_chips
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (p : B.PathPosition α) (q : B.PathPosition β)
    (hp : B.IsInteriorPosition α p)
    (hq : B.IsInteriorPosition β q) (hαβ : α ≠ β) :
    IsSemibreak B
      (one_chip (strandVertex B α p) + one_chip (strandVertex B β q)) := by
  let op := normalizedInteriorOffset B α p hp
  let oq := normalizedInteriorOffset B β q hq
  let chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)) :=
    fun γ => if hγα : γ = α then some (hγα ▸ op)
      else if hγβ : γ = β then some (hγβ ▸ oq) else none
  refine ⟨chips, ?_⟩
  rw [strandVertex_eq_interiorVertex_normalizedInteriorOffset B α p hp,
    strandVertex_eq_interiorVertex_normalizedInteriorOffset B β q hq]
  funext z
  rcases z with core | ⟨γ, offset⟩
  · simp [semibreakDivisor, one_chip,

      SubdivisionGraph.Spec.interiorVertex]
  · by_cases hγα : γ = α
    · subst γ
      simp [semibreakDivisor, chips, hαβ, one_chip,
        SubdivisionGraph.Spec.interiorVertex]
      aesop
    · by_cases hγβ : γ = β
      · subst γ
        simp [semibreakDivisor, chips, hγα, one_chip,
          SubdivisionGraph.Spec.interiorVertex]
        aesop
      · simp [semibreakDivisor, chips, hγα, hγβ, one_chip,
          SubdivisionGraph.Spec.interiorVertex]

private theorem linearEquiv_sub {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linear_equiv G A B) (h₂ : linear_equiv G C D) :
    linear_equiv G (A - C) (B - D) := by
  unfold linear_equiv at h₁ h₂ ⊢
  have h := (principal_divisors G).sub_mem h₁ h₂
  convert h using 1 ; abel

private theorem linearEquiv_add {G : CFGraph} {A B C D : CFDiv G}
    (h₁ : linear_equiv G A B) (h₂ : linear_equiv G C D) :
    linear_equiv G (A + C) (B + D) := by
  unfold linear_equiv at h₁ h₂ ⊢
  have h := (principal_divisors G).add_mem h₁ h₂
  convert h using 1 ; abel

private theorem linearEquiv_add_common {G : CFGraph} {A B : CFDiv G}
    (h : linear_equiv G A B) (C : CFDiv G) :
    linear_equiv G (C + A) (C + B) := by
  unfold linear_equiv at h ⊢
  convert h using 1 ; abel

/-- Paper Corollary 2.25(3), first rank-difference calculation, in normalized
coordinates. -/
theorem rankDelta_crossOneOff_two_interior_eq_one
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (p : B.PathPosition α) (q : B.PathPosition β) (c : ℕ)
    (hg : 2 ≤ g)
    (hαβ : α ≠ β)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length α)
    (hqLo : 1 ≤ q.val) (hqHi : q.val + 1 < B.length β)
    (hc : c ≤ g - 2) :
    rankDelta
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      ((c : ℤ) •
          (one_chip (leftEndpoint B) + one_chip (rightEndpoint B)) +
        one_chip (strandVertex B α p) + one_chip (strandVertex B β q)) = 1 := by
  let pPrev : B.PathPosition α := ⟨p.val - 1, by omega⟩
  let qNext : B.PathPosition β := ⟨q.val + 1, by omega⟩
  have hp : B.IsInteriorPosition α p := by
    change 0 < p.val ∧ p.val < B.length α
    omega
  have hpPrev : B.IsInteriorPosition α pPrev := by
    change 0 < p.val - 1 ∧ p.val - 1 < B.length α
    omega
  have hq : B.IsInteriorPosition β q := by
    change 0 < q.val ∧ q.val < B.length β
    omega
  have hqNext : B.IsInteriorPosition β qNext := by
    change 0 < q.val + 1 ∧ q.val + 1 < B.length β
    omega
  let E : CFDiv B.graph :=
    one_chip (strandVertex B α p) + one_chip (strandVertex B β q)
  let EU : CFDiv B.graph :=
    one_chip (strandVertex B α pPrev) + one_chip (strandVertex B β q)
  let EV : CFDiv B.graph :=
    one_chip (strandVertex B α p) + one_chip (strandVertex B β qNext)
  let EUV : CFDiv B.graph :=
    one_chip (strandVertex B α pPrev) + one_chip (strandVertex B β qNext)
  have hE : IsSemibreak B E := by
    dsimp [E]
    exact isSemibreak_two_distinct_strand_chips B α β p q hp hq hαβ
  have hEU : IsSemibreak B EU := by
    dsimp [EU]
    exact isSemibreak_two_distinct_strand_chips B α β pPrev q hpPrev hq hαβ
  have hEV : IsSemibreak B EV := by
    dsimp [EV]
    exact isSemibreak_two_distinct_strand_chips B α β p qNext hp hqNext hαβ
  have hEUV : IsSemibreak B EUV := by
    dsimp [EUV]
    exact isSemibreak_two_distinct_strand_chips B α β pPrev qNext
      hpPrev hqNext hαβ
  have hdegE : deg E = 2 := by
    simp [E, deg.map_add, deg_one_chip]
  have hdegEU : deg EU = 2 := by
    simp [EU, deg.map_add, deg_one_chip]
  have hdegEV : deg EV = 2 := by
    simp [EV, deg.map_add, deg_one_chip]
  have hdegEUV : deg EUV = 2 := by
    simp [EUV, deg.map_add, deg_one_chip]
  have hcInt : (c : ℤ) + 2 ≤ (g : ℤ) := by
    exact_mod_cast (show c + 2 ≤ g by omega)
  let D : CFDiv B.graph := bananaNormalForm B (c : ℤ) (c : ℤ) E
  have hDDef : D =
      (c : ℤ) • (one_chip (leftEndpoint B) + one_chip (rightEndpoint B)) +
        one_chip (strandVertex B α p) + one_chip (strandVertex B β q) := by
    dsimp [D, E]
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  have hShiftU := crossOneOff_sub_first_mark_shift B α p.val
    (by omega) (by omega)
  have hShiftV := crossOneOff_sub_second_mark_shift B β q.val (by omega)
  have hDU : linear_equiv B.graph
      (D - one_chip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))
      (bananaNormalForm B ((c : ℤ) - 1) (c : ℤ) EU) := by
    have h := linearEquiv_add_common hShiftU
      ((c : ℤ) •
          (one_chip (leftEndpoint B) + one_chip (rightEndpoint B)) +
        one_chip (strandVertex B β q))
    dsimp [D, E, EU, pPrev]
    unfold bananaNormalForm at h ⊢
    convert h using 1 <;>
      ext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  have hDV : linear_equiv B.graph
      (D - one_chip
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (bananaNormalForm B (c : ℤ) ((c : ℤ) - 1) EV) := by
    have h := linearEquiv_add_common hShiftV
      ((c : ℤ) •
          (one_chip (leftEndpoint B) + one_chip (rightEndpoint B)) +
        one_chip (strandVertex B α p))
    dsimp [D, E, EV, qNext]
    unfold bananaNormalForm at h ⊢
    convert h using 1 <;>
      ext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  have hDUV : linear_equiv B.graph
      (D - one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        one_chip
          (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (bananaNormalForm B ((c : ℤ) - 1) ((c : ℤ) - 1) EUV) := by
    have hPair := linearEquiv_add hShiftU hShiftV
    have h := linearEquiv_add_common hPair
      ((c : ℤ) •
        (one_chip (leftEndpoint B) + one_chip (rightEndpoint B)))
    dsimp [D, E, EUV, pPrev, qNext]
    unfold bananaNormalForm at h ⊢
    convert h using 1 <;>
      ext z <;>
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;>
      ring
  have hRankD : rank B.graph D = (c : ℤ) := by
    rw [rank_bananaNormalForm B (c : ℤ) (c : ℤ) E hE
      (by omega) (by omega)]
    · rw [hdegE]
      simp only [min_self]
      rw [max_eq_left]
      omega
    · rw [hdegE]
      exact hcInt
  have hRankDU : rank B.graph
      (D - one_chip
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)) =
        (c : ℤ) - 1 := by
    rw [rank_eq_of_linear_equiv B.graph hDU,
      rank_bananaNormalForm B ((c : ℤ) - 1) (c : ℤ) EU hEU
        (by omega) (by omega)]
    · rw [hdegEU]
      have hmin : min ((c : ℤ) - 1) (c : ℤ) = (c : ℤ) - 1 :=
        min_eq_left (by omega)
      rw [hmin, max_eq_left]
      omega
    · rw [hdegEU]
      exact hcInt
  have hRankDV : rank B.graph
      (D - one_chip
        (strandVertex B β ⟨B.length β - 1, by omega⟩)) =
        (c : ℤ) - 1 := by
    rw [rank_eq_of_linear_equiv B.graph hDV]
    by_cases hc0 : c = 0
    · subst c
      have hred := q_reduced_bananaNormalForm_right B 0 (-1) EV hEV
        (by omega) (by rw [hdegEV]; exact_mod_cast hg)
      apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
        (bananaNormalForm B 0 (-1) EV) hred
      rw [bananaNormalForm_rightEndpoint B 0 (-1) EV hEV]
      omega
    · rw [rank_bananaNormalForm B (c : ℤ) ((c : ℤ) - 1) EV hEV
          (by omega) (by omega)]
      · rw [hdegEV]
        have hmin : min (c : ℤ) ((c : ℤ) - 1) = (c : ℤ) - 1 :=
          min_eq_right (by omega)
        rw [hmin, max_eq_left]
        omega
      · rw [hdegEV]
        omega
  have hRankDUV : rank B.graph
      (D - one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        one_chip
          (strandVertex B β ⟨B.length β - 1, by omega⟩)) =
        (c : ℤ) - 1 := by
    by_cases hc0 : c = 0
    · subst c
      have hUpper := rank_sub_one_chip_le_rank B.graph
        (D - one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩))
        (strandVertex B β ⟨B.length β - 1, by omega⟩)
      have hLower := rank_geq_neg_one B.graph
        (D - one_chip
          (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
          one_chip
            (strandVertex B β ⟨B.length β - 1, by omega⟩))
      rw [hRankDU] at hUpper
      omega
    · rw [rank_eq_of_linear_equiv B.graph hDUV,
        rank_bananaNormalForm B ((c : ℤ) - 1) ((c : ℤ) - 1)
          EUV hEUV (by omega) (by omega)]
      · rw [hdegEUV]
        simp only [min_self]
        rw [max_eq_left]
        omega
      · rw [hdegEUV]
        omega
  rw [← hDDef]
  unfold rankDelta mark
  rw [hRankD, hRankDU, hRankDV, hRankDUV]
  ring

end Bananas
