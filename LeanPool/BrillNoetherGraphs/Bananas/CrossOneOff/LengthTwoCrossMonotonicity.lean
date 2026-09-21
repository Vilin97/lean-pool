/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.LengthTwoCrossBasePoint
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankDeltaDuality

/-!
# Monotonicity ingredients for the length-two cross exception

This file records the slightly enlarged midpoint base-point calculation needed
after a chip on another strand is put back into banana normal form.  That
operation can lower one endpoint coefficient from `0` to `-1`; the original
low-degree lemma only covered nonnegative endpoint coefficients.

## Elaboration cost

All divisor algebra used below is proved once in the `Generic` section, for an
abstract `CFGraph` and abstract divisors.  This is a performance requirement,
not a stylistic preference.  `change`, `convert` and `abel` applied to divisors
of a *concrete* banana graph let the unifier fall back on comparing divisors
pointwise: it then unfolds `one_chip` into `if v = w then 1 else 0` and starts
evaluating `DecidableEq` on the subdivision vertex type (a nested `Sum` of
`Fin`s built out of `pathVertex`/`strandVertex` dite-chains).  A single such
`change` costs minutes.  With abstract divisors the same steps are instant, and
every use downstream is a syntactic `rw`/`exact`.
-/

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The loss of rank on deleting one chip is always either zero or one. -/
theorem basePointDrop_nonneg (M : TwiceMarked) (D : CFDiv M.graph) :
    0 ≤ basePointDrop M D := by
  unfold basePointDrop
  have h := rank_add_one_chip_ge (D - one_chip M.u) M.u
    (rank M.graph (D - one_chip M.u)) le_rfl
  have heq : D - one_chip M.u + one_chip M.u = D := by abel
  rw [heq] at h
  omega

theorem basePointDrop_le_one (M : TwiceMarked) (D : CFDiv M.graph) :
    basePointDrop M D ≤ 1 := by
  unfold basePointDrop
  have h := rank_sub_one_chip_ge_rank_sub_one D M.u
  omega

/-! ## Graph-generic divisor algebra

See the note on elaboration cost in the module docstring: every statement in
this section is about an abstract graph, so that no use of it ever forces the
unifier to look inside a banana divisor. -/

section Generic

variable {G : CFGraph}

/-- `basePointDrop` of an explicitly marked graph, with the structure
projections already reduced away. -/
theorem basePointDrop_mark (u v : G.V) (D : CFDiv G) :
    basePointDrop (mark G u v) D = rank G D - rank G (D - one_chip u) := rfl

theorem basePointDrop_mark_nonneg (u v : G.V) (D : CFDiv G) :
    0 ≤ basePointDrop (mark G u v) D :=
  basePointDrop_nonneg (mark G u v) D

theorem basePointDrop_mark_le_one (u v : G.V) (D : CFDiv G) :
    basePointDrop (mark G u v) D ≤ 1 :=
  basePointDrop_le_one (mark G u v) D

theorem rankDelta_mark_eq_basePointDrop_sub (u v : G.V) (D : CFDiv G) :
    rankDelta (mark G u v) D =
      basePointDrop (mark G u v) D -
        basePointDrop (mark G u v) (D - one_chip v) :=
  rankDelta_eq_basePointDrop_sub (mark G u v) D

theorem rankDelta_mark_eq_of_linearEquiv (u v : G.V) {D D' : CFDiv G}
    (h : linear_equiv G D D') :
    rankDelta (mark G u v) D = rankDelta (mark G u v) D' :=
  rankDelta_eq_of_linearEquiv (M := mark G u v) h

theorem rankDelta_mark_canonical_dual (u v : G.V) (hconn : _root_.graph_connected G)
    (D : CFDiv G) :
    rankDelta (mark G u v) D =
      rankDelta (mark G u v)
        (canonical_divisor G + one_chip u + one_chip v - D) :=
  rankDelta_canonical_dual (mark G u v) hconn D

theorem rankDelta_mark_neg_iff_rank_pattern (u v : G.V) (D : CFDiv G) :
    rankDelta (mark G u v) D < 0 ↔
      rank G D = rank G (D - one_chip u) ∧
      rank G D = rank G (D - one_chip v) ∧
      rank G D = rank G (D - one_chip u - one_chip v) + 1 :=
  rankDelta_neg_iff_rank_pattern (mark G u v) D

/-- Linear equivalence is stable under subtracting a fixed divisor. -/
theorem linear_equiv_sub_fixed_right {D D' : CFDiv G} (C : CFDiv G)
    (h : linear_equiv G D D') : linear_equiv G (D - C) (D' - C) := by
  unfold linear_equiv at h ⊢
  have hEq : D' - C - (D - C) = D' - D := by abel
  rw [hEq]
  exact h

theorem basePointDrop_mark_eq_zero_of_rank_eq (u v : G.V) {D : CFDiv G}
    (h : rank G D = rank G (D - one_chip u)) :
    basePointDrop (mark G u v) D = 0 := by
  rw [basePointDrop_mark, h, sub_self]

/-- The workhorse: to see that a divisor is not a base point for `u`, move it
by a linear equivalence to a divisor where the rank comparison is known. -/
theorem basePointDrop_mark_eq_zero_of_linear_equiv (u v : G.V) {D D' : CFDiv G}
    (hEquiv : linear_equiv G D D')
    (hRank : rank G D' = rank G (D' - one_chip u)) :
    basePointDrop (mark G u v) D = 0 := by
  refine basePointDrop_mark_eq_zero_of_rank_eq u v ?_
  rw [rank_eq_of_linear_equiv G hEquiv,
    rank_eq_of_linear_equiv G (linear_equiv_sub_fixed_right (one_chip u) hEquiv),
    hRank]

/-- The two endpoints play symmetric roles in the reflection identity. -/
theorem linear_equiv_endpoint_swap {L R P P' : CFDiv G}
    (h : linear_equiv G (L + R) (P + P')) :
    linear_equiv G (R + L) (P + P') := by
  unfold linear_equiv at h ⊢
  have hEq : P + P' - (R + L) = P + P' - (L + R) := by abel
  rw [hEq]
  exact h

/-- Reflection in the strand midpoint followed by a slide of the old chip
towards the tail endpoint `L`. -/
theorem linear_equiv_pair_of_reflect_slide {L R P P' Q X : CFDiv G}
    (hReflect : linear_equiv G (L + R) (P + P'))
    (hSlide : linear_equiv G (Q + P') (L + X)) :
    linear_equiv G (R + Q) (P + X) := by
  unfold linear_equiv at hReflect hSlide ⊢
  have h := (principal_divisors G).add_mem hReflect hSlide
  have hEq : P + X - (R + Q) = P + P' - (L + R) + (L + X - (Q + P')) := by abel
  rw [hEq]
  exact h

/-- Variant of `linear_equiv_pair_of_reflect_slide` for the head-excess slide,
whose statement lists the endpoint chip second. -/
theorem linear_equiv_pair_of_reflect_slide' {L R P P' Q X : CFDiv G}
    (hReflect : linear_equiv G (L + R) (P + P'))
    (hSlide : linear_equiv G (Q + P') (X + L)) :
    linear_equiv G (R + Q) (P + X) := by
  unfold linear_equiv at hReflect hSlide ⊢
  have h := (principal_divisors G).add_mem hReflect hSlide
  have hEq : P + X - (R + Q) = P + P' - (L + R) + (X + L - (Q + P')) := by abel
  rw [hEq]
  exact h

/-- Boundary case: the old chip and the reflected mark are themselves a
reflected pair, so both endpoint chips cancel. -/
theorem linear_equiv_of_reflect_pair {L R P P' Q : CFDiv G}
    (hReflect : linear_equiv G (L + R) (P + P'))
    (hPair : linear_equiv G (L + R) (Q + P')) :
    linear_equiv G Q P := by
  unfold linear_equiv at hReflect hPair ⊢
  have h := (principal_divisors G).sub_mem hReflect hPair
  have hEq : P - Q = P + P' - (L + R) - (Q + P' - (L + R)) := by abel
  rw [hEq]
  exact h

/-- Normal-form bookkeeping: paying one chip at `R` moves the deleted mark `P`
to the new slot `X` and removes the old chip `Q`. -/
theorem linear_equiv_normalForm_sub_right {L R P Q X E : CFDiv G} (a b : ℤ)
    (h : linear_equiv G (R + Q) (P + X)) :
    linear_equiv G (a • L + b • R + E - P)
      (a • L + (b - 1) • R + (E + X - Q)) := by
  unfold linear_equiv at h ⊢
  have hsmul : (b - 1) • R = b • R - R := by rw [sub_zsmul, one_zsmul, sub_eq_add_neg]
  rw [hsmul]
  have hEq : a • L + (b • R - R) + (E + X - Q) - (a • L + b • R + E - P)
      = P + X - (R + Q) := by abel
  rw [hEq]
  exact h

/-- Mirror image of `linear_equiv_normalForm_sub_right`. -/
theorem linear_equiv_normalForm_sub_left {L R P Q X E : CFDiv G} (a b : ℤ)
    (h : linear_equiv G (L + Q) (P + X)) :
    linear_equiv G (a • L + b • R + E - P)
      ((a - 1) • L + b • R + (E + X - Q)) := by
  unfold linear_equiv at h ⊢
  have hsmul : (a - 1) • L = a • L - L := by rw [sub_zsmul, one_zsmul, sub_eq_add_neg]
  rw [hsmul]
  have hEq : a • L - L + b • R + (E + X - Q) - (a • L + b • R + E - P)
      = P + X - (L + Q) := by abel
  rw [hEq]
  exact h

/-- Reflection alone: the deleted mark `P` is replaced by its mirror `P'` at
the cost of one chip at each endpoint. -/
theorem linear_equiv_normalForm_sub_both {L R P P' E : CFDiv G} (a b : ℤ)
    (h : linear_equiv G (L + R) (P + P')) :
    linear_equiv G (a • L + b • R + E - P)
      ((a - 1) • L + (b - 1) • R + (E + P')) := by
  unfold linear_equiv at h ⊢
  have hsmulL : (a - 1) • L = a • L - L := by rw [sub_zsmul, one_zsmul, sub_eq_add_neg]
  have hsmulR : (b - 1) • R = b • R - R := by rw [sub_zsmul, one_zsmul, sub_eq_add_neg]
  rw [hsmulL, hsmulR]
  have hEq : a • L - L + (b • R - R) + (E + P') - (a • L + b • R + E - P)
      = P + P' - (L + R) := by abel
  rw [hEq]
  exact h

/-- Endpoint-pair case: no endpoint chip is spent, the old chip `Q` is simply
removed. -/
theorem linear_equiv_normalForm_sub_pair {L R P Q E : CFDiv G} (a b : ℤ)
    (h : linear_equiv G Q P) :
    linear_equiv G (a • L + b • R + E - P) (a • L + b • R + (E - Q)) := by
  unfold linear_equiv at h ⊢
  have hEq : a • L + b • R + (E - Q) - (a • L + b • R + E - P) = P - Q := by
    abel
  rw [hEq]
  exact h

end Generic

/-! ## Banana normal form as an explicit sum -/

/-- Definitional unfolding of `bananaNormalForm`, as a rewrite rule.  Stated
for a variable banana, so proving it costs nothing. -/
theorem bananaNormalForm_eq {g : ℕ} (B : Banana g) (a b : ℤ)
    (E : CFDiv B.graph) :
    bananaNormalForm B a b E =
      a • one_chip (leftEndpoint B) + b • one_chip (rightEndpoint B) + E := rfl

theorem bananaNormalForm_sub {g : ℕ} (B : Banana g) (a b : ℤ)
    (E C : CFDiv B.graph) :
    bananaNormalForm B a b E - C = bananaNormalForm B a b (E - C) := by
  rw [bananaNormalForm_eq, bananaNormalForm_eq, add_sub_assoc]

/-- Raw path-coordinate version of reflection in the midpoint of a strand. -/
theorem endpoint_sum_linearEquiv_path_reflection
    {g : ℕ} (B : Banana g) (β : Fin (g + 1))
    (p : B.PathPosition β) :
    linear_equiv B.graph
      (one_chip (leftEndpoint B) + one_chip (rightEndpoint B))
      (one_chip (B.pathVertex β p) +
        one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β))) := by
  by_cases htail : B.core.tail β = 0
  · simpa [strandVertex, strandMirror, htail] using
      endpoint_sum_linearEquiv_strand_reflection B β p
  · let q : B.PathPosition β := ⟨B.length β - p.val, by omega⟩
    have hsub : B.length β - (B.length β - p.val) = p.val :=
      Nat.sub_sub_self (Nat.le_of_lt_succ p.isLt)
    simpa [strandVertex, strandMirror, htail, q, hsub, add_comm] using
      endpoint_sum_linearEquiv_strand_reflection B β q

/-- An empty semibreak strand can be filled at any interior slot. -/
theorem isSemibreak_add_interior_chip_of_empty
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph)
    (hE : IsSemibreak B E) (β : Fin (g + 1))
    (newChip : Fin (B.length β - 1))
    (hEmpty : ∀ chip : Fin (B.length β - 1),
      E (B.interiorVertex β chip) = 0) :
    IsSemibreak (B := B) (E + one_chip (B.interiorVertex β newChip)) := by
  rcases hE with ⟨chips, rfl⟩
  have hnone : chips β = none := by
    cases hchip : chips β with
    | none => rfl
    | some chip =>
        have := hEmpty chip
        simp [semibreakDivisor_interiorVertex, hchip] at this
  have hreplaceNone : replaceSemibreakChip B chips β none = chips := by
    funext γ
    by_cases hγβ : γ = β
    · subst γ
      simp [hnone]
    · exact replaceSemibreakChip_other B chips β γ none hγβ
  refine ⟨replaceSemibreakChip B chips β (some newChip), ?_⟩
  rw [semibreakDivisor_add_chip B chips β newChip, hreplaceNone]

/-- Moving the unique chip on a semibreak strand to another interior slot
preserves semibreakness. -/
theorem isSemibreak_replace_interior_chip_of_eq_one
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph)
    (hE : IsSemibreak B E) (β : Fin (g + 1))
    (oldChip newChip : Fin (B.length β - 1))
    (hmem : E (B.interiorVertex β oldChip) = 1) :
    IsSemibreak (B := B)
      (E + one_chip (B.interiorVertex β newChip) -
        one_chip (B.interiorVertex β oldChip)) := by
  rcases hE with ⟨chips, rfl⟩
  have hchip : chips β = some oldChip := by
    simpa [semibreakDivisor_interiorVertex] using hmem
  have hsame : replaceSemibreakChip B chips β (some oldChip) = chips := by
    funext γ
    by_cases hγ : γ = β
    · subst γ
      simp [hchip]
    · exact replaceSemibreakChip_other B chips β γ _ hγ
  refine ⟨replaceSemibreakChip B chips β (some newChip), ?_⟩
  rw [semibreakDivisor_replace_chip B chips β oldChip newChip, hsame]

/-- A length-two midpoint is represented by the same raw path position in
either stored orientation. -/
theorem length_two_midpoint_strandVertex_eq_pathVertex
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) (hα : B.length α = 2) (hi : i.val = 1) :
    strandVertex B α i = B.pathVertex α i := by
  unfold strandVertex
  split_ifs
  · rfl
  · congr 1
    apply Fin.ext
    simp [hα, hi]

theorem length_two_midpoint_ne_pathVertex_of_distinct_strand
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (p : B.PathPosition β)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (_hp : B.IsInteriorPosition β p) :
    strandVertex B α i ≠ B.pathVertex β p := by
  intro hEq
  have hiInterior : B.IsInteriorPosition α i := by
    change 0 < i.val ∧ i.val < B.length α
    omega
  have hRaw : B.pathVertex β p = B.pathVertex α i := by
    rw [← length_two_midpoint_strandVertex_eq_pathVertex B α i hα hi]
    exact hEq.symm
  exact hαβ ((interior_and_strand_eq_of_pathVertex_eq_interior
    B β α p i hiInterior hRaw).2.symm)

/-- Removing an occupied length-two midpoint does not change rank in the
low-degree normal-form range even when one (but not both) endpoint
coefficients is `-1`.

The two separate endpoint-degree bounds are exactly what is produced by
normalizing the deletion of a vertex on a different strand. -/
theorem rank_bananaNormalForm_remove_midpoint_chip_of_ge_neg_one
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph)
    (hE : IsSemibreak B E) (α : Fin (g + 1)) (i : B.PathPosition α)
    (hα : B.length α = 2) (hi : i.val = 1)
    (a b : ℤ) (ha : -1 ≤ a) (hb : -1 ≤ b)
    (hOneNonneg : 0 ≤ a ∨ 0 ≤ b)
    (hLeftDeg : a + deg E ≤ (g : ℤ))
    (hRightDeg : b + deg E ≤ (g : ℤ))
    (hTotalDeg : a + b + deg E ≤ (g : ℤ))
    (hmem : E (strandVertex B α i) = 1) :
    rank B.graph (bananaNormalForm B a b E) =
      rank B.graph (bananaNormalForm B a b E -
        one_chip (strandVertex B α i)) := by
  have hEminus : IsSemibreak (B := B) (E - one_chip (strandVertex B α i)) :=
    isSemibreak_remove_midpoint_chip B E hE α i hα hi hmem
  have hdegMinus : deg (E - one_chip (strandVertex B α i)) = deg E - 1 := by
    rw [deg.map_sub, deg_one_chip]
  rw [bananaNormalForm_sub]
  by_cases haNonneg : 0 ≤ a
  · by_cases hbNonneg : 0 ≤ b
    · rw [← bananaNormalForm_sub]
      exact rank_bananaNormalForm_remove_midpoint_chip B E hE α i hα hi
        a b haNonneg hbNonneg hTotalDeg hmem
    · have hbEq : b = -1 := by omega
      subst b
      have hRank : rank B.graph (bananaNormalForm B a (-1) E) = -1 := by
        apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
          (bananaNormalForm B a (-1) E)
        · exact q_reduced_bananaNormalForm_right B a (-1) E hE haNonneg
            hLeftDeg
        · rw [bananaNormalForm_rightEndpoint B a (-1) E hE]
          omega
      have hRankMinus :
          rank B.graph
              (bananaNormalForm B a (-1) (E - one_chip (strandVertex B α i)))
            = -1 := by
        apply rank_eq_neg_one_of_qReduced_debt B.graph (rightEndpoint B)
        · exact q_reduced_bananaNormalForm_right B a (-1)
            (E - one_chip (strandVertex B α i)) hEminus haNonneg
            (by rw [hdegMinus]; omega)
        · rw [bananaNormalForm_rightEndpoint B a (-1)
            (E - one_chip (strandVertex B α i)) hEminus]
          omega
      rw [hRank, hRankMinus]
  · have haEq : a = -1 := by omega
    subst a
    have hbNonneg : 0 ≤ b := hOneNonneg.resolve_left (by omega)
    have hRank : rank B.graph (bananaNormalForm B (-1) b E) = -1 :=
      (rank_bananaNormalForm_neg_iff B (-1) b E hE hbNonneg
        hRightDeg).2 (by omega)
    have hRankMinus :
        rank B.graph
            (bananaNormalForm B (-1) b (E - one_chip (strandVertex B α i)))
          = -1 :=
      (rank_bananaNormalForm_neg_iff B (-1) b
        (E - one_chip (strandVertex B α i)) hEminus hbNonneg
        (by rw [hdegMinus]; omega)).2 (by omega)
    rw [hRank, hRankMinus]

/-- If the other marked strand is empty in the semibreak part, deleting its
marked point preserves the base-point status of an occupied length-two
midpoint.  This includes the boundary case `a = b = 0`, where the reflected
normal form has two endpoint debts and the rank formula does not apply. -/
theorem basePointDrop_bananaNormalForm_sub_empty_strand_eq_zero
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (p : B.PathPosition β)
    (a b : ℤ) (E : CFDiv B.graph)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (hp : B.IsInteriorPosition β p)
    (hE : IsSemibreak B E)
    (hmem : E (strandVertex B α i) = 1)
    (hEmpty : ∀ chip : Fin (B.length β - 1),
      E (B.interiorVertex β chip) = 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ)) :
    basePointDrop
      (mark B.graph (strandVertex B α i) (B.pathVertex β p))
      ((bananaNormalForm B a b E - one_chip (B.pathVertex β p) :
        CFDiv B.graph)) = 0 := by
  change 0 < p.val ∧ p.val < B.length β at hp
  have hr : B.IsInteriorPosition β
      (⟨B.length β - p.val, by omega⟩ : B.PathPosition β) := by
    change 0 < B.length β - p.val ∧ B.length β - p.val < B.length β
    omega
  have hrVertex : B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β) =
      B.interiorVertex β (⟨B.length β - p.val - 1, by omega⟩ : Fin (B.length β - 1)) := by
    rw [B.pathVertex_eq_interiorVertex β _ hr]
    congr 1
  have hvZero : E (B.pathVertex β p) = 0 := by
    rw [B.pathVertex_eq_interiorVertex β p hp]
    exact hEmpty _
  have huv : strandVertex B α i ≠ B.pathVertex β p :=
    length_two_midpoint_ne_pathVertex_of_distinct_strand B α β i p hαβ hα hi hp
  have hur : strandVertex B α i ≠
      B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β) :=
    length_two_midpoint_ne_pathVertex_of_distinct_strand B α β i _ hαβ hα hi hr
  by_cases habZero : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := habZero
    have hdegE : deg E ≤ (g : ℤ) := by simpa using hLowDeg
    have hRankV : rank B.graph (E - one_chip (B.pathVertex β p)) = -1 :=
      rank_semibreak_sub_vertex_eq_neg_one B E hE hdegE _ hvZero
    have hEminus : IsSemibreak (B := B) (E - one_chip (strandVertex B α i)) :=
      isSemibreak_remove_midpoint_chip B E hE α i hα hi hmem
    have hdegEminus : deg (E - one_chip (strandVertex B α i)) ≤ (g : ℤ) := by
      rw [deg.map_sub, deg_one_chip]
      omega
    have hvZeroMinus :
        (E - one_chip (strandVertex B α i)) (B.pathVertex β p) = 0 := by
      simp [Pi.sub_apply, one_chip, huv.symm, hvZero]
    have hRankUV : rank B.graph
        (E - one_chip (strandVertex B α i) - one_chip (B.pathVertex β p))
          = -1 :=
      rank_semibreak_sub_vertex_eq_neg_one B _ hEminus hdegEminus _ hvZeroMinus
    have hNormal : bananaNormalForm B 0 0 E = E := by
      rw [bananaNormalForm_eq]
      simp
    refine basePointDrop_mark_eq_zero_of_rank_eq _ _ ?_
    rw [hNormal, hRankV, sub_right_comm, hRankUV]
  · have hOneNonneg : 0 ≤ a - 1 ∨ 0 ≤ b - 1 := by omega
    have hEplus : IsSemibreak (B := B)
        (E + one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β))) := by
      rw [hrVertex]
      exact isSemibreak_add_interior_chip_of_empty B E hE β _ hEmpty
    have hdegPlus :
        deg (E + one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)))
          = deg E + 1 := by
      rw [deg.map_add, deg_one_chip]
    have hmemPlus :
        (E + one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)) :
        CFDiv B.graph) (strandVertex B α i) = 1 := by
      simpa [one_chip, hur] using hmem
    have hRankEq :=
      rank_bananaNormalForm_remove_midpoint_chip_of_ge_neg_one B _ hEplus
        α i hα hi (a - 1) (b - 1) (by omega) (by omega) hOneNonneg
        (by rw [hdegPlus]; omega) (by rw [hdegPlus]; omega)
        (by rw [hdegPlus]; omega) hmemPlus
    refine basePointDrop_mark_eq_zero_of_linear_equiv _ _ ?_ hRankEq
    rw [bananaNormalForm_eq, bananaNormalForm_eq]
    exact linear_equiv_normalForm_sub_both a b
      (endpoint_sum_linearEquiv_path_reflection B β p)

/-- Occupied-strand branch in which the old chip and the reflected marked
point slide to the raw tail endpoint. -/
theorem basePointDrop_bananaNormalForm_sub_occupied_tail_eq_zero
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (p : B.PathPosition β)
    (oldChip : Fin (B.length β - 1))
    (a b : ℤ) (E : CFDiv B.graph)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (hp : B.IsInteriorPosition β p)
    (hE : IsSemibreak B E)
    (huMem : E (strandVertex B α i) = 1)
    (hOld : E (B.interiorVertex β oldChip) = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ))
    (hSum : oldChip.val + 1 + (B.length β - p.val) < B.length β) :
    basePointDrop
      (mark B.graph (strandVertex B α i) (B.pathVertex β p))
      ((bananaNormalForm B a b E - one_chip (B.pathVertex β p) :
        CFDiv B.graph)) = 0 := by
  change 0 < p.val ∧ p.val < B.length β at hp
  have hOldLt : oldChip.val + 1 < B.length β := by
    have := oldChip.isLt
    omega
  have hq : B.IsInteriorPosition β
      (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) := by
    change 0 < oldChip.val + 1 ∧ oldChip.val + 1 < B.length β
    omega
  have hr : B.IsInteriorPosition β
      (⟨B.length β - p.val, by omega⟩ : B.PathPosition β) := by
    change 0 < B.length β - p.val ∧ B.length β - p.val < B.length β
    omega
  have hx : B.IsInteriorPosition β
      (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ :
        B.PathPosition β) := by
    change 0 < oldChip.val + 1 + (B.length β - p.val) ∧
      oldChip.val + 1 + (B.length β - p.val) < B.length β
    omega
  have hqVertex : B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) =
      B.interiorVertex β oldChip := by
    rw [B.pathVertex_eq_interiorVertex β _ hq]
    congr 1
  have hxVertex :
      B.pathVertex β (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β) =
        B.interiorVertex β
          (⟨oldChip.val + 1 + (B.length β - p.val) - 1, by omega⟩ : Fin (B.length β - 1)) := by
    rw [B.pathVertex_eq_interiorVertex β _ hx]
    congr 1
  have hE' : IsSemibreak (B := B)
      (E + one_chip (B.pathVertex β
            (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β)) -
        one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β))) := by
    rw [hqVertex, hxVertex]
    exact isSemibreak_replace_interior_chip_of_eq_one B E hE β oldChip _ hOld
  have hdegE' :
      deg (E + one_chip (B.pathVertex β
              (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β)) -
          one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β))) = deg E := by
    rw [deg.map_sub, deg.map_add, deg_one_chip, deg_one_chip]
    ring
  have huq : strandVertex B α i ≠
      B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) :=
    length_two_midpoint_ne_pathVertex_of_distinct_strand B α β i _ hαβ hα hi hq
  have hux : strandVertex B α i ≠
      B.pathVertex β (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β) :=
    length_two_midpoint_ne_pathVertex_of_distinct_strand B α β i _ hαβ hα hi hx
  have huMem' :
      (E + one_chip (B.pathVertex β
            (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β)) -
          one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) :
        CFDiv B.graph) (strandVertex B α i) = 1 := by
    simpa [one_chip, huq, hux] using huMem
  have hReflect := endpoint_sum_linearEquiv_path_reflection B β p
  have hSlide : linear_equiv B.graph
      (one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) +
        one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)))
      (one_chip (B.coreVertex (B.core.tail β)) +
        one_chip (B.pathVertex β
          (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β))) :=
    path_pair_linearEquiv_tail_sum B β _ _ hq.1 hr.1 hSum
  by_cases htail : B.core.tail β = 0
  · have hSlideL : linear_equiv B.graph
        (one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) +
          one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)))
        (one_chip (leftEndpoint B) +
          one_chip (B.pathVertex β
            (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β))) := by
      rw [htail] at hSlide
      exact hSlide
    have hRankEq :=
      rank_bananaNormalForm_remove_midpoint_chip_of_ge_neg_one B _ hE'
        α i hα hi a (b - 1) (by omega) (by omega) (Or.inl ha)
        (by rw [hdegE']; omega) (by rw [hdegE']; omega)
        (by rw [hdegE']; omega) huMem'
    refine basePointDrop_mark_eq_zero_of_linear_equiv _ _ ?_ hRankEq
    rw [bananaNormalForm_eq, bananaNormalForm_eq]
    exact linear_equiv_normalForm_sub_right a b
      (linear_equiv_pair_of_reflect_slide hReflect hSlideL)
  · have htailOne : B.core.tail β = 1 := by
      rcases fin_two_eq_zero_or_one (B.core.tail β) with h | h
      · exact (htail h).elim
      · exact h
    have hSlideR : linear_equiv B.graph
        (one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) +
          one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)))
        (one_chip (rightEndpoint B) +
          one_chip (B.pathVertex β
            (⟨oldChip.val + 1 + (B.length β - p.val), by omega⟩ : B.PathPosition β))) := by
      rw [htailOne] at hSlide
      exact hSlide
    have hRankEq :=
      rank_bananaNormalForm_remove_midpoint_chip_of_ge_neg_one B _ hE'
        α i hα hi (a - 1) b (by omega) (by omega) (Or.inr hb)
        (by rw [hdegE']; omega) (by rw [hdegE']; omega)
        (by rw [hdegE']; omega) huMem'
    refine basePointDrop_mark_eq_zero_of_linear_equiv _ _ ?_ hRankEq
    rw [bananaNormalForm_eq, bananaNormalForm_eq]
    refine linear_equiv_normalForm_sub_left a b ?_
    exact linear_equiv_pair_of_reflect_slide
      (linear_equiv_endpoint_swap hReflect) hSlideR

/-- Occupied-strand branch in which the old chip and the reflected marked
point slide to the raw head endpoint. -/
theorem basePointDrop_bananaNormalForm_sub_occupied_head_eq_zero
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (p : B.PathPosition β)
    (oldChip : Fin (B.length β - 1))
    (a b : ℤ) (E : CFDiv B.graph)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (hp : B.IsInteriorPosition β p)
    (hE : IsSemibreak B E)
    (huMem : E (strandVertex B α i) = 1)
    (hOld : E (B.interiorVertex β oldChip) = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ))
    (hSum : B.length β < oldChip.val + 1 + (B.length β - p.val)) :
    basePointDrop
      (mark B.graph (strandVertex B α i) (B.pathVertex β p))
      ((bananaNormalForm B a b E - one_chip (B.pathVertex β p) :
        CFDiv B.graph)) = 0 := by
  change 0 < p.val ∧ p.val < B.length β at hp
  have hOldLt : oldChip.val + 1 < B.length β := by
    have := oldChip.isLt
    omega
  have hq : B.IsInteriorPosition β
      (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) := by
    change 0 < oldChip.val + 1 ∧ oldChip.val + 1 < B.length β
    omega
  have hr : B.IsInteriorPosition β
      (⟨B.length β - p.val, by omega⟩ : B.PathPosition β) := by
    change 0 < B.length β - p.val ∧ B.length β - p.val < B.length β
    omega
  have hx : B.IsInteriorPosition β
      (⟨oldChip.val + 1 + (B.length β - p.val) - B.length β, by omega⟩ :
        B.PathPosition β) := by
    change 0 < oldChip.val + 1 + (B.length β - p.val) - B.length β ∧
      oldChip.val + 1 + (B.length β - p.val) - B.length β < B.length β
    omega
  have hqVertex : B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) =
      B.interiorVertex β oldChip := by
    rw [B.pathVertex_eq_interiorVertex β _ hq]
    congr 1
  have hxVertex :
      B.pathVertex β
          (⟨oldChip.val + 1 + (B.length β - p.val) - B.length β, by omega⟩ : B.PathPosition β) =
        B.interiorVertex β
          ⟨oldChip.val + 1 + (B.length β - p.val) - B.length β - 1,
            by omega⟩ := by
    rw [B.pathVertex_eq_interiorVertex β _ hx]
    congr 1
  have hE' : IsSemibreak (B := B)
      (E + one_chip (B.pathVertex β
            ⟨oldChip.val + 1 + (B.length β - p.val) - B.length β,
              by omega⟩) -
        one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β))) := by
    rw [hqVertex, hxVertex]
    exact isSemibreak_replace_interior_chip_of_eq_one B E hE β oldChip _ hOld
  have hdegE' :
      deg (E + one_chip (B.pathVertex β
              ⟨oldChip.val + 1 + (B.length β - p.val) - B.length β,
                by omega⟩) -
          one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β))) = deg E := by
    rw [deg.map_sub, deg.map_add, deg_one_chip, deg_one_chip]
    ring
  have huq : strandVertex B α i ≠
      B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) :=
    length_two_midpoint_ne_pathVertex_of_distinct_strand B α β i _ hαβ hα hi hq
  have hux : strandVertex B α i ≠
      B.pathVertex β
        (⟨oldChip.val + 1 + (B.length β - p.val) - B.length β, by omega⟩ : B.PathPosition β) :=
    length_two_midpoint_ne_pathVertex_of_distinct_strand B α β i _ hαβ hα hi hx
  have huMem' :
      (E + one_chip (B.pathVertex β
            ⟨oldChip.val + 1 + (B.length β - p.val) - B.length β,
              by omega⟩) -
          one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) :
        CFDiv B.graph) (strandVertex B α i) = 1 := by
    simpa [one_chip, huq, hux] using huMem
  have hReflect := endpoint_sum_linearEquiv_path_reflection B β p
  have hSlide : linear_equiv B.graph
      (one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) +
        one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)))
      (one_chip (B.pathVertex β
          (⟨oldChip.val + 1 + (B.length β - p.val) - B.length β, by omega⟩ : B.PathPosition β)) +
        one_chip (B.coreVertex (B.core.head β))) :=
    path_pair_linearEquiv_head_excess B β _ _ hq.2 hr.2 hSum
  by_cases htail : B.core.tail β = 0
  · have hhead : B.core.head β = 1 := head_eq_other_of_tail B β htail
    have hSlideR : linear_equiv B.graph
        (one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) +
          one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)))
        (one_chip (B.pathVertex β
            (⟨oldChip.val + 1 + (B.length β - p.val) - B.length β, by omega⟩ : B.PathPosition β)) +
          one_chip (rightEndpoint B)) := by
      rw [hhead] at hSlide
      exact hSlide
    have hRankEq :=
      rank_bananaNormalForm_remove_midpoint_chip_of_ge_neg_one B _ hE'
        α i hα hi (a - 1) b (by omega) (by omega) (Or.inr hb)
        (by rw [hdegE']; omega) (by rw [hdegE']; omega)
        (by rw [hdegE']; omega) huMem'
    refine basePointDrop_mark_eq_zero_of_linear_equiv _ _ ?_ hRankEq
    rw [bananaNormalForm_eq, bananaNormalForm_eq]
    refine linear_equiv_normalForm_sub_left a b ?_
    exact linear_equiv_pair_of_reflect_slide'
      (linear_equiv_endpoint_swap hReflect) hSlideR
  · have htailOne : B.core.tail β = 1 := by
      rcases fin_two_eq_zero_or_one (B.core.tail β) with h | h
      · exact (htail h).elim
      · exact h
    have hhead : B.core.head β = 0 := by
      rcases fin_two_eq_zero_or_one (B.core.head β) with h | h
      · exact h
      · exfalso
        apply B.core_loopless β
        simp [htailOne, h]
    have hSlideL : linear_equiv B.graph
        (one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) +
          one_chip (B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β)))
        (one_chip (B.pathVertex β
            (⟨oldChip.val + 1 + (B.length β - p.val) - B.length β, by omega⟩ : B.PathPosition β)) +
          one_chip (leftEndpoint B)) := by
      rw [hhead] at hSlide
      exact hSlide
    have hRankEq :=
      rank_bananaNormalForm_remove_midpoint_chip_of_ge_neg_one B _ hE'
        α i hα hi a (b - 1) (by omega) (by omega) (Or.inl ha)
        (by rw [hdegE']; omega) (by rw [hdegE']; omega)
        (by rw [hdegE']; omega) huMem'
    refine basePointDrop_mark_eq_zero_of_linear_equiv _ _ ?_ hRankEq
    rw [bananaNormalForm_eq, bananaNormalForm_eq]
    exact linear_equiv_normalForm_sub_right a b
      (linear_equiv_pair_of_reflect_slide' hReflect hSlideL)

/-- Occupied-strand boundary branch: the old chip and the reflected marked
point form a reflected pair, so both endpoint contributions cancel and the
old chip is simply removed from the semibreak part. -/
theorem basePointDrop_bananaNormalForm_sub_occupied_endpoint_pair_eq_zero
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (p : B.PathPosition β)
    (oldChip : Fin (B.length β - 1))
    (a b : ℤ) (E : CFDiv B.graph)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (hp : B.IsInteriorPosition β p)
    (hE : IsSemibreak B E)
    (huMem : E (strandVertex B α i) = 1)
    (hOld : E (B.interiorVertex β oldChip) = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ))
    (hSum : oldChip.val + 1 + (B.length β - p.val) = B.length β) :
    basePointDrop
      (mark B.graph (strandVertex B α i) (B.pathVertex β p))
      ((bananaNormalForm B a b E - one_chip (B.pathVertex β p) :
        CFDiv B.graph)) = 0 := by
  change 0 < p.val ∧ p.val < B.length β at hp
  have hOldLt : oldChip.val + 1 < B.length β := by
    have := oldChip.isLt
    omega
  have hq : B.IsInteriorPosition β
      (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) := by
    change 0 < oldChip.val + 1 ∧ oldChip.val + 1 < B.length β
    omega
  have hqVertex : B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) =
      B.interiorVertex β oldChip := by
    rw [B.pathVertex_eq_interiorVertex β _ hq]
    congr 1
  have hE' : IsSemibreak (B := B)
      (E - one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β))) := by
    rw [hqVertex]
    exact isSemibreak_remove_interior_chip_of_eq_one B E hE β oldChip hOld
  have hdegE' :
      deg (E - one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)))
        = deg E - 1 := by
    rw [deg.map_sub, deg_one_chip]
  have huq : strandVertex B α i ≠
      B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β) :=
    length_two_midpoint_ne_pathVertex_of_distinct_strand B α β i _ hαβ hα hi hq
  have huMem' :
      (E - one_chip (B.pathVertex β (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)) :
        CFDiv B.graph) (strandVertex B α i) = 1 := by
    simpa [one_chip, huq] using huMem
  have hReflect := endpoint_sum_linearEquiv_path_reflection B β p
  have hposEq : B.pathVertex β (⟨B.length β - (oldChip.val + 1), by omega⟩ : B.PathPosition β) =
      B.pathVertex β (⟨B.length β - p.val, by omega⟩ : B.PathPosition β) := by
    congr 1
    apply Fin.ext
    show B.length β - (oldChip.val + 1) = B.length β - p.val
    omega
  have hPair := endpoint_sum_linearEquiv_path_reflection B β
    (⟨oldChip.val + 1, by omega⟩ : B.PathPosition β)
  rw [hposEq] at hPair
  have hRankEq :=
    rank_bananaNormalForm_remove_midpoint_chip_of_ge_neg_one B _ hE'
      α i hα hi a b (by omega) (by omega) (Or.inl ha)
      (by rw [hdegE']; omega) (by rw [hdegE']; omega)
      (by rw [hdegE']; omega) huMem'
  refine basePointDrop_mark_eq_zero_of_linear_equiv _ _ ?_ hRankEq
  rw [bananaNormalForm_eq, bananaNormalForm_eq]
  exact linear_equiv_normalForm_sub_pair a b
    (linear_equiv_of_reflect_pair hReflect hPair)

/-- The marked rank second difference is nonnegative for every low-degree
banana normal form in the length-two cross configuration. -/
theorem rankDelta_bananaNormalForm_lengthTwoCross_nonneg
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (p : B.PathPosition β)
    (a b : ℤ) (E : CFDiv B.graph)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (hp : B.IsInteriorPosition β p)
    (hE : IsSemibreak B E)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLowDeg : a + b + deg E ≤ (g : ℤ)) :
    0 ≤ rankDelta
      (mark B.graph (strandVertex B α i) (B.pathVertex β p))
      (bananaNormalForm B a b E) := by
  rw [rankDelta_mark_eq_basePointDrop_sub]
  rcases semibreak_midpoint_eq_zero_or_one B E hE α i hα hi with
    hzero | hmem
  · have hDrop :
        basePointDrop (mark B.graph (strandVertex B α i) (B.pathVertex β p))
          (bananaNormalForm B a b E) = 1 :=
      basePointDrop_bananaNormalForm_eq_one_of_midpoint_eq_zero
        B α i (B.pathVertex β p) a b E hα hi hE hzero ha hb hLowDeg
    have hDropSub :=
      basePointDrop_mark_le_one (strandVertex B α i) (B.pathVertex β p)
        (bananaNormalForm B a b E - one_chip (B.pathVertex β p))
    omega
  · have hDrop :
        basePointDrop (mark B.graph (strandVertex B α i) (B.pathVertex β p))
          (bananaNormalForm B a b E) = 0 :=
      basePointDrop_bananaNormalForm_eq_zero_of_midpoint_mem
        B α i (B.pathVertex β p) a b E hα hi hE hmem ha hb hLowDeg
    rcases hE with ⟨chips, hchips⟩
    cases hβ : chips β with
    | none =>
        have hEmpty : ∀ chip : Fin (B.length β - 1),
            E (B.interiorVertex β chip) = 0 := by
          intro chip
          rw [hchips]
          simp [semibreakDivisor_interiorVertex, hβ]
        have hDropSub :=
          basePointDrop_bananaNormalForm_sub_empty_strand_eq_zero
            B α β i p a b E hαβ hα hi hp ⟨chips, hchips⟩ hmem
            hEmpty ha hb hLowDeg
        omega
    | some oldChip =>
        have hOld : E (B.interiorVertex β oldChip) = 1 := by
          rw [hchips]
          simp [semibreakDivisor_interiorVertex, hβ]
        rcases lt_trichotomy
            (oldChip.val + 1 + (B.length β - p.val)) (B.length β) with
          hlt | heq | hgt
        · have hDropSub :=
            basePointDrop_bananaNormalForm_sub_occupied_tail_eq_zero
              B α β i p oldChip a b E hαβ hα hi hp ⟨chips, hchips⟩
              hmem hOld ha hb hLowDeg hlt
          omega
        · have hDropSub :=
            basePointDrop_bananaNormalForm_sub_occupied_endpoint_pair_eq_zero
              B α β i p oldChip a b E hαβ hα hi hp ⟨chips, hchips⟩
              hmem hOld ha hb hLowDeg heq
          omega
        · have hDropSub :=
            basePointDrop_bananaNormalForm_sub_occupied_head_eq_zero
              B α β i p oldChip a b E hαβ hα hi hp ⟨chips, hchips⟩
              hmem hOld ha hb hLowDeg hgt
          omega

/-- Every divisor has nonnegative marked rank second difference when one mark
is a length-two midpoint and the other is an interior point of a distinct
strand (in raw path coordinates). -/
theorem rankDelta_lengthTwoCross_path_nonneg
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (p : B.PathPosition β)
    (hαβ : α ≠ β) (hα : B.length α = 2) (hi : i.val = 1)
    (hp : B.IsInteriorPosition β p) (D : CFDiv B.graph) :
    0 ≤ rankDelta
      (mark B.graph (strandVertex B α i) (B.pathVertex β p)) D := by
  by_contra hNot
  have hNeg : rankDelta
      (mark B.graph (strandVertex B α i) (B.pathVertex β p)) D < 0 := by
    omega
  obtain ⟨Dlow, hDlowDeg, hDlowNeg⟩ :
      ∃ Dlow : CFDiv B.graph,
        deg Dlow ≤ (g : ℤ) ∧
          rankDelta (mark B.graph (strandVertex B α i)
            (B.pathVertex β p)) Dlow < 0 := by
    by_cases hDeg : deg D ≤ (g : ℤ)
    · exact ⟨D, hDeg, hNeg⟩
    · refine ⟨canonical_divisor B.graph + one_chip (strandVertex B α i) +
        one_chip (B.pathVertex β p) - D, ?_, ?_⟩
      · rw [deg_canonical_dual B (strandVertex B α i) (B.pathVertex β p) D]
        omega
      · rw [rankDelta_mark_canonical_dual (strandVertex B α i)
          (B.pathVertex β p) (graph_connected B) D] at hNeg
        exact hNeg
  obtain ⟨a, b, E, hE, hb, hbdeg, hLinear⟩ :=
    exists_linearly_equiv_bananaNormalForm B Dlow
  have hNormalDeg : a + b + deg E ≤ (g : ℤ) := by
    have hDegEq := linear_equiv_preserves_deg B.graph Dlow
      (bananaNormalForm B a b E) hLinear
    rw [degree_bananaNormalForm] at hDegEq
    omega
  have hNegNormal : rankDelta
      (mark B.graph (strandVertex B α i) (B.pathVertex β p))
      (bananaNormalForm B a b E) < 0 := by
    rw [← rankDelta_mark_eq_of_linearEquiv (strandVertex B α i)
      (B.pathVertex β p) hLinear]
    exact hDlowNeg
  have hRankNormal : 0 ≤ rank B.graph (bananaNormalForm B a b E) := by
    obtain ⟨-, -, hStep⟩ :=
      (rankDelta_mark_neg_iff_rank_pattern (strandVertex B α i)
        (B.pathVertex β p) (bananaNormalForm B a b E)).mp hNegNormal
    have hLower := rank_geq_neg_one B.graph
      (bananaNormalForm B a b E - one_chip (strandVertex B α i) -
        one_chip (B.pathVertex β p))
    omega
  have ha : 0 ≤ a := by
    by_contra haNot
    have hRankNeg : rank B.graph (bananaNormalForm B a b E) = -1 :=
      (rank_bananaNormalForm_neg_iff B a b E hE hb hbdeg).2 (by omega)
    omega
  have hNonneg := rankDelta_bananaNormalForm_lengthTwoCross_nonneg
    B α β i p a b E hαβ hα hi hp hE ha hb hNormalDeg
  omega

/-- TeX label: `thm-NSMForBanana` (Theorem 3.9), corrected length-two
exception.

The extra all-submodular family identified by the external computational
audit: a midpoint on a length-two strand may be paired with any strictly
interior point on a different strand.  This is a *correction* to Theorem 3.9,
whose published proof handles the distinct-strand case by the divisor
`D = v_{α,1} + v_{α,i} + v_{β,n_β-1}` and asserts
`D ∼ v_{α,0} + v_{α,i+1} + v_{β,n_β-1}` is `v_{α,n_α}`-reduced of rank `0`.
When `n_α = 2` and `i = 1` this fails: `v_{α,i+1} = v_{α,n_α}` is
multivalent, so `D ∼ v_{α,0} + v_{α,n_α} + v_{β,n_β-1}` has rank `1` by
`lem:g12`.

The all-divisors rank argument is supplied by
`rankDelta_lengthTwoCross_path_nonneg`: after canonical duality and banana
normal-form reduction, deleting the second mark is normalized by one of the
empty, tail-sum, head-excess, or reflected-pair semibreak calculations. -/
theorem NSMForBananaLengthTwoCrossException :
  ∀ (g : ℕ) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β),
    3 ≤ g → α ≠ β → B.length α = 2 → i.val = 1 →
    B.IsInteriorPosition β j →
    AllSubmodular (mark B.graph (strandVertex B α i) (strandVertex B β j)) := by
  intro g B α β i j _hg hαβ hα hi hj
  change 0 < j.val ∧ j.val < B.length β at hj
  rw [allSubmodular_iff_rankDelta_nonneg]
  intro D
  -- `strandVertex` stores a strand in either orientation; move the second mark
  -- to its raw path coordinate before applying the path-coordinate theorem.
  let q : B.PathPosition β := normalizedPathPosition B β j
  have hq : B.IsInteriorPosition β q := normalizedPathPosition_isInterior B β j hj
  have hv : strandVertex B β j = B.pathVertex β q :=
    strandVertex_eq_pathVertex_normalized B β j
  rw [hv]
  exact rankDelta_lengthTwoCross_path_nonneg B α β i q hαβ hα hi hq D

end Bananas
