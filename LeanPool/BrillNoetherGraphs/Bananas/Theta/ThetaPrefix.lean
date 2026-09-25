/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrand

/-! # Theta Prefix -/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec
open Utilities.SegmentReflection


private theorem linear_equiv_add {G : CFGraph} {A B C D : CFDiv G}
    (hA : linearEquiv G A C) (hB : linearEquiv G B D) :
    linearEquiv G (A + B) (C + D) := by
  unfold linearEquiv at hA hB ⊢
  convert (principalDivisors G).add_mem hA hB using 1 ; abel

private theorem raw_endpoint_pair_linearEquiv
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (i k : B.PathPosition α)
    (hsum : i.val + k.val = B.length α) :
    linearEquiv B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex α k))
      (oneChip (B.pathVertex α ⟨0, by omega⟩) +
        oneChip (B.pathVertex α ⟨B.length α, by omega⟩)) := by
  have hk : k.val = B.length α - i.val := by omega
  have hkm : B.pathVertex α k =
      B.pathVertex α (SegmentReflection.symmetricPosition B α i) := by
    rw [B.pathVertex_eq_iff_val_eq]
    simp [SegmentReflection.symmetricPosition]
    omega
  have hScript := SegmentReflection.prin_script_eq_reflectionDivisor B α i
  unfold linearEquiv
  apply (principal_iff_eq_prin B.graph _).mpr
  refine ⟨-SegmentReflection.script B α i, ?_⟩
  rw [map_neg, hScript, ← hkm, B.pathVertex_zero, B.pathVertex_length]
  norm_num
  abel

theorem raw_strand_prefix_linearEquiv
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (n : ℕ)
    (hn : n ≤ B.length α) :
    linearEquiv B.graph
      ((n : ℤ) • (oneChip (B.pathVertex α ⟨1, by
        have := B.length_pos α; omega⟩) - oneChip (B.pathVertex α 0)))
      (oneChip (B.pathVertex α ⟨n, by omega⟩) - oneChip (B.pathVertex α 0)) := by
  have aux : ∀ m : ℕ, ∀ hm : m ≤ B.length α,
      linearEquiv B.graph
        ((m : ℤ) • (oneChip (B.pathVertex α ⟨1, by
          have := B.length_pos α; omega⟩) - oneChip (B.pathVertex α 0)))
        (oneChip (B.pathVertex α ⟨m, by omega⟩) - oneChip (B.pathVertex α 0)) := by
    intro m
    induction m with
    | zero => intro; simp [linearEquiv]
    | succ m ih =>
      intro hm
      by_cases hOne : m = 0
      · subst m
        unfold linearEquiv
        simp [sub_eq_add_neg]
      · by_cases hLast : m + 1 = B.length α
        · have hnPos : 0 < m := by omega
          have hPair := raw_endpoint_pair_linearEquiv B α
            ⟨1, by have := B.length_pos α; omega⟩
            ⟨m, by omega⟩ (by simpa [Nat.add_comm] using hLast)
          have hStep : linearEquiv B.graph
              (oneChip (B.pathVertex α ⟨1, by omega⟩) -
                oneChip (B.pathVertex α ⟨0, by omega⟩))
              (oneChip (B.pathVertex α ⟨B.length α, by omega⟩) -
                oneChip (B.pathVertex α ⟨m, by omega⟩)) := by
            unfold linearEquiv at hPair ⊢
            convert hPair using 1 ;
              simp [B.pathVertex_length,
                sub_eq_add_neg] ; abel
          have hAdd := linear_equiv_add (ih (by omega)) hStep
          unfold linearEquiv at hAdd ⊢
          convert hAdd using 1 ;
            simp [← hLast, sub_eq_add_neg, add_smul,
              Nat.cast_add] ; abel
        · have hsum : 1 + m < B.length α := by omega
          have hmPos : 0 < m := by omega
          have hmLt : m < B.length α + 1 := by omega
          have hSlide := path_pair_linearEquiv_tail_sum B α
            ⟨1, by have := B.length_pos α; omega⟩
            ⟨m, hmLt⟩ (by norm_num) (by exact hmPos) hsum
          have hStep : linearEquiv B.graph
              (oneChip (B.pathVertex α ⟨1, by omega⟩) -
                oneChip (B.pathVertex α ⟨0, by omega⟩))
              (oneChip (B.pathVertex α ⟨1 + m, by omega⟩) -
                oneChip (B.pathVertex α ⟨m, by omega⟩)) := by
            unfold linearEquiv at hSlide ⊢
            convert hSlide using 1 ; abel
          have hAdd := linear_equiv_add (ih (by omega)) hStep
          unfold linearEquiv at hAdd ⊢
          convert hAdd using 1 ;
            simp [sub_eq_add_neg, add_smul, Nat.cast_add] ; abel_nf
  exact aux n hn

/-! Paper source: the prefix firing calculation used in `eq:multDiffMarkedPts`.
This adapter is currently proved for slots stored in the left-to-right
orientation.  The reversed-orientation adapter is a separate endpoint
reflection calculation, not a definitional simplification. -/
theorem strand_prefix_linearEquiv_of_tail_zero
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (p : B.PathPosition α)
    (hTail : B.core.tail α = 0) :
    linearEquiv B.graph
      ((p.val : ℤ) •
        (oneChip (strandVertex B α ⟨1, by
          have := B.length_pos α; omega⟩) -
          oneChip (leftEndpoint B)))
      (oneChip (strandVertex B α p) - oneChip (leftEndpoint B)) := by
  have hz0 : B.pathVertex α (0 : B.PathPosition α) =
      B.coreVertex 0 := by simpa [hTail] using B.pathVertex_zero α
  have hRaw := raw_strand_prefix_linearEquiv B α p.val (by omega)
  rw [hz0] at hRaw
  -- Rewrite the two `strandVertex`s away one at a time rather than letting
  -- `simp` normalize whole divisors: on a concrete banana that makes the
  -- unifier compare divisors pointwise (see `LengthTwoCrossMonotonicity`).
  have hstrand : ∀ i : B.PathPosition α,
      strandVertex B α i = B.pathVertex α i := by
    intro i
    unfold strandVertex
    rw [ite_eq_left hTail]
  simp only [hstrand, leftEndpoint]
  exact hRaw

private theorem raw_strand_prefix_from_length_linearEquiv
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (m : ℕ)
    (hm : m ≤ B.length α) :
    linearEquiv B.graph
      ((m : ℤ) •
        (oneChip (B.pathVertex α ⟨B.length α - 1, by
          have := B.length_pos α; omega⟩) -
          oneChip (B.pathVertex α ⟨B.length α, by omega⟩)))
      (oneChip (B.pathVertex α ⟨B.length α - m, by omega⟩) -
        oneChip (B.pathVertex α ⟨B.length α, by omega⟩)) := by
  have aux : ∀ r : ℕ, ∀ hr : r ≤ B.length α,
      linearEquiv B.graph
        ((r : ℤ) •
          (oneChip (B.pathVertex α ⟨B.length α - 1, by
            have := B.length_pos α; omega⟩) -
            oneChip (B.pathVertex α ⟨B.length α, by omega⟩)))
        (oneChip (B.pathVertex α ⟨B.length α - r, by omega⟩) -
          oneChip (B.pathVertex α ⟨B.length α, by omega⟩)) := by
    intro r
    induction r with
    | zero => intro; simp [linearEquiv]
    | succ r ih =>
      intro hr
      by_cases hOne : r = 0
      · subst r
        unfold linearEquiv
        simp [sub_eq_add_neg]
      · by_cases hLast : r + 1 = B.length α
        · have hPair := raw_endpoint_pair_linearEquiv B α
            ⟨B.length α - 1, by have := B.length_pos α; omega⟩
            ⟨1, by have := B.length_pos α; omega⟩
              (by change (B.length α - 1) + 1 = B.length α; omega)
          have hStep : linearEquiv B.graph
              (oneChip (B.pathVertex α ⟨B.length α - 1, by omega⟩) -
                oneChip (B.pathVertex α ⟨B.length α, by omega⟩))
              (oneChip (B.pathVertex α ⟨0, by omega⟩) -
                oneChip (B.pathVertex α ⟨1, by omega⟩)) := by
            unfold linearEquiv at hPair ⊢
            convert hPair using 1 ;
              simp [B.pathVertex_length,
                sub_eq_add_neg] ; abel
          have hAdd := linear_equiv_add (ih (by omega)) hStep
          unfold linearEquiv at hAdd ⊢
          convert hAdd using 1 ;
            simp [← hLast, sub_eq_add_neg, add_smul,
              Nat.cast_add] ; abel
        · have hsum : B.length α < (B.length α - 1) +
              (B.length α - r) := by omega
          have hrpos : 0 < r := by omega
          have hSlide := path_pair_linearEquiv_head_excess B α
            ⟨B.length α - 1, by omega⟩
            ⟨B.length α - r, by omega⟩
              (by show B.length α - 1 < B.length α; omega)
              (by show B.length α - r < B.length α; omega) hsum
          have hStep : linearEquiv B.graph
              (oneChip (B.pathVertex α ⟨B.length α - 1, by omega⟩) -
                oneChip (B.pathVertex α ⟨B.length α, by omega⟩))
              (oneChip (B.pathVertex α ⟨B.length α - r - 1, by omega⟩) -
                oneChip (B.pathVertex α ⟨B.length α - r, by omega⟩)) := by
            unfold linearEquiv at hSlide ⊢
            have hidx : B.length α - 1 + (B.length α - r) - B.length α =
                B.length α - r - 1 := by omega
            convert hSlide using 1 ; simp [hidx] ; abel_nf
          have hAdd := linear_equiv_add (ih (by omega)) hStep
          unfold linearEquiv at hAdd ⊢
          have hidx : B.length α - (r + 1) = B.length α - r - 1 := by omega
          convert hAdd using 1 ;
            simp [hidx, sub_eq_add_neg, add_smul,
              Nat.cast_add] ; abel
  exact aux m hm

theorem strand_prefix_linearEquiv_of_tail_nonzero
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (p : B.PathPosition α)
    (hTail : B.core.tail α ≠ 0) :
    linearEquiv B.graph
      ((p.val : ℤ) •
        (oneChip (strandVertex B α ⟨1, by
          have := B.length_pos α; omega⟩) -
          oneChip (leftEndpoint B)))
      (oneChip (strandVertex B α p) - oneChip (leftEndpoint B)) := by
  unfold strandVertex
  have hTail' : B.core.tail α = 1 := by
    apply Fin.ext
    have hlt := (B.core.tail α).isLt
    have hne : (B.core.tail α).val ≠ 0 := by
      intro hzero
      apply hTail
      exact Fin.ext hzero
    omega
  have hHead : B.core.head α = 0 := by
    apply Fin.ext
    have hlt := (B.core.head α).isLt
    have hne : (B.core.head α).val ≠ 1 := by
      intro hone
      apply B.core_loopless α
      simpa [hTail'] using Fin.ext hone.symm
    omega
  have hRaw := raw_strand_prefix_from_length_linearEquiv B α p.val (by omega)
  have hzL : B.pathVertex α (⟨B.length α, by omega⟩ : B.PathPosition α) =
      B.coreVertex 0 := by simp [hHead]
  rw [hzL] at hRaw
  -- As above: finish by `exact` on syntactically aligned terms instead of an
  -- AC-normalizing `simp` over banana divisors.
  simp only [hTail', leftEndpoint]
  exact hRaw

/-! Full normalized form of the one-strand prefix identity used by
`eq:multDiffMarkedPts`; the two cases account for the subdivision model's
arbitrary storage orientation. -/
/- TeX label: `eq:multDiffMarkedPts` (prefix firing identity). -/
theorem strand_prefix_linearEquiv
    {g : ℕ} (B : Banana g) (α : Fin (g + 1)) (p : B.PathPosition α) :
    linearEquiv B.graph
      ((p.val : ℤ) •
        (oneChip (strandVertex B α ⟨1, by
          have := B.length_pos α; omega⟩) -
          oneChip (leftEndpoint B)))
      (oneChip (strandVertex B α p) - oneChip (leftEndpoint B)) := by
  by_cases hTail : B.core.tail α = 0
  · exact strand_prefix_linearEquiv_of_tail_zero B α p hTail
  · exact strand_prefix_linearEquiv_of_tail_nonzero B α p hTail

end Bananas
