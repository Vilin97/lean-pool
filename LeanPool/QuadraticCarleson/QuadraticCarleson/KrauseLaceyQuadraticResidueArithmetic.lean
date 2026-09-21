/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection

/-!
# Arithmetic for the seven separated frequency classes

The direct quadratic proof separates integer output scales into seven
residue classes. In each class, imposing a lower scale cutoff selects an
ordinary suffix of the natural-number index. This file records that exact
finite identity independently of the analytic estimates.
-/

namespace QuadraticCarleson.KrauseLaceyQuadraticResidueArithmetic

open KrauseLaceyQuadraticSmoothProjection


/-- The first index in residue class `r mod 7` whose scale is at least `q`.
The numerator is nonnegative because `r ≤ 6`. -/
def firstResidueIndex (r : Fin 7) (q : ℕ) : ℕ :=
  (q + 6 - (r : ℕ)) / 7

theorem firstResidueIndex_le_iff
    (r : Fin 7) (q n : ℕ) :
    firstResidueIndex r q ≤ n ↔
      (q : ℤ) ≤ residueScale r n := by
  unfold firstResidueIndex residueScale
  have hr : (r : ℕ) ≤ 6 := Nat.le_pred_of_lt r.isLt
  omega

/-- A lower scale cutoff inside one residue class is literally a finite
interval of natural indices. -/
theorem range_filter_residueScale_ge
    (r : Fin 7) (q N : ℕ) :
    (Finset.range N).filter (fun n ↦ (q : ℤ) ≤ residueScale r n) =
      Finset.Ico (firstResidueIndex r q) N := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  rw [← firstResidueIndex_le_iff]
  tauto

/-- Hence every truncated sum in a fixed residue class is one of the
ordinary suffixes used by the annular maximal-tail theorem. -/
theorem sum_filter_residueScale_ge_eq_Ico
    {E : Type*} [AddCommMonoid E] (u : ℕ → E)
    (r : Fin 7) (q N : ℕ) :
    ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u n =
      ∑ n ∈ Finset.Ico (firstResidueIndex r q) N, u n := by
  rw [range_filter_residueScale_ge]

/-- The cutoff sum is therefore represented by a tail whose starting index
always lies in `0, ..., N`, including the empty-tail case. -/
theorem sum_filter_residueScale_ge_eq_finitePieceTail
    (u : ℕ → ℝ → ℂ) (r : Fin 7) (q N : ℕ) (x : ℝ) :
    ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u n x =
      KrauseLaceyQuadraticAnnularTail.finitePieceTail N u
        (min (firstResidueIndex r q) N) x := by
  rw [KrauseLaceyQuadraticAnnularTail.finitePieceTail_eq_sum_Ico
    (min_le_right _ _)]
  rw [sum_filter_residueScale_ge_eq_Ico]
  by_cases h : firstResidueIndex r q ≤ N
  · rw [min_eq_left h]
  · have hN : N ≤ firstResidueIndex r q := Nat.le_of_not_ge h
    rw [min_eq_right hN]
    simp only [Finset.Ico_eq_empty (not_lt_of_ge hN), Finset.sum_empty,
      Finset.Ico_self]

/-- Each residue-class cutoff is pointwise bounded by the corresponding
finite annular tail maximum. -/
theorem enorm_sum_filter_residueScale_ge_le_tailMax
    (u : ℕ → ℝ → ℂ) (r : Fin 7) (q N : ℕ) (x : ℝ) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u n x‖ₑ ≤
      KrauseLaceyQuadraticAnnularTail.finitePieceTailMax N u x := by
  rw [sum_filter_residueScale_ge_eq_finitePieceTail]
  unfold KrauseLaceyQuadraticAnnularTail.finitePieceTailMax
  exact Finset.le_sup
    (s := Finset.range (N + 1))
    (f := fun n ↦ ‖KrauseLaceyQuadraticAnnularTail.finitePieceTail N u n x‖ₑ)
    (by
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (min_le_right _ _))


end QuadraticCarleson.KrauseLaceyQuadraticResidueArithmetic
