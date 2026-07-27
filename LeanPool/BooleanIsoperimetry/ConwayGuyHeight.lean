/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.BooleanIsoperimetry.ConwayGuyCoherentGap
import Mathlib.Tactic.Linarith

/-!
# The Conway--Guy triangular-block identity

This file derives the height identity used by every Conway--Guy principal
relation directly from the published difference recurrence.
-/

open scoped BigOperators

namespace BooleanIsoperimetry.CoherentGap

lemma guide_lt_dimension {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    guide dimension < dimension := by
  have hpositive := guide_pos hdimension
  have hlower := guide_lower hdimension
  have htriangular := self_le_triangular (guide dimension - 1)
  omega

lemma guide_at_triangular_end (width : ℕ) :
    guide (triangular width + 1) = width := by
  unfold guide
  apply Nat.find_eq_iff (guideWitness (triangular width + 1)) |>.mpr
  constructor
  · omega
  · intro smaller hsmaller
    have hstrict := triangular_strictMono hsmaller
    omega

lemma guide_eq_iff {dimension width : ℕ} (hwidth : 0 < width) :
    guide dimension = width ↔
      triangular (width - 1) + 2 ≤ dimension ∧
        dimension ≤ triangular width + 1 := by
  unfold guide
  rw [Nat.find_eq_iff]
  constructor
  · intro ⟨hupper, hminimal⟩
    constructor
    · by_contra hnot
      have hsmall : dimension - 1 ≤ triangular (width - 1) := by omega
      exact hminimal (width - 1) (by omega) hsmall
    · omega
  · intro ⟨hlower, hupper⟩
    constructor
    · omega
    · intro smaller hsmaller
      have hle : smaller ≤ width - 1 := by omega
      have htriangular := triangular_mono hle
      omega

/-- The left-hand residual of the Conway--Guy block recurrence. -/
noncomputable def residual (width dimension : ℕ) : ℤ :=
  conwayGuyHeight dimension -
    ∑ index : Fin width,
      conwayGuyHeight (dimension - index.val - 1)

lemma conwayGuyDifference_succ (index : ℕ) :
    conwayGuyDifference (index + 1) =
      ∑ offset ∈ Finset.range (guide (index + 2)),
        conwayGuyDifference (index - offset) := by
  simp [conwayGuyDifference, difference]

lemma residual_succ_eq {width dimension : ℕ}
    (hdimension : 0 < dimension)
    (hwidth : width ≤ dimension)
    (hguide : guide (dimension + 1) = width) :
    residual width (dimension + 1) = residual width dimension := by
  have hheight :
      ∀ index : Fin width,
        conwayGuyHeight (dimension + 1 - index.val - 1) =
          conwayGuyHeight (dimension - index.val - 1) +
            conwayGuyDifference (dimension - index.val - 1) := by
    intro index
    have hindex : index.val < dimension := index.isLt.trans_le hwidth
    have hsucc :
        dimension + 1 - index.val - 1 =
          (dimension - index.val - 1) + 1 := by
      omega
    rw [hsucc, conwayGuyHeight_succ]
  rw [residual, residual, conwayGuyHeight_succ]
  simp_rw [hheight]
  rw [Finset.sum_add_distrib]
  have hdifference :
      conwayGuyDifference dimension =
        ∑ index : Fin width,
          (conwayGuyDifference (dimension - index.val - 1) : ℤ) := by
    obtain ⟨previous, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (by omega : dimension ≠ 0)
    rw [conwayGuyDifference_succ, hguide]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro index hindex
    have hargument :
        previous.succ - index.val - 1 = previous - index.val := by
      omega
    rw [hargument]
  rw [hdifference]
  ring

lemma reverse_difference_sum (dimension : ℕ) :
    ∀ width : ℕ, width ≤ dimension →
      (∑ index : Fin width,
          (conwayGuyDifference (dimension - index.val - 1) : ℤ)) =
        conwayGuyHeight dimension -
          conwayGuyHeight (dimension - width)
  | 0, _ => by simp
  | width + 1, hwidth => by
      have hdimension : 0 < dimension := by omega
      obtain ⟨previous, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (by omega : dimension ≠ 0)
      rw [Fin.sum_univ_succ]
      have inductionHypothesis :=
        reverse_difference_sum previous width (by omega)
      have hargument :
          ∀ index : Fin width,
            previous.succ - index.succ.val - 1 =
              previous - index.val - 1 := by
        intro index
        change previous + 1 - (index.val + 1) - 1 =
          previous - index.val - 1
        omega
      simp_rw [hargument]
      rw [inductionHypothesis, conwayGuyHeight_succ]
      have htail :
          previous.succ - (width + 1) = previous - width := by
        omega
      rw [htail]
      have hzero :
          previous.succ - (0 : Fin (width + 1)).val - 1 = previous := by
        simp
      rw [hzero]
      ring

lemma conwayGuyDifference_eq_height_window (dimension : ℕ)
    (hdimension : 0 < dimension) :
    (conwayGuyDifference dimension : ℤ) =
      conwayGuyHeight dimension -
        conwayGuyHeight (dimension - guide (dimension + 1)) := by
  obtain ⟨previous, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : dimension ≠ 0)
  rw [conwayGuyDifference_succ]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range]
  have hwindow :=
    reverse_difference_sum previous.succ (guide (previous.succ + 1))
      (guide_lt_dimension (dimension := previous.succ + 1) (by omega) |>
        fun h => by omega)
  have hargument :
      ∀ index : Fin (guide (previous.succ + 1)),
        previous - index.val =
          previous.succ - index.val - 1 := by
    intro index
    omega
  simp_rw [hargument]
  exact hwindow

lemma residual_succ_width (width dimension : ℕ) :
    residual (width + 1) (dimension + 1) =
      residual width dimension +
        conwayGuyDifference dimension -
          conwayGuyHeight dimension := by
  rw [residual, residual, conwayGuyHeight_succ, Fin.sum_univ_succ]
  have hargument :
      ∀ index : Fin width,
        dimension + 1 - index.succ.val - 1 =
          dimension - index.val - 1 := by
    intro index
    change dimension + 1 - (index.val + 1) - 1 =
      dimension - index.val - 1
    omega
  simp_rw [hargument]
  have hzero :
      dimension + 1 - (0 : Fin (width + 1)).val - 1 = dimension := by
    simp
  rw [hzero]
  ring

lemma residual_eq_block_start {width dimension : ℕ}
    (hwidth : 0 < width)
    (hguide : guide dimension = width) :
    residual width dimension =
      residual width (triangular (width - 1) + 2) := by
  obtain ⟨hlower, hupper⟩ := (guide_eq_iff hwidth).mp hguide
  induction dimension, hlower using Nat.le_induction with
  | base => rfl
  | succ dimension hbase inductionHypothesis =>
      have hnextGuide : guide (dimension + 1) = width :=
        (guide_eq_iff hwidth).mpr ⟨by omega, by omega⟩
      have htriangular := self_le_triangular (width - 1)
      have hwidthLe : width ≤ dimension := by omega
      have hcurrentGuide : guide dimension = width :=
        (guide_eq_iff hwidth).mpr ⟨hbase, by omega⟩
      rw [residual_succ_eq (by omega) hwidthLe hnextGuide,
        inductionHypothesis hcurrentGuide (by omega)]

lemma residual_next_block_start (previous : ℕ) :
    residual (previous + 2) (triangular (previous + 1) + 2) =
      residual (previous + 1) (triangular (previous + 1) + 1) -
        conwayGuyHeight (triangular previous) := by
  have htriangular :
      triangular (previous + 1) = triangular previous + previous + 1 := by
    rfl
  have hnextGuide :
      guide (triangular (previous + 1) + 2) = previous + 2 := by
    apply (guide_eq_iff (by omega)).mpr
    constructor
    · have hpred :
          previous + 2 - 1 = previous + 1 := by omega
      rw [hpred]
    · have hnextTriangular :
          triangular (previous + 2) =
            triangular (previous + 1) + previous + 2 := by
          change triangular ((previous + 1) + 1) =
            triangular (previous + 1) + previous + 2
          rw [triangular]
          omega
      rw [hnextTriangular]
      omega
  have hwindow :=
    conwayGuyDifference_eq_height_window
      (triangular (previous + 1) + 1) (by omega)
  rw [hnextGuide] at hwindow
  have htail :
      triangular (previous + 1) + 1 - (previous + 2) =
        triangular previous := by
    omega
  rw [htail] at hwindow
  calc
    residual (previous + 2) (triangular (previous + 1) + 2) =
        residual (previous + 1) (triangular (previous + 1) + 1) +
          conwayGuyDifference (triangular (previous + 1) + 1) -
            conwayGuyHeight (triangular (previous + 1) + 1) := by
      simpa [Nat.add_assoc] using
        residual_succ_width (previous + 1)
          (triangular (previous + 1) + 1)
    _ = residual (previous + 1) (triangular (previous + 1) + 1) -
          conwayGuyHeight (triangular previous) := by
      rw [hwindow]
      ring

lemma correction_sum_succ (previous : ℕ) :
    (∑ index : Fin (previous + 1),
        conwayGuyHeight (triangular index.val)) =
      (∑ index : Fin previous,
          conwayGuyHeight (triangular index.val)) +
        conwayGuyHeight (triangular previous) := by
  rw [Fin.sum_univ_eq_sum_range
      (fun index => conwayGuyHeight (triangular index)) (previous + 1),
    Fin.sum_univ_eq_sum_range
      (fun index => conwayGuyHeight (triangular index)) previous,
    Finset.sum_range_succ]

theorem block_identity_by_width :
    ∀ previous dimension : ℕ,
      guide dimension = previous + 1 →
        residual (previous + 1) dimension +
          ∑ index : Fin previous,
            conwayGuyHeight (triangular index.val) = 1
  | 0, dimension, hguide => by
      have hdimension : dimension = 2 := by
        obtain ⟨hlower, hupper⟩ :=
          (guide_eq_iff (dimension := dimension) (width := 1) (by omega)).mp
            hguide
        simp [triangular] at hlower hupper
        omega
      subst dimension
      have hguideTwo : guide 2 = 1 := by
        simpa [triangular] using guide_at_triangular_end 1
      have hheightOne : conwayGuyHeight 1 = 1 := by
        simp [conwayGuyHeight, conwayGuyDifference, difference]
      have hdifferenceOne : conwayGuyDifference 1 = 1 := by
        rw [conwayGuyDifference_succ, hguideTwo]
        simp [conwayGuyDifference, difference]
      have hheightTwo : conwayGuyHeight 2 = 2 := by
        rw [show 2 = 1 + 1 by omega, conwayGuyHeight_succ,
          hheightOne, hdifferenceOne]
        norm_num
      simp [residual, hheightOne, hheightTwo]
  | previous + 1, dimension, hguide => by
      have hstart :=
        residual_eq_block_start (width := previous + 2)
          (dimension := dimension) (by omega) hguide
      have hpreviousGuide :
          guide (triangular (previous + 1) + 1) = previous + 1 :=
        guide_at_triangular_end (previous + 1)
      have inductionHypothesis :=
        block_identity_by_width previous
          (triangular (previous + 1) + 1) hpreviousGuide
      have hpred :
          previous + 2 - 1 = previous + 1 := by omega
      rw [hpred] at hstart
      rw [hstart, residual_next_block_start, correction_sum_succ]
      linarith

/-- The exact triangular-block identity for every Conway--Guy height. -/
theorem conwayGuy_block_identity (dimension : ℕ)
    (hdimension : 2 ≤ dimension) :
    conwayGuyHeight dimension -
          ∑ index : Fin (guide dimension),
            conwayGuyHeight (dimension - index.val - 1) +
        ∑ index : Fin (guide dimension - 1),
          conwayGuyHeight (triangular index.val) = 1 := by
  have hwidth := guide_pos hdimension
  have hguide :
      guide dimension - 1 + 1 = guide dimension := by
    omega
  have hidentity :=
    block_identity_by_width (guide dimension - 1) dimension hguide.symm
  rw [hguide] at hidentity
  simpa only [residual] using hidentity

end BooleanIsoperimetry.CoherentGap
