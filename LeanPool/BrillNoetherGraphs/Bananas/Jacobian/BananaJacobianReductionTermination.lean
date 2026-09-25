/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianQuotientCertificate

/-!
# A well-founded measure for banana-coordinate reduction

The prose reduction in Proposition 2.14 alternates two operations: transfer
one strand length from an over-length coordinate to a zero coordinate, then
(if that consumed the last zero) subtract the new positive minimum from every
coordinate.  The lexicographic termination measure is

`(sum (a_alpha / n_alpha), number of zero coordinates)`.

This module proves the strict-decrease facts behind that measure.  They are
kept on natural-valued nonnegative coordinates; the separate quotient
certificate module translates a terminal vector into the displayed integer
relation lattice.
-/

@[expose] public section

namespace Bananas

open Utilities

open scoped BigOperators

/-- Sum of the integral strand-length quotients of a nonnegative coordinate
vector. -/
def bananaQuotientWeight {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) : ℕ :=
  ∑ alpha : Fin (g + 1), a alpha / B.length alpha

/-- Coordinates currently equal to zero. -/
def bananaZeroSet {g : ℕ} (a : Fin (g + 1) → ℕ) :
    Finset (Fin (g + 1)) :=
  Finset.univ.filter fun alpha => a alpha = 0

/-- Move one full strand length from coordinate `alpha` to the zero
coordinate `beta`. -/
def bananaLengthTransfer {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta : Fin (g + 1)) :
    Fin (g + 1) → ℕ :=
  fun gamma =>
    if gamma = alpha then a gamma - B.length gamma
    else if gamma = beta then B.length gamma
    else a gamma

private theorem alpha_ne_beta_of_overlength_of_zero {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta : Fin (g + 1))
    (hOver : B.length alpha < a alpha) (hZero : a beta = 0) :
    alpha ≠ beta := by
  intro h
  subst beta
  omega

@[simp] theorem bananaLengthTransfer_apply_alpha {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta : Fin (g + 1)) :
    bananaLengthTransfer B a alpha beta alpha =
      a alpha - B.length alpha := by
  simp [bananaLengthTransfer]

@[simp] theorem bananaLengthTransfer_apply_beta {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta : Fin (g + 1))
    (hNe : alpha ≠ beta) :
    bananaLengthTransfer B a alpha beta beta = B.length beta := by
  simp [bananaLengthTransfer, hNe.symm]

theorem bananaLengthTransfer_apply_other {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta gamma : Fin (g + 1))
    (hAlpha : gamma ≠ alpha) (hBeta : gamma ≠ beta) :
    bananaLengthTransfer B a alpha beta gamma = a gamma := by
  simp [bananaLengthTransfer, hAlpha, hBeta]

private theorem sub_length_div_add_one {x n : ℕ} (hn : 0 < n)
    (h : n ≤ x) :
    (x - n) / n + 1 = x / n := by
  have hx : x - n + n = x := Nat.sub_add_cancel h
  calc
    (x - n) / n + 1 = ((x - n) + n * 1) / n := by
      rw [Nat.add_mul_div_left (x - n) 1 hn]
    _ = x / n := by simp [hx]

/-- A length transfer preserves the quotient-weight component of the
termination measure. -/
theorem bananaQuotientWeight_lengthTransfer {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta : Fin (g + 1))
    (hOver : B.length alpha < a alpha) (hZero : a beta = 0) :
    bananaQuotientWeight B (bananaLengthTransfer B a alpha beta) =
      bananaQuotientWeight B a := by
  classical
  have hNe := alpha_ne_beta_of_overlength_of_zero B a alpha beta hOver hZero
  unfold bananaQuotientWeight
  let rest : Finset (Fin (g + 1)) :=
    (Finset.univ.erase alpha).erase beta
  have splitSum (f : Fin (g + 1) → ℕ) :
      ∑ gamma : Fin (g + 1), f gamma =
        f alpha + f beta + ∑ gamma ∈ rest, f gamma := by
    have hAlpha := Finset.sum_erase_add (Finset.univ : Finset (Fin (g + 1)))
      f (Finset.mem_univ alpha)
    have hBeta := Finset.sum_erase_add (Finset.univ.erase alpha) f
      (show beta ∈ Finset.univ.erase alpha by simp [hNe.symm])
    change (∑ gamma ∈ Finset.univ, f gamma) = _
    change (∑ gamma ∈ Finset.univ.erase alpha, f gamma) + f alpha =
      ∑ gamma ∈ Finset.univ, f gamma at hAlpha
    change (∑ gamma ∈ rest, f gamma) + f beta =
      ∑ gamma ∈ Finset.univ.erase alpha, f gamma at hBeta
    rw [← hAlpha, ← hBeta]
    ac_rfl
  rw [splitSum, splitSum]
  have hLengthAlpha := B.length_pos alpha
  have hLengthBeta := B.length_pos beta
  rw [bananaLengthTransfer_apply_alpha,
    bananaLengthTransfer_apply_beta B a alpha beta hNe]
  have hAlphaQuotient := sub_length_div_add_one hLengthAlpha hOver.le
  have hBetaOld : a beta / B.length beta = 0 := by simp [hZero]
  have hBetaNew : B.length beta / B.length beta = 1 :=
    Nat.div_self hLengthBeta
  rw [hBetaOld, hBetaNew]
  have hRest :
      ∑ gamma ∈ rest,
          bananaLengthTransfer B a alpha beta gamma / B.length gamma =
        ∑ gamma ∈ rest,
          a gamma / B.length gamma := by
    apply Finset.sum_congr rfl
    intro gamma hGamma
    have hGammaBeta : gamma ≠ beta := by
      exact (Finset.mem_erase.mp hGamma).1
    have hGammaAlpha : gamma ≠ alpha := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hGamma).2).1
    rw [bananaLengthTransfer_apply_other B a alpha beta gamma
      hGammaAlpha hGammaBeta]
  rw [hRest]
  omega

/-- A transfer removes the chosen zero and creates no new zero.  Consequently
its zero set is a strict subset of the old zero set whenever some other zero
remains. -/
theorem bananaZeroSet_lengthTransfer_ssubset {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta : Fin (g + 1))
    (hOver : B.length alpha < a alpha) (hZero : a beta = 0) :
    bananaZeroSet (bananaLengthTransfer B a alpha beta) ⊂ bananaZeroSet a := by
  classical
  have hNe := alpha_ne_beta_of_overlength_of_zero B a alpha beta hOver hZero
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro gamma hGamma
    simp only [bananaZeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hGamma ⊢
    by_cases hGammaAlpha : gamma = alpha
    · subst gamma
      rw [bananaLengthTransfer_apply_alpha] at hGamma
      omega
    · by_cases hGammaBeta : gamma = beta
      · subst gamma
        rw [bananaLengthTransfer_apply_beta B a alpha beta hNe] at hGamma
        exact (Nat.ne_of_gt (B.length_pos beta) hGamma).elim
      · rwa [bananaLengthTransfer_apply_other B a alpha beta gamma
          hGammaAlpha hGammaBeta] at hGamma
  · intro hEqual
    have hBetaOld : beta ∈ bananaZeroSet a := by simp [bananaZeroSet, hZero]
    have hBetaNew : beta ∉
        bananaZeroSet (bananaLengthTransfer B a alpha beta) := by
      simp [bananaZeroSet, bananaLengthTransfer_apply_beta B a alpha beta hNe,
        Nat.ne_of_gt (B.length_pos beta)]
    exact hBetaNew (hEqual.symm ▸ hBetaOld)

/-- Subtract a common natural number from all coordinates. -/
def bananaShiftDown {g : ℕ} (a : Fin (g + 1) → ℕ) (m : ℕ) :
    Fin (g + 1) → ℕ := fun alpha => a alpha - m

/-- If a positive common shift is bounded by every coordinate, then quotient
weight cannot increase and strictly drops at any coordinate equal to one full
strand length.  This is the case used after consuming the unique zero. -/
theorem bananaQuotientWeight_shiftDown_lt {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (m : ℕ) (beta : Fin (g + 1))
    (hmPos : 0 < m) (hmLe : ∀ alpha, m ≤ a alpha)
    (hBeta : a beta = B.length beta) :
    bananaQuotientWeight B (bananaShiftDown a m) <
      bananaQuotientWeight B a := by
  classical
  unfold bananaQuotientWeight
  apply Finset.sum_lt_sum
  · intro alpha _
    exact Nat.div_le_div_right (Nat.sub_le (a alpha) m)
  · refine ⟨beta, Finset.mem_univ beta, ?_⟩
    rw [bananaShiftDown, hBeta]
    have hmLength : m ≤ B.length beta := by simpa [hBeta] using hmLe beta
    have hSubLt : B.length beta - m < B.length beta := by omega
    rw [Nat.div_eq_of_lt hSubLt, Nat.div_self (B.length_pos beta)]
    omega

/-- A single natural number encoding the lexicographic pair
`(quotient weight, zero count)`.  The block size `g+2` is one larger than the
number of coordinates, so a drop in quotient weight dominates any change in
the zero count. -/
def bananaReductionMeasure {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) : ℕ :=
  bananaQuotientWeight B a * (g + 2) + (bananaZeroSet a).card

private theorem bananaZeroSet_card_lt_block {g : ℕ}
    (a : Fin (g + 1) → ℕ) :
    (bananaZeroSet a).card < g + 2 := by
  have hSubset : bananaZeroSet a ⊆
      (Finset.univ : Finset (Fin (g + 1))) := Finset.filter_subset _ _
  have hCard := Finset.card_le_card hSubset
  simp only [Finset.card_univ, Fintype.card_fin] at hCard
  omega

/-- If another zero remains, a length transfer strictly decreases the encoded
measure through its zero-count component. -/
theorem bananaReductionMeasure_lengthTransfer_lt
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℕ)
    (alpha beta : Fin (g + 1))
    (hOver : B.length alpha < a alpha) (hZero : a beta = 0) :
    bananaReductionMeasure B (bananaLengthTransfer B a alpha beta) <
      bananaReductionMeasure B a := by
  have hWeight := bananaQuotientWeight_lengthTransfer B a alpha beta hOver hZero
  have hZeroSubset := bananaZeroSet_lengthTransfer_ssubset B a alpha beta hOver hZero
  have hCard := Finset.card_lt_card hZeroSubset
  unfold bananaReductionMeasure
  rw [hWeight]
  omega

/-- Whenever quotient weight drops, the encoded measure drops as well,
regardless of the new zero set. -/
theorem bananaReductionMeasure_lt_of_quotientWeight_lt {g : ℕ}
    (B : Banana g) (a b : Fin (g + 1) → ℕ)
    (hWeight : bananaQuotientWeight B b < bananaQuotientWeight B a) :
    bananaReductionMeasure B b < bananaReductionMeasure B a := by
  have hZeroBound := bananaZeroSet_card_lt_block b
  have hBlock :
      bananaQuotientWeight B b * (g + 2) + (bananaZeroSet b).card <
        (bananaQuotientWeight B b + 1) * (g + 2) := by
    rw [Nat.add_mul]
    omega
  have hNext : bananaQuotientWeight B b + 1 ≤ bananaQuotientWeight B a :=
    Nat.succ_le_iff.mpr hWeight
  have hScaled :
      (bananaQuotientWeight B b + 1) * (g + 2) ≤
        bananaQuotientWeight B a * (g + 2) :=
    Nat.mul_le_mul_right (g + 2) hNext
  unfold bananaReductionMeasure
  exact hBlock.trans_le (hScaled.trans (Nat.le_add_right _ _))

/-- In the unique-zero case, the post-transfer positive-minimum shift strictly
decreases the encoded measure through its quotient-weight component. -/
theorem bananaReductionMeasure_shiftDown_lengthTransfer_lt
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℕ)
    (alpha beta : Fin (g + 1)) (m : ℕ)
    (hOver : B.length alpha < a alpha) (hZero : a beta = 0)
    (hmPos : 0 < m)
    (hmLe : ∀ gamma, m ≤ bananaLengthTransfer B a alpha beta gamma) :
    bananaReductionMeasure B
        (bananaShiftDown (bananaLengthTransfer B a alpha beta) m) <
      bananaReductionMeasure B a := by
  have hNe := alpha_ne_beta_of_overlength_of_zero B a alpha beta hOver hZero
  have hShiftWeight := bananaQuotientWeight_shiftDown_lt B
    (bananaLengthTransfer B a alpha beta) m beta hmPos hmLe
    (bananaLengthTransfer_apply_beta B a alpha beta hNe)
  have hTransferWeight :=
    bananaQuotientWeight_lengthTransfer B a alpha beta hOver hZero
  apply bananaReductionMeasure_lt_of_quotientWeight_lt B
  rw [hTransferWeight] at hShiftWeight
  exact hShiftWeight

/-- If `beta` is the unique zero, then after transferring a length away from
an over-length coordinate every coordinate is positive.  Subtracting the
finite minimum therefore restores a zero with a positive common shift. -/
theorem exists_positive_minimum_after_uniqueZero_transfer
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℕ)
    (alpha beta : Fin (g + 1))
    (hOver : B.length alpha < a alpha) (hZero : a beta = 0)
    (hUnique : ∀ gamma, a gamma = 0 → gamma = beta) :
    ∃ m : ℕ, 0 < m ∧
      (∀ gamma, m ≤ bananaLengthTransfer B a alpha beta gamma) ∧
      ∃ delta, bananaShiftDown (bananaLengthTransfer B a alpha beta) m delta = 0 := by
  classical
  let transferred := bananaLengthTransfer B a alpha beta
  obtain ⟨delta, _hDeltaMem, hMinimal⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (g + 1))) transferred
      Finset.univ_nonempty
  have hNe := alpha_ne_beta_of_overlength_of_zero B a alpha beta hOver hZero
  have hDeltaPos : 0 < transferred delta := by
    by_cases hDeltaAlpha : delta = alpha
    · subst delta
      simp only [transferred, bananaLengthTransfer_apply_alpha]
      omega
    · by_cases hDeltaBeta : delta = beta
      · subst delta
        simp only [transferred,
          bananaLengthTransfer_apply_beta B a alpha beta hNe]
        exact B.length_pos beta
      · rw [show transferred delta = a delta by
          exact bananaLengthTransfer_apply_other B a alpha beta delta
            hDeltaAlpha hDeltaBeta]
        exact Nat.pos_of_ne_zero fun hDeltaZero =>
          hDeltaBeta (hUnique delta hDeltaZero)
  refine ⟨transferred delta, hDeltaPos, ?_, ⟨delta, ?_⟩⟩
  · intro gamma
    exact hMinimal gamma (Finset.mem_univ gamma)
  · change transferred delta - transferred delta = 0
    omega

/-- Regard nonnegative natural coordinates as integer coordinate vectors. -/
def bananaNatCoordinates {g : ℕ} (a : Fin (g + 1) → ℕ) :
    Fin (g + 1) → ℤ := fun alpha => a alpha

/-- A transfer is exactly the pairwise displayed strand-length relation. -/
theorem natCoordinates_sub_lengthTransfer {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (alpha beta : Fin (g + 1))
    (hOver : B.length alpha < a alpha) (hZero : a beta = 0) :
    bananaNatCoordinates a -
        bananaNatCoordinates (bananaLengthTransfer B a alpha beta) =
      bananaPairwiseLengthRelation B alpha beta := by
  have hNe := alpha_ne_beta_of_overlength_of_zero B a alpha beta hOver hZero
  funext gamma
  by_cases hGammaAlpha : gamma = alpha
  · subst gamma
    simp [bananaNatCoordinates, bananaPairwiseLengthRelation,
      bananaCoordinateBasis, hNe, Nat.cast_sub hOver.le]
  · by_cases hGammaBeta : gamma = beta
    · subst gamma
      change (a beta : ℤ) -
        (bananaLengthTransfer B a alpha beta beta : ℤ) =
          bananaPairwiseLengthRelation B alpha beta beta
      rw [show bananaLengthTransfer B a alpha beta beta = B.length beta by
        exact bananaLengthTransfer_apply_beta B a alpha beta hNe]
      simp [bananaPairwiseLengthRelation,
        bananaCoordinateBasis, hNe.symm, hZero]
    · simp [bananaNatCoordinates, bananaLengthTransfer,
        bananaPairwiseLengthRelation, bananaCoordinateBasis,
        hGammaAlpha, hGammaBeta]

theorem natCoordinates_sub_shiftDown {g : ℕ}
    (a : Fin (g + 1) → ℕ) (m : ℕ) (hmLe : ∀ alpha, m ≤ a alpha) :
    bananaNatCoordinates a - bananaNatCoordinates (bananaShiftDown a m) =
      (m : ℤ) • bananaDiagonalRelation := by
  funext alpha
  simp [bananaNatCoordinates, bananaShiftDown, bananaDiagonalRelation,
    Nat.cast_sub (hmLe alpha)]

/-- From any nonnegative vector with a zero and an over-length coordinate,
there is a strictly smaller normalized vector in the same displayed-lattice
class.  This is the complete recursive step for the first two paper-reduced
conditions. -/
theorem exists_reductionStep_mod_displayedRelations {g : ℕ} (B : Banana g)
    (a : Fin (g + 1) → ℕ) (hHasZero : ∃ beta, a beta = 0)
    (alpha : Fin (g + 1)) (hOver : B.length alpha < a alpha) :
    ∃ b : Fin (g + 1) → ℕ,
      (∃ beta, b beta = 0) ∧
      bananaReductionMeasure B b < bananaReductionMeasure B a ∧
      bananaNatCoordinates a - bananaNatCoordinates b ∈
        bananaDisplayedRelations B := by
  classical
  obtain ⟨beta, hZero⟩ := hHasZero
  let transferred := bananaLengthTransfer B a alpha beta
  by_cases hOther : ∃ delta, a delta = 0 ∧ delta ≠ beta
  · obtain ⟨delta, hDeltaZero, hDeltaNe⟩ := hOther
    refine ⟨transferred, ⟨delta, ?_⟩,
      bananaReductionMeasure_lengthTransfer_lt B a alpha beta hOver hZero, ?_⟩
    · have hDeltaAlpha : delta ≠ alpha := by
        intro h
        subst delta
        omega
      change bananaLengthTransfer B a alpha beta delta = 0
      rw [bananaLengthTransfer_apply_other B a alpha beta delta
        hDeltaAlpha hDeltaNe]
      exact hDeltaZero
    · rw [natCoordinates_sub_lengthTransfer B a alpha beta hOver hZero]
      exact bananaPairwiseLengthRelation_mem_displayedRelations B alpha beta
  · have hUnique : ∀ gamma, a gamma = 0 → gamma = beta := by
      intro gamma hGamma
      by_contra hGammaNe
      exact hOther ⟨gamma, hGamma, hGammaNe⟩
    obtain ⟨m, hmPos, hmLe, delta, hDeltaZero⟩ :=
      exists_positive_minimum_after_uniqueZero_transfer B a alpha beta
        hOver hZero hUnique
    let b := bananaShiftDown transferred m
    refine ⟨b, ⟨delta, hDeltaZero⟩,
      bananaReductionMeasure_shiftDown_lengthTransfer_lt B a alpha beta m
        hOver hZero hmPos hmLe, ?_⟩
    have hTransfer : bananaNatCoordinates a - bananaNatCoordinates transferred ∈
        bananaDisplayedRelations B := by
      rw [natCoordinates_sub_lengthTransfer B a alpha beta hOver hZero]
      exact bananaPairwiseLengthRelation_mem_displayedRelations B alpha beta
    have hShift : bananaNatCoordinates transferred - bananaNatCoordinates b ∈
        bananaDisplayedRelations B := by
      rw [natCoordinates_sub_shiftDown transferred m hmLe]
      exact (bananaDisplayedRelations B).zsmul_mem
        (bananaDiagonalRelation_mem_displayedRelations B) m
    have hCombined := (bananaDisplayedRelations B).add_mem hTransfer hShift
    convert hCombined using 1
    abel

/-- The strict relation induced by `bananaReductionMeasure` is well founded;
this is the recursion principle needed to iterate the paper's reduction
moves. -/
def bananaReductionDecreases {g : ℕ} (B : Banana g)
    (next current : Fin (g + 1) → ℕ) : Prop :=
  bananaReductionMeasure B next < bananaReductionMeasure B current

theorem bananaReductionDecreases_wellFounded {g : ℕ} (B : Banana g) :
    WellFounded (bananaReductionDecreases B) := by
  exact (measure (bananaReductionMeasure B)).wf

/-- Terminating existence for the first two paper-reduced conditions.  Every
nonnegative coordinate vector having a zero is congruent modulo the displayed
lattice to another such vector lying in all closed strand intervals. -/
theorem exists_bounded_zero_natCoordinates_mod_displayedRelations
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℕ)
    (hHasZero : ∃ beta, a beta = 0) :
    ∃ b : Fin (g + 1) → ℕ,
      (∃ beta, b beta = 0) ∧
      (∀ alpha, b alpha ≤ B.length alpha) ∧
      bananaNatCoordinates a - bananaNatCoordinates b ∈
        bananaDisplayedRelations B := by
  classical
  revert hHasZero
  apply (bananaReductionDecreases_wellFounded B).induction a
  intro current ih hCurrentZero
  by_cases hBounded : ∀ alpha, current alpha ≤ B.length alpha
  · exact ⟨current, hCurrentZero, hBounded, by simp⟩
  · push Not at hBounded
    obtain ⟨alpha, hOver⟩ := hBounded
    obtain ⟨next, hNextZero, hDecrease, hCurrentNext⟩ :=
      exists_reductionStep_mod_displayedRelations B current hCurrentZero
        alpha hOver
    obtain ⟨terminal, hTerminalZero, hTerminalBounded, hNextTerminal⟩ :=
      ih next hDecrease hNextZero
    refine ⟨terminal, hTerminalZero, hTerminalBounded, ?_⟩
    have hCombined := (bananaDisplayedRelations B).add_mem
      hCurrentNext hNextTerminal
    convert hCombined using 1
    abel

/-- Every integer vector has a representative by valid strand positions with
at least one zero coordinate, modulo exactly the displayed relation lattice.
This completes conditions (1) and (2) of the paper's reduction convention;
the ordering of terminal coordinates versus zeros is the remaining finite
left-justification step. -/
theorem exists_positionCoordinates_with_zero_mod_displayedRelations
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℤ) :
    ∃ p : ∀ alpha : Fin (g + 1), B.PathPosition alpha,
      (∃ alpha, (p alpha).val = 0) ∧
      a - bananaPositionCoordinates B p ∈ bananaDisplayedRelations B := by
  classical
  obtain ⟨nonnegative, hNonnegativeZero, hNonnegative, hInitial⟩ :=
    exists_nonnegative_zero_mod_displayedRelations B a
  let natural : Fin (g + 1) → ℕ := fun alpha => (nonnegative alpha).toNat
  have hNaturalCast : bananaNatCoordinates natural = nonnegative := by
    funext alpha
    simp [bananaNatCoordinates, natural, Int.toNat_of_nonneg (hNonnegative alpha)]
  have hNaturalZero : ∃ alpha, natural alpha = 0 := by
    obtain ⟨alpha, hAlpha⟩ := hNonnegativeZero
    refine ⟨alpha, ?_⟩
    simp [natural, hAlpha]
  obtain ⟨bounded, hBoundedZero, hBounded, hNaturalBounded⟩ :=
    exists_bounded_zero_natCoordinates_mod_displayedRelations B natural hNaturalZero
  let p : ∀ alpha : Fin (g + 1), B.PathPosition alpha :=
    fun alpha => ⟨bounded alpha, Nat.lt_succ_of_le (hBounded alpha)⟩
  have hPosition : bananaPositionCoordinates B p = bananaNatCoordinates bounded := by
    funext alpha
    rfl
  refine ⟨p, ?_, ?_⟩
  · obtain ⟨alpha, hAlpha⟩ := hBoundedZero
    exact ⟨alpha, hAlpha⟩
  · have hInitialNatural :
        a - bananaNatCoordinates natural ∈ bananaDisplayedRelations B := by
      rwa [hNaturalCast]
    have hCombined := (bananaDisplayedRelations B).add_mem
      hInitialNatural hNaturalBounded
    rw [hPosition]
    convert hCombined using 1
    abel

end Bananas
