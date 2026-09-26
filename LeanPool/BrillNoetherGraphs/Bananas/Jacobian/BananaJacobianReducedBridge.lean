/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianReducedInjectivity
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffDelta

/-!
# Paper coordinate representatives are q-reduced

This file supplies the concrete bridge left open by
`BananaJacobianReducedInjectivity.lean`.  An interior coordinate contributes
the corresponding semibreak chip, a terminal coordinate contributes a chip at
the right endpoint, and every nonzero coordinate contributes one unit of debt
at the left endpoint.
-/

@[expose] public section

namespace Bananas

open Utilities
open scoped BigOperators
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- The decidable numerical form of being an interior normalized position. -/
def IsPaperInteriorCoordinate {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (alpha : Fin (g + 1)) : Prop :=
  0 < (p alpha).val ∧ (p alpha).val < B.length alpha

/-- The storage-oriented semibreak chips encoded by a vector of normalized
strand positions. -/
noncomputable def paperCoordinateChips {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    ∀ alpha : Fin (g + 1), Option (Fin (B.length alpha - 1)) :=
  fun alpha => if h : 0 < (p alpha).val ∧
      (p alpha).val < B.length alpha then
    some (normalizedInteriorOffset B alpha (p alpha) h) else none

/-- One unit of left-endpoint debt for every nonzero coordinate. -/
def paperCoordinateLeftCoefficient {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) : ℤ :=
  ∑ alpha : Fin (g + 1), if (p alpha).val = 0 then 0 else -1

/-- One right-endpoint chip for every terminal coordinate. -/
def paperCoordinateRightCoefficient {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) : ℤ :=
  ∑ alpha : Fin (g + 1),
    if (p alpha).val = B.length alpha then 1 else 0

/-- The semibreak part of the paper coordinate divisor. -/
noncomputable def paperCoordinateSemibreak {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) : CFDiv B.graph :=
  semibreakDivisor B (paperCoordinateChips B p)

theorem isSemibreak_paperCoordinateSemibreak {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    IsSemibreak B (paperCoordinateSemibreak B p) := by
  exact ⟨paperCoordinateChips B p, rfl⟩
private theorem paperCoordinateSemibreak_eq_sum {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    paperCoordinateSemibreak B p =
      ∑ alpha : Fin (g + 1),
        if _h : 0 < (p alpha).val ∧ (p alpha).val < B.length alpha then
          oneChip (strandVertex B alpha (p alpha)) else 0 := by
  classical
  funext z
  rw [Finset.sum_apply]
  rcases z with core | ⟨gamma, offset⟩
  · change 0 = _
    symm
    apply Finset.sum_eq_zero
    intro alpha _
    by_cases halpha : 0 < (p alpha).val ∧
        (p alpha).val < B.length alpha
    · rw [dite_eq_left halpha,
        strandVertex_eq_interiorVertex_normalizedInteriorOffset B alpha
          (p alpha) halpha]
      simp [oneChip, SubdivisionGraph.Spec.interiorVertex]
    · rw [dite_eq_right halpha]
      rfl
  · change (if paperCoordinateChips B p gamma = some offset then 1 else 0) = _
    by_cases hgamma : 0 < (p gamma).val ∧
        (p gamma).val < B.length gamma
    · rw [show paperCoordinateChips B p gamma =
          some (normalizedInteriorOffset B gamma (p gamma) hgamma) by
        simp only [paperCoordinateChips, dite_eq_left hgamma]]
      simp only [Option.some.injEq]
      rw [Finset.sum_eq_single gamma]
      · simp [hgamma, oneChip,
          strandVertex_eq_interiorVertex_normalizedInteriorOffset B gamma
            (p gamma) hgamma,
          SubdivisionGraph.Spec.interiorVertex]
        by_cases hoffset :
            normalizedInteriorOffset B gamma (p gamma) hgamma = offset
        · simp [hoffset]
        · simp [hoffset, Ne.symm hoffset]
      · intro alpha _ hne
        by_cases halpha : 0 < (p alpha).val ∧
            (p alpha).val < B.length alpha
        · rw [dite_eq_left halpha,
            strandVertex_eq_interiorVertex_normalizedInteriorOffset B alpha
              (p alpha) halpha]
          simp [oneChip, SubdivisionGraph.Spec.interiorVertex, hne.symm]
        · rw [dite_eq_right halpha]
          rfl
      · simp
    · rw [show paperCoordinateChips B p gamma = none by
        simp only [paperCoordinateChips, dite_eq_right hgamma]]
      simp only [reduceCtorEq, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro alpha _
      by_cases halpha : 0 < (p alpha).val ∧
          (p alpha).val < B.length alpha
      · rw [dite_eq_left halpha,
          strandVertex_eq_interiorVertex_normalizedInteriorOffset B alpha
            (p alpha) halpha]
        simp only [oneChip, SubdivisionGraph.Spec.interiorVertex]
        by_cases hag : alpha = gamma
        · subst alpha
          exact (hgamma halpha).elim
        · have hne : (Sum.inr ⟨gamma, offset⟩ : B.graph.V) ≠
              Sum.inr ⟨alpha, normalizedInteriorOffset B alpha (p alpha) halpha⟩ := by
            intro heq
            have hsigma := Sum.inr.inj heq
            have hslots : gamma = alpha := congrArg Sigma.fst hsigma
            exact hag hslots.symm
          exact ite_eq_right hne
      · rw [dite_eq_right halpha]
        rfl

private theorem positionCoordinate_summand_eq_normalForm_summand {g : ℕ}
    (B : Banana g) (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (alpha : Fin (g + 1)) :
    oneChip (strandVertex B alpha (p alpha)) - oneChip (leftEndpoint B) =
      (if (p alpha).val = 0 then 0 else (-1 : ℤ)) •
          oneChip (leftEndpoint B) +
        (if (p alpha).val = B.length alpha then (1 : ℤ) else 0) •
          oneChip (rightEndpoint B) +
        (if _h : 0 < (p alpha).val ∧ (p alpha).val < B.length alpha then
          oneChip (strandVertex B alpha (p alpha)) else 0) := by
  by_cases hzero : (p alpha).val = 0
  · have hp : p alpha = ⟨0, by omega⟩ := Fin.ext hzero
    have hlength := B.length_pos alpha
    have hnotInterior : ¬(0 < (p alpha).val ∧
        (p alpha).val < B.length alpha) := by omega
    rw [dite_eq_right hnotInterior]
    rw [hp, strandVertex_zero]
    rw [ite_eq_left rfl, ite_eq_right (Nat.ne_of_gt hlength).symm]
    simp
  · by_cases hlast : (p alpha).val = B.length alpha
    · have hp : p alpha = ⟨B.length alpha, by omega⟩ := Fin.ext hlast
      have hlength := B.length_pos alpha
      have hnotInterior : ¬(0 < (p alpha).val ∧
          (p alpha).val < B.length alpha) := by omega
      rw [dite_eq_right hnotInterior]
      rw [hp, strandVertex_length]
      rw [ite_eq_right (Nat.ne_of_gt hlength), ite_eq_left rfl]
      simp
      abel
    · have hinterior : 0 < (p alpha).val ∧
          (p alpha).val < B.length alpha := by
        have hpBound := (p alpha).isLt
        omega
      rw [dite_eq_left hinterior, ite_eq_right hzero, ite_eq_right hlast]
      simp
      abel

/-- The paper coordinate divisor is exactly an endpoint/semibreak normal
form. -/
theorem bananaPositionCoordinateDivisor_eq_normalForm {g : ℕ}
    (B : Banana g) (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    bananaPositionCoordinateDivisor B p =
      bananaNormalForm B (paperCoordinateLeftCoefficient B p)
        (paperCoordinateRightCoefficient B p)
        (paperCoordinateSemibreak B p) := by
  classical
  rw [bananaPositionCoordinateDivisor, paperCoordinateSemibreak_eq_sum]
  simp_rw [positionCoordinate_summand_eq_normalForm_summand B p]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  unfold bananaNormalForm paperCoordinateLeftCoefficient
    paperCoordinateRightCoefficient
  rw [Finset.sum_smul, Finset.sum_smul]

private theorem degree_paperCoordinateSemibreak {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    deg (paperCoordinateSemibreak B p) =
      ∑ alpha : Fin (g + 1),
        if 0 < (p alpha).val ∧ (p alpha).val < B.length alpha then
          (1 : ℤ) else 0 := by
  classical
  rw [paperCoordinateSemibreak, degree_semibreakDivisor]
  apply Finset.sum_congr rfl
  intro alpha _
  by_cases hinterior : 0 < (p alpha).val ∧
      (p alpha).val < B.length alpha
  · rw [ite_eq_left hinterior]
    simp only [paperCoordinateChips, dite_eq_left hinterior,
      Option.isSome_some, ite_true]
  · rw [ite_eq_right hinterior]
    simp only [paperCoordinateChips, dite_eq_right hinterior,
      Option.isSome_none]
    norm_num

/-- The numerical normal-form bound follows from the required zero
coordinate.  The ordering clause in the paper's representative convention is
not needed for this reducedness argument. -/
theorem paperCoordinateRightCoefficient_add_degree_le_genus {g : ℕ}
    (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hPaper : IsPaperReducedPositionCoordinates B p) :
    paperCoordinateRightCoefficient B p +
      deg (paperCoordinateSemibreak B p) ≤ (g : ℤ) := by
  classical
  rcases hPaper.1 with ⟨zeroSlot, hzeroSlot⟩
  rw [paperCoordinateRightCoefficient, degree_paperCoordinateSemibreak,
    ← Finset.sum_add_distrib]
  have hPartition : ∀ alpha : Fin (g + 1),
      (if (p alpha).val = B.length alpha then (1 : ℤ) else 0) +
          (if 0 < (p alpha).val ∧
              (p alpha).val < B.length alpha then (1 : ℤ) else 0) =
        if (p alpha).val = 0 then 0 else 1 := by
    intro alpha
    have hlength := B.length_pos alpha
    have hpBound := (p alpha).isLt
    by_cases hzero : (p alpha).val = 0
    · rw [ite_eq_left hzero, ite_eq_right (by omega), ite_eq_right (by omega)]
      norm_num
    · by_cases hlast : (p alpha).val = B.length alpha
      · rw [ite_eq_right hzero, ite_eq_left hlast, ite_eq_right (by omega)]
        norm_num
      · have hinterior : 0 < (p alpha).val ∧
            (p alpha).val < B.length alpha := by omega
        rw [ite_eq_right hzero, ite_eq_right hlast, ite_eq_left hinterior]
        norm_num
  rw [Finset.sum_congr rfl (fun alpha _ => hPartition alpha)]
  let active : Fin (g + 1) → ℤ := fun alpha =>
    if (p alpha).val = 0 then 0 else 1
  change (∑ alpha : Fin (g + 1), active alpha) ≤ (g : ℤ)
  have hZeroActive : active zeroSlot = 0 := by
    unfold active
    rw [ite_eq_left hzeroSlot]
  have hSplit : (∑ alpha : Fin (g + 1), active alpha) =
      ∑ alpha ∈ (Finset.univ.erase zeroSlot), active alpha := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (g + 1)))
      active (Finset.mem_univ zeroSlot), hZeroActive, add_zero]
  rw [hSplit]
  have hLe : (∑ alpha ∈ (Finset.univ.erase zeroSlot), active alpha) ≤
      ∑ _alpha ∈ (Finset.univ.erase zeroSlot), (1 : ℤ) := by
    apply Finset.sum_le_sum
    intro alpha _
    unfold active
    split <;> omega
  have hCard : (Finset.univ.erase zeroSlot).card = g := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ zeroSlot)]
    simp
  calc
    (∑ alpha ∈ (Finset.univ.erase zeroSlot), active alpha) ≤
        ∑ _alpha ∈ (Finset.univ.erase zeroSlot), (1 : ℤ) := hLe
    _ = ((Finset.univ.erase zeroSlot).card : ℤ) := by simp
    _ = (g : ℤ) := by rw [hCard]

/-- The paper's preferred coordinate representative is reduced at the common
left endpoint. -/
theorem q_reduced_bananaPositionCoordinateDivisor_of_paperReduced {g : ℕ}
    (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hPaper : IsPaperReducedPositionCoordinates B p) :
    qReduced B.graph (leftEndpoint B)
      (bananaPositionCoordinateDivisor B p) := by
  rw [bananaPositionCoordinateDivisor_eq_normalForm]
  apply q_reduced_bananaNormalForm
  · exact isSemibreak_paperCoordinateSemibreak B p
  · unfold paperCoordinateRightCoefficient
    apply Finset.sum_nonneg
    intro alpha _
    split <;> omega
  · exact paperCoordinateRightCoefficient_add_degree_le_genus B p hPaper

/-- Full kernel-triviality statement for the paper's reduced coordinate
representatives. -/
theorem bananaPositionCoordinates_eq_zero_of_paperReduced_of_mem_relations
    {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hPaper : IsPaperReducedPositionCoordinates B p)
    (hKernel : bananaPositionCoordinates B p ∈ bananaCoordinateRelations B) :
    bananaPositionCoordinates B p = 0 := by
  exact bananaPositionCoordinates_eq_zero_of_qReduced_of_mem_relations B p
    (q_reduced_bananaPositionCoordinateDivisor_of_paperReduced B p hPaper)
    hKernel

end Bananas
