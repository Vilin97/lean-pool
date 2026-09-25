/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianReducedBridge
import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianLatticeReduction

/-!
# Uniqueness of the paper's reduced banana coordinates

This is the uniqueness layer in Proposition 2.14.  Two preferred position
vectors differing by the displayed lattice first give linearly equivalent
left-reduced divisors, hence equal divisors by uniqueness of q-reduction.
-/

namespace Bananas

open Utilities
open scoped BigOperators

/-- The q-reduced core of uniqueness: displayed-equivalent paper
representatives have exactly the same position-coordinate divisor. -/
theorem bananaPositionCoordinateDivisor_eq_of_paperReduced_mod_displayed
    {g : ℕ} (B : Banana g)
    (p q : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hp : IsPaperReducedPositionCoordinates B p)
    (hq : IsPaperReducedPositionCoordinates B q)
    (hrel : bananaPositionCoordinates B p - bananaPositionCoordinates B q ∈
      bananaDisplayedRelations B) :
    bananaPositionCoordinateDivisor B p = bananaPositionCoordinateDivisor B q := by
  have hKernel : bananaPositionCoordinates B p -
      bananaPositionCoordinates B q ∈ bananaCoordinateRelations B :=
    bananaDisplayedRelations_le_coordinateRelations B hrel
  rw [bananaCoordinateRelations, AddMonoidHom.mem_ker] at hKernel
  have hPrincipal : bananaCoordinateDivisorHom B
      (bananaPositionCoordinates B p - bananaPositionCoordinates B q) ∈
        principalDivisors B.graph :=
    (QuotientAddGroup.eq_zero_iff _).mp hKernel
  rw [map_sub] at hPrincipal
  have hCoordinates : linearEquiv B.graph
      (bananaCoordinateDivisorHom B (bananaPositionCoordinates B p))
      (bananaCoordinateDivisorHom B (bananaPositionCoordinates B q)) := by
    unfold linearEquiv
    simpa only [neg_sub] using (principalDivisors B.graph).neg_mem hPrincipal
  have hPosition : linearEquiv B.graph
      (bananaPositionCoordinateDivisor B p)
      (bananaPositionCoordinateDivisor B q) :=
    (bananaCoordinateDivisorHom_linearEquiv_positionDivisor B p).symm.trans
      (hCoordinates.trans
        (bananaCoordinateDivisorHom_linearEquiv_positionDivisor B q))
  exact q_reduced_unique B.graph (leftEndpoint B)
    (bananaPositionCoordinateDivisor B p)
    (bananaPositionCoordinateDivisor B q)
    ⟨q_reduced_bananaPositionCoordinateDivisor_of_paperReduced B p hp,
      q_reduced_bananaPositionCoordinateDivisor_of_paperReduced B q hq,
      hPosition⟩

/-- Equality of position-coordinate divisors remembers the semibreak chip on
each individual strand, despite the common endpoint aliases. -/
theorem paperCoordinateChips_eq_of_positionCoordinateDivisor_eq
    {g : ℕ} (B : Banana g)
    (p q : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hDiv : bananaPositionCoordinateDivisor B p =
      bananaPositionCoordinateDivisor B q) :
    paperCoordinateChips B p = paperCoordinateChips B q := by
  have hNormal := hDiv
  rw [bananaPositionCoordinateDivisor_eq_normalForm,
    bananaPositionCoordinateDivisor_eq_normalForm] at hNormal
  have hLeft : paperCoordinateLeftCoefficient B p =
      paperCoordinateLeftCoefficient B q := by
    have h := congrFun hNormal (leftEndpoint B)
    simpa only [bananaNormalForm_leftEndpoint B _ _ _
      (isSemibreak_paperCoordinateSemibreak B p),
      bananaNormalForm_leftEndpoint B _ _ _
        (isSemibreak_paperCoordinateSemibreak B q)] using h
  have hRight : paperCoordinateRightCoefficient B p =
      paperCoordinateRightCoefficient B q := by
    have h := congrFun hNormal (rightEndpoint B)
    simpa only [bananaNormalForm_rightEndpoint B _ _ _
      (isSemibreak_paperCoordinateSemibreak B p),
      bananaNormalForm_rightEndpoint B _ _ _
        (isSemibreak_paperCoordinateSemibreak B q)] using h
  have hSemibreak : paperCoordinateSemibreak B p =
      paperCoordinateSemibreak B q := by
    unfold bananaNormalForm at hNormal
    rw [hLeft, hRight] at hNormal
    exact add_left_cancel hNormal
  funext alpha
  cases hpChip : paperCoordinateChips B p alpha with
  | none =>
      cases hqChip : paperCoordinateChips B q alpha with
      | none => rfl
      | some offset =>
          have h := congrFun hSemibreak (B.interiorVertex alpha offset)
          simp [paperCoordinateSemibreak, hpChip, hqChip] at h
  | some offset =>
      cases hqChip : paperCoordinateChips B q alpha with
      | none =>
          have h := congrFun hSemibreak (B.interiorVertex alpha offset)
          simp [paperCoordinateSemibreak, hpChip, hqChip] at h
      | some offset' =>
          have h := congrFun hSemibreak (B.interiorVertex alpha offset)
          have hoffset : offset' = offset := by
            simp [paperCoordinateSemibreak, hpChip, hqChip] at h
            exact h
          simp [hoffset]

/-- An interior coordinate is recovered strand-by-strand from the associated
position-coordinate divisor. -/
theorem positionCoordinate_eq_of_interior_of_divisor_eq
    {g : ℕ} (B : Banana g)
    (p q : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hDiv : bananaPositionCoordinateDivisor B p =
      bananaPositionCoordinateDivisor B q)
    (alpha : Fin (g + 1))
    (hpInterior : IsPaperInteriorCoordinate B p alpha) :
    p alpha = q alpha := by
  change 0 < (p alpha).val ∧
    (p alpha).val < B.length alpha at hpInterior
  have hChips := congrFun
    (paperCoordinateChips_eq_of_positionCoordinateDivisor_eq B p q hDiv) alpha
  rw [show paperCoordinateChips B p alpha =
      some (normalizedInteriorOffset B alpha (p alpha) hpInterior) by
    simp only [paperCoordinateChips, dif_pos hpInterior]] at hChips
  by_cases hqInterior : IsPaperInteriorCoordinate B q alpha
  · change 0 < (q alpha).val ∧
      (q alpha).val < B.length alpha at hqInterior
    rw [show paperCoordinateChips B q alpha =
        some (normalizedInteriorOffset B alpha (q alpha) hqInterior) by
      simp only [paperCoordinateChips, dif_pos hqInterior]] at hChips
    have hOffset := Option.some.inj hChips
    apply strandVertex_injective B alpha
    rw [strandVertex_eq_interiorVertex_normalizedInteriorOffset B alpha
      (p alpha) hpInterior,
      strandVertex_eq_interiorVertex_normalizedInteriorOffset B alpha
        (q alpha) hqInterior, hOffset]
  · change ¬ (0 < (q alpha).val ∧
      (q alpha).val < B.length alpha) at hqInterior
    rw [show paperCoordinateChips B q alpha = none by
        simp only [paperCoordinateChips, dif_neg hqInterior]] at hChips
    contradiction

private def paperTerminalSlots {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) :
    Finset (Fin (g + 1)) :=
  Finset.univ.filter fun alpha => (p alpha).val = B.length alpha

private theorem paperTerminalSlots_card_eq_of_divisor_eq
    {g : ℕ} (B : Banana g)
    (p q : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hDiv : bananaPositionCoordinateDivisor B p =
      bananaPositionCoordinateDivisor B q) :
    (paperTerminalSlots B p).card = (paperTerminalSlots B q).card := by
  have hNormal := hDiv
  rw [bananaPositionCoordinateDivisor_eq_normalForm,
    bananaPositionCoordinateDivisor_eq_normalForm] at hNormal
  have hRight : paperCoordinateRightCoefficient B p =
      paperCoordinateRightCoefficient B q := by
    have h := congrFun hNormal (rightEndpoint B)
    simpa only [bananaNormalForm_rightEndpoint B _ _ _
      (isSemibreak_paperCoordinateSemibreak B p),
      bananaNormalForm_rightEndpoint B _ _ _
        (isSemibreak_paperCoordinateSemibreak B q)] using h
  unfold paperCoordinateRightCoefficient at hRight
  have hpCount : (∑ alpha : Fin (g + 1),
      if (p alpha).val = B.length alpha then (1 : ℤ) else 0) =
      ((paperTerminalSlots B p).card : ℤ) := by
    simp [paperTerminalSlots]
  have hqCount : (∑ alpha : Fin (g + 1),
      if (q alpha).val = B.length alpha then (1 : ℤ) else 0) =
      ((paperTerminalSlots B q).card : ℤ) := by
    simp [paperTerminalSlots]
  rw [hpCount, hqCount] at hRight
  exact_mod_cast hRight

/-- The apparent endpoint aliases do not create a second preferred
representative: the ordering clause makes the endpoint assignment unique. -/
theorem paperReducedPositionCoordinates_eq_of_divisor_eq
    {g : ℕ} (B : Banana g)
    (p q : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hp : IsPaperReducedPositionCoordinates B p)
    (hq : IsPaperReducedPositionCoordinates B q)
    (hDiv : bananaPositionCoordinateDivisor B p =
      bananaPositionCoordinateDivisor B q) :
    p = q := by
  classical
  let P := paperTerminalSlots B p
  let Q := paperTerminalSlots B q
  have hInteriorP : ∀ alpha, IsPaperInteriorCoordinate B p alpha →
      p alpha = q alpha :=
    positionCoordinate_eq_of_interior_of_divisor_eq B p q hDiv
  have hInteriorQ : ∀ alpha, IsPaperInteriorCoordinate B q alpha →
      q alpha = p alpha :=
    positionCoordinate_eq_of_interior_of_divisor_eq B q p hDiv.symm
  have hCard : P.card = Q.card := by
    simpa [P, Q] using paperTerminalSlots_card_eq_of_divisor_eq B p q hDiv
  have hSubset : P ⊆ Q := by
    intro alpha hAlphaP
    by_contra hAlphaQ
    have hpFull : (p alpha).val = B.length alpha := by
      simpa [P, paperTerminalSlots] using hAlphaP
    have hqNotFull : (q alpha).val ≠ B.length alpha := by
      simpa [Q, paperTerminalSlots] using hAlphaQ
    have hqNotInterior : ¬ IsPaperInteriorCoordinate B q alpha := by
      intro hInt
      have heq := hInteriorQ alpha hInt
      have hpBound := (p alpha).isLt
      change 0 < (q alpha).val ∧ (q alpha).val < B.length alpha at hInt
      rw [heq] at hInt
      omega
    have hqZero : (q alpha).val = 0 := by
      have hqBound := (q alpha).isLt
      change ¬ (0 < (q alpha).val ∧
        (q alpha).val < B.length alpha) at hqNotInterior
      omega
    have hExists : ∃ beta, beta ∈ Q ∧ beta ∉ P := by
      by_contra hNo
      push Not at hNo
      have hSubset : Q ⊆ P := fun beta hBeta => hNo beta hBeta
      have hEq : Q = P := Finset.eq_of_subset_of_card_le hSubset (by omega)
      exact hAlphaQ (hEq.symm ▸ hAlphaP)
    obtain ⟨beta, hBetaQ, hBetaP⟩ := hExists
    have hqFull : (q beta).val = B.length beta := by
      simpa [Q, paperTerminalSlots] using hBetaQ
    have hpNotFull : (p beta).val ≠ B.length beta := by
      simpa [P, paperTerminalSlots] using hBetaP
    have hpNotInterior : ¬ IsPaperInteriorCoordinate B p beta := by
      intro hInt
      have heq := hInteriorP beta hInt
      change 0 < (p beta).val ∧ (p beta).val < B.length beta at hInt
      rw [heq] at hInt
      omega
    have hpZero : (p beta).val = 0 := by
      have hpBound := (p beta).isLt
      change ¬ (0 < (p beta).val ∧
        (p beta).val < B.length beta) at hpNotInterior
      omega
    have hab := hp.2 alpha beta hpFull hpZero
    have hba := hq.2 beta alpha hqFull hqZero
    omega
  have hTerminal : P = Q :=
    Finset.eq_of_subset_of_card_le hSubset (by omega)
  funext alpha
  by_cases hpInt : IsPaperInteriorCoordinate B p alpha
  · exact hInteriorP alpha hpInt
  have hqInt : ¬ IsPaperInteriorCoordinate B q alpha := by
    intro hInt
    have heq := hInteriorQ alpha hInt
    change 0 < (q alpha).val ∧ (q alpha).val < B.length alpha at hInt
    rw [heq] at hInt
    change ¬ (0 < (p alpha).val ∧
      (p alpha).val < B.length alpha) at hpInt
    exact hpInt hInt
  by_cases hpFull : (p alpha).val = B.length alpha
  · have hpMem : alpha ∈ P := by simp [P, paperTerminalSlots, hpFull]
    have hqMem : alpha ∈ Q := hTerminal ▸ hpMem
    have hqFull : (q alpha).val = B.length alpha := by
      simpa [Q, paperTerminalSlots] using hqMem
    exact Fin.ext (hpFull.trans hqFull.symm)
  · have hpZero : (p alpha).val = 0 := by
      have hpBound := (p alpha).isLt
      change ¬ (0 < (p alpha).val ∧
        (p alpha).val < B.length alpha) at hpInt
      omega
    have hpNotMem : alpha ∉ P := by simp [P, paperTerminalSlots, hpFull]
    have hqNotMem : alpha ∉ Q := by simpa [hTerminal] using hpNotMem
    have hqNotFull : (q alpha).val ≠ B.length alpha := by
      simpa [Q, paperTerminalSlots] using hqNotMem
    have hqZero : (q alpha).val = 0 := by
      have hqBound := (q alpha).isLt
      change ¬ (0 < (q alpha).val ∧
        (q alpha).val < B.length alpha) at hqInt
      omega
    exact Fin.ext (hpZero.trans hqZero.symm)

/-- Full uniqueness/injectivity statement for Proposition 2.14. -/
theorem paperReducedPositionCoordinates_eq_mod_displayedRelations
    {g : ℕ} (B : Banana g)
    (p q : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hp : IsPaperReducedPositionCoordinates B p)
    (hq : IsPaperReducedPositionCoordinates B q)
    (hrel : bananaPositionCoordinates B p - bananaPositionCoordinates B q ∈
      bananaDisplayedRelations B) :
    p = q := by
  apply paperReducedPositionCoordinates_eq_of_divisor_eq B p q hp hq
  exact bananaPositionCoordinateDivisor_eq_of_paperReduced_mod_displayed
    B p q hp hq hrel

end Bananas
