/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianReductionTermination

/-!
# Finite left-justification of banana position coordinates

After the terminating length-reduction pass, coordinates are valid strand
positions and at least one is zero.  This module formalizes the paper's final
sorting pass: terminal coordinates move left of zero coordinates.  The sum of
the reverse indices of all zeros is a strictly decreasing natural measure.
-/

@[expose] public section

namespace Bananas

open Utilities

open scoped BigOperators

/-- A decreasing measure for the paper's final left-justification pass. -/
def bananaLeftJustifyMeasure {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha) : ℕ :=
  ∑ alpha : Fin (g + 1),
    if (p alpha).val = 0 then g + 1 - alpha.val else 0

theorem bananaLeftJustifyMeasure_swap_lt {g : ℕ} (B : Banana g)
    (p : ∀ gamma : Fin (g + 1), B.PathPosition gamma)
    (alpha beta : Fin (g + 1)) (hOrder : beta < alpha)
    (hFull : (p alpha).val = B.length alpha)
    (hZero : (p beta).val = 0) :
    bananaLeftJustifyMeasure B (bananaLeftJustifySwap B p alpha beta) <
      bananaLeftJustifyMeasure B p := by
  classical
  have hNe : alpha ≠ beta := ne_of_gt hOrder
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
  unfold bananaLeftJustifyMeasure
  rw [splitSum, splitSum]
  have hRest :
      ∑ gamma ∈ rest,
          (if (bananaLeftJustifySwap B p alpha beta gamma).val = 0 then
            g + 1 - gamma.val else 0) =
        ∑ gamma ∈ rest,
          (if (p gamma).val = 0 then g + 1 - gamma.val else 0) := by
    apply Finset.sum_congr rfl
    intro gamma hGamma
    have hGammaBeta : gamma ≠ beta := (Finset.mem_erase.mp hGamma).1
    have hGammaAlpha : gamma ≠ alpha :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hGamma).2).1
    rw [bananaLeftJustifySwap_at_other B p alpha beta gamma
      hGammaAlpha hGammaBeta]
  rw [hRest]
  have hFullNeZero : (p alpha).val ≠ 0 := by
    rw [hFull]
    exact Nat.ne_of_gt (B.length_pos alpha)
  simp only [bananaLeftJustifySwap_at_full, ↓reduceIte]
  rw [bananaLeftJustifySwap_at_zero B p alpha beta hNe.symm]
  rw [ite_eq_right (Nat.ne_of_gt (B.length_pos beta)), ite_eq_right hFullNeZero,
    ite_eq_left hZero]
  have hValues : beta.val < alpha.val := hOrder
  omega

/-- The strict decrease relation for the measure controlling left justification of strand
positions. -/
def bananaLeftJustifyDecreases {g : ℕ} (B : Banana g)
    (next current : ∀ alpha : Fin (g + 1), B.PathPosition alpha) : Prop :=
  bananaLeftJustifyMeasure B next < bananaLeftJustifyMeasure B current

theorem bananaLeftJustifyDecreases_wellFounded {g : ℕ} (B : Banana g) :
    WellFounded (bananaLeftJustifyDecreases B) := by
  exact (measure (bananaLeftJustifyMeasure B)).wf

/-- The finite left-justification pass terminates and produces the paper's
ordering convention, without leaving the displayed relation class. -/
theorem exists_paperReduced_of_positionCoordinates_with_zero
    {g : ℕ} (B : Banana g)
    (p : ∀ alpha : Fin (g + 1), B.PathPosition alpha)
    (hHasZero : ∃ alpha, (p alpha).val = 0) :
    ∃ q : ∀ alpha : Fin (g + 1), B.PathPosition alpha,
      IsPaperReducedPositionCoordinates B q ∧
      bananaPositionCoordinates B p - bananaPositionCoordinates B q ∈
        bananaDisplayedRelations B := by
  classical
  revert hHasZero
  apply (bananaLeftJustifyDecreases_wellFounded B).induction p
  intro current ih hCurrentZero
  by_cases hReduced : IsPaperReducedPositionCoordinates B current
  · exact ⟨current, hReduced, by simp⟩
  · have hBad : ∃ alpha beta, beta < alpha ∧
        (current alpha).val = B.length alpha ∧
        (current beta).val = 0 := by
      by_contra hNoBad
      exact hReduced ((isPaperReduced_iff_no_leftJustify_pair B current).2
        ⟨hCurrentZero, hNoBad⟩)
    obtain ⟨alpha, beta, hOrder, hFull, hZero⟩ := hBad
    let next := bananaLeftJustifySwap B current alpha beta
    have hDecrease : bananaLeftJustifyDecreases B next current :=
      bananaLeftJustifyMeasure_swap_lt B current alpha beta hOrder hFull hZero
    have hNextZero : ∃ gamma, (next gamma).val = 0 :=
      ⟨alpha, bananaLeftJustifySwap_at_full B current alpha beta⟩
    obtain ⟨terminal, hTerminalReduced, hNextTerminal⟩ :=
      ih next hDecrease hNextZero
    refine ⟨terminal, hTerminalReduced, ?_⟩
    have hCurrentNext :
        bananaPositionCoordinates B current - bananaPositionCoordinates B next ∈
          bananaDisplayedRelations B := by
      exact leftJustifySwap_mod_displayedRelations B current alpha beta hFull hZero
    have hCombined := (bananaDisplayedRelations B).add_mem
      hCurrentNext hNextTerminal
    convert hCombined using 1
    abel

/-- Full existence of the paper's preferred representative modulo the exact
displayed diagonal and strand-length lattice. -/
theorem exists_paperReducedPositionCoordinates_mod_displayedRelations
    {g : ℕ} (B : Banana g) (a : Fin (g + 1) → ℤ) :
    ∃ p : ∀ alpha : Fin (g + 1), B.PathPosition alpha,
      IsPaperReducedPositionCoordinates B p ∧
      a - bananaPositionCoordinates B p ∈ bananaDisplayedRelations B := by
  obtain ⟨initial, hInitialZero, hInitialRelation⟩ :=
    exists_positionCoordinates_with_zero_mod_displayedRelations B a
  obtain ⟨terminal, hTerminalReduced, hJustifyRelation⟩ :=
    exists_paperReduced_of_positionCoordinates_with_zero B initial hInitialZero
  refine ⟨terminal, hTerminalReduced, ?_⟩
  have hCombined := (bananaDisplayedRelations B).add_mem
    hInitialRelation hJustifyRelation
  convert hCombined using 1
  abel

end Bananas
