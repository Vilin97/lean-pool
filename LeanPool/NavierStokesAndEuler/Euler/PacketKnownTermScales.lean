/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownDecomposition
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceScales

/-! Every nonzero known summand fits strictly below its target forcing shift. -/

@[expose] public section


namespace EulerPacketCylinderField.KnownTerm

open EulerPacketShiftArithmetic

/-- Budget shift as an element of `ℕ`. -/
def budgetShift (k : KnownTerm) (p i j : ℕ) : ℕ :=
  match k with
  | .previousLinear | .previousPressure => if i=0 ∧ j=0 then highShift (p-1) else 0
  | .slow l r => if i+j=p ∧ l.active p i ∧ r.active p j then l.shift i+r.shift j+1 else 0
  | .fastMeanHigh =>
      if i+j=p+1 ∧ KnownPiece.mean.active p i ∧ KnownPiece.high.active p j then
        KnownPiece.mean.shift i+KnownPiece.high.shift j+1 else 0
  | .fastMeanCorrector =>
      if i+j=p+1 ∧ KnownPiece.mean.active p i ∧ KnownPiece.corrector.active p j then
        KnownPiece.mean.shift i+KnownPiece.corrector.shift j+1 else 0
  | .fastCorrectorHigh =>
      if i+j=p+1 ∧ KnownPiece.corrector.active p i ∧ KnownPiece.high.active p j then
        KnownPiece.corrector.shift i+KnownPiece.high.shift j+1 else 0
  | .fastCorrectorCorrector =>
      if i+j=p+1 ∧ KnownPiece.corrector.active p i ∧ KnownPiece.corrector.active p j then
        KnownPiece.corrector.shift i+KnownPiece.corrector.shift j+1 else 0

private theorem previous_shift_lt (p : ℕ) (hp : 2 ≤ p) : highShift (p-1) < meanForceShift p := by
  have h := previous_linear_room p hp
  omega

theorem budgetShift_lt_mean (k : KnownTerm) (p i j : ℕ) (hp : 2 ≤ p)
    (hk : k.zeroMean = false) : k.budgetShift p i j < meanForceShift p := by
  have hpos : 0 < meanForceShift p := by have h := force_shift_dominates_grade p hp; omega
  cases k with
  | previousLinear =>
      simp only [budgetShift]
      split_ifs <;> first | exact previous_shift_lt p hp | exact hpos
  | previousPressure =>
      simp only [budgetShift]
      split_ifs <;> first | exact previous_shift_lt p hp | exact hpos
  | slow l r =>
      simp only [budgetShift]
      split_ifs with h
      · exact KnownPiece.slow_shift_room l r i j p (l.active_one_le p i h.2.1)
          (r.active_one_le p j h.2.2) h.1
      · exact hpos
  | fastMeanHigh => simp [zeroMean] at hk
  | fastMeanCorrector => simp [zeroMean] at hk
  | fastCorrectorHigh =>
      simp only [budgetShift]
      split_ifs with h
      · exact KnownPiece.fast_corrector_shift_room .high i j p h.2.1.1 h.2.2.1 h.1
      · exact hpos
  | fastCorrectorCorrector =>
      simp only [budgetShift]
      split_ifs with h
      · exact KnownPiece.fast_corrector_shift_room .corrector i j p h.2.1.1
          (KnownPiece.active_one_le .corrector p j h.2.2) h.1
      · exact hpos

theorem budgetShift_lt_high (k : KnownTerm) (p i j : ℕ) (hp : 2 ≤ p) :
    k.budgetShift p i j < highForceShift p := by
  by_cases hk : k.zeroMean = false
  · exact lt_of_lt_of_le (k.budgetShift_lt_mean p i j hp hk) (mean_force_le_high_force p)
  have hpos : 0 < highForceShift p := by have h := force_shift_dominates_grade p hp; omega
  cases k <;> simp only [zeroMean, not_true_eq_false] at hk
  all_goals simp only [budgetShift]
  all_goals split_ifs with h
  · exact KnownPiece.fast_mean_shift_room .high i j p h.2.1.1 h.2.2.1 h.1
  · exact hpos
  · exact KnownPiece.fast_mean_shift_room .corrector i j p h.2.1.1
      (KnownPiece.active_one_le .corrector p j h.2.2) h.1
  · exact hpos

end EulerPacketCylinderField.KnownTerm
