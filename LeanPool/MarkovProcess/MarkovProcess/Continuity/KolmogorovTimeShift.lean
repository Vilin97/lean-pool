/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DyadicFloor

/-!
# Nonnegative-rational time shifts

This file translates a dense-time process by a nonnegative rational time.  Translation is an
isometry of `NNRat`, so the Kolmogorov increment condition is preserved with exactly the same
exponents and constant.  The final definitions and identities identify the unit-interval
dyadic samples and canonical limit for the shifted process with samples of the original process
on the interval starting at the shift.

No global path is glued here, and no measurability of the canonical limit or modification-law
assertion is made.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

variable {Ω E : Type*}

/-- Translate a dense-time process by a nonnegative rational time. -/
def timeShift (k : NNRat) (X : NNRat → Ω → E) : NNRat → Ω → E :=
  fun q ω ↦ X (k + q) ω

@[simp]
theorem timeShift_apply (k q : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    timeShift k X q ω = X (k + q) ω :=
  rfl

/-- Nonnegative-rational translation preserves the Kolmogorov condition without changing its
exponents or constant. -/
theorem IsKolmogorovProcess.timeShift
    {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (k : NNRat) :
    IsKolmogorovProcess (timeShift k X) P p q M where
  measurablePair s t := hX.measurablePair (k + s) (k + t)
  kolmogorovCondition s t := by
    have hdist : dist (k + s) (k + t) = dist s t := by
      rw [NNRat.dist_eq, NNRat.dist_eq, Rat.dist_eq, Rat.dist_eq]
      push_cast
      rw [add_sub_add_left_eq_sub]
    simpa only [timeShift, edist_dist, hdist] using!
      hX.kolmogorovCondition (k + s) (k + t)
  p_pos := hX.p_pos
  q_pos := hX.q_pos

/-- The level-`n` dyadic time in the unit interval, translated to the interval beginning at
`k`. -/
noncomputable def shiftedUnitDyadicFloorValue (k : NNRat) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) : NNRat :=
  k + unitDyadicFloorValue n t

theorem timeShift_unitDyadicFloorValue_apply
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) :
    timeShift k X (unitDyadicFloorValue n t) ω =
      X (shiftedUnitDyadicFloorValue k n t) ω :=
  rfl

noncomputable section

variable [PseudoMetricSpace E]

/-- The canonical unit-interval dyadic-floor limit of the process translated by `k`.  Its time
parameter represents the original interval `[k, k + 1]`. -/
def shiftedUnitDyadicFloorLimit (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    Set.Icc (0 : ℝ) 1 → E :=
  unitDyadicFloorLimit (timeShift k X) ω

@[simp]
theorem shiftedUnitDyadicFloorLimit_apply
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) (t : Set.Icc (0 : ℝ) 1) :
    shiftedUnitDyadicFloorLimit k X ω t = unitDyadicFloorLimit (timeShift k X) ω t :=
  rfl

variable [CompleteSpace E]

/-- Cauchy control of samples of the original process at translated dyadic times gives
convergence to the translated canonical unit-interval limit. -/
theorem tendsto_shiftedUnitDyadicFloorLimit_of_cauchySeq
    {k : NNRat} {X : NNRat → Ω → E} {ω : Ω} {t : Set.Icc (0 : ℝ) 1}
    (h : CauchySeq (fun n : ℕ ↦ X (shiftedUnitDyadicFloorValue k n t) ω)) :
    Tendsto (fun n : ℕ ↦ X (shiftedUnitDyadicFloorValue k n t) ω) atTop
      (nhds (shiftedUnitDyadicFloorLimit k X ω t)) := by
  simpa only [shiftedUnitDyadicFloorLimit, timeShift_unitDyadicFloorValue_apply] using
    tendsto_unitDyadicFloorLimit_of_cauchySeq
      (X := timeShift k X) (ω := ω) (t := t) h

end

end MarkovProcess
