/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.KolmogorovTimeShift
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DyadicFloor

/-!
# Continuous modifications on shifted unit intervals

This file applies the unit-interval totalization to a nonnegative-rational time shift.  It also
identifies the endpoints of the underlying canonical limit exactly, for every sample, using the
eventual constancy of dyadic approximations at dyadic grid times.

No global path is glued here, and no path-space measurability, law, or Hunt-process property is
asserted.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The total continuous unit path obtained from the process translated by `k`.  Its local time
parameter represents the original interval `[k, k + 1]`. -/
def continuousShiftedUnitDyadicFloorLimit
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) : Set.Icc (0 : ℝ) 1 → E :=
  continuousUnitDyadicFloorLimit (timeShift k X) ω

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Every shifted totalized unit path is continuous. -/
theorem continuous_continuousShiftedUnitDyadicFloorLimit
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    Continuous (continuousShiftedUnitDyadicFloorLimit k X ω) := by
  exact continuous_continuousUnitDyadicFloorLimit (timeShift k X) ω

/-- At each fixed rational local time, the shifted total path is a modification of the original
process at the translated time `k + t`. -/
theorem IsKolmogorovProcess.ae_eq_continuousShiftedUnitDyadicFloorLimit
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (k t : NNRat) (ht : t ≤ 1) :
    X (k + t) =ᵐ[P] fun ω ↦
      continuousShiftedUnitDyadicFloorLimit k X ω (unitIccOfNNRat t ht) := by
  simpa only [continuousShiftedUnitDyadicFloorLimit, timeShift_apply] using!
    IsKolmogorovProcess.ae_eq_continuousUnitDyadicFloorLimit
      (IsKolmogorovProcess.timeShift hX k) hγ hγq t ht

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- At every dyadic grid time, the shifted canonical limit is exactly the corresponding sample
of the original process.  This is a pointwise identity for every `ω`, not an almost-sure one. -/
theorem shiftedUnitDyadicFloorLimit_gridTime_eq_sample
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω)
    (n : ℕ) (i : Fin (2 ^ n + 1)) :
    shiftedUnitDyadicFloorLimit k X ω (unitDyadicGridTime n i) =
      X (k + unitDyadicGrid n i) ω := by
  have hevent :=
    eventually_sample_unitDyadicFloorValue_gridTime (timeShift k X) n i ω
  have htendsto : Tendsto
      (fun m ↦ timeShift k X
        (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω)
      atTop (nhds (timeShift k X (unitDyadicGrid n i) ω)) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ hm ↦ hm.symm)
  have hcanonical := tendsto_unitDyadicFloorLimit_of_cauchySeq htendsto.cauchySeq
  exact eq_sample_of_tendsto_unitDyadicFloorValue_gridTime
    (timeShift k X) n i ω (shiftedUnitDyadicFloorLimit k X ω (unitDyadicGridTime n i))
    (by simpa only [shiftedUnitDyadicFloorLimit] using hcanonical)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The local zero endpoint of a shifted canonical unit path is exactly the sample at `k`. -/
theorem shiftedUnitDyadicFloorLimit_zero
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    shiftedUnitDyadicFloorLimit k X ω (0 : Set.Icc (0 : ℝ) 1) = X k ω := by
  let i : Fin (2 ^ 0 + 1) := ⟨0, by norm_num⟩
  have htime : unitDyadicGridTime 0 i = (0 : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    norm_num [unitDyadicGridTime, unitDyadicGrid, i]
  rw [← htime]
  simpa only [unitDyadicGrid, i, Nat.cast_zero, zero_div, add_zero] using
    shiftedUnitDyadicFloorLimit_gridTime_eq_sample k X ω 0 i

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The local one endpoint of a shifted canonical unit path is exactly the sample at `k + 1`. -/
theorem shiftedUnitDyadicFloorLimit_one
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    shiftedUnitDyadicFloorLimit k X ω (1 : Set.Icc (0 : ℝ) 1) = X (k + 1) ω := by
  let i : Fin (2 ^ 0 + 1) := ⟨1, by norm_num⟩
  have htime : unitDyadicGridTime 0 i = (1 : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    norm_num [unitDyadicGridTime, unitDyadicGrid, i]
  rw [← htime]
  simpa only [unitDyadicGrid, i, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, pow_zero,
    div_one] using shiftedUnitDyadicFloorLimit_gridTime_eq_sample k X ω 0 i

end

end MarkovProcess

end PortComputability
