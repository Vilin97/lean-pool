/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTime
public import LeanPool.MarkovProcess.MarkovProcess.Path.Shift


/-!
# Exit times under shifts

Path-space identities relating the exit time `ContinuousPath.exitTime U` of an open set to the
shift `ContinuousPath.shift t`, and the measurability of the survival events they generate.

* `exitTime_shift_add`: before the exit time, shifting by `t` subtracts `t` from the exit time,
  `τ(θ_t ω) + t = τ(ω)` whenever `t < τ(ω)`;
* `coe_add_lt_exitTime_iff`: the event identity `{t + s < τ} = {t < τ} ∩ {s < τ ∘ θ_t}`, which is
  the Chapman--Kolmogorov identity for the process killed at `τ`;
* `measurableSet_lt_exitTime_canonicalFiltration`, `measurableSet_lt_exitTime`,
  `measurable_exitTime`: the survival event `{t < τ}` is measurable for the canonical filtration
  at time `t`, and the exit time is a Borel function on path space.

Nothing here involves a probability law.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

section Shift

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- A bound `a ≤ exitTime U omega` holds exactly when `a ≤ v` at every time `v` at which the
path is outside `U`. -/
theorem le_exitTime_iff (U : Set alpha) (omega : ContinuousPath alpha) (a : ℝ≥0∞) :
    a ≤ exitTime U omega ↔ ∀ v : NNReal, omega v ∉ U → a ≤ (v : ℝ≥0∞) := by
  rw [exitTime, le_sInf_iff]
  constructor
  · intro h v hv
    exact h _ ⟨v, rfl, hv⟩
  · rintro h _ ⟨v, rfl, hv⟩
    exact h v hv

/-- Before the exit time, shifting by `t` subtracts `t` from the exit time:
`exitTime U (shift t omega) + t = exitTime U omega` whenever `t < exitTime U omega`. -/
theorem exitTime_shift_add (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) < exitTime U omega) :
    exitTime U (shift t omega) + t = exitTime U omega := by
  apply le_antisymm
  · rw [le_exitTime_iff]
    intro v hv
    have hle : exitTime U omega ≤ v := exitTime_le_of_notMem U omega v hv
    have htv : t ≤ v := ENNReal.coe_le_coe.mp (ht.trans_le hle).le
    have hbad : shift t omega (v - t) ∉ U := by
      rw [shift_apply, add_tsub_cancel_of_le htv]
      exact hv
    calc exitTime U (shift t omega) + (t : ℝ≥0∞) ≤ ((v - t : NNReal) : ℝ≥0∞) + t :=
          add_le_add (exitTime_le_of_notMem U (shift t omega) (v - t) hbad) le_rfl
      _ = v := by rw [← ENNReal.coe_add, tsub_add_cancel_of_le htv]
  · rw [← tsub_le_iff_right, le_exitTime_iff]
    intro u hu
    have hle : exitTime U omega ≤ ((t + u : NNReal) : ℝ≥0∞) :=
      exitTime_le_of_notMem U omega (t + u) hu
    rw [tsub_le_iff_right, ← ENNReal.coe_add, add_comm]
    exact hle

/-- The event identity `{t + s < τ} = {t < τ} ∩ {s < τ ∘ θ_t}` for the exit time `τ` of `U`. -/
theorem coe_add_lt_exitTime_iff (U : Set alpha) (omega : ContinuousPath alpha) (t s : NNReal) :
    ((t + s : NNReal) : ℝ≥0∞) < exitTime U omega ↔
      (t : ℝ≥0∞) < exitTime U omega ∧ (s : ℝ≥0∞) < exitTime U (shift t omega) := by
  constructor
  · intro h
    have ht : (t : ℝ≥0∞) < exitTime U omega :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.mpr le_self_add) h
    refine ⟨ht, ?_⟩
    rw [← exitTime_shift_add U omega t ht, ENNReal.coe_add, add_comm] at h
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).mp h
  · rintro ⟨ht, hs⟩
    rw [← exitTime_shift_add U omega t ht, ENNReal.coe_add, add_comm]
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).mpr hs

end Shift

section Measurable

variable {alpha : Type*} [PseudoMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The survival event `{t < exitTime U}` of an open set is measurable for the canonical
filtration at time `t`. -/
theorem measurableSet_lt_exitTime_canonicalFiltration (U : Set alpha) (hU : IsOpen U)
    (t : NNReal) :
    MeasurableSet[canonicalFiltration (alpha := alpha) t]
      {omega : ContinuousPath alpha | (t : ℝ≥0∞) < exitTime U omega} := by
  have hcompl : {omega : ContinuousPath alpha | (t : ℝ≥0∞) < exitTime U omega} =
      {omega : ContinuousPath alpha | exitTimeTop U omega ≤ (t : WithTop NNReal)}ᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    exact Iff.rfl
  rw [hcompl]
  exact (isStoppingTime_exitTime U hU t).compl

/-- The survival event `{t < exitTime U}` of an open set is a Borel set of path space. -/
theorem measurableSet_lt_exitTime (U : Set alpha) (hU : IsOpen U) (t : NNReal) :
    MeasurableSet {omega : ContinuousPath alpha | (t : ℝ≥0∞) < exitTime U omega} :=
  (canonicalFiltration (alpha := alpha)).le t _
    (measurableSet_lt_exitTime_canonicalFiltration U hU t)

/-- The exit time of an open set is a Borel function on path space. -/
theorem measurable_exitTime (U : Set alpha) (hU : IsOpen U) :
    Measurable (exitTime U : ContinuousPath alpha → ℝ≥0∞) := by
  refine measurable_of_Ioi fun a ↦ ?_
  induction a with
  | top =>
    have h : (exitTime U : ContinuousPath alpha → ℝ≥0∞) ⁻¹' Set.Ioi ⊤ = ∅ := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_Ioi, not_top_lt, Set.mem_empty_iff_false]
    rw [h]
    exact MeasurableSet.empty
  | coe t =>
    exact measurableSet_lt_exitTime U hU t

end Measurable

end MarkovProcess.ContinuousPath
