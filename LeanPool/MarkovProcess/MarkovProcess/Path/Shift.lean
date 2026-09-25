/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.Basic


/-!
# Deterministic shifts of continuous paths

This file defines translation by a fixed nonnegative time on canonical continuous-path space.
The shift is jointly continuous in the shift time and path for the compact-open topology.  It also
records the corresponding deterministic relation between the canonical filtrations.

No random-time shift, Markov property, strong Markov property, or Hunt-process assertion is made.
-/

@[expose] public section

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Translation of nonnegative time by `S`, as a continuous self-map of `NNReal`. -/
def timeTranslation (S : NNReal) : C(NNReal, NNReal) where
  toFun t := S + t
  continuous_toFun := continuous_const.add continuous_id

@[simp]
theorem timeTranslation_apply (S t : NNReal) : timeTranslation S t = S + t := rfl

/-- Shift a continuous path forward by the deterministic time `S`. -/
def shift (S : NNReal) (omega : ContinuousPath alpha) : ContinuousPath alpha :=
  omega.comp (timeTranslation S)

@[simp]
theorem shift_apply (S t : NNReal) (omega : ContinuousPath alpha) :
    shift S omega t = omega (S + t) := rfl

@[simp]
theorem shift_zero (omega : ContinuousPath alpha) : shift 0 omega = omega := by
  ext t
  simp only [shift_apply, zero_add]

theorem shift_add (S T : NNReal) (omega : ContinuousPath alpha) :
    shift T (shift S omega) = shift (S + T) omega := by
  ext t
  simp only [shift_apply, add_assoc]

/-- The family of time translations is continuous for the compact-open topology. -/
theorem continuous_timeTranslation : Continuous (timeTranslation : NNReal → C(NNReal, NNReal)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_fst.add continuous_snd

/-- Deterministic path shifting is jointly continuous in the shift time and the path. -/
theorem continuous_shift :
    Continuous (fun p : NNReal × ContinuousPath alpha ↦ shift p.1 p.2) := by
  exact ContinuousMap.continuous_comp'.comp
    ((continuous_timeTranslation.comp continuous_fst).prodMk continuous_snd)

/-- Shifting by a fixed deterministic time is continuous. -/
theorem continuous_shift_fixed (S : NNReal) :
    Continuous (shift S : ContinuousPath alpha → ContinuousPath alpha) :=
  continuous_shift.comp (continuous_const.prodMk continuous_id)

/-- Shifting by a fixed deterministic time is Borel measurable. -/
theorem measurable_shift_fixed (S : NNReal) :
    Measurable[borel (ContinuousPath alpha), borel (ContinuousPath alpha)]
      (shift S : ContinuousPath alpha → ContinuousPath alpha) :=
  (continuous_shift_fixed S).borel_measurable

/-- A shifted event observable by shifted time `t` is observable by original time `S + t`. -/
theorem measurable_shift_canonicalFiltration [MeasurableSpace alpha] [BorelSpace alpha]
    (S t : NNReal) :
    Measurable[canonicalFiltration (alpha := alpha) (S + t),
      canonicalFiltration (alpha := alpha) t]
      (shift S : ContinuousPath alpha → ContinuousPath alpha) := by
  apply Measurable.of_comap_le
  rw [canonicalFiltration, MeasurableSpace.comap_iSup]
  rw [iSup_le_iff]
  intro u
  rw [MeasurableSpace.comap_comp]
  have hfun : coordinateProcess (alpha := alpha) u ∘ shift S =
      coordinateProcess (alpha := alpha) (S + u) := by
    funext omega
    exact shift_apply S u omega
  rw [hfun]
  exact le_iSup_of_le
    (⟨S + u.1, by
      exact add_le_add (le_refl S) (show (u : NNReal) ≤ t from u.property)⟩ :
      Set.Iic (S + t)) le_rfl

end ContinuousPath
end MarkovProcess
