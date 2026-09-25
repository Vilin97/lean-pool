/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamCharacteristicConverse
public import LeanPool.DavisKahan.DavisKahan.Analysis.FourthOrderODE.SmoothGreenIdentity
public import Mathlib.Tactic

/-!
# Classical characteristic modes as fourth-order derivative data

This file connects the closed-form mode calculations to the smooth Green and
kernel infrastructure.  A characteristic root now produces a concrete
`FourthOrderData` object satisfying the free conditions and the fourth-order
eigen-equation.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Classical

noncomputable section

open FreeBeam

/-- The real closed-form beam mode bundled with all four derivative
relations. -/
noncomputable def modeData (beta a b c d : ℝ) : FourthOrderData where
  f0 := FreeBeam.mode beta a b c d
  f1 := FreeBeam.modeD1 beta a b c d
  f2 := FreeBeam.modeD2 beta a b c d
  f3 := FreeBeam.modeD3 beta a b c d
  f4 := FreeBeam.modeD4 beta a b c d
  continuous0 := continuous_iff_continuousAt.mpr fun x =>
    (FreeBeam.hasDerivAt_mode beta a b c d x).continuousAt
  continuous1 := continuous_iff_continuousAt.mpr fun x =>
    (FreeBeam.hasDerivAt_modeD1 beta a b c d x).continuousAt
  continuous2 := continuous_iff_continuousAt.mpr fun x =>
    (FreeBeam.hasDerivAt_modeD2 beta a b c d x).continuousAt
  continuous3 := continuous_iff_continuousAt.mpr fun x =>
    (FreeBeam.hasDerivAt_modeD3 beta a b c d x).continuousAt
  continuous4 := by
    unfold FreeBeam.modeD4
    exact continuous_const.mul
      (continuous_iff_continuousAt.mpr fun x =>
        (FreeBeam.hasDerivAt_mode beta a b c d x).continuousAt)
  deriv0 := FreeBeam.hasDerivAt_mode beta a b c d
  deriv1 := FreeBeam.hasDerivAt_modeD1 beta a b c d
  deriv2 := FreeBeam.hasDerivAt_modeD2 beta a b c d
  deriv3 := FreeBeam.hasDerivAt_modeD3 beta a b c d

/-- The bundled mode data reproduces the mode itself in slot `f0`. -/
@[simp] theorem modeData_f0 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f0 x =
      FreeBeam.mode beta a b c d x := rfl

/-- Slot `f1` of the bundled mode data is the first derivative of the mode. -/
@[simp] theorem modeData_f1 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f1 x =
      FreeBeam.modeD1 beta a b c d x := rfl

/-- Slot `f2` of the bundled mode data is the second derivative of the mode. -/
@[simp] theorem modeData_f2 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f2 x =
      FreeBeam.modeD2 beta a b c d x := rfl

/-- Slot `f3` of the bundled mode data is the third derivative of the mode. -/
@[simp] theorem modeData_f3 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f3 x =
      FreeBeam.modeD3 beta a b c d x := rfl

/-- Slot `f4` of the bundled mode data is the fourth derivative of the mode. -/
@[simp] theorem modeData_f4 (beta a b c d x : ℝ) :
    (modeData beta a b c d).f4 x =
      FreeBeam.modeD4 beta a b c d x := rfl

/-- The bundled and unbundled free boundary predicates agree exactly. -/
theorem modeData_freeBoundary_iff (beta a b c d : ℝ) :
    (modeData beta a b c d).FreeBoundary ↔
      FreeBeam.FreeBoundary beta a b c d := by
  rfl

/-- Every bundled mode satisfies the fourth-order eigen-equation. -/
theorem modeData_eigen_equation (beta a b c d x : ℝ) :
    (modeData beta a b c d).f4 x =
      beta ^ 4 * (modeData beta a b c d).f0 x := by
  rfl

/-- Initial value of the identified-coefficient mode. -/
theorem mode_identified_value_zero (beta a b : ℝ) :
    FreeBeam.mode beta a b a b 0 = 2 * a := by
  simp [FreeBeam.mode]
  ring

/-- Initial derivative of the identified-coefficient mode. -/
theorem modeD1_identified_value_zero (beta a b : ℝ) :
    FreeBeam.modeD1 beta a b a b 0 =
      2 * beta * b := by
  simp [FreeBeam.modeD1]
  ring

/-- A nonzero reduced coefficient vector at nonzero frequency has a nonzero
initial position-or-velocity jet. -/
theorem mode_identified_nontrivial_jet
    {beta a b : ℝ} (hbeta : beta ≠ 0)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    (modeData beta a b a b).f0 0 ≠ 0 ∨
      (modeData beta a b a b).f1 0 ≠ 0 := by
  rcases hab with ha | hb
  · left
    rw [modeData_f0, mode_identified_value_zero]
    exact mul_ne_zero (by norm_num) ha
  · right
    rw [modeData_f1, modeD1_identified_value_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hbeta) hb

/-- A characteristic root produces a concrete free fourth-order datum with a
nonzero initial jet. -/
theorem exists_free_modeData_of_characteristic
    {beta : ℝ} (hbeta : beta ≠ 0)
    (hroot : FreeBeam.characteristic beta = 0) :
    ∃ u : FourthOrderData,
      u.FreeBoundary ∧
      (∀ x, u.f4 x = beta ^ 4 * u.f0 x) ∧
      (u.f0 0 ≠ 0 ∨ u.f1 0 ≠ 0) := by
  obtain ⟨a, b, hab, hfree⟩ :=
    exists_nontrivial_freeBoundary_of_characteristic hbeta hroot
  refine ⟨modeData beta a b a b, ?_, ?_, ?_⟩
  · exact (modeData_freeBoundary_iff beta a b a b).mpr hfree
  · exact modeData_eigen_equation beta a b a b
  · exact mode_identified_nontrivial_jet hbeta hab

/-- Positive characteristic roots produce nonzero smooth eigenvalues above
`500` once the scalar localization interface is supplied. -/
theorem free_modeData_eigenvalue_gt_five_hundred
    (L : FreeBeam.PositiveRootLocalization)
    {beta : ℝ} (hbeta : 0 < beta)
    (hroot : FreeBeam.characteristic beta = 0) :
    ∃ u : FourthOrderData,
      u.FreeBoundary ∧
      (∀ x, u.f4 x = beta ^ 4 * u.f0 x) ∧
      (u.f0 0 ≠ 0 ∨ u.f1 0 ≠ 0) ∧
      500 < beta ^ 4 := by
  obtain ⟨u, hu, heig, hnonzero⟩ :=
    exists_free_modeData_of_characteristic hbeta.ne' hroot
  exact ⟨u, hu, heig, hnonzero,
    FreeBeam.positive_root_fourth_power_gt_five_hundred
      L hbeta hroot⟩

end

end Classical
end FreeBeam
end DavisKahan
end TauCeti
