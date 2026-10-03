/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# Indicator

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set
open scoped ENNReal


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The Morrey cylinder integral of a set indicator equals the integral restricted
to the intersection of the cylinder with the set. -/
theorem cylinderPowerIntegral_indicator {p : ℝ} (hp : 0 < p)
    {S : Set ParabolicPoint} (hS : MeasurableSet S)
    (g : ParabolicPoint → ℝ) (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral p (S.indicator g) z r =
      ∫⁻ w in parabolicCylinder z.1 z.2 r ∩ S, ENNReal.ofReal |g w| ^ p := by
  have heq : (fun w => ENNReal.ofReal |S.indicator g w| ^ p) =
      S.indicator (fun w => ENNReal.ofReal |g w| ^ p) := by
    funext w
    by_cases hw : w ∈ S
    · simp only [indicator_of_mem hw]
    · simp only [indicator_of_notMem hw, abs_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp]
  rw [cylinderPowerIntegral, heq, lintegral_indicator hS,
    Measure.restrict_restrict hS, inter_comm S]

end CKN.Foundation.Parabolic.Morrey
