/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPHarmonicCells
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative

/-!
# Pressure Gradient Origin KPHarmonic Small Cells

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4
/-- The source collar is never smaller than one quarter, while its half-ball
contains the tested small cell. -/
def originHarmonicCellRadius (r : ℝ) : ℝ := max (1/4) (2*r)

end CKN.Core.Step4
