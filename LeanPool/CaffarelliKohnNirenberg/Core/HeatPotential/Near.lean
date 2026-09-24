/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Exponents
public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Morrey
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge

/-!
# Near

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

/-!
The source block used for the local part of a heat potential.  The radius is
written with the gauge `parabolicRho₂`, whose time component is symmetric;
this is the geometry needed for a genuine parabolic metric ball.
-/
def heatPotentialNearSet (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  {v | parabolicRho₂ z v < (64 : ℝ) * r}




end CKN.Core.HeatPotential
