/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralBivariateAffineHasseWeil
public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.WeilFromGeneralHasse
public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Nonsplit.HasseFromGeneral
public import LeanPool.MarkoffModP.BGS.Markoff.Cage.EstimateFromPlane
public import LeanPool.MarkoffModP.BGS.Markoff.Cage.PlaneHasseWeil

/-!
# Fixed point-count estimates for explicit strong approximation

The general affine Hasse--Weil theorem in this repository has coefficient
`8`.  This file records, without existentially choosing any constants, the
four numerical specializations used by the explicit Markoff argument.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The fixed split trace estimate obtained from affine coefficient `8`. -/
theorem weightedSplitTraceWeilBoundAssumption_thirtyThree :
    WeightedSplitTraceWeilBoundAssumption 33 := by
  simpa using
    weightedSplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound 8
      BGS.HasseWeil.bivariateAffineHasseWeilBound_eight

/-- The fixed nonsplit trace estimate obtained from affine coefficient `8`. -/
theorem seededNonsplitTraceWeilBoundAssumption_thirtyFour :
    SeededNonsplitTraceWeilBoundAssumption 34 := by
  simpa using
    seededNonsplitTraceWeilBoundAssumption_of_bivariateAffineHasseWeilBound 8
      BGS.HasseWeil.bivariateAffineHasseWeilBound_eight

/-- The fixed cage-plane estimate obtained from affine coefficient `8`. -/
theorem cagePlanePointEstimate_twoHundredFiftySix :
    CagePlanePointEstimate 256 := by
  simpa using
    cagePlanePointEstimate_of_bivariateAffineHasseWeilBound 8
      BGS.HasseWeil.bivariateAffineHasseWeilBound_eight

/-- The resulting fixed cage-witness estimate. -/
theorem cageWitnessPointEstimate_oneHundredThousandFiveHundredTwentyTwo :
    CageWitnessPointEstimate 100522 := by
  simpa using
    cageWitnessPointEstimate_of_cagePlanePointEstimate 256
      cagePlanePointEstimate_twoHundredFiftySix

end

end BGS.Markoff
