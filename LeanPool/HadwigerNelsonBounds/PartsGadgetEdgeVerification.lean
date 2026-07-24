/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetEdgeVerification0
import LeanPool.HadwigerNelsonBounds.PartsGadgetEdgeVerification1
import LeanPool.HadwigerNelsonBounds.PartsGadgetEdgeVerification2
import LeanPool.HadwigerNelsonBounds.PartsGadgetEdgeVerification3

/-! Aggregated edge-geometry checks for the finite gadget. -/

namespace HadwigerNelsonBounds

lemma partsGadget_edgeCase {vertex neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors vertex) :
    PartsGadgetEdgeCase vertex neighbor := by
  fin_cases vertex
  · exact partsGadgetEdgeCase0 hadj
  · exact partsGadgetEdgeCase1 hadj
  · exact partsGadgetEdgeCase2 hadj
  · exact partsGadgetEdgeCase3 hadj
  · exact partsGadgetEdgeCase4 hadj
  · exact partsGadgetEdgeCase5 hadj
  · exact partsGadgetEdgeCase6 hadj
  · exact partsGadgetEdgeCase7 hadj
  · exact partsGadgetEdgeCase8 hadj
  · exact partsGadgetEdgeCase9 hadj
  · exact partsGadgetEdgeCase10 hadj
  · exact partsGadgetEdgeCase11 hadj
  · exact partsGadgetEdgeCase12 hadj
  · exact partsGadgetEdgeCase13 hadj
  · exact partsGadgetEdgeCase14 hadj
  · exact partsGadgetEdgeCase15 hadj
  · exact partsGadgetEdgeCase16 hadj
  · exact partsGadgetEdgeCase17 hadj
  · exact partsGadgetEdgeCase18 hadj
  · exact partsGadgetEdgeCase19 hadj
  · exact partsGadgetEdgeCase20 hadj
  · exact partsGadgetEdgeCase21 hadj
  · exact partsGadgetEdgeCase22 hadj
  · exact partsGadgetEdgeCase23 hadj
  · exact partsGadgetEdgeCase24 hadj
  · exact partsGadgetEdgeCase25 hadj
  · exact partsGadgetEdgeCase26 hadj
  · exact partsGadgetEdgeCase27 hadj
  · exact partsGadgetEdgeCase28 hadj
  · exact partsGadgetEdgeCase29 hadj
  · exact partsGadgetEdgeCase30 hadj
  · exact partsGadgetEdgeCase31 hadj
  · exact partsGadgetEdgeCase32 hadj
  · exact partsGadgetEdgeCase33 hadj
  · exact partsGadgetEdgeCase34 hadj
  · exact partsGadgetEdgeCase35 hadj
  · exact partsGadgetEdgeCase36 hadj
  · exact partsGadgetEdgeCase37 hadj
  · exact partsGadgetEdgeCase38 hadj
  · exact partsGadgetEdgeCase39 hadj
  · exact partsGadgetEdgeCase40 hadj
  · exact partsGadgetEdgeCase41 hadj
  · exact partsGadgetEdgeCase42 hadj
  · exact partsGadgetEdgeCase43 hadj
  · exact partsGadgetEdgeCase44 hadj
  · exact partsGadgetEdgeCase45 hadj
  · exact partsGadgetEdgeCase46 hadj
  · exact partsGadgetEdgeCase47 hadj
  · exact partsGadgetEdgeCase48 hadj
  · exact partsGadgetEdgeCase49 hadj
  · exact partsGadgetEdgeCase50 hadj
  · exact partsGadgetEdgeCase51 hadj
  · exact partsGadgetEdgeCase52 hadj
  · exact partsGadgetEdgeCase53 hadj
  · exact partsGadgetEdgeCase54 hadj
  · exact partsGadgetEdgeCase55 hadj
  · exact partsGadgetEdgeCase56 hadj
  · exact partsGadgetEdgeCase57 hadj
  · exact partsGadgetEdgeCase58 hadj
  · exact partsGadgetEdgeCase59 hadj
  · exact partsGadgetEdgeCase60 hadj
  · exact partsGadgetEdgeCase61 hadj
  · exact partsGadgetEdgeCase62 hadj
  · exact partsGadgetEdgeCase63 hadj
  · exact partsGadgetEdgeCase64 hadj
  · exact partsGadgetEdgeCase65 hadj
  · exact partsGadgetEdgeCase66 hadj
  · exact partsGadgetEdgeCase67 hadj
  · exact partsGadgetEdgeCase68 hadj
  · exact partsGadgetEdgeCase69 hadj
  · exact partsGadgetEdgeCase70 hadj
  · exact partsGadgetEdgeCase71 hadj
  · exact partsGadgetEdgeCase72 hadj

end HadwigerNelsonBounds
