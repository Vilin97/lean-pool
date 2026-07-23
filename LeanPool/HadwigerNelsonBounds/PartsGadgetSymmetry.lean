/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetSymmetry0
import LeanPool.HadwigerNelsonBounds.PartsGadgetSymmetry1
import LeanPool.HadwigerNelsonBounds.PartsGadgetSymmetry2
import LeanPool.HadwigerNelsonBounds.PartsGadgetSymmetry3

/-! Aggregated central-inversion facts for the finite gadget. -/

namespace HadwigerNelsonBounds

lemma partsGadgetNegation_neighbor {vertex neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors vertex) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation vertex) := by
  fin_cases vertex
  · exact partsGadgetNegationNeighbor0 hadj
  · exact partsGadgetNegationNeighbor1 hadj
  · exact partsGadgetNegationNeighbor2 hadj
  · exact partsGadgetNegationNeighbor3 hadj
  · exact partsGadgetNegationNeighbor4 hadj
  · exact partsGadgetNegationNeighbor5 hadj
  · exact partsGadgetNegationNeighbor6 hadj
  · exact partsGadgetNegationNeighbor7 hadj
  · exact partsGadgetNegationNeighbor8 hadj
  · exact partsGadgetNegationNeighbor9 hadj
  · exact partsGadgetNegationNeighbor10 hadj
  · exact partsGadgetNegationNeighbor11 hadj
  · exact partsGadgetNegationNeighbor12 hadj
  · exact partsGadgetNegationNeighbor13 hadj
  · exact partsGadgetNegationNeighbor14 hadj
  · exact partsGadgetNegationNeighbor15 hadj
  · exact partsGadgetNegationNeighbor16 hadj
  · exact partsGadgetNegationNeighbor17 hadj
  · exact partsGadgetNegationNeighbor18 hadj
  · exact partsGadgetNegationNeighbor19 hadj
  · exact partsGadgetNegationNeighbor20 hadj
  · exact partsGadgetNegationNeighbor21 hadj
  · exact partsGadgetNegationNeighbor22 hadj
  · exact partsGadgetNegationNeighbor23 hadj
  · exact partsGadgetNegationNeighbor24 hadj
  · exact partsGadgetNegationNeighbor25 hadj
  · exact partsGadgetNegationNeighbor26 hadj
  · exact partsGadgetNegationNeighbor27 hadj
  · exact partsGadgetNegationNeighbor28 hadj
  · exact partsGadgetNegationNeighbor29 hadj
  · exact partsGadgetNegationNeighbor30 hadj
  · exact partsGadgetNegationNeighbor31 hadj
  · exact partsGadgetNegationNeighbor32 hadj
  · exact partsGadgetNegationNeighbor33 hadj
  · exact partsGadgetNegationNeighbor34 hadj
  · exact partsGadgetNegationNeighbor35 hadj
  · exact partsGadgetNegationNeighbor36 hadj
  · exact partsGadgetNegationNeighbor37 hadj
  · exact partsGadgetNegationNeighbor38 hadj
  · exact partsGadgetNegationNeighbor39 hadj
  · exact partsGadgetNegationNeighbor40 hadj
  · exact partsGadgetNegationNeighbor41 hadj
  · exact partsGadgetNegationNeighbor42 hadj
  · exact partsGadgetNegationNeighbor43 hadj
  · exact partsGadgetNegationNeighbor44 hadj
  · exact partsGadgetNegationNeighbor45 hadj
  · exact partsGadgetNegationNeighbor46 hadj
  · exact partsGadgetNegationNeighbor47 hadj
  · exact partsGadgetNegationNeighbor48 hadj
  · exact partsGadgetNegationNeighbor49 hadj
  · exact partsGadgetNegationNeighbor50 hadj
  · exact partsGadgetNegationNeighbor51 hadj
  · exact partsGadgetNegationNeighbor52 hadj
  · exact partsGadgetNegationNeighbor53 hadj
  · exact partsGadgetNegationNeighbor54 hadj
  · exact partsGadgetNegationNeighbor55 hadj
  · exact partsGadgetNegationNeighbor56 hadj
  · exact partsGadgetNegationNeighbor57 hadj
  · exact partsGadgetNegationNeighbor58 hadj
  · exact partsGadgetNegationNeighbor59 hadj
  · exact partsGadgetNegationNeighbor60 hadj
  · exact partsGadgetNegationNeighbor61 hadj
  · exact partsGadgetNegationNeighbor62 hadj
  · exact partsGadgetNegationNeighbor63 hadj
  · exact partsGadgetNegationNeighbor64 hadj
  · exact partsGadgetNegationNeighbor65 hadj
  · exact partsGadgetNegationNeighbor66 hadj
  · exact partsGadgetNegationNeighbor67 hadj
  · exact partsGadgetNegationNeighbor68 hadj
  · exact partsGadgetNegationNeighbor69 hadj
  · exact partsGadgetNegationNeighbor70 hadj
  · exact partsGadgetNegationNeighbor71 hadj
  · exact partsGadgetNegationNeighbor72 hadj

lemma partsGadgetNegation_triple {vertex : Fin 73}
    {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs vertex) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation vertex) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation vertex) := by
  fin_cases vertex
  · exact partsGadgetNegationTriple0 hpair
  · exact partsGadgetNegationTriple1 hpair
  · exact partsGadgetNegationTriple2 hpair
  · exact partsGadgetNegationTriple3 hpair
  · exact partsGadgetNegationTriple4 hpair
  · exact partsGadgetNegationTriple5 hpair
  · exact partsGadgetNegationTriple6 hpair
  · exact partsGadgetNegationTriple7 hpair
  · exact partsGadgetNegationTriple8 hpair
  · exact partsGadgetNegationTriple9 hpair
  · exact partsGadgetNegationTriple10 hpair
  · exact partsGadgetNegationTriple11 hpair
  · exact partsGadgetNegationTriple12 hpair
  · exact partsGadgetNegationTriple13 hpair
  · exact partsGadgetNegationTriple14 hpair
  · exact partsGadgetNegationTriple15 hpair
  · exact partsGadgetNegationTriple16 hpair
  · exact partsGadgetNegationTriple17 hpair
  · exact partsGadgetNegationTriple18 hpair
  · exact partsGadgetNegationTriple19 hpair
  · exact partsGadgetNegationTriple20 hpair
  · exact partsGadgetNegationTriple21 hpair
  · exact partsGadgetNegationTriple22 hpair
  · exact partsGadgetNegationTriple23 hpair
  · exact partsGadgetNegationTriple24 hpair
  · exact partsGadgetNegationTriple25 hpair
  · exact partsGadgetNegationTriple26 hpair
  · exact partsGadgetNegationTriple27 hpair
  · exact partsGadgetNegationTriple28 hpair
  · exact partsGadgetNegationTriple29 hpair
  · exact partsGadgetNegationTriple30 hpair
  · exact partsGadgetNegationTriple31 hpair
  · exact partsGadgetNegationTriple32 hpair
  · exact partsGadgetNegationTriple33 hpair
  · exact partsGadgetNegationTriple34 hpair
  · exact partsGadgetNegationTriple35 hpair
  · exact partsGadgetNegationTriple36 hpair
  · exact partsGadgetNegationTriple37 hpair
  · exact partsGadgetNegationTriple38 hpair
  · exact partsGadgetNegationTriple39 hpair
  · exact partsGadgetNegationTriple40 hpair
  · exact partsGadgetNegationTriple41 hpair
  · exact partsGadgetNegationTriple42 hpair
  · exact partsGadgetNegationTriple43 hpair
  · exact partsGadgetNegationTriple44 hpair
  · exact partsGadgetNegationTriple45 hpair
  · exact partsGadgetNegationTriple46 hpair
  · exact partsGadgetNegationTriple47 hpair
  · exact partsGadgetNegationTriple48 hpair
  · exact partsGadgetNegationTriple49 hpair
  · exact partsGadgetNegationTriple50 hpair
  · exact partsGadgetNegationTriple51 hpair
  · exact partsGadgetNegationTriple52 hpair
  · exact partsGadgetNegationTriple53 hpair
  · exact partsGadgetNegationTriple54 hpair
  · exact partsGadgetNegationTriple55 hpair
  · exact partsGadgetNegationTriple56 hpair
  · exact partsGadgetNegationTriple57 hpair
  · exact partsGadgetNegationTriple58 hpair
  · exact partsGadgetNegationTriple59 hpair
  · exact partsGadgetNegationTriple60 hpair
  · exact partsGadgetNegationTriple61 hpair
  · exact partsGadgetNegationTriple62 hpair
  · exact partsGadgetNegationTriple63 hpair
  · exact partsGadgetNegationTriple64 hpair
  · exact partsGadgetNegationTriple65 hpair
  · exact partsGadgetNegationTriple66 hpair
  · exact partsGadgetNegationTriple67 hpair
  · exact partsGadgetNegationTriple68 hpair
  · exact partsGadgetNegationTriple69 hpair
  · exact partsGadgetNegationTriple70 hpair
  · exact partsGadgetNegationTriple71 hpair
  · exact partsGadgetNegationTriple72 hpair

lemma partsGadgetTriangleWitness_valid {vertex : Fin 73}
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses vertex) :
    witness.Valid vertex := by
  fin_cases vertex
  · exact partsGadgetTriangleWitnessValid0 hwitness
  · exact partsGadgetTriangleWitnessValid1 hwitness
  · exact partsGadgetTriangleWitnessValid2 hwitness
  · exact partsGadgetTriangleWitnessValid3 hwitness
  · exact partsGadgetTriangleWitnessValid4 hwitness
  · exact partsGadgetTriangleWitnessValid5 hwitness
  · exact partsGadgetTriangleWitnessValid6 hwitness
  · exact partsGadgetTriangleWitnessValid7 hwitness
  · exact partsGadgetTriangleWitnessValid8 hwitness
  · exact partsGadgetTriangleWitnessValid9 hwitness
  · exact partsGadgetTriangleWitnessValid10 hwitness
  · exact partsGadgetTriangleWitnessValid11 hwitness
  · exact partsGadgetTriangleWitnessValid12 hwitness
  · exact partsGadgetTriangleWitnessValid13 hwitness
  · exact partsGadgetTriangleWitnessValid14 hwitness
  · exact partsGadgetTriangleWitnessValid15 hwitness
  · exact partsGadgetTriangleWitnessValid16 hwitness
  · exact partsGadgetTriangleWitnessValid17 hwitness
  · exact partsGadgetTriangleWitnessValid18 hwitness
  · exact partsGadgetTriangleWitnessValid19 hwitness
  · exact partsGadgetTriangleWitnessValid20 hwitness
  · exact partsGadgetTriangleWitnessValid21 hwitness
  · exact partsGadgetTriangleWitnessValid22 hwitness
  · exact partsGadgetTriangleWitnessValid23 hwitness
  · exact partsGadgetTriangleWitnessValid24 hwitness
  · exact partsGadgetTriangleWitnessValid25 hwitness
  · exact partsGadgetTriangleWitnessValid26 hwitness
  · exact partsGadgetTriangleWitnessValid27 hwitness
  · exact partsGadgetTriangleWitnessValid28 hwitness
  · exact partsGadgetTriangleWitnessValid29 hwitness
  · exact partsGadgetTriangleWitnessValid30 hwitness
  · exact partsGadgetTriangleWitnessValid31 hwitness
  · exact partsGadgetTriangleWitnessValid32 hwitness
  · exact partsGadgetTriangleWitnessValid33 hwitness
  · exact partsGadgetTriangleWitnessValid34 hwitness
  · exact partsGadgetTriangleWitnessValid35 hwitness
  · exact partsGadgetTriangleWitnessValid36 hwitness
  · exact partsGadgetTriangleWitnessValid37 hwitness
  · exact partsGadgetTriangleWitnessValid38 hwitness
  · exact partsGadgetTriangleWitnessValid39 hwitness
  · exact partsGadgetTriangleWitnessValid40 hwitness
  · exact partsGadgetTriangleWitnessValid41 hwitness
  · exact partsGadgetTriangleWitnessValid42 hwitness
  · exact partsGadgetTriangleWitnessValid43 hwitness
  · exact partsGadgetTriangleWitnessValid44 hwitness
  · exact partsGadgetTriangleWitnessValid45 hwitness
  · exact partsGadgetTriangleWitnessValid46 hwitness
  · exact partsGadgetTriangleWitnessValid47 hwitness
  · exact partsGadgetTriangleWitnessValid48 hwitness
  · exact partsGadgetTriangleWitnessValid49 hwitness
  · exact partsGadgetTriangleWitnessValid50 hwitness
  · exact partsGadgetTriangleWitnessValid51 hwitness
  · exact partsGadgetTriangleWitnessValid52 hwitness
  · exact partsGadgetTriangleWitnessValid53 hwitness
  · exact partsGadgetTriangleWitnessValid54 hwitness
  · exact partsGadgetTriangleWitnessValid55 hwitness
  · exact partsGadgetTriangleWitnessValid56 hwitness
  · exact partsGadgetTriangleWitnessValid57 hwitness
  · exact partsGadgetTriangleWitnessValid58 hwitness
  · exact partsGadgetTriangleWitnessValid59 hwitness
  · exact partsGadgetTriangleWitnessValid60 hwitness
  · exact partsGadgetTriangleWitnessValid61 hwitness
  · exact partsGadgetTriangleWitnessValid62 hwitness
  · exact partsGadgetTriangleWitnessValid63 hwitness
  · exact partsGadgetTriangleWitnessValid64 hwitness
  · exact partsGadgetTriangleWitnessValid65 hwitness
  · exact partsGadgetTriangleWitnessValid66 hwitness
  · exact partsGadgetTriangleWitnessValid67 hwitness
  · exact partsGadgetTriangleWitnessValid68 hwitness
  · exact partsGadgetTriangleWitnessValid69 hwitness
  · exact partsGadgetTriangleWitnessValid70 hwitness
  · exact partsGadgetTriangleWitnessValid71 hwitness
  · exact partsGadgetTriangleWitnessValid72 hwitness

end HadwigerNelsonBounds
