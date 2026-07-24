/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetData

/-! Generated central-inversion checks, group 2. -/

namespace HadwigerNelsonBounds

lemma partsGadgetNegationNeighbor38 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 38) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 38) := by
  change neighbor ∈ [37, 39, 42, 43] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple38 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 38) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 38) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 38) := by
  change pair ∈ [(41, 48), (44, 48)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid38
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 38) : witness.Valid 38 := by
  change witness ∈ [
    ⟨41, 48, 48, 41, 38, true, -2, 0, false⟩,
    ⟨44, 48, 38, 44, 48, true, -2, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor39 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 39) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 39) := by
  change neighbor ∈ [38, 40, 43, 44] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple39 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 39) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 39) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 39) := by
  change pair ∈ [(42, 49), (45, 49)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid39
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 39) : witness.Valid 39 := by
  change witness ∈ [
    ⟨42, 49, 49, 42, 39, true, -2, 1, false⟩,
    ⟨45, 49, 39, 45, 49, true, -2, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor40 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 40) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 40) := by
  change neighbor ∈ [39, 44, 45] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple40 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 40) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 40) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 40) := by
  change pair ∈ [(43, 50)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid40
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 40) : witness.Valid 40 := by
  change witness ∈ [
    ⟨43, 50, 50, 43, 40, true, -2, 2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

lemma partsGadgetNegationNeighbor41 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 41) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 41) := by
  change neighbor ∈ [37, 42, 46, 47] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple41 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 41) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 41) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 41) := by
  change pair ∈ [(38, 48), (48, 53)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid41
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 41) : witness.Valid 41 := by
  change witness ∈ [
    ⟨38, 48, 48, 41, 38, true, -2, 0, false⟩,
    ⟨48, 53, 41, 48, 53, true, -1, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor42 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 42) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 42) := by
  change neighbor ∈ [5, 37, 38, 41, 43, 47, 48] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple42 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 42) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 42) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 42) := by
  change pair ∈ [(39, 49), (46, 54), (49, 54)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid42
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 42) : witness.Valid 42 := by
  change witness ∈ [
    ⟨39, 49, 49, 42, 39, true, -2, 1, false⟩,
    ⟨46, 54, 54, 46, 42, true, -1, -1, false⟩,
    ⟨49, 54, 42, 49, 54, true, -1, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor43 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 43) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 43) := by
  change neighbor ∈ [38, 39, 42, 44, 48, 49] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple43 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 43) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 43) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 43) := by
  change pair ∈ [(18, 47), (18, 50), (37, 47), (40, 50)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid43
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 43) : witness.Valid 43 := by
  change witness ∈ [
    ⟨18, 47, 18, 47, 43, true, -1, 0, false⟩,
    ⟨18, 50, 43, 50, 18, true, -1, 1, true⟩,
    ⟨37, 47, 37, 43, 47, true, -2, 0, true⟩,
    ⟨40, 50, 50, 43, 40, true, -2, 2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor44 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 44) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 44) := by
  change neighbor ∈ [7, 39, 40, 43, 45, 49, 50] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple44 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 44) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 44) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 44) := by
  change pair ∈ [(38, 48), (48, 55), (51, 55)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid44
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 44) : witness.Valid 44 := by
  change witness ∈ [
    ⟨38, 48, 38, 44, 48, true, -2, 1, true⟩,
    ⟨48, 55, 55, 48, 44, true, -1, 1, false⟩,
    ⟨51, 55, 44, 51, 55, true, -1, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor45 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 45) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 45) := by
  change neighbor ∈ [40, 44, 50, 51] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple45 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 45) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 45) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 45) := by
  change pair ∈ [(39, 49), (49, 56)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid45
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 45) : witness.Valid 45 := by
  change witness ∈ [
    ⟨39, 49, 39, 45, 49, true, -2, 2, true⟩,
    ⟨49, 56, 56, 49, 45, true, -1, 2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor46 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 46) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 46) := by
  change neighbor ∈ [41, 47, 52, 53] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple46 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 46) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 46) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 46) := by
  change pair ∈ [(42, 54), (54, 58)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid46
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 46) : witness.Valid 46 := by
  change witness ∈ [
    ⟨42, 54, 54, 46, 42, true, -1, -1, false⟩,
    ⟨54, 58, 46, 54, 58, true, 0, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor47 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 47) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 47) := by
  change neighbor ∈ [41, 42, 46, 48, 53, 54] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple47 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 47) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 47) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 47) := by
  change pair ∈ [(18, 43), (18, 59), (37, 43), (52, 59)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid47
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 47) : witness.Valid 47 := by
  change witness ∈ [
    ⟨18, 43, 18, 47, 43, true, -1, 0, false⟩,
    ⟨18, 59, 47, 18, 59, true, 0, -1, true⟩,
    ⟨37, 43, 37, 43, 47, true, -2, 0, true⟩,
    ⟨52, 59, 59, 52, 47, true, 0, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor48 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 48) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 48) := by
  change neighbor ∈ [18, 42, 43, 47, 49, 54] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple48 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 48) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 48) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 48) := by
  change pair ∈ [(38, 41), (38, 44), (41, 53), (44, 55), (53, 60), (55, 60)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid48
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 48) : witness.Valid 48 := by
  change witness ∈ [
    ⟨38, 41, 48, 41, 38, true, -2, 0, false⟩,
    ⟨38, 44, 38, 44, 48, true, -2, 1, true⟩,
    ⟨41, 53, 41, 48, 53, true, -1, -1, true⟩,
    ⟨44, 55, 55, 48, 44, true, -1, 1, false⟩,
    ⟨53, 60, 60, 53, 48, true, 0, -1, false⟩,
    ⟨55, 60, 48, 55, 60, true, 0, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor49 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 49) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 49) := by
  change neighbor ∈ [18, 43, 44, 48, 50, 55] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple49 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 49) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 49) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 49) := by
  change pair ∈ [(39, 42), (39, 45), (42, 54), (45, 56), (54, 61), (56, 61)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid49
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 49) : witness.Valid 49 := by
  change witness ∈ [
    ⟨39, 42, 49, 42, 39, true, -2, 1, false⟩,
    ⟨39, 45, 39, 45, 49, true, -2, 2, true⟩,
    ⟨42, 54, 42, 49, 54, true, -1, 0, true⟩,
    ⟨45, 56, 56, 49, 45, true, -1, 2, false⟩,
    ⟨54, 61, 61, 54, 49, true, 0, 0, false⟩,
    ⟨56, 61, 49, 56, 61, true, 0, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor50 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 50) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 50) := by
  change neighbor ∈ [44, 45, 49, 51, 55, 56] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple50 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 50) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 50) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 50) := by
  change pair ∈ [(18, 43), (18, 62), (40, 43), (57, 62)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid50
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 50) : witness.Valid 50 := by
  change witness ∈ [
    ⟨18, 43, 43, 50, 18, true, -1, 1, true⟩,
    ⟨18, 62, 62, 18, 50, true, 0, 1, false⟩,
    ⟨40, 43, 50, 43, 40, true, -2, 2, false⟩,
    ⟨57, 62, 50, 57, 62, true, 0, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor51 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 51) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 51) := by
  change neighbor ∈ [45, 50, 56, 57] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple51 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 51) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 51) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 51) := by
  change pair ∈ [(44, 55), (55, 63)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid51
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 51) : witness.Valid 51 := by
  change witness ∈ [
    ⟨44, 55, 44, 51, 55, true, -1, 2, true⟩,
    ⟨55, 63, 63, 55, 51, true, 0, 2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor52 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 52) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 52) := by
  change neighbor ∈ [46, 53, 58] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple52 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 52) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 52) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 52) := by
  change pair ∈ [(47, 59)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid52
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 52) : witness.Valid 52 := by
  change witness ∈ [
    ⟨47, 59, 59, 52, 47, true, 0, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

lemma partsGadgetNegationNeighbor53 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 53) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 53) := by
  change neighbor ∈ [16, 46, 47, 52, 54, 58, 59] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple53 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 53) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 53) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 53) := by
  change pair ∈ [(41, 48), (48, 60), (60, 64)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid53
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 53) : witness.Valid 53 := by
  change witness ∈ [
    ⟨41, 48, 41, 48, 53, true, -1, -1, true⟩,
    ⟨48, 60, 60, 53, 48, true, 0, -1, false⟩,
    ⟨60, 64, 53, 60, 64, true, 1, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor54 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 54) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 54) := by
  change neighbor ∈ [18, 47, 48, 53, 59, 60] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple54 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 54) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 54) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 54) := by
  change pair ∈ [(42, 46), (42, 49), (46, 58), (49, 61), (58, 65), (61, 65)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid54
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 54) : witness.Valid 54 := by
  change witness ∈ [
    ⟨42, 46, 54, 46, 42, true, -1, -1, false⟩,
    ⟨42, 49, 42, 49, 54, true, -1, 0, true⟩,
    ⟨46, 58, 46, 54, 58, true, 0, -2, true⟩,
    ⟨49, 61, 61, 54, 49, true, 0, 0, false⟩,
    ⟨58, 65, 65, 58, 54, true, 1, -2, false⟩,
    ⟨61, 65, 54, 61, 65, true, 1, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor55 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 55) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 55) := by
  change neighbor ∈ [18, 49, 50, 56, 61, 62] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple55 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 55) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 55) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 55) := by
  change pair ∈ [(44, 48), (44, 51), (48, 60), (51, 63), (60, 67), (63, 67)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid55
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 55) : witness.Valid 55 := by
  change witness ∈ [
    ⟨44, 48, 55, 48, 44, true, -1, 1, false⟩,
    ⟨44, 51, 44, 51, 55, true, -1, 2, true⟩,
    ⟨48, 60, 48, 55, 60, true, 0, 0, true⟩,
    ⟨51, 63, 63, 55, 51, true, 0, 2, false⟩,
    ⟨60, 67, 67, 60, 55, true, 1, 0, false⟩,
    ⟨63, 67, 55, 63, 67, true, 1, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor56 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 56) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 56) := by
  change neighbor ∈ [20, 50, 51, 55, 57, 62, 63] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple56 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 56) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 56) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 56) := by
  change pair ∈ [(45, 49), (49, 61), (61, 68)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid56
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 56) : witness.Valid 56 := by
  change witness ∈ [
    ⟨45, 49, 56, 49, 45, true, -1, 2, false⟩,
    ⟨49, 61, 49, 56, 61, true, 0, 1, true⟩,
    ⟨61, 68, 68, 61, 56, true, 1, 1, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

end HadwigerNelsonBounds
