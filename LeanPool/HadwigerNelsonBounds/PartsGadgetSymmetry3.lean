/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetData

/-! Generated central-inversion checks, group 3. -/

namespace HadwigerNelsonBounds

lemma partsGadgetNegationNeighbor57 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 57) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 57) := by
  change neighbor ∈ [51, 56, 63] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple57 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 57) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 57) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 57) := by
  change pair ∈ [(50, 62)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid57
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 57) : witness.Valid 57 := by
  change witness ∈ [
    ⟨50, 62, 50, 57, 62, true, 0, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

lemma partsGadgetNegationNeighbor58 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 58) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 58) := by
  change neighbor ∈ [52, 53, 59, 64] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple58 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 58) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 58) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 58) := by
  change pair ∈ [(46, 54), (54, 65)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid58
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 58) : witness.Valid 58 := by
  change witness ∈ [
    ⟨46, 54, 46, 54, 58, true, 0, -2, true⟩,
    ⟨54, 65, 65, 58, 54, true, 1, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor59 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 59) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 59) := by
  change neighbor ∈ [53, 54, 58, 60, 64, 65] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple59 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 59) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 59) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 59) := by
  change pair ∈ [(18, 47), (18, 66), (47, 52), (66, 69)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid59
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 59) : witness.Valid 59 := by
  change witness ∈ [
    ⟨18, 47, 47, 18, 59, true, 0, -1, true⟩,
    ⟨18, 66, 66, 59, 18, true, 1, -1, false⟩,
    ⟨47, 52, 59, 52, 47, true, 0, -2, false⟩,
    ⟨66, 69, 59, 66, 69, true, 2, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor60 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 60) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 60) := by
  change neighbor ∈ [18, 54, 59, 61, 65, 66] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple60 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 60) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 60) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 60) := by
  change pair ∈ [(48, 53), (48, 55), (53, 64), (55, 67), (64, 70), (67, 70)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid60
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 60) : witness.Valid 60 := by
  change witness ∈ [
    ⟨48, 53, 60, 53, 48, true, 0, -1, false⟩,
    ⟨48, 55, 48, 55, 60, true, 0, 0, true⟩,
    ⟨53, 64, 53, 60, 64, true, 1, -2, true⟩,
    ⟨55, 67, 67, 60, 55, true, 1, 0, false⟩,
    ⟨64, 70, 70, 64, 60, true, 2, -2, false⟩,
    ⟨67, 70, 60, 67, 70, true, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor61 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 61) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 61) := by
  change neighbor ∈ [18, 55, 60, 62, 66, 67] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple61 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 61) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 61) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 61) := by
  change pair ∈ [(49, 54), (49, 56), (54, 65), (56, 68), (65, 71), (68, 71)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid61
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 61) : witness.Valid 61 := by
  change witness ∈ [
    ⟨49, 54, 61, 54, 49, true, 0, 0, false⟩,
    ⟨49, 56, 49, 56, 61, true, 0, 1, true⟩,
    ⟨54, 65, 54, 61, 65, true, 1, -1, true⟩,
    ⟨56, 68, 68, 61, 56, true, 1, 1, false⟩,
    ⟨65, 71, 71, 65, 61, true, 2, -1, false⟩,
    ⟨68, 71, 61, 68, 71, true, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor62 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 62) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 62) := by
  change neighbor ∈ [55, 56, 61, 63, 67, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple62 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 62) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 62) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 62) := by
  change pair ∈ [(18, 50), (18, 66), (50, 57), (66, 72)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid62
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 62) : witness.Valid 62 := by
  change witness ∈ [
    ⟨18, 50, 62, 18, 50, true, 0, 1, false⟩,
    ⟨18, 66, 18, 62, 66, true, 1, 0, true⟩,
    ⟨50, 57, 50, 57, 62, true, 0, 2, true⟩,
    ⟨66, 72, 72, 66, 62, true, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor63 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 63) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 63) := by
  change neighbor ∈ [56, 57, 62, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple63 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 63) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 63) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 63) := by
  change pair ∈ [(51, 55), (55, 67)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid63
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 63) : witness.Valid 63 := by
  change witness ∈ [
    ⟨51, 55, 63, 55, 51, true, 0, 2, false⟩,
    ⟨55, 67, 55, 63, 67, true, 1, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor64 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 64) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 64) := by
  change neighbor ∈ [58, 59, 65, 69] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple64 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 64) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 64) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 64) := by
  change pair ∈ [(53, 60), (60, 70)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid64
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 64) : witness.Valid 64 := by
  change witness ∈ [
    ⟨53, 60, 53, 60, 64, true, 1, -2, true⟩,
    ⟨60, 70, 70, 64, 60, true, 2, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor65 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 65) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 65) := by
  change neighbor ∈ [29, 59, 60, 64, 66, 69, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple65 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 65) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 65) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 65) := by
  change pair ∈ [(54, 58), (54, 61), (61, 71)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid65
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 65) : witness.Valid 65 := by
  change witness ∈ [
    ⟨54, 58, 65, 58, 54, true, 1, -2, false⟩,
    ⟨54, 61, 54, 61, 65, true, 1, -1, true⟩,
    ⟨61, 71, 71, 65, 61, true, 2, -1, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor66 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 66) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 66) := by
  change neighbor ∈ [60, 61, 65, 67, 70, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple66 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 66) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 66) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 66) := by
  change pair ∈ [(18, 59), (18, 62), (59, 69), (62, 72)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid66
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 66) : witness.Valid 66 := by
  change witness ∈ [
    ⟨18, 59, 66, 59, 18, true, 1, -1, false⟩,
    ⟨18, 62, 18, 62, 66, true, 1, 0, true⟩,
    ⟨59, 69, 59, 66, 69, true, 2, -2, true⟩,
    ⟨62, 72, 72, 66, 62, true, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor67 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 67) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 67) := by
  change neighbor ∈ [31, 61, 62, 66, 68, 71, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple67 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 67) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 67) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 67) := by
  change pair ∈ [(55, 60), (55, 63), (60, 70)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid67
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 67) : witness.Valid 67 := by
  change witness ∈ [
    ⟨55, 60, 67, 60, 55, true, 1, 0, false⟩,
    ⟨55, 63, 55, 63, 67, true, 1, 1, true⟩,
    ⟨60, 70, 60, 67, 70, true, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor68 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 68) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 68) := by
  change neighbor ∈ [62, 63, 67, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple68 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 68) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 68) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 68) := by
  change pair ∈ [(56, 61), (61, 71)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid68
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 68) : witness.Valid 68 := by
  change witness ∈ [
    ⟨56, 61, 68, 61, 56, true, 1, 1, false⟩,
    ⟨61, 71, 61, 68, 71, true, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor69 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 69) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 69) := by
  change neighbor ∈ [64, 65, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple69 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 69) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 69) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 69) := by
  change pair ∈ [(59, 66)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid69
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 69) : witness.Valid 69 := by
  change witness ∈ [
    ⟨59, 66, 59, 66, 69, true, 2, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

lemma partsGadgetNegationNeighbor70 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 70) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 70) := by
  change neighbor ∈ [65, 66, 69, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple70 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 70) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 70) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 70) := by
  change pair ∈ [(60, 64), (60, 67)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid70
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 70) : witness.Valid 70 := by
  change witness ∈ [
    ⟨60, 64, 70, 64, 60, true, 2, -2, false⟩,
    ⟨60, 67, 60, 67, 70, true, 2, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor71 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 71) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 71) := by
  change neighbor ∈ [66, 67, 70, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple71 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 71) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 71) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 71) := by
  change pair ∈ [(61, 65), (61, 68)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid71
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 71) : witness.Valid 71 := by
  change witness ∈ [
    ⟨61, 65, 71, 65, 61, true, 2, -1, false⟩,
    ⟨61, 68, 61, 68, 71, true, 2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor72 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 72) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 72) := by
  change neighbor ∈ [67, 68, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple72 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 72) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 72) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 72) := by
  change pair ∈ [(62, 66)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid72
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 72) : witness.Valid 72 := by
  change witness ∈ [
    ⟨62, 66, 72, 66, 62, true, 2, 0, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

end HadwigerNelsonBounds
