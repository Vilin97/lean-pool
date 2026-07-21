/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetData

/-! Generated central-inversion checks, group 0. -/

namespace HadwigerNelsonBounds

lemma partsGadgetNegationNeighbor0 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 0) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 0) := by
  change neighbor ∈ [1, 4, 5] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple0 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 0) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 0) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 0) := by
  change pair ∈ [(6, 10)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid0
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 0) : witness.Valid 0 := by
  change witness ∈ [
    ⟨6, 10, 0, 6, 10, false, -2, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

lemma partsGadgetNegationNeighbor1 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 1) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 1) := by
  change neighbor ∈ [0, 2, 5, 6] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple1 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 1) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 1) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 1) := by
  change pair ∈ [(4, 11), (7, 11)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid1
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 1) : witness.Valid 1 := by
  change witness ∈ [
    ⟨4, 11, 11, 4, 1, false, -2, 0, false⟩,
    ⟨7, 11, 1, 7, 11, false, -2, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor2 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 2) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 2) := by
  change neighbor ∈ [1, 3, 6, 7] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple2 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 2) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 2) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 2) := by
  change pair ∈ [(5, 12), (8, 12)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid2
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 2) : witness.Valid 2 := by
  change witness ∈ [
    ⟨5, 12, 12, 5, 2, false, -2, 1, false⟩,
    ⟨8, 12, 2, 8, 12, false, -2, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor3 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 3) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 3) := by
  change neighbor ∈ [2, 7, 8] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple3 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 3) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 3) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 3) := by
  change pair ∈ [(6, 13)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid3
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 3) : witness.Valid 3 := by
  change witness ∈ [
    ⟨6, 13, 13, 6, 3, false, -2, 2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

lemma partsGadgetNegationNeighbor4 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 4) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 4) := by
  change neighbor ∈ [0, 5, 9, 10] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple4 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 4) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 4) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 4) := by
  change pair ∈ [(1, 11), (11, 16)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid4
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 4) : witness.Valid 4 := by
  change witness ∈ [
    ⟨1, 11, 11, 4, 1, false, -2, 0, false⟩,
    ⟨11, 16, 4, 11, 16, false, -1, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor5 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 5) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 5) := by
  change neighbor ∈ [0, 1, 4, 6, 10, 11, 42] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple5 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 5) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 5) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 5) := by
  change pair ∈ [(2, 12), (9, 17), (12, 17)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid5
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 5) : witness.Valid 5 := by
  change witness ∈ [
    ⟨2, 12, 12, 5, 2, false, -2, 1, false⟩,
    ⟨9, 17, 17, 9, 5, false, -1, -1, false⟩,
    ⟨12, 17, 5, 12, 17, false, -1, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor6 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 6) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 6) := by
  change neighbor ∈ [1, 2, 5, 7, 11, 12] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple6 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 6) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 6) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 6) := by
  change pair ∈ [(0, 10), (3, 13), (10, 18), (13, 18)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid6
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 6) : witness.Valid 6 := by
  change witness ∈ [
    ⟨0, 10, 0, 6, 10, false, -2, 0, true⟩,
    ⟨3, 13, 13, 6, 3, false, -2, 2, false⟩,
    ⟨10, 18, 18, 10, 6, false, -1, 0, false⟩,
    ⟨13, 18, 6, 13, 18, false, -1, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor7 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 7) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 7) := by
  change neighbor ∈ [2, 3, 6, 8, 12, 13, 44] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple7 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 7) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 7) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 7) := by
  change pair ∈ [(1, 11), (11, 19), (14, 19)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid7
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 7) : witness.Valid 7 := by
  change witness ∈ [
    ⟨1, 11, 1, 7, 11, false, -2, 1, true⟩,
    ⟨11, 19, 19, 11, 7, false, -1, 1, false⟩,
    ⟨14, 19, 7, 14, 19, false, -1, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor8 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 8) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 8) := by
  change neighbor ∈ [3, 7, 13, 14] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple8 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 8) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 8) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 8) := by
  change pair ∈ [(2, 12), (12, 20)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid8
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 8) : witness.Valid 8 := by
  change witness ∈ [
    ⟨2, 12, 2, 8, 12, false, -2, 2, true⟩,
    ⟨12, 20, 20, 12, 8, false, -1, 2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor9 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 9) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 9) := by
  change neighbor ∈ [4, 10, 15, 16] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple9 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 9) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 9) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 9) := by
  change pair ∈ [(5, 17), (17, 22)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid9
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 9) : witness.Valid 9 := by
  change witness ∈ [
    ⟨5, 17, 17, 9, 5, false, -1, -1, false⟩,
    ⟨17, 22, 9, 17, 22, false, 0, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor10 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 10) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 10) := by
  change neighbor ∈ [4, 5, 9, 11, 16, 17] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple10 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 10) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 10) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 10) := by
  change pair ∈ [(0, 6), (6, 18), (15, 23), (18, 23)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid10
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 10) : witness.Valid 10 := by
  change witness ∈ [
    ⟨0, 6, 0, 6, 10, false, -2, 0, true⟩,
    ⟨6, 18, 18, 10, 6, false, -1, 0, false⟩,
    ⟨15, 23, 23, 15, 10, false, 0, -2, false⟩,
    ⟨18, 23, 10, 18, 23, false, 0, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor11 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 11) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 11) := by
  change neighbor ∈ [5, 6, 10, 12, 17, 18] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple11 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 11) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 11) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 11) := by
  change pair ∈ [(1, 4), (1, 7), (4, 16), (7, 19), (16, 24), (19, 24)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid11
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 11) : witness.Valid 11 := by
  change witness ∈ [
    ⟨1, 4, 11, 4, 1, false, -2, 0, false⟩,
    ⟨1, 7, 1, 7, 11, false, -2, 1, true⟩,
    ⟨4, 16, 4, 11, 16, false, -1, -1, true⟩,
    ⟨7, 19, 19, 11, 7, false, -1, 1, false⟩,
    ⟨16, 24, 24, 16, 11, false, 0, -1, false⟩,
    ⟨19, 24, 11, 19, 24, false, 0, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor12 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 12) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 12) := by
  change neighbor ∈ [6, 7, 11, 13, 18, 19] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple12 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 12) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 12) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 12) := by
  change pair ∈ [(2, 5), (2, 8), (5, 17), (8, 20), (17, 25), (20, 25)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid12
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 12) : witness.Valid 12 := by
  change witness ∈ [
    ⟨2, 5, 12, 5, 2, false, -2, 1, false⟩,
    ⟨2, 8, 2, 8, 12, false, -2, 2, true⟩,
    ⟨5, 17, 5, 12, 17, false, -1, 0, true⟩,
    ⟨8, 20, 20, 12, 8, false, -1, 2, false⟩,
    ⟨17, 25, 25, 17, 12, false, 0, 0, false⟩,
    ⟨20, 25, 12, 20, 25, false, 0, 1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor13 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 13) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 13) := by
  change neighbor ∈ [7, 8, 12, 14, 19, 20] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple13 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 13) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 13) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 13) := by
  change pair ∈ [(3, 6), (6, 18), (18, 26), (21, 26)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid13
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 13) : witness.Valid 13 := by
  change witness ∈ [
    ⟨3, 6, 13, 6, 3, false, -2, 2, false⟩,
    ⟨6, 18, 6, 13, 18, false, -1, 1, true⟩,
    ⟨18, 26, 26, 18, 13, false, 0, 1, false⟩,
    ⟨21, 26, 13, 21, 26, false, 0, 2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor14 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 14) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 14) := by
  change neighbor ∈ [8, 13, 20, 21] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple14 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 14) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 14) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 14) := by
  change pair ∈ [(7, 19), (19, 27)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid14
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 14) : witness.Valid 14 := by
  change witness ∈ [
    ⟨7, 19, 7, 14, 19, false, -1, 2, true⟩,
    ⟨19, 27, 27, 19, 14, false, 0, 2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor15 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 15) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 15) := by
  change neighbor ∈ [9, 16, 22] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple15 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 15) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 15) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 15) := by
  change pair ∈ [(10, 23)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid15
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 15) : witness.Valid 15 := by
  change witness ∈ [
    ⟨10, 23, 23, 15, 10, false, 0, -2, false⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl
  all_goals decide

lemma partsGadgetNegationNeighbor16 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 16) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 16) := by
  change neighbor ∈ [9, 10, 15, 17, 22, 23, 53] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple16 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 16) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 16) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 16) := by
  change pair ∈ [(4, 11), (11, 24), (24, 28)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid16
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 16) : witness.Valid 16 := by
  change witness ∈ [
    ⟨4, 11, 4, 11, 16, false, -1, -1, true⟩,
    ⟨11, 24, 24, 16, 11, false, 0, -1, false⟩,
    ⟨24, 28, 16, 24, 28, false, 1, -2, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor17 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 17) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 17) := by
  change neighbor ∈ [10, 11, 16, 18, 23, 24] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple17 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 17) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 17) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 17) := by
  change pair ∈ [(5, 9), (5, 12), (9, 22), (12, 25), (22, 29), (25, 29)] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid17
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 17) : witness.Valid 17 := by
  change witness ∈ [
    ⟨5, 9, 17, 9, 5, false, -1, -1, false⟩,
    ⟨5, 12, 5, 12, 17, false, -1, 0, true⟩,
    ⟨9, 22, 9, 17, 22, false, 0, -2, true⟩,
    ⟨12, 25, 25, 17, 12, false, 0, 0, false⟩,
    ⟨22, 29, 29, 22, 17, false, 1, -2, false⟩,
    ⟨25, 29, 17, 25, 29, false, 1, -1, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationNeighbor18 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 18) :
    partsGadgetNegation neighbor ∈
      partsGadgetNeighbors (partsGadgetNegation 18) := by
  change neighbor ∈ [11, 12, 17, 19, 24, 25, 48, 49, 54, 55, 60, 61] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetNegationTriple18 {pair : Fin 73 × Fin 73}
    (hpair : pair ∈ partsGadgetTriplePairs 18) :
    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈
        partsGadgetTriplePairs (partsGadgetNegation 18) ∨
      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈
        partsGadgetTriplePairs (partsGadgetNegation 18) := by
  change pair ∈ [
    (6, 10),
    (6, 13),
    (10, 23),
    (13, 26),
    (23, 30),
    (26, 30),
    (43, 47),
    (43, 50),
    (47, 59),
    (50, 62),
    (59, 66),
    (62, 66),
  ] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetTriangleWitnessValid18
    {witness : PartsGadgetTriangleWitnessData}
    (hwitness : witness ∈ partsGadgetTriangleWitnesses 18) : witness.Valid 18 := by
  change witness ∈ [
    ⟨6, 10, 18, 10, 6, false, -1, 0, false⟩,
    ⟨6, 13, 6, 13, 18, false, -1, 1, true⟩,
    ⟨10, 23, 10, 18, 23, false, 0, -1, true⟩,
    ⟨13, 26, 26, 18, 13, false, 0, 1, false⟩,
    ⟨23, 30, 30, 23, 18, false, 1, -1, false⟩,
    ⟨26, 30, 18, 26, 30, false, 1, 0, true⟩,
    ⟨43, 47, 18, 47, 43, true, -1, 0, false⟩,
    ⟨43, 50, 43, 50, 18, true, -1, 1, true⟩,
    ⟨47, 59, 47, 18, 59, true, 0, -1, true⟩,
    ⟨50, 62, 62, 18, 50, true, 0, 1, false⟩,
    ⟨59, 66, 66, 59, 18, true, 1, -1, false⟩,
    ⟨62, 66, 18, 62, 66, true, 1, 0, true⟩,
  ] at hwitness
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness
  rcases hwitness with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

end HadwigerNelsonBounds
