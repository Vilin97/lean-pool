/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore

/-! Generated edge-geometry checks, group 3. -/

namespace HadwigerNelsonBounds

lemma partsGadgetEdgeCase57 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 57) :
    PartsGadgetEdgeCase 57 neighbor := by
  change neighbor ∈ [51, 56, 63] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase58 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 58) :
    PartsGadgetEdgeCase 58 neighbor := by
  change neighbor ∈ [52, 53, 59, 64] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase59 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 59) :
    PartsGadgetEdgeCase 59 neighbor := by
  change neighbor ∈ [53, 54, 58, 60, 64, 65] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase60 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 60) :
    PartsGadgetEdgeCase 60 neighbor := by
  change neighbor ∈ [18, 54, 59, 61, 65, 66] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase61 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 61) :
    PartsGadgetEdgeCase 61 neighbor := by
  change neighbor ∈ [18, 55, 60, 62, 66, 67] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase62 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 62) :
    PartsGadgetEdgeCase 62 neighbor := by
  change neighbor ∈ [55, 56, 61, 63, 67, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase63 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 63) :
    PartsGadgetEdgeCase 63 neighbor := by
  change neighbor ∈ [56, 57, 62, 68] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase64 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 64) :
    PartsGadgetEdgeCase 64 neighbor := by
  change neighbor ∈ [58, 59, 65, 69] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase65 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 65) :
    PartsGadgetEdgeCase 65 neighbor := by
  change neighbor ∈ [29, 59, 60, 64, 66, 69, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase66 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 66) :
    PartsGadgetEdgeCase 66 neighbor := by
  change neighbor ∈ [60, 61, 65, 67, 70, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase67 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 67) :
    PartsGadgetEdgeCase 67 neighbor := by
  change neighbor ∈ [31, 61, 62, 66, 68, 71, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase68 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 68) :
    PartsGadgetEdgeCase 68 neighbor := by
  change neighbor ∈ [62, 63, 67, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase69 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 69) :
    PartsGadgetEdgeCase 69 neighbor := by
  change neighbor ∈ [64, 65, 70] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase70 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 70) :
    PartsGadgetEdgeCase 70 neighbor := by
  change neighbor ∈ [65, 66, 69, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase71 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 71) :
    PartsGadgetEdgeCase 71 neighbor := by
  change neighbor ∈ [66, 67, 70, 72] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl | rfl
  all_goals decide

lemma partsGadgetEdgeCase72 {neighbor : Fin 73}
    (hadj : neighbor ∈ partsGadgetNeighbors 72) :
    PartsGadgetEdgeCase 72 neighbor := by
  change neighbor ∈ [67, 68, 71] at hadj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj
  rcases hadj with rfl | rfl | rfl
  all_goals decide

end HadwigerNelsonBounds
