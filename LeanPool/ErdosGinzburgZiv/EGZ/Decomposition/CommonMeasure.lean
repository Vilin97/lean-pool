/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LargeFaceSequence

/-!
# Large faces after passing to a common measure

Deleting at most `ε² / 4` of the global reference mass preserves positivity
and makes every old `ε`-large face `ε / 2`-large for the retained measure.
The estimates apply to finite real weights, including natural weights by
`WeightedIncidence.mass_natCast`.
-/

open scoped BigOperators

namespace EGZ

namespace WeightedIncidence

variable {α : Type*} [Fintype α]

theorem mass_weight_mono (w u : α → ℝ) (h : ∀ a, u a ≤ w a) (S : Set α) :
    mass u S ≤ mass w S := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ S <;> simp [ha, h a]

theorem mass_sub_weight (w u : α → ℝ) (S : Set α) :
    mass (fun a ↦ w a - u a) S = mass w S - mass u S := by
  classical
  rw [mass, mass, mass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

/-- The loss on any set is bounded by the loss on all atoms. -/
theorem mass_loss_le_total (w u : α → ℝ) (h : ∀ a, u a ≤ w a) (S : Set α) :
    mass w S - mass u S ≤ ∑ a, (w a - u a) := by
  rw [← mass_sub_weight]
  exact mass_le_total _ (fun a ↦ sub_nonneg.mpr (h a)) S

end WeightedIncidence

namespace CommonMeasure

/-- Numerical form of the mass-and-tail estimate. The strict proper-face
inequality has enough room to tolerate the whole permitted tail loss. -/
theorem mass_tail_estimates {ε R D a b : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R)
    (hD : 0 ≤ D) (hDsmall : D ≤ ε ^ 2 / 4 * R)
    (ha : ε * R ≤ a) (hb : a - D ≤ b) :
    0 < b ∧ ε / 2 * R ≤ b ∧ (1 - ε) * a < (1 - ε / 2) * b := by
  have ha_pos : 0 < a := (mul_pos hε hR).trans_le ha
  have hDa : D ≤ ε / 4 * a := by
    have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ ε / 4 by positivity)
    nlinarith
  have hεsmall : ε ^ 2 / 4 ≤ ε / 2 := by nlinarith
  have hDR : D ≤ ε / 2 * R :=
    hDsmall.trans (mul_le_mul_of_nonneg_right hεsmall hR.le)
  have hhalf : ε / 2 * R ≤ b := by linarith
  have hbpos : 0 < b := (mul_pos (by positivity : 0 < ε / 2) hR).trans_le hhalf
  refine ⟨hbpos, hhalf, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1 - ε / 2 by linarith)
  have hεD := mul_nonneg hε.le hD
  have hεa := mul_pos hε ha_pos
  nlinarith

variable {α : Type*} [Fintype α]

open WeightedIncidence

/-- Positivity, reference-mass largeness, and strict proper-subface
separation for a retained finite measure. -/
theorem face_estimates (w u : α → ℝ)
    (hle : ∀ a, u a ≤ w a) {ε R : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R)
    (hloss : (∑ a, (w a - u a)) ≤ ε ^ 2 / 4 * R)
    (S : Set α) (hlarge : ε * R ≤ mass w S) :
    0 < mass u S ∧ ε / 2 * R ≤ mass u S ∧
      ∀ T : Set α, mass w T ≤ (1 - ε) * mass w S →
        mass u T < (1 - ε / 2) * mass u S := by
  have h := mass_tail_estimates (b := mass u S) hε hεhalf hR
    (Finset.sum_nonneg (fun a _ ↦ sub_nonneg.mpr (hle a))) hloss hlarge
    (by linarith [mass_loss_le_total w u hle S])
  exact ⟨h.1, h.2.1, fun T hT ↦ (mass_weight_mono w u hle T).trans_lt
    (hT.trans_lt h.2.2)⟩

/-- Largeness relative to any polytope whose old mass is below the global
reference mass. -/
theorem relative_mass_le (w u : α → ℝ)
    (hle : ∀ a, u a ≤ w a) {ε R : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R)
    (hloss : (∑ a, (w a - u a)) ≤ ε ^ 2 / 4 * R)
    (S P : Set α) (hlarge : ε * R ≤ mass w S) (hP : mass w P ≤ R) :
    ε / 2 * mass u P ≤ mass u S := by
  have h := (face_estimates w u hle hε hεhalf hR hloss S hlarge).2.1
  exact (mul_le_mul_of_nonneg_left ((mass_weight_mono w u hle P).trans hP)
    (by positivity : 0 ≤ ε / 2)).trans h

/-- A retained large face inside the final polytope bounds the final
polytope mass relative to any initial set below the same reference mass. -/
theorem final_mass_le (w u : α → ℝ) (hu : ∀ a, 0 ≤ u a)
    (hle : ∀ a, u a ≤ w a) {ε R : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R)
    (hloss : (∑ a, (w a - u a)) ≤ ε ^ 2 / 4 * R)
    (S P Q : Set α) (hlarge : ε * R ≤ mass w S)
    (hSQ : S ⊆ Q) (hP : mass w P ≤ R) :
    ε / 2 * mass u P ≤ mass u Q :=
  (relative_mass_le w u hle hε hεhalf hR hloss S P hlarge hP).trans
    (mass_mono u hu hSQ)

end CommonMeasure

/-- Apply the uniform large-face bound to varying old measures and one
common retained measure. Only the dimension and `ε` occur in the bound. -/
theorem card_largeFaceSequence_of_mass_loss {α : Type*} [Fintype α] {d N : ℕ}
    (q : α → RealCoord d) (u : α → ℝ) (hu : ∀ a, 0 ≤ u a)
    (w : Fin (N + 1) → α → ℝ) (R : Fin (N + 1) → ℝ)
    (hle : ∀ i a, u a ≤ w i a) (hR : ∀ i, 0 < R i)
    (htotal : ∀ i, (∑ a, w i a) ≤ R i)
    (P : Fin (N + 1) → RationalPolytope d) (Γ : ∀ i, (P i).Face)
    (hnested : ∀ i j, i < j → (P j).carrier ⊆ (P i).carrier)
    (hdistinct : ∀ i j, i < j → (Γ i).carrier ∩ (P j).carrier ≠ (Γ j).carrier)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hloss : ∀ i, (∑ a, (w i a - u a)) ≤ ε ^ 2 / 4 * R i)
    (hlarge : ∀ i, ε * R i ≤ WeightedIncidence.mass (w i) (q ⁻¹' (Γ i).carrier))
    (hproper : ∀ i (Δ : (P i).Face), Δ.carrier ⊂ (Γ i).carrier →
      WeightedIncidence.mass (w i) (q ⁻¹' Δ.carrier) ≤
        (1 - ε) * WeightedIncidence.mass (w i) (q ⁻¹' (Γ i).carrier)) :
    ((N + 1 : ℕ) : ℝ) ≤ (((ε / 2) ^ 3)⁻¹ + (d : ℝ) + 2) ^ (d + 2) := by
  have hw : ∀ i a, 0 ≤ w i a := fun i a ↦ (hu a).trans (hle i a)
  have hmass : ∀ i S, WeightedIncidence.mass (w i) S ≤ R i :=
    fun i S ↦ (WeightedIncidence.mass_le_total (w i) (hw i) S).trans (htotal i)
  have hface := fun i ↦ CommonMeasure.face_estimates (w i) u (hle i)
    hε hεhalf (hR i) (hloss i) (q ⁻¹' (Γ i).carrier) (hlarge i)
  apply card_largeFaceSequence_le_paper q u hu P Γ hnested hdistinct
    (ε / 2) (by positivity)
  · exact (hface 0).1.trans_le (WeightedIncidence.mass_mono u hu
      (fun _ ha ↦ (Γ 0).subset_polytope ha))
  · exact CommonMeasure.final_mass_le (w (Fin.last N)) u hu (hle (Fin.last N))
      hε hεhalf (hR _) (hloss _) _ _ _ (hlarge _)
      (fun _ ha ↦ (Γ (Fin.last N)).subset_polytope ha) (hmass _ _)
  · intro i
    exact CommonMeasure.relative_mass_le (w i) u (hle i) hε hεhalf (hR i)
      (hloss i) _ _ (hlarge i) (hmass i _)
  · intro i Δ hΔ
    exact ((hface i).2.2 _ (hproper i Δ hΔ)).le

end EGZ
