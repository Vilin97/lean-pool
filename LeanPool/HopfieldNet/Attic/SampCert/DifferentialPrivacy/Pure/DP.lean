/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.SLang
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Neighbours
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Sensitivity
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Approximate.DP

noncomputable section

open Classical

variable { T : Type }

namespace SLang

def DP (m : Mechanism T U) (ε : ℝ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ S : Set U,
  (∑' x : U, if x ∈ S then m l₁ x else 0) / (∑' x : U, if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal (Real.exp ε)

def PureDP (m : Mechanism T U) (ε : NNReal) : Prop :=
  DP m ε

def DP_singleton (m : Mechanism T U) (ε : ℝ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ x : U,
  (m l₁ x) / (m l₂ x) ≤ ENNReal.ofReal (Real.exp ε)

theorem singleton_to_event (m : Mechanism T U) (ε : ℝ) (h : DP_singleton m ε) :
  DP m ε := by
  simp [DP]
  simp [DP_singleton] at h
  intros l₁ l₂ h1 S
  replace h1 := h l₁ l₂ h1
  have A : ∀ (x : U), (if x ∈ S then m l₁ x else 0) / (if x ∈ S then m l₂ x else 0) ≤ ENNReal.ofReal ε.exp := by
    aesop
  have B : ∀ b : ENNReal, b ≠ 0 ∨ ENNReal.ofReal ε.exp ≠ ⊤ := by
    aesop
  have C : ∀ b : ENNReal, b ≠ ⊤ ∨ ENNReal.ofReal ε.exp ≠ 0 := by
    intro b
    right
    simp
    exact Real.exp_pos ε
  have D := fun { x : U } => @ENNReal.div_le_iff_le_mul (if x ∈ S then m l₁ x else 0) (if x ∈ S then m l₂ x else 0) (ENNReal.ofReal ε.exp) (B (if x ∈ S then m l₂ x else 0)) (C (if x ∈ S then m l₂ x else 0))
  have E := fun x : U => D.1 (A x)
  have F := ENNReal.tsum_le_tsum E
  rw [ENNReal.tsum_mul_left] at F
  rw [← ENNReal.div_le_iff_le_mul] at F
  · clear h1 A B C D
    trivial
  · aesop
  · right
    simp
    exact Real.exp_pos ε

theorem event_to_singleton (m : Mechanism T U) (ε : ℝ) (h : DP m ε) :
  DP_singleton m ε := by
  simp [DP_singleton]
  simp [DP] at h
  intros l₁ l₂ h1 x
  replace h1 := h l₁ l₂ h1 {x}
  simp at h1
  rw [tsum_eq_single x] at h1
  · simp at h1
    rw [tsum_eq_single x] at h1
    · simp at h1
      trivial
    · aesop
  · aesop

theorem event_eq_singleton (m : Mechanism T U) (ε : ℝ) :
  DP m ε ↔ DP_singleton m ε := by
  constructor
  · apply event_to_singleton
  · apply singleton_to_event

lemma PureDP_mono {m : Mechanism T U} {ε₁ ε₂ : NNReal} (H : ε₁ ≤ ε₂) (Hε : PureDP m ε₁) : PureDP m ε₂ := by
  rw [PureDP] at *
  apply (event_eq_singleton _ _).mpr
  apply (event_eq_singleton _ _).mp at Hε
  simp [DP_singleton] at *
  intro l₁ l₂ N x
  apply (@le_trans _ _ _ (ENNReal.ofReal (Real.exp ↑ε₁)) _ (Hε l₁ l₂ N x))
  apply ENNReal.coe_mono
  refine (Real.toNNReal_le_toNNReal_iff ?a.hp).mpr ?a.a
  · exact Real.exp_nonneg ↑ε₂
  · exact Real.exp_le_exp.mpr H


theorem ApproximateDP_of_DP (m : Mechanism T U) (ε : ℝ) (h : DP m ε) :
  ∀ δ : NNReal, DP' m ε δ := by
  simp [DP] at h
  simp [DP']
  intros δ l₁ l₂ neighs S
  replace h := h l₁ l₂ neighs S
  rw [ENNReal.div_le_iff_le_mul ?G1 ?G2] at h
  case G1 =>
    right
    simp
  case G2 =>
    left
    have H1 : (∑' (x : U), if x ∈ S then (m l₂) x else 0) ≤ (∑' (x : U), m l₂ x) := by
      apply ENNReal.tsum_le_tsum
      intro u
      split <;> simp
    rw [PMF.tsum_coe] at H1
    intro HK
    simp_all
  apply le_trans h
  simp

/--
Pure DP is no weaker than approximate DP, up to a loss of parameters
-/
lemma pure_ApproximateDP [Countable U] {m : Mechanism T U} :
    ∃ (degrade : (δ : NNReal) -> (ε' : NNReal) -> NNReal), ∀ (δ : NNReal) (_ : 0 < δ) (ε' : NNReal),
     (DP m (degrade δ ε') -> ApproximateDP m ε' δ) := by
  let degrade (_ : NNReal) (ε' : NNReal) : NNReal := ε'
  exists degrade
  intro δ _ ε' HDP
  rw [ApproximateDP]
  apply ApproximateDP_of_DP
  have R1 : degrade δ ε' = ε' := by stop simp
  rw [R1] at HDP
  trivial

end SLang
