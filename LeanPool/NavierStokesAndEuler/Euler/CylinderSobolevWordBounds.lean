/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOrbit
import LeanPool.NavierStokesAndEuler.Euler.ParameterNestedWordSum
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient

/-!
# Fixed Sobolev path norms and actual external word sums

The finite Sobolev array gives equivalent norms with constants depending
only on its fixed order. No tensor norm conversion or external-order
alphabet factor enters either comparison.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerLpCylinderTranslation EulerParameterWordGevrey
  EulerCylinderSobolev
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Path word operator, given by `(wordOperator P w).compLeftContinuous ℝ K`. -/
def pathWordOperator {q : ℕ} (w : SobolevWord q) :
    C(K,SobolevSpace P q) →L[ℝ] C(K,LiftL2 P) :=
  (wordOperator P w).compLeftContinuous ℝ K

theorem pathWordOperator_norm_le {q : ℕ} (w : SobolevWord q) (u : C(K, SobolevSpace P q)) :
    ‖pathWordOperator P w u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  exact (word_norm_le P (u t) w).trans (u.norm_coe_le_norm t)

theorem path_norm_le_sum_words {q : ℕ} (u : C(K, SobolevSpace P q)) :
    ‖u‖ ≤ ∑ w : SobolevWord q, ‖pathWordOperator P w u‖ := by
  apply (ContinuousMap.norm_le _ (sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro t
  apply (norm_le_sumNorm P (u t)).trans
  exact sum_le_sum (fun w _ => (pathWordOperator P w u).norm_coe_le_norm t)

variable (q : ℕ) (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

theorem pathWordOperator_sobolevOrbit (w : SobolevWord q) :
    pathWordOperator P w ∘ sobolevOrbit P q p hp =
      wordDerivative standardDirection (fun a : LiftTangent => pathTranslate P a p) w.2 := by
  funext a
  apply ContinuousMap.ext
  intro t
  exact sobolevOrbit_coordinate P q p hp a t w

theorem sobolevOrbit_word_coordinate {n : ℕ} (v : Fin n → Fin 4)
    (w : SobolevWord q) (a : LiftTangent) :
    pathWordOperator P w (wordDerivative standardDirection (sobolevOrbit P q p hp) v a) =
      wordDerivative standardDirection
        (wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2) v a :=
            by
  have h := wordDerivative_comp_clm standardDirection (pathWordOperator P w)
    (sobolevOrbit P q p hp) (sobolevOrbit_contDiff P q p hp) v a
  rw [pathWordOperator_sobolevOrbit P q p hp w] at h
  exact h.symm

include hp in
theorem sum_sobolev_word_levels (n : ℕ) (a : LiftTangent) :
    (∑ w : SobolevWord q,
      wordSum standardDirection
        (wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2) n a) =
      block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a := by
  simp only [Fintype.sum_sigma]
  simp_rw [sum_wordSum_wordDerivative standardDirection _ hp]
  rw [block_eq_sum_levels standardDirection q _ hp]
  rw [← Fin.sum_univ_eq_sum_range (fun k =>
    wordSum standardDirection (fun b : LiftTangent => pathTranslate P b p) (n+k) a) (q+1)]
  exact sum_congr rfl (fun k _ => by rw [Nat.add_comm k.val n])

/-- Promotion to the actual Hq path norm costs no external-order factor. -/
theorem sobolevOrbit_wordSum_le_block (n : ℕ) (a : LiftTangent) :
    wordSum standardDirection (sobolevOrbit P q p hp) n a ≤
      block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a := by
  rw [← sum_sobolev_word_levels P q p hp n a]
  unfold wordSum
  calc
    _ ≤ ∑ v : Fin n → Fin 4, ∑ w : SobolevWord q,
        ‖pathWordOperator P w (wordDerivative standardDirection (sobolevOrbit P q p hp) v a)‖ :=
      sum_le_sum (fun v _ => path_norm_le_sum_words P _)
    _ = _ := by
      rw [sum_comm]
      simp_rw [sobolevOrbit_word_coordinate P q p hp]

/-- Returning to the source derivative sum costs only the fixed Hq array size. -/
theorem block_le_card_sobolevOrbit_wordSum (n : ℕ) (a : LiftTangent) :
    block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n a ≤
      (Fintype.card (SobolevWord q) : ℝ)*wordSum standardDirection (sobolevOrbit P q p hp) n a := by
  rw [← sum_sobolev_word_levels P q p hp n a]
  calc
    _ ≤ ∑ _w : SobolevWord q, wordSum standardDirection (sobolevOrbit P q p hp) n a := by
      apply sum_le_sum
      intro w _
      unfold wordSum
      apply sum_le_sum
      intro v _
      rw [← sobolevOrbit_word_coordinate P q p hp v w a]
      exact pathWordOperator_norm_le P w _
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]

end EulerCylinderSmoothOrbit
