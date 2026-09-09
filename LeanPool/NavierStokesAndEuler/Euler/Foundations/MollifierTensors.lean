/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm

/-! Full Fréchet tensor convergence from the genuine cylinder derivative words. -/

@[expose] public section

noncomputable section

namespace EulerMollifierTensors

open MeasureTheory Filter EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerSobolevDerivativeNorm
open scoped ContDiff Topology

variable (period : ℝ)

/-- The operator norm of a difference of derivative tensors is controlled by the finite coordinate
sum. -/
theorem tensor_difference_le_word_sum (m : ℕ) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z‖ ≤
    ∑ w : Fin m → Fin 4,
      ‖iteratedFieldDerivative period w f (euclideanCover period z + x) -
        iteratedFieldDerivative period w g (euclideanCover period z + x)‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 m
    (iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z)
  simpa only [sub_apply,
    ← euclideanLift_iteratedFieldDerivative period _ f hf,
    ← euclideanLift_iteratedFieldDerivative period _ g hg,
    euclideanLift_eq_translated_cover, translated] using h

/-- Uniform Cauchy convergence of every coordinate word gives uniform Cauchy convergence of the full
tensor. -/
theorem tensor_uniformCauchy_of_words (m : ℕ) (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ w : Fin m → Fin 4,
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (x : LiftDomain period) :
    UniformCauchySeqOn
      (fun k => iteratedFDeriv ℝ m (euclideanLift period (f k) x)) atTop Set.univ := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hc : 0 < (4 : ℝ)^m := pow_pos (by norm_num) _
  have hsmall := fun w : Fin m → Fin 4 =>
    Metric.uniformCauchySeqOn_iff.mp (hC w) (ε / (4 : ℝ)^m) (div_pos hε hc)
  choose N hN using hsmall
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl z _
  have hword (w : Fin m → Fin 4) :
      ‖iteratedFieldDerivative period w (f k) (euclideanCover period z + x) -
        iteratedFieldDerivative period w (f l) (euclideanCover period z + x)‖ < ε / (4 : ℝ)^m := by
    simpa only [dist_eq_norm] using hN w k
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hk) l
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hl)
      (euclideanCover period z + x) (Set.mem_univ _)
  rw [dist_eq_norm]
  apply (tensor_difference_le_word_sum period m (f k) (f l) (hf k) (hf l) x z).trans_lt
  calc
    _ < ∑ _w : Fin m → Fin 4, ε / (4 : ℝ)^m := by
      apply Finset.sum_lt_sum (fun w _ => (hword w).le)
      exact ⟨fun _ => 0, Finset.mem_univ _, hword _⟩
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
      push_cast
      exact mul_div_cancel₀ ε hc.ne'

end EulerMollifierTensors
