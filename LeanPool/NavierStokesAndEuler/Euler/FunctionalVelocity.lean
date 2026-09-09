/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ExternalTransportCommutator
public import LeanPool.NavierStokesAndEuler.Euler.LiftedTransportComponents

@[expose] public section

/-! Actual four-dimensional velocity fields assembled from bounded vector functionals. -/

noncomputable section

namespace EulerFunctionalVelocity

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
  EulerCylinderSobolev EulerRealCylinder EulerVectorCylinder EulerH6Nonlinear
open scoped ContDiff ENNReal Topology

/-- Assemble the four actual cylinder-velocity components as a bounded linear map. -/
def velocityMap (L : Fin 4 → Vector3 →L[ℝ] ℝ) : Vector3 →L[ℝ] Domain 4 :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi L)

@[simp] theorem velocityMap_apply (L : Fin 4 → Vector3 →L[ℝ] ℝ) (z : Vector3) (i : Fin 4) :
    velocityMap L z i = L i z := rfl

variable (period : ℝ) [Fact (0 < period)]

/-- Coordinate decomposition of the actual external-word Sobolev norm. -/
theorem wordSobolevNorm_coordinates (q n d : ℕ) (f : LiftDomain period → Domain d)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period)) :
    wordSobolevNorm period q n f ≤ ∑ i : Fin d, wordSobolevNorm period q n (coordinate d i ∘ f) :=
      by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Fin 4))) (fun w _ =>
    vector_sobolevNorm_le_sum_coordinates period d q (iteratedFieldDerivative period w f)
      (iteratedFieldDerivative_smooth period w f hf)
      (fun i j _ a => postcomp_word_memLp period (le_refl j) (coordinate d i)
        (iteratedFieldDerivative period w f) (iteratedFieldDerivative_smooth period w f hf)
        (fun r _ b => word_all_memLp period w f hfL r b) a))
  rw [Finset.sum_comm] at h
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro w _
  rw [iteratedFieldDerivative_postcomp period (coordinate d i) w f hf]

/-- Passing from a three-vector to its four lifted velocity coefficients costs only the fixed dimension factor. -/
theorem velocityMap_word_bound (q n : ℕ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (f : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period)) :
    wordSobolevNorm period q n (velocityMap L ∘ f) ≤ 4 * wordSobolevNorm period q n f := by
  have hb := postcomp_smooth period (velocityMap L) f hf
  have hbL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w (velocityMap L ∘ f))
    2 (liftMeasure period) :=
    fun j w => postcomp_word_memLp period (le_refl j) (velocityMap L) f hf (fun r _ a => hfL r a) w
  have h := wordSobolevNorm_coordinates period q n 4 (velocityMap L ∘ f) hb hbL
  have hc (i : Fin 4) : coordinate 4 i ∘ (velocityMap L ∘ f) = L i ∘ f := rfl
  simp only [hc] at h
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun i _ =>
    wordSobolevNorm_postcomp_le period q n (L i) (hL i) f hf hfL)
  exact h.trans (hs.trans_eq (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat]))

end EulerFunctionalVelocity
