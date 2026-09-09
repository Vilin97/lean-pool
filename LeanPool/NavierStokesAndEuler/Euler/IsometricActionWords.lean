/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Exact word-norm invariance along a genuine isometric orbit

Every actual derivative word of a smooth linear-isometric orbit is the orbit
of its derivative at zero. Consequently its fixed-Sobolev word block is
independent of the translation parameter, with constant one and no radius
change. This applies equally to spatial L² and its time-function spaces.
-/

@[expose] public section


noncomputable section

namespace EulerIsometricAction

open ContinuousLinearMap Finset EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (τ : X → E →ₗᵢ[ℝ] E) (hadd : ∀ a b u, τ a (τ b u) = τ (a + b) u)
  (hzero : ∀ u, τ 0 u = u)

/-- Derivative at zero, given by `fderiv ℝ (fun a => τ a u) 0 v`. -/
def derivativeAtZero (u : E) (v : X) : E := fderiv ℝ (fun a => τ a u) 0 v

include hadd in
theorem derivativeAtZero_translation (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u)) (v a : X) :
    τ a (derivativeAtZero τ u v) = fderiv ℝ (fun b => τ b u) a v := by
  have h := hasFDerivAt_all τ hadd u (fderiv ℝ (fun b => τ b u) 0)
    ((hu.differentiable (by simp) (0 : X)).hasFDerivAt) a
  exact (congrArg (fun D : X →L[ℝ] E => D v) h.fderiv).symm

include hadd in
theorem derivativeAtZero_smooth (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u)) (v : X) :
    ContDiff ℝ ∞ (fun a => τ a (derivativeAtZero τ u v)) := by
  have he : (fun a => τ a (derivativeAtZero τ u v)) =
      fun a => fderiv ℝ (fun b => τ b u) a v :=
    funext (fun a => derivativeAtZero_translation τ hadd u hu v a)
  rw [he]
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Word at zero, given by `wordDerivative directions (fun a => τ a u) w 0`. -/
def wordAtZero (directions : ι → X) (u : E) {n : ℕ} (w : Fin n → ι) : E :=
  wordDerivative directions (fun a => τ a u) w 0

include hzero in
theorem wordAtZero_zero (directions : ι → X) (u : E) (w : Fin 0 → ι) :
    wordAtZero τ directions u w = u := by
  simp only [wordAtZero,wordDerivative_zero,hzero]

include hadd in
theorem wordAtZero_snoc (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) (i : ι) :
    wordAtZero τ directions u (Fin.snoc w i) =
      wordAtZero τ directions (derivativeAtZero τ u (directions i)) w := by
  have he : directional directions (fun a => τ a u) i =
      fun a => τ a (derivativeAtZero τ u (directions i)) :=
    funext (fun a => (derivativeAtZero_translation τ hadd u hu (directions i) a).symm)
  unfold wordAtZero
  rw [wordDerivative_snoc directions _ hu w i 0,he]

include hadd hzero in
theorem wordAtZero_translation (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) (a : X) :
    τ a (wordAtZero τ directions u w) = wordDerivative directions (fun b => τ b u) w a := by
  induction n generalizing u with
  | zero => simp only [wordAtZero_zero τ hzero,wordDerivative_zero]
  | succ n ih =>
    have hw : wordAtZero τ directions u w =
        wordAtZero τ directions (derivativeAtZero τ u (directions (w (Fin.last n)))) (Fin.init w)
            := by
      simpa only [Fin.snoc_init_self] using wordAtZero_snoc τ hadd directions u hu (Fin.init w) (w
          (Fin.last n))
    rw [hw,ih _ (derivativeAtZero_smooth τ hadd u hu _) (Fin.init w)]
    have he : directional directions (fun b => τ b u) (w (Fin.last n)) =
        fun b => τ b (derivativeAtZero τ u (directions (w (Fin.last n)))) :=
      funext (fun b => (derivativeAtZero_translation τ hadd u hu _ b).symm)
    simpa only [Fin.snoc_init_self,he] using
      (wordDerivative_snoc directions (fun b => τ b u) hu (Fin.init w) (w (Fin.last n)) a).symm

include hadd hzero in
theorem wordAtZero_smooth (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    {n : ℕ} (w : Fin n → ι) : ContDiff ℝ ∞ (fun a => τ a (wordAtZero τ directions u w)) := by
  have he : (fun a => τ a (wordAtZero τ directions u w)) =
      wordDerivative directions (fun b => τ b u) w :=
    funext (wordAtZero_translation τ hadd hzero directions u hu w)
  rw [he]
  exact wordDerivative_contDiff directions _ hu w

variable [Fintype ι]

include hadd hzero in
theorem wordSum_orbit_constant (directions : ι → X) (u : E) (hu : ContDiff ℝ ∞ (fun a => τ a u))
    (n : ℕ) (a : X) : wordSum directions (fun b => τ b u) n a =
      wordSum directions (fun b => τ b u) n 0 := by
  unfold wordSum
  apply sum_congr rfl
  intro w _
  rw [← wordAtZero_translation τ hadd hzero directions u hu w a]
  exact (τ a).norm_map (wordAtZero τ directions u w)

include hadd hzero in
theorem baseSize_orbit_constant (directions : ι → X) (q : ℕ) (u : E)
    (hu : ContDiff ℝ ∞ (fun a => τ a u)) (a : X) :
    baseSize directions q (fun b => τ b u) a = baseSize directions q (fun b => τ b u) 0 := by
  unfold baseSize
  apply sum_congr rfl
  intro k _
  exact wordSum_orbit_constant τ hadd hzero directions u hu k a

include hadd hzero in
theorem block_orbit_constant (directions : ι → X) (q : ℕ) (u : E)
    (hu : ContDiff ℝ ∞ (fun a => τ a u)) (n : ℕ) (a : X) :
    block directions q (fun b => τ b u) n a = block directions q (fun b => τ b u) n 0 := by
  unfold block
  apply sum_congr rfl
  intro w _
  have he : wordDerivative directions (fun b => τ b u) w =
      fun b => τ b (wordAtZero τ directions u w) :=
    (funext (wordAtZero_translation τ hadd hzero directions u hu w)).symm
  rw [he]
  exact baseSize_orbit_constant τ hadd hzero directions q _
    (wordAtZero_smooth τ hadd hzero directions u hu w) a

end EulerIsometricAction
