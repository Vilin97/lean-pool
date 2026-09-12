/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Harmonicity of actual coordinate derivatives on an open subset of R³. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff Topology

theorem partialDerivative_sum (f : Fin 3 → Space → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (j : Fin 3) (x : Space) :
    partialDerivative (fun y => ∑ i : Fin 3, f i y) j x =
      ∑ i : Fin 3, partialDerivative (f i) j x := by
  unfold partialDerivative
  rw [(HasFDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    (((hf i).differentiable (by simp)).differentiableAt).hasFDerivAt)).fderiv]
  simp

theorem laplacian_partialDerivative (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (x : Space) :
    Δ (partialDerivative f i) x = partialDerivative (Δ f) i x := by
  have hsum : Δ f = fun y => ∑ j : Fin 3, partialDerivative (partialDerivative f j) j y :=
    funext fun y => laplacian_eq_coordinate_sum f hf y
  rw [laplacian_eq_coordinate_sum _ (contDiff_partialDerivative f hf i) x, hsum,
    partialDerivative_sum _ (fun j => contDiff_partialDerivative _
      (contDiff_partialDerivative f hf j) j)]
  apply Finset.sum_congr rfl
  intro j _
  have heq : partialDerivative (partialDerivative f i) j =
      partialDerivative (partialDerivative f j) i :=
    funext fun y => partialDerivative_comm f (hf.of_le (by simp)) i j y
  rw [heq]
  exact partialDerivative_comm (partialDerivative f j)
    ((contDiff_partialDerivative f hf j).of_le (by simp)) i j x

/-- Differentiating a harmonic function preserves harmonicity on the same open set. -/
theorem partialDerivative_harmonic_on (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (U : Set Space) (hU : IsOpen U) (hh : ∀ x ∈ U, Δ f x = 0) (i : Fin 3) :
    ∀ x ∈ U, Δ (partialDerivative f i) x = 0 := by
  intro x hx
  rw [laplacian_partialDerivative f hf i x]
  have heq : Δ f =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hh y hy
  unfold partialDerivative
  rw [heq.fderiv_eq]
  simp

/-- Word derivative as an element of `word, f => partialDerivative (wordDerivative word f) i`. -/
def wordDerivative : List (Fin 3) → (Space → ℝ) → Space → ℝ
  | [], f => f
  | i :: word, f => partialDerivative (wordDerivative word f) i

theorem wordDerivative_smooth (word : List (Fin 3)) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (wordDerivative word f) := by
  induction word with
  | nil => exact hf
  | cons i word ih => exact contDiff_partialDerivative _ ih i

theorem wordDerivative_harmonic_on (word : List (Fin 3)) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (U : Set Space) (hU : IsOpen U)
    (hh : ∀ x ∈ U, Δ f x = 0) : ∀ x ∈ U, Δ (wordDerivative word f) x = 0 := by
  induction word with
  | nil => exact hh
  | cons i word ih =>
    exact partialDerivative_harmonic_on _ (wordDerivative_smooth word f hf) U hU ih i

end EulerMeanHarmonic
