/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatMildEuclidean

/-!
# Initial trace of the Euclidean symmetric-tensor heat evolution

The positive-time classical matrix solution is placed in its natural
closed-time path space.  For Lipschitz initial coefficients this path is
continuous in the bounded-continuous-function norm, agrees with the
classical mild formula for every `t > t₀`, and takes the prescribed initial
matrix exactly at `t₀`.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The entrywise mild heat evolution as a total path of matrices of bounded
continuous functions.  Unlike the positive-time spatial formula, this is
defined at the initial time as well. -/
def matrixHeatMildPathBcf (n d : ℕ) (t₀ : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C : ℝ} (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C) :
    ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ) :=
  fun t i j ↦ heatMildValuePathBcf t₀ (u₀ i j) (hq i j)
    (fun s y ↦ hqb s y i j) t

/-- At positive time, evaluation of the total path is the previously
constructed classical spatial mild solution. -/
theorem matrixHeatMildPathBcf_apply_of_lt
    {n d : ℕ} {t₀ t : ℝ} (ht : t₀ < t)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C : ℝ} (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (x : Fin n → ℝ) :
    (matrixHeatMildPathBcf n d t₀ u₀ hq hqb t).map (fun f ↦ f x) =
      matrixHeatMildSpatialND n d t₀ t u₀ q x := by
  ext i j
  simp only [matrixHeatMildPathBcf, Matrix.map_apply,
    matrixHeatMildSpatialND]
  rw [heatMildValuePathBcf_of_lt ht, heatMildValueNDbcf_apply]
  rfl

/-- The total matrix path takes the prescribed initial coefficient matrix
exactly at `t₀`. -/
theorem matrixHeatMildPathBcf_initial
    {n d : ℕ} (t₀ : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C : ℝ} (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C) :
    matrixHeatMildPathBcf n d t₀ u₀ hq hqb t₀ = u₀ := by
  apply Matrix.ext
  intro i j
  exact heatMildValuePathBcf_initial t₀ (u₀ i j) (hq i j)
    (fun s y ↦ hqb s y i j)

/-- Lipschitz initial coefficients give a matrix-valued mild trajectory that
is continuous in the product `C_b` norm on the whole closed time interval. -/
theorem continuousOn_matrixHeatMildPathBcf_Icc
    {n d : ℕ} (t₀ T : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {L : ℝ} (hLnn : 0 ≤ L)
    (hlip : ∀ a b i j, |u₀ i j a - u₀ i j b| ≤ L * ‖a - b‖)
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C : ℝ} (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C) :
    ContinuousOn (matrixHeatMildPathBcf n d t₀ u₀ hq hqb)
      (Set.Icc t₀ T) := by
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  exact continuousOn_heatMildValuePathBcf_Icc t₀ T (u₀ i j) hLnn
    (fun a b ↦ hlip a b i j) (hq i j) (fun s y ↦ hqb s y i j)

/-- Symmetry is preserved by the total path, including at the initial time. -/
theorem matrixHeatMildPathBcf_isSymm
    {n d : ℕ} (t₀ : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C : ℝ} (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hu₀ : ∀ i j, u₀ i j = u₀ j i)
    (hqSymm : ∀ s i j, q s i j = q s j i)
    (t : ℝ) :
    (matrixHeatMildPathBcf n d t₀ u₀ hq hqb t).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [matrixHeatMildPathBcf]
  rw [hu₀ i j]
  congr 1
  funext s
  exact (hqSymm s i j).symm

end AnalyticPDE
end RicciFlow
