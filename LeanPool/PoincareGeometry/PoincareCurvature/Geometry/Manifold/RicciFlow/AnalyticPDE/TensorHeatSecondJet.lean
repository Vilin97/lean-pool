/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildSecondJet

/-!
# Parabolic second jet of the Euclidean symmetric-tensor heat flow

This file lifts the scalar second-jet construction entrywise to finite
matrices, the local-coordinate model for covariant two-tensors.  Each matrix
coefficient has actual time, gradient, and Hessian derivatives, and its time
derivative is the corresponding coefficient of `Δu + q`.  Symmetric data
remain symmetric.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- A matrix-valued parabolic second jet, stated entrywise so every scalar
coefficient remains directly auditable. -/
structure MatrixEuclideanParabolicSecondJetND {n d : ℕ}
    (u : ℝ × (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (s : Set (ℝ × (Fin n → ℝ))) where
  entryJet : ∀ i j, EuclideanParabolicSecondJetND (fun z ↦ u z i j) s

/-- The matrix mild solution as one time-space function. -/
def matrixHeatMildSpaceTimeND (n d : ℕ) (t₀ : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)) :
    ℝ × (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ :=
  fun z ↦ matrixHeatMildSpatialND n d t₀ z.1 u₀ q z.2

/-- **The finite-matrix heat evolution has an actual parabolic second jet.**
This is the local symmetric-covariant-two-tensor model, obtained from the
proved scalar heat-kernel derivatives rather than from an assumed PDE
solution. -/
def matrixHeatMildParabolicSecondJetND
    {n d : ℕ} {t₀ r : ℝ} (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    MatrixEuclideanParabolicSecondJetND
      (matrixHeatMildSpaceTimeND n d t₀ u₀ q)
      (Set.Ioi t₀ ×ˢ (Set.univ : Set (Fin n → ℝ))) where
  entryJet := by
    intro i j
    change EuclideanParabolicSecondJetND
      (heatMildSpaceTimeND t₀ (u₀ i j) (fun s ↦ q s i j))
      (Set.Ioi t₀ ×ˢ (Set.univ : Set (Fin n → ℝ)))
    exact heatMildParabolicSecondJetND (t₀ := t₀) hr0 (u₀ i j) (hq i j) hH
      (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j)

@[simp] theorem matrixHeatMildParabolicSecondJetND_entryJet
    {n d : ℕ} {t₀ r : ℝ} (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (i j : Fin d) :
    (matrixHeatMildParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb
      hqholder).entryJet i j =
      heatMildParabolicSecondJetND (t₀ := t₀) hr0 (u₀ i j) (hq i j) hH
        (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) := by
  rfl

/-- Entrywise PDE readout for the matrix second jet. -/
theorem matrixHeatMildParabolicSecondJetND_timeDeriv
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) (i j : Fin d) :
    ((matrixHeatMildParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb
      hqholder).entryJet i j).timeDeriv (t, x) =
      matrixHeatMildLaplacianND n d t₀ t u₀ q x i j + q t i j x := by
  change
    (heatMildParabolicSecondJetND (t₀ := t₀) hr0 (u₀ i j) (hq i j) hH
      (fun s y ↦ hqb s y i j) (fun s y z ↦ hqholder s y z i j)).timeDeriv
        (t, x) =
      heatMildSpatialLaplacianND t₀ t (u₀ i j) (fun s ↦ q s i j) x + q t i j x
  exact heatMildParabolicSecondJetND_timeDeriv ht hr0 (u₀ i j) (hq i j) hH
    (fun s y ↦ hqb s y i j) (fun s y z ↦ hqholder s y z i j) x

/-- Symmetric initial data and forcing make every slice represented by the
matrix second jet symmetric. -/
theorem matrixHeatMildParabolicSecondJetND_isSymm
    {n d : ℕ} (t₀ t : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hu₀ : ∀ i j, u₀ i j = u₀ j i)
    (hqSymm : ∀ s i j, q s i j = q s j i)
    (x : Fin n → ℝ) :
    (matrixHeatMildSpaceTimeND n d t₀ u₀ q (t, x)).IsSymm := by
  exact matrixHeatMildSpatialND_isSymm t₀ t u₀ q hu₀ hqSymm x

end AnalyticPDE
end RicciFlow
