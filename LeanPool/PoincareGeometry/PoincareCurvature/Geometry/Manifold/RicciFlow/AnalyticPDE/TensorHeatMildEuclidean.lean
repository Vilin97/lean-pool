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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildClassical
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Inhomogeneous Euclidean heat evolution for symmetric tensor coefficients

The scalar classical mild equation is assembled entrywise into a finite
matrix field.  This gives the full constant-principal-part local model used
for symmetric covariant two-tensors: symmetry is preserved, every spatial
slice is genuinely `C²`, and the matrix-valued time derivative equals the
entrywise Hessian trace plus the source.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The complete entrywise mild heat evolution of a finite matrix of bounded
continuous coefficient functions. -/
def matrixHeatMildSpatialND (n d : ℕ) (t₀ t : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (x : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => heatMildSpatialND t₀ t (u₀ i j) (fun s => q s i j) x

/-- The entrywise spatial Laplacian of the matrix mild evolution. -/
def matrixHeatMildLaplacianND (n d : ℕ) (t₀ t : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (x : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => heatMildSpatialLaplacianND t₀ t (u₀ i j) (fun s => q s i j) x

/-- Symmetric initial coefficients and symmetric forcing produce symmetric
coefficients at every time. -/
theorem matrixHeatMildSpatialND_isSymm
    {n d : ℕ} (t₀ t : ℝ)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    (hu₀ : ∀ i j, u₀ i j = u₀ j i)
    (hqSymm : ∀ s i j, q s i j = q s j i)
    (x : Fin n → ℝ) :
    (matrixHeatMildSpatialND n d t₀ t u₀ q x).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [matrixHeatMildSpatialND]
  rw [hu₀ i j]
  congr 1
  funext s
  rw [hqSymm s i j]

/-- Every positive-time matrix slice is genuinely twice continuously Frechet
differentiable in the spatial variables, entry by entry. -/
theorem contDiff_two_matrixHeatMildSpatialND
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s => q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ∀ i j, ContDiff ℝ 2 (fun x => matrixHeatMildSpatialND n d t₀ t u₀ q x i j) := by
  intro i j
  exact contDiff_two_heatMildSpatialND ht hr0 (u₀ i j) (hq i j) hH
    (fun s y => hqb s y i j) (fun s x y => hqholder s x y i j)

/-- Entrywise, the displayed matrix Laplacian is the trace of the genuine
spatial Frechet Hessian of the mild solution. -/
theorem sum_matrixHeatMildSpatialHessianCLM_diag_eq_laplacian
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s => q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ∀ i j, (∑ k : Fin n,
      heatMildSpatialHessianCLM ht.le hr0 (u₀ i j) (hq i j) hH
        (fun s y => hqb s y i j) (fun s x y => hqholder s x y i j) x
        (Pi.single k 1) (Pi.single k 1)) =
      matrixHeatMildLaplacianND n d t₀ t u₀ q x i j := by
  intro i j
  exact sum_heatMildSpatialHessianCLM_diag_eq_laplacian
    ht hr0 (u₀ i j) (hq i j) hH (fun s y => hqb s y i j)
      (fun s x y => hqholder s x y i j) x

/-- **Classical matrix-valued inhomogeneous heat equation.**  The entrywise
mild construction has actual matrix-valued time derivative equal to its
spatial Laplacian plus the prescribed source. -/
theorem hasDerivAt_matrixHeatMildSpatialND_time
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s => q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ∀ i j, @HasDerivAt ℝ _ ℝ NormedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun u => matrixHeatMildSpatialND n d t₀ u u₀ q x i j)
      (matrixHeatMildLaplacianND n d t₀ t u₀ q x i j + q t i j x) t := by
  intro i j
  exact hasDerivAt_heatMildSpatialND_time_eq_laplacian_add_source
    ht hr0 (u₀ i j) (hq i j) hH (fun s y => hqb s y i j)
      (fun s x y => hqholder s x y i j) x

end AnalyticPDE
end RicciFlow
