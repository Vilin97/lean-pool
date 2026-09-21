/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildParabolicSchauder

/-!
# Quantitative Hessian control for Euclidean tensor heat flow

The scalar full-Hessian Schauder estimate is lifted to every coefficient of
the finite symmetric-matrix model for a covariant two-tensor.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Every coefficient of the actual matrix-valued parabolic second jet obeys
the explicit full mixed-Hessian Schauder bound, uniformly under common Holder
constants for the initial tensor and forcing. -/
theorem norm_matrixHeatMildParabolicSecondJetND_entry_spaceSecondDeriv_le
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y i j, |u₀ i j y - u₀ i j x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) (i j : Fin d) :
    ‖(heatMildParabolicSecondJetND (t₀ := t₀) hr0 (u₀ i j) (hq i j) hH
      (fun s y ↦ hqb s y i j)
      (fun s y z ↦ hqholder s y z i j)).spaceSecondDeriv (t, x)‖ ≤
      (∑ a : Fin n, ∑ b : Fin n,
        H₀ * (t - t₀) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r a b) +
      ∑ a : Fin n, ∑ b : Fin n,
        H * heatHessianEntryHolderMoment n r a b *
          ((t - t₀) ^ (r / 2) / (r / 2)) := by
  simpa [heatMildParabolicSecondJetND, heatMildSpaceHessianND, ht] using
    (norm_heatMildSpatialHessianCLM_le_explicit ht hr0 (u₀ i j) hH₀
      (fun y z ↦ hu₀holder y z i j) (hq i j) hH
      (fun s y ↦ hqb s y i j) (fun s y z ↦ hqholder s y z i j) x)

/-- Entrywise tensor form of the non-singular C2 initial-data endpoint.  Each
matrix coefficient carries its actual bounded first and second derivatives,
so the homogeneous Hessian is controlled uniformly down to the initial time. -/
theorem norm_matrixHeatMildParabolicSecondJetND_entry_spaceSecondDeriv_le_of_boundedC2
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) (i j : Fin d) :
    ‖(heatMildParabolicSecondJetND (t₀ := t₀) hr0 (D i j).value
      (hq i j) hH (fun s y ↦ hqb s y i j)
      (fun s y z ↦ hqholder s y z i j)).spaceSecondDeriv (t, x)‖ ≤
      (∑ a : Fin n, ∑ b : Fin n, ‖(D i j).second a b‖) +
      ∑ a : Fin n, ∑ b : Fin n,
        H * heatHessianEntryHolderMoment n r a b *
          ((t - t₀) ^ (r / 2) / (r / 2)) := by
  simpa [heatMildParabolicSecondJetND, heatMildSpaceHessianND, ht] using
    (norm_heatMildSpatialHessianCLM_le_of_boundedC2 ht hr0 (D i j)
      (hq i j) hH (fun s y ↦ hqb s y i j)
      (fun s y z ↦ hqholder s y z i j) x)

/-- Every tensor coefficient of the genuine parabolic second jet has a
spatially Holder full Frechet Hessian, uniformly in positive final time. -/
theorem norm_matrixHeatMildParabolicSecondJetND_entry_spaceSecondDeriv_sub_le_holder
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r) (hr1 : r < 1)
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n))
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ i j a b x y,
      |(D i j).second a b x - (D i j).second a b y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) (i j : Fin d) :
    ‖((matrixHeatMildParabolicSecondJetND (t₀ := t₀) hr0
        (fun i j ↦ (D i j).value) hq hH hqb hqholder).entryJet i j).spaceSecondDeriv
          (t, x) -
      ((matrixHeatMildParabolicSecondJetND (t₀ := t₀) hr0
        (fun i j ↦ (D i j).value) hq hH hqb hqholder).entryJet i j).spaceSecondDeriv
          (t, y)‖ ≤
      heatMildHessianSpatialHolderConstant n r H₀ H * ‖x - y‖ ^ r := by
  have hx :
      ((matrixHeatMildParabolicSecondJetND (t₀ := t₀) hr0
        (fun i j ↦ (D i j).value) hq hH hqb hqholder).entryJet i j).spaceSecondDeriv
          (t, x) =
      heatMildSpatialHessianCLM ht.le hr0 (D i j).value (hq i j) hH
        (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) x := by
    change heatMildSpaceHessianND t₀ hr0 (D i j).value (hq i j) hH
        (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) (t, x) = _
    simp [heatMildSpaceHessianND, ht]
  have hy :
      ((matrixHeatMildParabolicSecondJetND (t₀ := t₀) hr0
        (fun i j ↦ (D i j).value) hq hH hqb hqholder).entryJet i j).spaceSecondDeriv
          (t, y) =
      heatMildSpatialHessianCLM ht.le hr0 (D i j).value (hq i j) hH
        (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) y := by
    change heatMildSpaceHessianND t₀ hr0 (D i j).value (hq i j) hH
        (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) (t, y) = _
    simp [heatMildSpaceHessianND, ht]
  rw [hx, hy]
  exact norm_heatMildSpatialHessianCLM_sub_le_holder ht hr0 hr1 (D i j) hH₀
    (fun a b x y ↦ hsecondHolder i j a b x y) (hq i j) hH
    (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) x y

/-- Matrix-valued field of genuine mild Hessians, represented entrywise. -/
def matrixHeatMildHessianFieldND
    {n d : ℕ} {r : ℝ} (t₀ : ℝ) (hr0 : 0 < r)
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ℝ × (Fin n → ℝ) → Matrix (Fin d) (Fin d)
      ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  fun z i j ↦ heatMildHessianFieldND t₀ hr0 (D i j) (hq i j) hH
    (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) z

/-- **Every tensor coefficient of the genuine mild Hessian is parabolically
`r`-Holder with one uniform constant.** -/
theorem parabolicHolderWith_matrixHeatMildHessianFieldND_entry
    {n d : ℕ} (t₀ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n))
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ i j a b x y,
      |(D i j).second a b x - (D i j).second a b y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (i j : Fin d) :
    ParabolicHolderWith (heatMildHessianParabolicHolderConstant n r H₀ H) r
      (fun z ↦ matrixHeatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder z i j)
      {p : ℝ × (Fin n → ℝ) | t₀ < p.1} := by
  simpa only [matrixHeatMildHessianFieldND] using
    (parabolicHolderWith_heatMildHessianFieldND t₀ hr0 hr1 (D i j) hH₀
      (fun a b x y ↦ hsecondHolder i j a b x y) (hq i j) hH
      (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j))

/-- On the positive-time cylinder, the matrix Hessian field is exactly the
space-second-derivative component of the constructed parabolic jet. -/
theorem matrixHeatMildHessianFieldND_eq_entryJet_spaceSecondDeriv
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (D : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n))
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) (i j : Fin d) :
    matrixHeatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder (t, x) i j =
      ((matrixHeatMildParabolicSecondJetND (t₀ := t₀) hr0
        (fun i j ↦ (D i j).value) hq hH hqb hqholder).entryJet i j).spaceSecondDeriv
          (t, x) := by
  change heatMildHessianFieldND t₀ hr0 (D i j) (hq i j) hH
      (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) (t, x) =
    heatMildSpaceHessianND t₀ hr0 (D i j).value (hq i j) hH
      (fun s y ↦ hqb s y i j) (fun s x y ↦ hqholder s x y i j) (t, x)
  simp only [heatMildHessianFieldND, heatMildSpaceHessianND, dif_pos ht]

end AnalyticPDE
end RicciFlow
