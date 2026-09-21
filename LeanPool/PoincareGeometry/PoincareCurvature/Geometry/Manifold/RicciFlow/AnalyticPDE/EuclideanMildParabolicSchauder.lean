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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildSchauder
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelHessianTimeHolder

/-!
# Parabolic Holder control of the Euclidean mild Hessian

This module combines the translated homogeneous heat Hessian with the full
space-time Holder estimate for the Duhamel Hessian.  The result is the actual
Frechet Hessian of the mild solution, not merely a coordinate trace.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section MildParabolicHessian

local instance mildParabolicCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildParabolicCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildParabolicCoordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- The homogeneous heat Hessian with absolute time shifted by `t₀`. -/
def shiftedHeatSemigroupHessianFieldND
    {n : ℕ} (t₀ : ℝ) (D : EuclideanBoundedC2Data n) :
    ℝ × (Fin n → ℝ) →
      (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  fun z ↦ heatSemigroupHessianCLM (z.1 - t₀) D.value z.2

/-- Time translation preserves the parabolic Holder estimate for the
homogeneous heat Hessian. -/
theorem parabolicHolderWith_shiftedHeatSemigroupHessianFieldND
    {n : ℕ} (t₀ : ℝ) (D : EuclideanBoundedC2Data n) {r H₀ : ℝ}
    (hr0 : 0 < r) (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicHolderWith
      (heatInitialHessianSpatialHolderConstant n H₀ +
        heatInitialHessianTimeHolderConstant n r H₀) r
      (shiftedHeatSemigroupHessianFieldND t₀ D)
      {p : ℝ × (Fin n → ℝ) | t₀ < p.1} := by
  intro p hp q hq
  have hp' : (0 : ℝ) < p.1 - t₀ := sub_pos.mpr hp
  have hq' : (0 : ℝ) < q.1 - t₀ := sub_pos.mpr hq
  have hmain := parabolicHolderWith_heatSemigroupHessianCLM
    D hr0.le hH₀ hsecondHolder
      (p := (p.1 - t₀, p.2)) (q := (q.1 - t₀, q.2)) hp' hq'
  change ‖shiftedHeatSemigroupHessianFieldND t₀ D p -
    shiftedHeatSemigroupHessianFieldND t₀ D q‖ ≤ _
  refine hmain.trans_eq ?_
  congr 1
  unfold parabolicDistance
  congr 2
  ring_nf

/-- The genuine mild Hessian as a total time-space field, set to zero before
the positive-time cylinder. -/
def heatMildHessianFieldND
    {n : ℕ} {r : ℝ} (t₀ : ℝ) (hr0 : 0 < r)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ℝ × (Fin n → ℝ) →
      (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  fun z ↦ if hz : t₀ < z.1 then
    heatMildSpatialHessianCLM hz.le hr0 D.value hq hH hqb hqholder z.2
  else 0

/-- Full parabolic Holder constant for the mild Hessian. -/
def heatMildHessianParabolicHolderConstant
    (n : ℕ) (r H₀ H : ℝ) : ℝ :=
  (heatInitialHessianSpatialHolderConstant n H₀ +
    heatInitialHessianTimeHolderConstant n r H₀) +
  (heatDuhamelHessianSpatialHolderConstant n r H +
    heatDuhamelHessianTimeHolderConstant n r H)

/-- **The genuine full Frechet Hessian of the Euclidean mild solution is
parabolically `r`-Holder on the positive-time cylinder.** -/
theorem parabolicHolderWith_heatMildHessianFieldND
    {n : ℕ} (t₀ : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicHolderWith
      (heatMildHessianParabolicHolderConstant n r H₀ H) r
      (heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder)
      {p : ℝ × (Fin n → ℝ) | t₀ < p.1} := by
  let S : Set (ℝ × (Fin n → ℝ)) := {p | t₀ < p.1}
  have hhom := parabolicHolderWith_shiftedHeatSemigroupHessianFieldND
    t₀ D hr0 hH₀ hsecondHolder
  have hduhClosed := parabolicHolderWith_heatDuhamelHessianFieldND
    t₀ hr0 hr1 hq hH hqb hqholder
  have hsub : S ⊆ {p : ℝ × (Fin n → ℝ) | t₀ ≤ p.1} := by
    intro p hp
    change t₀ < p.1 at hp
    exact hp.le
  have hduh := hduhClosed.mono_set hsub
  have hadd := hhom.add hduh
  intro p hp z hz
  have hp' : t₀ < p.1 := hp
  have hz' : t₀ < z.1 := hz
  have hbound := hadd hp hz
  change ‖heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder p -
    heatMildHessianFieldND t₀ hr0 D hq hH hqb hqholder z‖ ≤ _
  simp only [heatMildHessianFieldND, dif_pos hp', dif_pos hz',
    heatMildSpatialHessianCLM]
  simpa only [heatMildHessianParabolicHolderConstant,
    shiftedHeatSemigroupHessianFieldND, heatDuhamelHessianFieldND,
    dif_pos hp'.le, dif_pos hz'.le] using hbound

end MildParabolicHessian

end AnalyticPDE
end RicciFlow
