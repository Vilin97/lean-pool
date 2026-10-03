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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder

/-!
# Parabolic Holder endpoint for the homogeneous Euclidean heat Hessian

The spatial and temporal endpoint estimates for bounded C2,alpha data are
combined here into genuine parabolic Holder control of the full Frechet
Hessian on the positive-time half cylinder.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Finite-dimensional constant for the spatial Hessian Holder estimate. -/
def heatInitialHessianSpatialHolderConstant (n : ℕ) (H₂ : ℝ) : ℝ :=
  ∑ _j : Fin n, ∑ _k : Fin n, H₂ * (n : ℝ)

/-- Finite-dimensional constant for the temporal Hessian Holder estimate. -/
def heatInitialHessianTimeHolderConstant (n : ℕ) (r H₂ : ℝ) : ℝ :=
  ∑ _j : Fin n, ∑ _k : Fin n,
    H₂ * (n : ℝ) * gaussianAbsMoment r

lemma heatInitialHessianSpatialHolderConstant_nonneg
    (n : ℕ) {H₂ : ℝ} (hH₂ : 0 ≤ H₂) :
    0 ≤ heatInitialHessianSpatialHolderConstant n H₂ := by
  unfold heatInitialHessianSpatialHolderConstant
  positivity

lemma heatInitialHessianTimeHolderConstant_nonneg
    (n : ℕ) (r : ℝ) {H₂ : ℝ} (hH₂ : 0 ≤ H₂) :
    0 ≤ heatInitialHessianTimeHolderConstant n r H₂ := by
  unfold heatInitialHessianTimeHolderConstant
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (mul_nonneg hH₂ (Nat.cast_nonneg n))
      (gaussianAbsMoment_nonneg r)

/-- Distance-form spatial Holder estimate for the homogeneous heat Hessian. -/
theorem norm_heatSemigroupHessianCLM_sub_le_dist_rpow
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t r H₂ : ℝ}
    (ht : 0 < t) (hr : 0 ≤ r) (hH₂ : 0 ≤ H₂)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t D.value x -
        heatSemigroupHessianCLM t D.value y‖ ≤
      heatInitialHessianSpatialHolderConstant n H₂ * ‖x - y‖ ^ r := by
  have hmain := D.norm_heatSemigroupHessianCLM_sub_le
    ht hH₂ hsecondHolder x y
  refine hmain.trans ?_
  have hcoord : ∀ ell : Fin n, |(x - y) ell| ≤ ‖x - y‖ := by
    intro ell
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x - y) ell
  calc
    (∑ _j : Fin n, ∑ _k : Fin n,
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r) ≤
        ∑ _j : Fin n, ∑ _k : Fin n,
          H₂ * ∑ _ell : Fin n, ‖x - y‖ ^ r := by
      gcongr with j k ell
      exact hcoord ell
    _ = heatInitialHessianSpatialHolderConstant n H₂ * ‖x - y‖ ^ r := by
      simp only [heatInitialHessianSpatialHolderConstant, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring

/-- The full homogeneous heat Hessian is parabolically r-Holder on positive
times, with constants determined by the Holder modulus of the actual initial
Hessian. -/
theorem parabolicHolderWith_heatSemigroupHessianCLM
    {n : ℕ} (D : EuclideanBoundedC2Data n) {r H₂ : ℝ}
    (hr : 0 ≤ r) (hH₂ : 0 ≤ H₂)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicHolderWith
      (heatInitialHessianSpatialHolderConstant n H₂ +
        heatInitialHessianTimeHolderConstant n r H₂) r
      (fun p : ℝ × (Fin n → ℝ) ↦
        heatSemigroupHessianCLM p.1 D.value p.2)
      {p : ℝ × (Fin n → ℝ) | 0 < p.1} := by
  apply parabolicHolderWith_of_forall_same_time_same_space hr
    (heatInitialHessianSpatialHolderConstant_nonneg n hH₂)
    (heatInitialHessianTimeHolderConstant_nonneg n r hH₂)
  · rintro ⟨t, x⟩ ht ⟨s, y⟩ hs
    exact ht
  · intro t x y htx hty
    have ht : 0 < t := htx
    have hmain := D.norm_heatSemigroupHessianCLM_sub_le
      ht hH₂ hsecondHolder x y
    refine hmain.trans ?_
    have hcoord : ∀ ell : Fin n, |(x - y) ell| ≤ dist x y := by
      intro ell
      rw [dist_eq_norm]
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        norm_le_pi_norm (x - y) ell
    calc
      (∑ _j : Fin n, ∑ _k : Fin n,
          H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r) ≤
          ∑ _j : Fin n, ∑ _k : Fin n,
            H₂ * ∑ _ell : Fin n, dist x y ^ r := by
        gcongr with j k ell
        exact hcoord ell
      _ = heatInitialHessianSpatialHolderConstant n H₂ * dist x y ^ r := by
        simp only [heatInitialHessianSpatialHolderConstant, Finset.sum_const,
          nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        ring
  · intro x t s htx hsx
    have ht : 0 < t := htx
    have hs : 0 < s := hsx
    change ‖heatSemigroupHessianCLM t D.value x -
      heatSemigroupHessianCLM s D.value x‖ ≤
        heatInitialHessianTimeHolderConstant n r H₂ * |t - s| ^ (r / 2)
    rcases le_total t s with hts | hst
    · have hmain := D.norm_heatSemigroupHessianCLM_time_sub_le
        ht hts hr hH₂ hsecondHolder x
      rw [norm_sub_rev (heatSemigroupHessianCLM t D.value x)
        (heatSemigroupHessianCLM s D.value x)]
      refine hmain.trans ?_
      have habs : |t - s| = s - t := by
        rw [abs_of_nonpos (sub_nonpos.mpr hts)]
        ring
      rw [habs, Real.rpow_div_two_eq_sqrt r (sub_nonneg.mpr hts)]
      simp only [heatInitialHessianTimeHolderConstant, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring_nf
      exact le_rfl
    · have hmain := D.norm_heatSemigroupHessianCLM_time_sub_le
        hs hst hr hH₂ hsecondHolder x
      refine hmain.trans ?_
      have habs : |t - s| = t - s := abs_of_nonneg (sub_nonneg.mpr hst)
      rw [habs, Real.rpow_div_two_eq_sqrt r (sub_nonneg.mpr hst)]
      simp only [heatInitialHessianTimeHolderConstant, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring_nf
      exact le_rfl

end AnalyticPDE
end RicciFlow
