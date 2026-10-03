/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorFluxGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DivergenceLinearity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxDerivative

/-! Finite-support assembly of the selected per-corrector flux divergences. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

/-- Pass a finite selected sum of corrector fluxes through divergence and
apply the per-index expansion. -/
theorem selected_corrector_flux_sum_divergence
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    (S : Finset {k : ℤ // Odd k})
    (hxi : ∀ q ∈ S, I.xiMK m q.1 t ≠ 0)
    {LB : {k : ℤ // Odd k} → Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    {LG : {k : ℤ // Odd k} → Vec 2 →L[ℝ] Vec 2}
    (hB : ∀ q ∈ S, ∀ i j,
      HasFDerivAt (fun y => correctorFlux I hΦ m κ q.1 t y i j)
        (LB q i j) x)
    (hG : ∀ q ∈ S,
      HasFDerivAt
        (fun y => G I hΦ m T (lIdx β I.Λ m q.1) t y) (LG q) x) :
    vecDiv (fun y => ∑ q ∈ S, I.xiMK m q.1 t •
      (correctorFlux I hΦ m κ q.1 t y).mulVec
        (G I hΦ m T (lIdx β I.Λ m q.1) t y)) x =
      ∑ q ∈ S, I.xiMK m q.1 t *
        (vecDot (matDiv (correctorDefectMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
          vecDot (matDiv (correctorPushforwardMatrix I hΦ m q.1 t κ) x)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x) +
          frob (correctorFlux I hΦ m κ q.1 t x)
            (gradMatrix (G I hΦ m T (lIdx β I.Λ m q.1) t) x) +
          vecDot (fun j => deriv (fun s => I.chiMK κ m q.1 s
            (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
            (G I hΦ m T (lIdx β I.Λ m q.1) t x)) := by
  classical
  let F : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun q y =>
    (correctorFlux I hΦ m κ q.1 t y).mulVec
      (G I hΦ m T (lIdx β I.Λ m q.1) t y)
  let LF : {k : ℤ // Odd k} → Vec 2 →L[ℝ] Vec 2 := fun q =>
    ContinuousLinearMap.pi fun i =>
      ∑ j : Fin 2, (
        (G I hΦ m T (lIdx β I.Λ m q.1) t x j) • LB q i j +
          (correctorFlux I hΦ m κ q.1 t x i j) •
            ((ContinuousLinearMap.proj j).comp (LG q)))
  have hF : ∀ q ∈ S, HasFDerivAt (F q) (LF q) x := by
    intro q hq
    simpa [F, LF] using hasFDerivAt_matrix_mulVec (hB q hq) (hG q hq)
  have hsum := vecDiv_finite_weighted_sum S
    (fun q => I.xiMK m q.1 t) F x (LF := LF) hF
  rw [hsum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [correctorFlux_mulVec_G_divergence_expansion I hΦ m hm κ T q.1 t x
    q.2 (hxi q hq) (hB q hq) (hG q hq)]
  simp only [mul_add]
  ring

end AVenhance.Infra.Section5

end
