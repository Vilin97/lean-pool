/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorDiffusionSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxProduct

/-! The corrector divergence expansion paired with a selected pulled gradient.
-/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

/-- Pairing the selected corrector flux divergence with its pulled gradient
gives the corrector time term, the two flow errors, and the Frobenius
contraction with `gradG`. -/
theorem correctorFlux_mulVec_G_divergence_expansion
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) (hk : Odd k)
    (hxi : I.xiMK m k t ≠ 0)
    {LB : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    {LG : Vec 2 →L[ℝ] Vec 2}
    (hB : ∀ i j, HasFDerivAt
      (fun y => correctorFlux I hΦ m κ k t y i j) (LB i j) x)
    (hG : HasFDerivAt
      (fun y => G I hΦ m T (lIdx β I.Λ m k) t y) LG x) :
    vecDiv (fun y => (correctorFlux I hΦ m κ k t y).mulVec
        (G I hΦ m T (lIdx β I.Λ m k) t y)) x =
      vecDot (fun j => deriv (fun s => I.chiMK κ m k s
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t)
          (G I hΦ m T (lIdx β I.Λ m k) t x) +
        vecDot (matDiv (correctorDefectMatrix I hΦ m k t κ) x)
          (G I hΦ m T (lIdx β I.Λ m k) t x) +
        vecDot (matDiv (correctorPushforwardMatrix I hΦ m k t κ) x)
          (G I hΦ m T (lIdx β I.Λ m k) t x) +
        frob (correctorFlux I hΦ m κ k t x)
          (gradMatrix (G I hΦ m T (lIdx β I.Λ m k) t) x) := by
  have hcolumns :
      matDiv (correctorFlux I hΦ m κ k t) x =
        (fun j => deriv (fun s => I.chiMK κ m k s
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t) +
          matDiv (correctorDefectMatrix I hΦ m k t κ) x +
          matDiv (correctorPushforwardMatrix I hΦ m k t κ) x := by
    have hflux := diffusionMatrix_mul_one_plus_gradChi_eq_correctorFlux
      I hΦ m hm κ k t hk hxi
    have hmat :
        matDiv (correctorFlux I hΦ m κ k t) x =
          matDiv (fun y => diffusionMatrix I hΦ m κ t y *
            (1 + gradChiTilde I hΦ m κ k t y)) x := by
      ext j
      unfold matDiv
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      funext y
      exact (congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j)
        (congrFun hflux y)).symm
    rw [hmat]
    ext j
    exact diffusionMatrix_selected_corrector_column_divergence_source
      I hΦ m hm k t x κ j hk hxi
  rw [vecDiv_matrixMulVec_frob hB hG, hcolumns]
  simp only [vecDot, Pi.add_apply, Fin.sum_univ_two]
  ring

end AVenhance.Infra.Section5

end
