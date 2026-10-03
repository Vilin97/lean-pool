/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorDiffusionDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiolaDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorLocalization

/-! flow and cutoff specializations of the corrector diffusion rule. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

/-- The per-index corrector diffusion identity with the cofactor Piola
hypothesis discharged from the C² inverse-flow slice. The remaining
differentiability premises are precisely those of the three flux pieces in
the product rule. -/
theorem frozen_corrector_diffusion_column_divergence_flow
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (κ : ℝ) (j : Fin 2)
    {LB : Vec 2 →L[ℝ] Vec 2} {LD LE : Vec 2 →L[ℝ] Vec 2}
    (hB : HasFDerivAt (frozenCorrectorFlux I κ m k j t)
      LB (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (hD : HasFDerivAt (correctorDefectColumn I hΦ m k t κ j) LD x)
    (hE : HasFDerivAt (correctorShearCrossColumn I hΦ m k t κ j) LE x)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    matDiv (correctorFlux I hΦ m κ k t) x j =
      deriv (fun s => I.chiMK κ m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t +
        matDiv (correctorDefectMatrix I hΦ m k t κ) x j +
        matDiv (correctorPushforwardMatrix I hΦ m k t κ) x j := by
  let M := I.xFlowInv hΦ m (lIdx β I.Λ m k) t
  have hM : HasFDerivAt M (fderiv ℝ M x) x := by
    have hMdiff : DifferentiableAt ℝ M x :=
      (xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t).differentiable
        (by norm_num) x
    exact hMdiff.hasFDerivAt
  rcases xFlowInv_cofactor_piolaInputs I hΦ m (lIdx β I.Λ m k) t x with
    ⟨hQ, hPiolaDiv⟩
  exact frozen_corrector_diffusion_column_divergence I hΦ m k t x κ j
    hM hB hD hE hQ hPiolaDiv hdiv

/-- The source's selected diffusion column agrees with the per-index corrector
flux column on the support of its odd cutoff, so the corrected divergence
expansion applies directly to the full twisted diffusion matrix. -/
theorem diffusionMatrix_selected_corrector_column_divergence
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (k : ℤ) (t : ℝ) (x : Vec 2) (κ : ℝ) (j : Fin 2)
    (hk : Odd k) (hxi : I.xiMK m k t ≠ 0)
    {LB : Vec 2 →L[ℝ] Vec 2} {LD LE : Vec 2 →L[ℝ] Vec 2}
    (hB : HasFDerivAt (frozenCorrectorFlux I κ m k j t)
      LB (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (hD : HasFDerivAt (correctorDefectColumn I hΦ m k t κ j) LD x)
    (hE : HasFDerivAt (correctorShearCrossColumn I hΦ m k t κ j) LE x)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    matDiv (fun y => diffusionMatrix I hΦ m κ t y *
      (1 + gradChiTilde I hΦ m κ k t y)) x j =
      deriv (fun s => I.chiMK κ m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t +
        matDiv (correctorDefectMatrix I hΦ m k t κ) x j +
        matDiv (correctorPushforwardMatrix I hΦ m k t κ) x j := by
  have hflux :
      (fun y i => (diffusionMatrix I hΦ m κ t y *
        (1 + gradChiTilde I hΦ m κ k t y)) i j) =
      fun y i => correctorFlux I hΦ m κ k t y i j := by
    funext y i
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j)
      (congrFun (diffusionMatrix_mul_one_plus_gradChi_eq_correctorFlux
        I hΦ m hm κ k t hk hxi) y)
  have hmatDiv : matDiv (fun y => diffusionMatrix I hΦ m κ t y *
      (1 + gradChiTilde I hΦ m κ k t y)) x j =
      matDiv (correctorFlux I hΦ m κ k t) x j := by
    unfold matDiv
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext y
    exact congrFun (congrFun hflux y) i
  rw [hmatDiv]
  exact frozen_corrector_diffusion_column_divergence_flow
    I hΦ m k t x κ j hB hD hE hdiv

end AVenhance.Infra.Section5
