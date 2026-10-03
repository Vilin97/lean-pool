/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PiolaFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.RegroupSmooth

/-! Left-Jacobian form: spatial smoothness of the pulled gap fluxes
`y ↦ Σ_l ξ̂_l F_lᵀ M F_l ∇T` (constant matrix `M`), which carry the base flux
(`M = JHat - K`) and the first summand of `sourceErrorD` (`M = JHat - 𝒥`). -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem contDiff_flowGrad_entry (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ)
    (i j : Fin 2) : ContDiff ℝ ∞ (fun y => I.flowGrad hΦ m l t y i j) :=
  (contDiff_gradMatrix_entry (RelativeError.contDiff_xFlow_slice I hΦ m l t) i j).comp
    (RelativeError.contDiff_xFlowInv_slice I hΦ m l t)

/-- `y ↦ Σ_l ξ̂_l F_lᵀ M F_l ∇T` is spatially `C^∞` for a constant matrix `M`. -/
theorem contDiff_pulledGapFlux (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (hT : ContDiff ℝ ∞ (T t)) :
    ContDiff ℝ ∞ (fun y => ∑' l : ℤ, I.hatXiML m l t •
      ((I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y))))) := by
  have hfun : (fun y => ∑' l : ℤ, I.hatXiML m l t •
      ((I.flowGrad hΦ m l t y).transpose.mulVec
        (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y))))) =
      fun y => ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t y).transpose.mulVec
          (M.mulVec ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)))) := by
    funext y
    exact tsum_hatXiML_smul_eq_sum I m hm t _
  rw [hfun]
  refine ContDiff.sum (fun l _ => ContDiff.const_smul _ ?_)
  have hg := contDiff_spaceGrad_T hT
  have hF := contDiff_flowGrad_entry I hΦ m l t
  apply contDiff_pi.2
  intro i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine ContDiff.sum (fun p _ => (hF p i).mul ?_)
  refine ContDiff.sum (fun q _ => contDiff_const.mul ?_)
  refine ContDiff.sum (fun r _ => (hF q r).mul ((contDiff_pi.1 hg) r))

end AVenhance.Infra.Section5.LeftJacobian

end
