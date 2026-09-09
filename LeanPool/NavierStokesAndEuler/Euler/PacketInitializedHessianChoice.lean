/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedPhysicalFieldsChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCorrectionPotential

@[expose] public section

/-! The same constructed correction is small in the actual physical
velocity gradient and the Hessian of its actual scalar pressure. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketCorrectionScalar
  EulerPacketSourceFrequency EulerGraphPressurePotential EulerGevrey
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (Ξ Y : Icc (0 : ℝ) D.T → Space → Space)
  (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hΞY : ∀ t x, Ξ t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)
  (R CF : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF)
  (hFb : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ CF*majorant R 0 n)

include hδ1 hα L NB LM hΞ hF hΞY hY hdet hR hCF hFb in
theorem initialized_correction_gradient_hessian_eventually (p : ℝ) :
    ∃ ρ0 G : ℝ, 0 < ρ0 ∧ 0 < G ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=G ∧
        ∀ (t : Icc (0 : ℝ) D.T) (x : Space),
          ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y t y)
            (Q.pointField period t (cylinderGraph period k D.m₀ (Y t y)))) x‖ < k^(-p) ∧
          ‖fderiv ℝ (gradient (Q.physicalPotential D period k Y t)) x‖ < k^(-p) := by
  obtain ⟨ρ0,G,hρ,hG,hQ⟩ := initialized_correction_physical_fields_eventually
    M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree
    Ξ Y hΞ hF hΞY hY hdet R CF hR hCF hFb 1 p
  have hX : ∀ t x, HasFDerivAt (Ξ t) (D.F.field t x) x := by
    intro t x
    rw [← hF t x]
    exact ((hΞ t).differentiable (by simp) x).hasFDerivAt
  refine ⟨ρ0,G,hρ,hG,?_⟩
  filter_upwards [hQ] with k hQ
  obtain ⟨hk,hn,Q,hδQ,hρQ,hGQ,hbounds⟩ := hQ
  refine ⟨hk,hn,Q,hδQ,hρQ,hGQ,?_⟩
  intro t x
  have h := hbounds 1 le_rfl t x
  constructor
  · simpa only [norm_iteratedFDeriv_one] using h.1
  · have hkκ : k*(initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
        (truncation k) hn k hk).κ=1 := by
      change k*k⁻¹=1
      exact mul_inv_cancel₀ (by linarith)
    rw [Q.physicalPotential_hessian_norm D period Ξ Y hX hΞY hY k hkκ t x]
    exact h.2

end EulerPacketTerminalDatum
