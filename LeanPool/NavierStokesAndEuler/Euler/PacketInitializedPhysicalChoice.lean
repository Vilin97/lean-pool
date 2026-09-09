/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedPointwiseChoice
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFrequencyBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse

@[expose] public section

/-! The actual initialized correction is smaller than every prescribed
inverse power in every fixed physical C^N norm, uniformly over the full
time interval. All coordinate-change costs are fixed by the parent data. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter Finset EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketCorrectionScalar
  EulerPacketSourceFrequency EulerLiftedGradientSpace EulerCylinderSobolev
  EulerPacketPhysicalGevrey EulerPacketInverseFlowGevrey EulerGraphPressurePotential
  EulerCylinderPhysicalTensor EulerGevrey
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
theorem initialized_correction_physical_derivatives_eventually (N : ℕ) (p : ℝ) :
    ∃ ρ0 G : ℝ, 0 < ρ0 ∧ 0 < G ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=G ∧
        ∀ n, n ≤ N → ∀ (t : Icc (0 : ℝ) D.T) (x : Space),
          ‖iteratedFDeriv ℝ n (fun y => k⁻¹ • D.F.field t (Y t y)
            (Q.pointField period t (cylinderGraph period k D.m₀ (Y t y)))) x‖ < k^(-p) := by
  obtain ⟨ρ0,G,Cpt,hρ,hG,hCpt,hQ⟩ := initialized_correction_pointwise_eventually
    M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree Ξ hΞ hF hdet
  have hS : 0 ≤ 4/ρ0 := by positivity
  let Ctop := ∑ i : Fin (N+1), physicalFixedCost D R CF (4/ρ0) i.val
  have hCtop : 0 ≤ Ctop :=
    sum_nonneg (fun i _ => physicalFixedCost_nonneg D R CF (4/ρ0) i.val hR hCF hS)
  have hX : ∀ t x, HasFDerivAt (Ξ t) (D.F.field t x) x := by
    intro t x
    rw [← hF t x]
    exact ((hΞ t).differentiable (by simp) x).hasFDerivAt
  have hYd := continuousInverse_differentiable D Ξ Y hX hΞY hY
  refine ⟨ρ0,G,hρ,hG,?_⟩
  filter_upwards [hQ,correction_with_power_loss_eventually (Ctop*Cpt) (N : ℝ) p] with k hQ hkbound
  obtain ⟨hk,hn,Q,hδQ,hρQ,hGQ,hbounds⟩ := hQ
  have hδk : 0 ≤ delta (expansion k) := (delta_pos (expansion k)).le
  refine ⟨hk,hn,Q,hδQ,hρQ,hGQ,?_⟩
  intro n hnN t x
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hκ : |k⁻¹| ≤ 1 := by
    rw [abs_inv,abs_of_nonneg hk0]
    exact inv_le_one_of_one_le₀ hk1
  have he := physicalReconstruction_power_bound D period k⁻¹ k (Q.pointField period)
    (Q.pointField_smooth period) R CF (Cpt*delta (expansion k)) (4/ρ0)
    hR hCF (by positivity) hS hFb (fun j s y => (hbounds j s y).1)
    Ξ Y hX hYd hΞY hdet hk1 hκ n t x
  have hcn : physicalFixedCost D R CF (4/ρ0) n ≤ Ctop := by
    exact single_le_sum
      (f := fun i : Fin (N+1) => physicalFixedCost D R CF (4/ρ0) i.val)
      (fun i _ => physicalFixedCost_nonneg D R CF (4/ρ0) i.val hR hCF hS)
      (mem_univ (⟨n,by omega⟩ : Fin (N+1)))
  have hupper : physicalFixedCost D R CF (4/ρ0) n*(Cpt*delta (expansion k))*k^n ≤
      Ctop*(Cpt*delta (expansion k))*k^N :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcn (by positivity))
      (pow_le_pow_right₀ hk1 hnN) (pow_nonneg hk0 n) (by positivity)
  have hsmall : Ctop*(Cpt*delta (expansion k))*k^N < k^(-p) := by
    simpa only [Real.rpow_natCast,mul_assoc,mul_left_comm,mul_comm] using hkbound
  exact he.trans_lt (hupper.trans_lt hsmall)

end EulerPacketTerminalDatum
