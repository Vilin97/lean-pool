/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionEstimateChoice
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPointwiseBounds

@[expose] public section

/-! Source-only pointwise mixed-derivative Gevrey estimates for the
actual initialized correction and its pressure and time derivative. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set Filter Finset EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketSourceFrequency EulerSobolevGevreyOperators EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerAllOrderCorrectionData EulerMetricTransport
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
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

include hδ1 hα L NB LM hΞ hF hdet

/-- The actual weighted correction estimates imply literal pointwise
mixed-word Gevrey estimates, uniformly in time, order and position.
The radius 4/ρ0 and amplitude constant depend only on the fixed source data. -/
theorem initialized_correction_pointwise_eventually :
    ∃ ρ0 G C : ℝ, 0 < ρ0 ∧ 0 < G ∧ 0 < C ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=G ∧
        ∀ (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : LiftDomain period),
          (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative period w (Q.pointField period t) x‖) ≤
            C*delta (expansion k)*(4/ρ0)^n*(n.factorial : ℝ)^2 ∧
          (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative period w (Q.pointPressure period t) x‖) ≤
            C*delta (expansion k)*(4/ρ0)^n*(n.factorial : ℝ)^2 ∧
          (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative period w (Q.pointTimeDerivative period t)
            x‖) ≤
            C*delta (expansion k)*(4/ρ0)^n*(n.factorial : ℝ)^2 := by
  obtain ⟨ρ0,G,C,hρ,hG,hC,hQ⟩ := initialized_correction_estimates_eventually
    M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree Ξ hΞ hF hdet
  let Cpt := 1+sobolevEmbeddingConstant period 3*C
  have hS := sobolevEmbeddingConstant_nonneg period 3
  have hCpt : 0 < Cpt := by dsimp [Cpt]; positivity
  refine ⟨ρ0,G,Cpt,hρ,hG,hCpt,?_⟩
  filter_upwards [hQ] with k hQ
  obtain ⟨hk,hn,Q,hδQ,hρQ,hGQ,hbounds⟩ := hQ
  refine ⟨hk,hn,Q,hδQ,hρQ,hGQ,?_⟩
  intro n t x
  have hr : 0 < ρ0/4 := by positivity
  have hInv : (ρ0/4)⁻¹=4/ρ0 := inv_div _ _
  have hbound (F : FieldTower period D.T)
      (hF : weightedNorm period 6 n (ρ0/4) (F.realization (n+6) t) ≤ C*delta (expansion k)) :
      (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative period w (F.pointField t) x‖) ≤
        Cpt*delta (expansion k)*(4/ρ0)^n*(n.factorial : ℝ)^2 := by
    have h := F.pointField_wordSum_gevrey (n+6) 6 n n (by omega) (by omega) le_rfl
      (ρ0/4) (C*delta (expansion k)) hr t hF x
    rw [hInv] at h
    have hAmp : sobolevEmbeddingConstant period 3*C ≤ Cpt := by dsimp [Cpt]; linarith
    have hscale := mul_le_mul_of_nonneg_right hAmp (delta_pos (expansion k)).le
    have hp := mul_le_mul_of_nonneg_right hscale (pow_nonneg (by positivity : 0 ≤ 4/ρ0) n)
    have hf := mul_le_mul_of_nonneg_right hp (sq_nonneg (n.factorial : ℝ))
    apply h.trans
    simpa only [mul_assoc] using hf
  have he := hbound (Q.fieldTower period) (hbounds (n+6) n (by omega) t).1
  have hp := hbound (Q.pressureTower period) (hbounds (n+6) n (by omega) t).2.1
  have ht := hbound (Q.timeDerivativeTower period) (hbounds (n+6) n (by omega) t).2.2
  simpa only [Q.correctionTower_pointField period t,Q.pressureTower_pointField period t,
    Q.timeDerivativeTower_pointField period t] using And.intro he (And.intro hp ht)

/-- Even after any fixed physical polynomial loss, the whole actual
pointwise mixed-derivative Gevrey envelope is smaller than a prescribed
inverse power of the frequency. -/
theorem initialized_correction_pointwise_power_loss_eventually
    (physicalCost loss p : ℝ) (hphysicalCost : 0 ≤ physicalCost) :
    ∃ ρ0 G : ℝ, 0 < ρ0 ∧ 0 < G ∧ ∀ᶠ k : ℝ in atTop,
      ∃ (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
        (Q : EulerAllOrderDriftCorrection.Budget period D.T_pos
          (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
            (truncation k) hn k hk)),
        Q.delta=delta (expansion k) ∧ Q.initialRadius=ρ0 ∧ Q.growthCoefficient=G ∧
        ∀ (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : LiftDomain period),
          physicalCost*k^loss*(∑ w : Fin n → Fin 4,
              ‖iteratedFieldDerivative period w (Q.pointField period t) x‖) <
            k^(-p)*(4/ρ0)^n*(n.factorial : ℝ)^2 ∧
          physicalCost*k^loss*(∑ w : Fin n → Fin 4,
              ‖iteratedFieldDerivative period w (Q.pointPressure period t) x‖) <
            k^(-p)*(4/ρ0)^n*(n.factorial : ℝ)^2 ∧
          physicalCost*k^loss*(∑ w : Fin n → Fin 4,
              ‖iteratedFieldDerivative period w (Q.pointTimeDerivative period t) x‖) <
            k^(-p)*(4/ρ0)^n*(n.factorial : ℝ)^2 := by
  obtain ⟨ρ0,G,C,hρ,hG,_hC,hQ⟩ := initialized_correction_pointwise_eventually
    M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree Ξ hΞ hF hdet
  refine ⟨ρ0,G,hρ,hG,?_⟩
  filter_upwards [hQ,correction_with_power_loss_eventually (physicalCost*C) loss p] with k hQ
    hkbound
  obtain ⟨hk,hn,Q,hδQ,hρQ,hGQ,hbounds⟩ := hQ
  refine ⟨hk,hn,Q,hδQ,hρQ,hGQ,?_⟩
  intro n t x
  have hscale : 0 ≤ physicalCost*k^loss :=
    mul_nonneg hphysicalCost (Real.rpow_nonneg (by linarith) _)
  have hword : 0 < (4/ρ0)^n*(n.factorial : ℝ)^2 := by positivity
  have hm := mul_lt_mul_of_pos_right hkbound hword
  have hbound (X : ℝ) (hX : X ≤ C*delta (expansion k)*(4/ρ0)^n*(n.factorial : ℝ)^2) :
      physicalCost*k^loss*X < k^(-p)*(4/ρ0)^n*(n.factorial : ℝ)^2 := by
    apply (mul_le_mul_of_nonneg_left hX hscale).trans_lt
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  exact ⟨hbound _ (hbounds n t x).1,hbound _ (hbounds n t x).2.1,hbound _ (hbounds n t x).2.2⟩

end EulerPacketTerminalDatum
