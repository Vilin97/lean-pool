/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryInitialAmplitude
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedInitial
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialPolynomialBounds

/-! Source-only initial estimates for the actual packet constructed from
a parent and its activation geometry. No initial-field estimate is an input. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerParentInitializedRadius EulerPacketUniformSource
  EulerPacketTerminalDatum EulerPacketCylinderField EulerMeanHarmonic EulerPhysicalL2Scaling
  EulerPacketSourceFrequency

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (J : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (Ti TiTotal : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))

local notation "A" => L.geometryInputs H m hm R S hS τ hτ hτT P J hball Ti TiTotal
  hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball
local notation "BC" => joinedCoefficientBudget period (G.meanData H)
  (G.transverseData m hm R S hS) rfl τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT)
  (JoinedInputs.normal A)

theorem geometry_initial_primitives (ξ : U) (hδ : 0 < J.δ) :
    let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
    1 ≤ X ∧ P.horizon ≤ X ∧ J.hchild ≤ X ∧
      EulerPacketRadiusPolynomial.RadiusPrimitives (A).mean (A).linear (A).normal BC J.δ ξ
        (sourceEnvelope X) := by
  let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨hx,hK,hI,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K Ti TiTotal
    (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ (zero_le_one.trans L.K_one)
    ((inv_pos.mpr hτ).le.trans hTi) ((inv_pos.mpr G.T_pos).le.trans hTiTotal)
    J.growth_constant_pos.le hL0 hδ (norm_nonneg ξ)
  have hbase : parameterSize L.K Ti TiTotal (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ ≤ X :=
    le_add_of_nonneg_right J.child_nonneg
  have hX : 1 ≤ X := hx.trans hbase
  have hhX : J.hchild ≤ X := le_add_of_nonneg_left (zero_le_one.trans hx)
  have hp := L.joined_radius_primitives H m hm R S hS τ hτ hτT Ti
    (560*P.horizon^10/P.epsilon) hτ1 hTi J.growth_constant_pos.le
    (J.sourceGrowthProfile hball) (J.sourceGrowthProfile_positive hball)
    (J.sourceGrowthProfile_initial hball) Ω hΩ hΩo hsub hΩball
    (J.sourceGrowthProfile_propagator hball) TiTotal hT1 hTiTotal J.δ ξ X
    (hK.trans hbase) (hI.trans hbase) (hIT.trans hbase) (hC.trans hbase)
    (hB.trans hbase) (hD.trans hbase) (hN.trans hbase)
  exact ⟨hX,J.horizon_le_growthCost.trans (hC.trans hbase),hhX,hp⟩

include hτ1 hTi hT1 hTiTotal hΩ hΩo hsub hΩball

theorem geometry_initial_amplitude (ξ : U) (hδ : 0 < J.δ) (hδ1 : J.δ ≤ 1)
    (x : ℝ) (hσ : P.sigma * x ≤ 2) :
    let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
    J.primaryAmplitude hball ≤ EulerPacketInitialAmplitude.boundConstant *
      X^EulerPacketInitialAmplitude.degree*Real.exp (-x/8) := by
  obtain ⟨hX,hH,hh,hp⟩ := L.geometry_initial_primitives H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ
  exact J.primaryAmplitude_polynomial hball (A).linear _ x hX hH hh hδ1 hp.joined_frame hσ

theorem geometry_initial_bounds (ξ : U) (hs : tsupport EulerSpatialCutoffs.innerCutoff ⊆ S)
    (hδ : 0 < J.δ) (hδ1 : J.δ ≤ 1) (hh : 0 < J.hchild)
    (x : ℝ) (hσ : P.sigma * x ≤ 2) (k : ℝ) (hk : 4 ≤ k)
    (hfrequency : frequencyConstant *
      (L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ) ^ frequencyPower ≤
          smallPower
          k)
    (s : ℕ) :
    let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
    derivativeSum s (initializedInitialHigh (G.meanData H) (G.transverseData m hm R S hS)
      τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) J.δ hδ ξ hs
      (J.primaryAmplitude hball) (truncation k) k) ≤
      (G.ell⁻¹)^s*k^s*(EulerPacketInitialAmplitude.boundConstant *
        EulerPacketInitialCost.sourceConstant s *
        X^(EulerPacketInitialAmplitude.degree+EulerPacketInitialCost.sourcePower s))*Real.exp
            (-x/8) ∧
    derivativeSum s (initializedInitialMean (G.meanData H) (G.transverseData m hm R S hS)
      τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) J.δ hδ ξ hs
      (J.primaryAmplitude hball) (truncation k) k) ≤
      (G.ell⁻¹)^s/k^2*(EulerPacketInitialCost.sourceConstant s *
        X^EulerPacketInitialCost.sourcePower s) := by
  let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
  have hp := L.geometry_uniform_primitives H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ hδ1
  have hx := L.geometry_initial_primitives H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ
  have ha := L.geometry_initial_amplitude H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ hδ1 x hσ
  have hb := initialized_initial_polynomial_bounds (G.meanData H) (G.transverseData m hm R S hS)
    rfl τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) J.δ hδ hδ1 ξ hs
    (J.primaryAmplitude hball) (J.primaryAmplitude_pos hball hδ hh)
    (A).linear (A).normal (A).mean X hx.1 hp.1 hp.2.1 k hk hfrequency s
  have hell : 0 ≤ G.ell⁻¹ := (inv_pos.mpr G.ell_pos).le
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hX0 : 0 ≤ X := zero_le_one.trans hx.1
  have hC0 := (EulerPacketInitialCost.sourceConstant_pos s).le
  refine ⟨hb.1.trans ?_,hb.2⟩
  calc
    _ ≤ (G.ell⁻¹)^s*k^s*(EulerPacketInitialAmplitude.boundConstant *
        X^EulerPacketInitialAmplitude.degree*Real.exp (-x/8)) *
        (EulerPacketInitialCost.sourceConstant s*X^EulerPacketInitialCost.sourcePower s) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha (by positivity)) (by positivity)
    _ = _ := by rw [pow_add]; ring

end EulerParentPacketFrames.LabelData
