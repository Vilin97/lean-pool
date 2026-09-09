/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedResidualEquation
public import LeanPool.NavierStokesAndEuler.Euler.PacketRemainderBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensor
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPiolaData

/-! The literal initialized finite packet is its actual primary plus a
remainder with a proved physical C1 bound. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
  EulerPacketPrimaryShear EulerPacketPrimaryFactorization EulerTransversePacketPrimary
  EulerCylinderCoordinates
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem initializedProfiles_zero : initializedProfiles M D τ hτ hτT B δ hδ ξ hs α 0 = 0 :=
  profiles_zero _ _

theorem initializedProfiles_one_high :
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α 1).high =
      vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs) := by
  simp only [initializedProfiles,joinedSourceProfiles,profiles_one]
  rfl

theorem initializedProfiles_one_mean :
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α 1).mean = 0 := by
  simp only [initializedProfiles,joinedSourceProfiles,profiles_one]
  rfl

/-- Initialized primary remainder, given by `initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N κ
- κ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)`. -/
def initializedPrimaryRemainder (N : ℕ) (κ : ℝ) : VectorField :=
  initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N κ -
    κ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)

/-- Initialized primary remainder field as an element of `Field period D.T
(initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N κ)`. -/
def initializedPrimaryRemainderField (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) :
    Field period D.T (initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N κ) :=
  ((ProfileRegularity.primaryRemainderField M.T_pos
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    hN (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α)
    (initializedProfiles_one_mean M D τ hτ hτT B δ hδ ξ hs α) κ).changeTime hTime).congr
      (fun _ _ _ => by rw [initializedProfiles_one_high]; rfl)

include hTime in
/-- The exact derivative split, with the primary's genuine canonical
velocity and transported normal. -/
theorem initializedVelocity_gradient_split (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    fderiv ℝ (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) (X 0) =
      (α/δ) • rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t 0) (D.normal.field t 0) +
      fderiv ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*inner ℝ D.m₀ (Y y)))) (X 0) := by
  let V := vectorField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
  have hp := ((V.smul k⁻¹).raw_graph_contDiff t k D.m₀).differentiable (by simp)
  have hr := ((initializedPrimaryRemainderField M D hTime τ hτ hτT B δ hδ ξ hs α N hN
      k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp)
  have hp' : DifferentiableAt ℝ (fun y => k⁻¹ • vector τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) (t,(Y y,k*inner ℝ D.m₀ (Y y)))) (X 0) := by
    simpa only [Function.comp_def,Pi.smul_apply] using (hp (Y (X 0))).comp (X 0) hY
  have hr' : DifferentiableAt ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N
      k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) (X 0) := by
    simpa only [Function.comp_def] using (hr (Y (X 0))).comp (X 0) hY
  have he : (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) =
      (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
        (t,(Y y,k*inner ℝ D.m₀ (Y y)))) +
      (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*inner ℝ D.m₀ (Y y)))) := by
    funext y
    dsimp only [initializedPrimaryRemainder,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [he,fderiv_add hp' hr',
    scaled_terminal_physical_gradient τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft]

variable
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedPrimaryRemainder_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (initializedPrimaryRemainderField M D hTime τ hτ hτT B δ hδ ξ hs α N hN k⁻¹).WordBound
      6 (4*L.R) ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2) 0 := by
  let G := fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have h := ProfileRegularity.primaryRemainder_bound M.T_pos G hG L.radius_bounds.1
    (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α)
    (initializedProfiles_one_mean M D τ hτ hτT B δ hδ ξ hs α) hN BC k hk hbase
  exact (h.changeTime hTime).ofRawEq _ (fun _ _ _ => by rw [initializedProfiles_one_high]; rfl)

theorem initializedPrimaryRemainder_physical_norm (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) :
    ‖initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y x,k*inner ℝ D.m₀ (Y x)))‖ ≤
      sobolevEmbeddingConstant period 3*((fixedVelocityGradeCost L.R S.H0 2+2)/k^2) :=
  (initializedPrimaryRemainder_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).raw_graph_norm_le
      (by norm_num) t k D.m₀ (Y x)

theorem initializedPrimaryRemainder_physical_fderiv (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : DifferentiableAt ℝ Y x) :
    ‖fderiv ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x‖ ≤
      (frequencyFactor k D.m₀*(sobolevEmbeddingConstant period 3 *
        ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R)))*‖fderiv ℝ Y x‖ :=
  (initializedPrimaryRemainder_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase).raw_physical_fderiv_le
      (by norm_num) t k D.m₀ Y x hY

omit H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth in
/-- The constant contains no packet frequency or derivative of the inverse flow. -/
def initializedRemainderDerivativeCost (R H0 : ℝ) : ℝ :=
  8*‖coordinateEquiv.symm.toContinuousLinearMap‖*sobolevEmbeddingConstant period 3 *
    R*(fixedVelocityGradeCost R H0 2+2)

theorem initializedPrimaryRemainder_physical_fderiv_inv (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : DifferentiableAt ℝ Y x) :
    ‖fderiv ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) x‖ ≤
      (initializedRemainderDerivativeCost L.R S.H0/k)*‖fderiv ℝ Y x‖ := by
  have hk0 : k ≠ 0 := by linarith
  have hc := fixedVelocityGradeCost_nonneg L.R S.H0 (zero_le_one.trans L.radius_bounds.1) 2
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hr : 0 ≤ L.R := zero_le_one.trans L.radius_bounds.1
  have hb : 0 ≤ sobolevEmbeddingConstant period 3 *
      ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R) := by positivity
  have hf := frequencyFactor_le_linear k (by linarith) D.m₀
  rw [D.m₀_unit] at hf
  norm_num only at hf
  have h := initializedPrimaryRemainder_physical_fderiv M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY
  calc
    _ ≤ (frequencyFactor k D.m₀*(sobolevEmbeddingConstant period 3 *
        ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R)))*‖fderiv ℝ Y x‖ := h
    _ ≤ ((‖coordinateEquiv.symm.toContinuousLinearMap‖*2*k)*(sobolevEmbeddingConstant period 3 *
        ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2)*(4*L.R)))*‖fderiv ℝ Y x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf hb) (norm_nonneg _)
    _ = _ := by unfold initializedRemainderDerivativeCost; field_simp; ring

/-- The finite packet's actual center gradient differs from its exact
primary shear by O(1/k), with the genuine inverse frame norm. -/
theorem initializedVelocity_gradient_error (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    ‖fderiv ℝ (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*inner ℝ D.m₀ (Y y)))) (X 0) -
      (α/δ) • rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t 0) (D.normal.field t 0)‖ ≤
      (initializedRemainderDerivativeCost L.R S.H0/k)*‖D.FInv.field t 0‖ := by
  have hk0 : k ≠ 0 := by linarith
  rw [initializedVelocity_gradient_split M D hTime τ hτ hτT B δ hδ ξ hs α
    N hN k hk0 t X Y hX hY hleft,add_sub_cancel_left]
  have he : Y ∘ X = id := funext hleft
  have hdY := EulerLagrangian.derivative_pullback_inverse Y X (D.deformationEquiv t 0) 0 hX hY
  rw [he,fderiv_id,id_comp] at hdY
  have h := initializedPrimaryRemainder_physical_fderiv_inv M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y (X 0) hY
  rw [hdY] at h
  exact h

end EulerPacketTerminalDatum
