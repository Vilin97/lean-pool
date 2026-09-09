/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedPressureAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastHessian

@[expose] public section

/-! The initialized finite pressure has its actual leading angular force
and a uniformly small covector remainder. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerTransversePacketPrimary
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem initializedProfiles_one_highPressure :
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α 1).highPressure =
      scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs) := by
  simp only [initializedProfiles,joinedSourceProfiles,profiles_one]
  rfl

theorem initializedProfiles_one_meanPressure :
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α 1).meanPressure = 0 := by
  simp only [initializedProfiles,joinedSourceProfiles,profiles_one]
  rfl

def initializedAngularPressure : ScalarField := fun z =>
  (pressureJet (scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) z).2 angleDirection

def initializedCovectorRemainder (N : ℕ) (κ : ℝ) : VectorField :=
  covectorRemainder (N := N) (a := initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) D.m₀ κ

include hTime in
theorem initializedPressure_gradient_decomposition (N : ℕ) (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    gradient (fun y => initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x =
      fastForce (fun z => initializedAngularPressure D τ hτ hτT B δ hδ ξ hs α (t,z))
        k D.m₀ Y (fun y => D.FInv.field t (Y y)) x +
      (D.FInv.field t (Y x)).adjoint
        (initializedCovectorRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
          (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))) := by
  let tm : Icc (0 : ℝ) M.T := ⟨t.val,by simpa only [hTime] using t.property⟩
  let a := initializedProfiles M D τ hτ hτT B δ hδ ξ hs α
  let primary := joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
  let hprimary := joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B
    (initialData D δ hδ (α • ξ) hs)
  have hm (i : ℕ) : ContDiff ℝ ∞ (fun z => (a i).meanPressure (t,z)) :=
    joinedSource_meanPressure_smooth_all period M D hTime τ hτ hτT B primary hprimary rfl i tm
  have hh (i : ℕ) : ContDiff ℝ ∞ (fun z => (a i).highPressure (t,z)) :=
    joinedSource_highPressure_smooth_all period M D hTime τ hτ hτT B primary hprimary
      (fun s => joinedTerminalPrimary_pressure_smooth period M D τ hτ hτT B _ s.val) i tm
  have ha (i : ℕ) : (pressureJet (a i).meanPressure (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))).2 angleDirection=0 :=
    joinedSource_meanPressure_angle_all period M D hTime τ hτ hτT B primary hprimary rfl i tm _ _
  have hp : DifferentiableAt ℝ
      (fun z => initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹ (t,z))
      (graphMap k D.m₀ (Y x)) :=
    ((initializedPressureWitness M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).smooth tm).differentiable
      (by simp) _
  rw [gradient_physical_covector k D.m₀ _ t Y _ x hY hp]
  have he := covector_finite N k⁻¹ (inv_ne_zero hk) D.m₀ a
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))
    (fun i _ => (hm i).differentiable (by simp) _) (fun i _ => (hh i).differentiable (by simp) _)
    (fun i _ => ha i)
  rw [inv_inv] at he
  change covector k D.m₀ (initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹)
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) = _ at he
  rw [he]
  have h1 : (a 1).highPressure=scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs) :=
    initializedProfiles_one_highPressure M D τ hτ hτT B δ hδ ξ hs α
  have hv : fieldSum (N+1) k⁻¹ (covectorGrades N D.m₀ a) (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) =
      k⁻¹ • angularPressure D.m₀ (a 1).highPressure (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) +
      initializedCovectorRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) := by
    dsimp only [initializedCovectorRemainder,covectorRemainder,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [hv,map_add,map_smul]
  simp only [fastForce,transportedNormal,graphMap_apply,angularPressure,
    initializedAngularPressure,map_smul,h1]

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
    δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.fullProfile)

def initializedPressureBudget (p : ℕ) :=
  Classical.choice (initializedPressureBudget_exists M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth p)

def initializedAngularPressureField :
    Field period D.T (fun z => initializedAngularPressure D τ hτ hτT B δ hδ ξ hs α z • D.m₀) :=
  (((initializedPressureBudget M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1).angular).changeTime hTime).congr
      (fun _ _ _ => by rw [initializedProfiles_one_highPressure]; rfl)

theorem initializedAngularPressure_bound :
    (initializedAngularPressureField M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth).WordBound
      6 (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) 0 := by
  let K := initializedPressureBudget M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1
  have hb := K.angular_bound.remove_profile M.T_pos.le (S.high 1) (S.high_pos 1)
    (S.H0^(2*1)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse 1 le_rfl)
  simp only [mul_one] at hb
  have ha : S.H0^2 ≤ 3*S.H0^(2*1) := by
    norm_num only [Nat.mul_one]
    nlinarith [sq_nonneg S.H0]
  have hc := (hb.mono_amplitude (zero_le_one.trans L.radius_bounds.1) ha).fixed_velocity_grade
    (n := 1) (zero_le_one.trans L.radius_bounds.1) S.H0_pos.le
  exact (hc.changeTime hTime).of_raw_eq _
    (fun _ _ _ => by rw [initializedProfiles_one_highPressure]; rfl)

def initializedCovectorRemainderField (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) :
    Field period D.T (initializedCovectorRemainder M D τ hτ hτT B δ hδ ξ hs α N κ) :=
  (covectorRemainderField M.T_pos D.m₀
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    (fun i (_ : i ≤ N) => initializedPressureBudget M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i)
    (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α) hN
    (initializedProfiles_one_meanPressure M D τ hτ hτT B δ hδ ξ hs α) κ).changeTime hTime

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth
theorem initializedCovectorRemainder_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (initializedCovectorRemainderField M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k⁻¹).WordBound
      6 (4*L.R) ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2) 0 := by
  exact (covectorRemainder_bound M.T_pos D.m₀
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    (fun i (_ : i ≤ N) => initializedPressureBudget M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i)
    (fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi)
    L.radius_bounds.1 (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α) hN
    (initializedProfiles_one_meanPressure M D τ hτ hτT B δ hδ ξ hs α) BC k hk hbase).changeTime
      hTime

end EulerPacketTerminalDatum
