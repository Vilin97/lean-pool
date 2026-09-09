/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardPressureBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastHessian
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! The actual forward finite pressure has its actual leading angular force
and a uniformly small covector remainder. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerPacketForwardPrimary
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem forwardInitializedProfiles_one_highPressure :
    (forwardInitializedProfiles M D δ hδ ξ hs α 1).highPressure =
      scalar D (initialData D δ hδ (α • ξ) hs) := by
  simp only [forwardInitializedProfiles,sourceProfiles,profiles_one]
  rfl

theorem forwardInitializedProfiles_one_meanPressure :
    (forwardInitializedProfiles M D δ hδ ξ hs α 1).meanPressure = 0 := by
  simp only [forwardInitializedProfiles,sourceProfiles,profiles_one]
  rfl

/-- Forward initialized angular pressure, defined pointwise by `(pressureJet (scalar D
(initialData D δ hδ (α • ξ) hs)) z).2 angleDirection`. -/
def forwardInitializedAngularPressure : ScalarField := fun z =>
  (pressureJet (scalar D (initialData D δ hδ (α • ξ) hs)) z).2 angleDirection

/-- Forward initialized covector remainder, given by `covectorRemainder (N := N) (a :=
forwardInitializedProfiles M D δ hδ ξ hs α) D.m₀ κ`. -/
def forwardInitializedCovectorRemainder (N : ℕ) (κ : ℝ) : VectorField :=
  covectorRemainder (N := N) (a := forwardInitializedProfiles M D δ hδ ξ hs α) D.m₀ κ

include hTime in
theorem forwardInitializedPressure_gradient_decomposition (N : ℕ) (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    gradient (fun y => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x =
      fastForce (fun z => forwardInitializedAngularPressure D δ hδ ξ hs α (t,z))
        k D.m₀ Y (fun y => D.FInv.field t (Y y)) x +
      (D.FInv.field t (Y x)).adjoint
        (forwardInitializedCovectorRemainder M D δ hδ ξ hs α N k⁻¹
          (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))) := by
  let tm : Icc (0 : ℝ) M.T := ⟨t.val,by simpa only [hTime] using t.property⟩
  let a := forwardInitializedProfiles M D δ hδ ξ hs α
  have hm (i : ℕ) : ContDiff ℝ ∞ (fun z => (a i).meanPressure (t,z)) :=
    source_meanPressure_smooth period M D hTime (InitialData.zero period D)
      (initialData D δ hδ (α • ξ) hs) i t
  have hh (i : ℕ) : ContDiff ℝ ∞ (fun z => (a i).highPressure (t,z)) :=
    source_highPressure_smooth period M D hTime (InitialData.zero period D)
      (initialData D δ hδ (α • ξ) hs) i t
  have ha (i : ℕ) : (pressureJet (a i).meanPressure (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))).2 angleDirection=0 :=
    source_meanPressure_angle period M D hTime (InitialData.zero period D)
      (initialData D δ hδ (α • ξ) hs) i t _ _
  have hp : DifferentiableAt ℝ
      (fun z => forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹ (t,z))
      (graphMap k D.m₀ (Y x)) :=
    ((forwardInitializedPressureWitness M D hTime δ hδ ξ hs α N k⁻¹).smooth tm).differentiable
      (by simp) _
  rw [gradient_physical_covector k D.m₀ _ t Y _ x hY hp]
  have he := covector_finite N k⁻¹ (inv_ne_zero hk) D.m₀ a
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))
    (fun i _ => (hm i).differentiable (by simp) _) (fun i _ => (hh i).differentiable (by simp) _)
    (fun i _ => ha i)
  rw [inv_inv] at he
  change covector k D.m₀ (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) = _ at he
  rw [he]
  have h1 : (a 1).highPressure=scalar D (initialData D δ hδ (α • ξ) hs) :=
    forwardInitializedProfiles_one_highPressure M D δ hδ ξ hs α
  have hv : fieldSum (N+1) k⁻¹ (covectorGrades N D.m₀ a) (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) =
      k⁻¹ • angularPressure D.m₀ (a 1).highPressure (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) +
      forwardInitializedCovectorRemainder M D δ hδ ξ hs α N k⁻¹
        (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ)) := by
    dsimp only [forwardInitializedCovectorRemainder,covectorRemainder,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [hv,map_add,map_smul]
  simp only [fastForce,transportedNormal,graphMap_apply,angularPressure,
    forwardInitializedAngularPressure,map_smul,h1]

variable
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)

/-- Forward initialized pressure budget, constructed using `Classical.choice`. -/
def forwardInitializedPressureBudget (p : ℕ) :=
  Classical.choice (forwardInitializedPressureBudget_exists M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth p)

/-- Forward initialized angular pressure field as an element of `Field period D.T (fun z =>
forwardInitializedAngularPressure D δ hδ ξ hs α z • D.m₀)`. -/
def forwardInitializedAngularPressureField :
    Field period D.T (fun z => forwardInitializedAngularPressure D δ hδ ξ hs α z • D.m₀) :=
  (((forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1).angular).changeTime hTime).congr
      (fun _ _ _ => by rw [forwardInitializedProfiles_one_highPressure]; rfl)

theorem forwardInitializedAngularPressure_bound :
    (forwardInitializedAngularPressureField M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth).WordBound
      6 (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) 0 := by
  let K := forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1
  have hb := K.angular_bound.remove_profile M.T_pos.le (S.high 1) (S.high_pos 1)
    (S.H0^(2*1)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse 1 le_rfl)
  simp only [mul_one] at hb
  have ha : S.H0^2 ≤ 3*S.H0^(2*1) := by
    norm_num only [Nat.mul_one]
    nlinarith [sq_nonneg S.H0]
  have hc := (hb.mono_amplitude (zero_le_one.trans L.radius_one) ha).fixed_velocity_grade
    (n := 1) (zero_le_one.trans L.radius_one) S.H0_pos.le
  exact (hc.changeTime hTime).ofRawEq _
    (fun _ _ _ => by rw [forwardInitializedProfiles_one_highPressure]; rfl)

/-- Forward initialized covector remainder field as an element of `Field period D.T
(forwardInitializedCovectorRemainder M D δ hδ ξ hs α N κ)`. -/
def forwardInitializedCovectorRemainderField (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) :
    Field period D.T (forwardInitializedCovectorRemainder M D δ hδ ξ hs α N κ) :=
  (covectorRemainderField M.T_pos D.m₀
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i)
    (fun i (_ : i ≤ N) => forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i)
    (forwardInitializedProfiles_zero M D δ hδ ξ hs α) hN
    (forwardInitializedProfiles_one_meanPressure M D δ hδ ξ hs α) κ).changeTime hTime

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth
theorem forwardInitializedCovectorRemainder_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (forwardInitializedCovectorRemainderField M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k⁻¹).WordBound
      6 (4*L.R) ((fixedVelocityGradeCost L.R S.H0 2+2)/k^2) 0 := by
  exact (covectorRemainder_bound M.T_pos D.m₀
    (fun i (_ : i ≤ N) => forwardInitializedProfileWitness M D hTime δ hδ ξ hs α i)
    (fun i (_ : i ≤ N) => forwardInitializedPressureBudget M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i)
    (fun i _ hi => forwardInitialized_profile_budgets M D hTime δ hδ ξ hs α
      L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi)
    L.radius_one (forwardInitializedProfiles_zero M D δ hδ ξ hs α) hN
    (forwardInitializedProfiles_one_meanPressure M D δ hδ ξ hs α) BC k hk hbase).changeTime hTime

end EulerPacketTerminalDatum
