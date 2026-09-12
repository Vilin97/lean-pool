/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphHessian
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPressure
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastHessian
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! The actual finite pressure Hessian is its primary normal tensor plus
a uniform inverse-frequency error. No derivative or remainder estimate
is assumed for a solved field. -/

section

/-! The initialized finite pressure has its actual leading angular force
and a uniformly small covector remainder. -/

@[expose] public section

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

/-- Initialized angular pressure, defined pointwise by `(pressureJet (scalar τ hτ hτT B
(initialData D δ hδ (α • ξ) hs)) z).2 angleDirection`. -/
def initializedAngularPressure : ScalarField := fun z =>
  (pressureJet (scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) z).2 angleDirection

/-- Initialized covector remainder, given by `covectorRemainder (N := N) (a :=
initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) D.m₀ κ`. -/
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
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)

/-- Initialized pressure budget, constructed using `Classical.choice`. -/
def initializedPressureBudget (p : ℕ) :=
  Classical.choice (initializedPressureBudget_exists M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth p)

/-- Initialized angular pressure field as an element of `Field period D.T (fun z =>
initializedAngularPressure D τ hτ hτT B δ hδ ξ hs α z • D.m₀)`. -/
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
  exact (hc.changeTime hTime).ofRawEq _
    (fun _ _ _ => by rw [initializedProfiles_one_highPressure]; rfl)

/-- Initialized covector remainder field as an element of `Field period D.T
(initializedCovectorRemainder M D τ hτ hτT B δ hδ ξ hs α N κ)`. -/
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
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
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

end
end

end

section

/-! The leading pressure tensor of the actual joined primary.  Both angular
derivatives below are derivatives of its constructed scalar pressure. -/

@[expose] public section

noncomputable section

namespace EulerPacketPrimaryPressure

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerTransversePacketProvider EulerTransversePacketPrimary
  EulerPacketTerminalDatum EulerPacketPrimaryFactorization EulerPacketPrimaryShear
  EulerSpatialCutoffs EulerPeriodicProfile EulerPacketGraphHessian
  EulerGraphPullback EulerPacketInverseFlowGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

/-- Coefficient, given by `-(2*a*⟪D.normal.field t x, D.M.field t x (canonicalVelocity τ hτ hτT
B ξ hs t x)⟫_ℝ)/‖D.normal.field t x‖^2`. -/
def coefficient (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) : ℝ :=
  -(2*a*⟪D.normal.field t x,
    D.M.field t x (canonicalVelocity τ hτ hτT B ξ hs t x)⟫_ℝ)/‖D.normal.field t x‖^2

theorem scalar_hasDerivAt (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s)))
      (coefficient τ hτ hτT B ξ hs a t x * profile δ θ) θ := by
  have he : (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s))) =
      fun s : ℝ => pressureField τ hτ hτT B (initialData D δ hδ (a • ξ) hs) t
        (x,(s : AddCircle period)) :=
    funext (scalar_eq_pressureField τ hτ hτT B _ t x)
  rw [he]
  have ha := pressureField_angle τ hτ hτT B (initialData D δ hδ (a • ξ) hs) t x θ
  have hv := vector_terminal_smul τ hτ hτT B δ hδ ξ hs a t x θ
  rw [vector_factorization_canonical τ hτ hτT B δ hδ ξ hs t x θ] at hv
  simp only [vector,Data.clamp_coe] at hv
  have hr : normalResidual τ hτ hτT B (initialData D δ hδ (a • ξ) hs) t
      (x,(θ : AddCircle period)) = coefficient τ hτ hτT B ξ hs a t x * profile δ θ := by
    unfold normalResidual
    rw [hv]
    simp only [coefficient,map_smul,inner_smul_right]
    ring
  exact hr ▸ ha

theorem scalar_deriv (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    deriv (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s))) θ =
      coefficient τ hτ hτT B ξ hs a t x * profile δ θ :=
  (scalar_hasDerivAt τ hτ hτT B δ hδ ξ hs a t x θ).deriv

theorem scalar_deriv_hasDerivAt (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt
      (deriv (fun s => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,s))))
      (coefficient τ hτ hτT B ξ hs a t x * deriv (profile δ) θ) θ := by
  have he := funext (scalar_deriv τ hτ hτT B δ hδ ξ hs a t x)
  rw [he]
  exact ((profile_contDiff δ hδ).differentiable (by simp) θ).hasDerivAt.const_mul _

theorem scalar_second_deriv (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    deriv (deriv (fun s => scalar τ hτ hτT B
      (initialData D δ hδ (a • ξ) hs) (t,(x,s)))) θ =
      coefficient τ hτ hτT B ξ hs a t x * deriv (profile δ) θ :=
  (scalar_deriv_hasDerivAt τ hτ hτT B δ hδ ξ hs a t x θ).deriv

theorem scalar_second_deriv_zero (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    deriv (deriv (fun s => scalar τ hτ hτT B
      (initialData D δ hδ (a • ξ) hs) (t,(x,s)))) 0 =
      coefficient τ hτ hτT B ξ hs a t x / δ := by
  rw [scalar_second_deriv,profile_deriv_zero δ hδ,div_eq_mul_inv]

/-- Physical pressure, given by `k⁻¹^2 * scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(Y
x,k*⟪D.m₀,Y x⟫_ℝ))`. -/
def physicalPressure (a k : ℝ) (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) : ℝ :=
  k⁻¹^2 * scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
    (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))

/-- Hessian remainder, given by `lowerHessian (fun z => scalar τ hτ hτT B (initialData D δ hδ (a
• ξ) hs) (t,z)) k D.m₀ Y (fun y => D.FInv.field t (Y y)) x`. -/
def hessianRemainder (a k : ℝ) (t : Icc (0 : ℝ) D.T) (Y : Space → Space)
    (x : Space) : Space →L[ℝ] Space :=
  lowerHessian (fun z => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,z))
    k D.m₀ Y (fun y => D.FInv.field t (Y y)) x

/-- The leading term is the literal normal tensor in source (20); the
remainder contains only terms with at least one factor of k⁻¹. -/
theorem physicalPressure_hessian (a k : ℝ) (hk : k ≠ 0) (t : Icc (0 : ℝ) D.T)
    (Y : Space → Space) (hY : ∀ x, HasFDerivAt Y (D.FInv.field t (Y x)) x) (x : Space) :
    fderiv ℝ (gradient (physicalPressure τ hτ hτT B δ hδ ξ hs a k t Y)) x =
      (coefficient τ hτ hτT B ξ hs a t (Y x) * deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (D.normal.field t (Y x)) (D.normal.field t (Y x)) +
      hessianRemainder τ hτ hτT B δ hδ ξ hs a k t Y x := by
  let q : LiftTangent → ℝ := fun z => scalar τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,z)
  have hq : ContDiff ℝ ∞ q := scalar_smooth τ hτ hτT B _ t
  have hJ : DifferentiableAt ℝ (fun y => D.FInv.field t (Y y)) x :=
    ((D.FInv.smooth t).differentiable (by simp) (Y x)).comp x (hY x).differentiableAt
  have hh := hessian_physical hq k hk D.m₀ Y (fun y => D.FInv.field t (Y y)) hY x hJ
  have ha : angularDerivative (angularDerivative q) (graphMap k D.m₀ (Y x)) =
      coefficient τ hτ hτT B ξ hs a t (Y x) * deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ) := by
    rw [angularSecond_eq_deriv hq]
    exact scalar_second_deriv τ hτ hτT B δ hδ ξ hs a t (Y x) (k*⟪D.m₀,Y x⟫_ℝ)
  rw [ha] at hh
  exact hh

theorem physicalPressure_hessian_of_inverse (a k : ℝ) (hk : k ≠ 0)
    (X Y : Icc (0 : ℝ) D.T → Space → Space)
    (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
    (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    fderiv ℝ (gradient (physicalPressure τ hτ hτT B δ hδ ξ hs a k t (Y t))) x =
      (coefficient τ hτ hτT B ξ hs a t (Y t x) * deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
        rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x)) +
      hessianRemainder τ hτ hτT B δ hδ ξ hs a k t (Y t) x :=
  physicalPressure_hessian τ hτ hτT B δ hδ ξ hs a k hk t (Y t)
    (continuousInverse_hasFDerivAt D X Y hX hXY hY t) x

end EulerPacketPrimaryPressure

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPacketPressure EulerPacketGraphHessian
  EulerGraphPullback EulerTransversePacketPrimary EulerPeriodicProfile
  EulerPacketInverseFlowGevrey EulerPacketPhysicalGevrey EulerGevrey
  EulerLiftedGradientSpace EulerCylinderSobolevSpace
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Initialized pressure hessian cost, constructed using `fastHessianCost`. -/
def initializedPressureHessianCost {D : Data U} {q : ℕ} {R₀ : ℝ}
    (NB : EulerTransversePacketJoin.NormalBudget D q R₀) (R H0 Rc C : ℝ) : ℝ :=
  fastHessianCost (P := period) NB (4*R) (fixedVelocityGradeCost R H0 1) +
    9*C*physicalFixedCost D Rc C (4*R) 1*sobolevEmbeddingConstant period 3 *
      (fixedVelocityGradeCost R H0 2+2)

variable (M : EulerMeanPacketProvider.Data) (D : Data U) (hTime : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T) (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

theorem initializedAngularPressure_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun z => initializedAngularPressure D τ hτ hτT B δ hδ ξ hs α (t,z)) := by
  have hq := scalar_smooth τ hτ hτT B (initialData D δ hδ (α • ξ) hs) t
  simp only [initializedAngularPressure,pressureJet_angle]
  change ContDiff ℝ ∞ (angularDerivative (fun y =>
    scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs) (t,y)))
  exact angularDerivative_contDiff hq

theorem initializedAngularPressure_second (t : Icc (0 : ℝ) D.T) (z : LiftTangent) :
    angularDerivative (fun w => initializedAngularPressure D τ hτ hτT B δ hδ ξ hs α (t,w)) z =
      EulerPacketPrimaryPressure.coefficient τ hτ hτT B ξ hs α t z.1 * deriv (profile δ) z.2 := by
  have hq := scalar_smooth τ hτ hτT B (initialData D δ hδ (α • ξ) hs) t
  simp only [initializedAngularPressure,pressureJet_angle]
  change angularDerivative (angularDerivative (fun w =>
    scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs) (t,w))) z = _
  rw [angularSecond_eq_deriv hq]
  exact EulerPacketPrimaryPressure.scalar_second_deriv τ hτ hτT B δ hδ ξ hs α t z.1 z.2

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

theorem initializedPressure_hessian_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (X Y : Icc (0 : ℝ) D.T → Space → Space)
    (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
    (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (gradient (fun y => initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ)))) x -
      (EulerPacketPrimaryPressure.coefficient τ hτ hτT B ξ hs α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
      rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x))‖ ≤
        initializedPressureHessianCost NB L.R S.H0 L.Rc L.C₀/k := by
  have hk0 : 0 < k := by linarith
  have hr0 : 0 ≤ L.R := zero_le_one.trans L.radius_bounds.1
  let AF := initializedAngularPressureField M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth
  let RF := initializedCovectorRemainderField M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k⁻¹
  let a : LiftTangent → ℝ := fun z => initializedAngularPressure D τ hτ hτT B δ hδ ξ hs α (t,z)
  let J : Space → Space →L[ℝ] Space := fun y => D.FInv.field t (Y t y)
  have hYd := continuousInverse_differentiable D X Y hX hXY hY
  have hYder := continuousInverse_hasFDerivAt D X Y hX hXY hY
  have hJ : DifferentiableAt ℝ J x :=
    ((D.FInv.smooth t).differentiable (by simp) (Y t x)).comp x (hYd t x)
  have ha : ContDiff ℝ ∞ a := initializedAngularPressure_smooth D τ hτ hτT B δ hδ ξ hs α t
  have hf := fastForce_hasFDerivAt a k hk0.ne' D.m₀ (Y t) J x (hYder t x) hJ
    (ha.differentiable (by simp) _)
  have hsecond : angularDerivative a (graphMap k D.m₀ (Y t x)) =
      EulerPacketPrimaryPressure.coefficient τ hτ hτT B ξ hs α t (Y t x) *
        deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ) :=
    initializedAngularPressure_second D τ hτ hτT B δ hδ ξ hs α t _
  have hn : transportedNormal D.m₀ J x = D.normal.field t (Y t x) := rfl
  rw [hsecond,hn] at hf
  have hRF := initializedCovectorRemainder_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hAF := initializedAngularPressure_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth
  have hfast := fastHessianRemainder_bound NB
    (initializedAngularPressure D τ hτ hτT B δ hδ ξ hs α) AF (4*L.R)
    (fixedVelocityGradeCost L.R S.H0 1) (by positivity)
    (fixedVelocityGradeCost_nonneg L.R S.H0 hr0 1) hAF k hk0 t (Y t) x (hYder t x)
    (ha.differentiable (by simp) _)
  have htail := physicalCovector_error_bound D RF (4*L.R)
    (fixedVelocityGradeCost L.R S.H0 2+2) (by positivity)
    (by have h := fixedVelocityGradeCost_nonneg L.R S.H0 hr0 2; linarith)
    k (by linarith) hRF L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg hdet L.frame_bound
    X Y hX hYd hXY t x
  have htaild : DifferentiableAt ℝ (physicalCovector D RF k Y t) x := by
    have hI := (adjoint.differentiableAt.comp x hJ)
    have hR := (RF.raw_graph_contDiff t k D.m₀).differentiable (by simp) (Y t x)
    have hRg := hR.comp x (hYd t x)
    exact hI.clm_apply hRg
  have he : gradient (fun y => initializedPressure M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y t y,k*⟪D.m₀,Y t y⟫_ℝ))) =
      fastForce a k D.m₀ (Y t) J + physicalCovector D RF k Y t := by
    funext y
    exact initializedPressure_gradient_decomposition M D hTime τ hτ hτT B δ hδ ξ hs α
      N k hk0.ne' t (Y t) y (hYder t y)
  calc
    _ = ‖fastHessianRemainder a k D.m₀ (Y t) J x +
        fderiv ℝ (physicalCovector D RF k Y t) x‖ := by
      rw [he,fderiv_add hf.differentiableAt htaild,hf.fderiv]
      congr 1
      abel
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hfast htail).trans_eq (by
      unfold initializedPressureHessianCost
      ring))

end EulerPacketTerminalDatum
