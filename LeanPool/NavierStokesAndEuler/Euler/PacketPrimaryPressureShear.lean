/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphHessian
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryScaling
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPressure

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
