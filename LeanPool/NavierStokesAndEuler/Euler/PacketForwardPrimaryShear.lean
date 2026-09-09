/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardFactorization
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGlobalShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphHessian
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTensorBounds

/-! Literal shear and pressure Hessian of the primary starting at time
zero.  The leading tensors are derivatives of the actual constructed
velocity and scalar pressure, with the slow terms retained exactly. -/

@[expose] public section


noncomputable section

namespace EulerPacketForwardShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketForwardPrimary EulerPacketTerminalDatum
  EulerPacketForwardFactorization EulerPacketGraphHessian EulerGraphPullback
  EulerPacketCylinderField EulerLiftedGradientSpace EulerPeriodicProfile
  EulerCylinderCoordinates EulerCylinderSobolevSpace EulerGevrey
  EulerPacketPrimaryShear EulerPacketInverseFlowGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)

theorem angular_fderiv (a : ℝ) (t : Icc (0 : ℝ) D.T) (z : LiftTangent) :
    fderiv ℝ (fun y => vector D (initialData D δ hδ (a • ξ) hs) (t,y)) z (0,1) =
      (a*deriv (profile δ) z.2) • canonicalVelocity D ξ t z.1 := by
  let q : LiftTangent → Space := fun y => vector D (initialData D δ hδ (a • ξ) hs) (t,y)
  have he : (fun θ => q (z.1,θ)) = fun θ =>
      (a*profile δ θ) • canonicalVelocity D ξ t z.1 := by
    funext θ
    exact vector_factorization D δ hδ ξ hs a t z.1 θ
  have hd := (((profile_contDiff δ hδ).differentiable (by
      simp) z.2).hasDerivAt.const_mul a).smul_const
    (canonicalVelocity D ξ t z.1)
  have hq : DifferentiableAt ℝ q z :=
    (((forcing D).vectorField (initialData D δ hδ (a • ξ) hs)).raw_smooth t).differentiable
      (by simp) z
  have hv := (hq.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
  change deriv (fun θ => q (z.1,θ)) z.2 = _ at hv
  rw [he,hd.deriv] at hv
  exact hv.symm

theorem global_gradient (a k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    fderiv ℝ (fun y => k⁻¹ • vector D (initialData D δ hδ (a • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x =
      (a*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity D ξ t (Y x)) (D.normal.field t (Y x)) +
      slowGraphDerivative (fun z => vector D (initialData D δ hδ (a • ξ) hs) (t,z))
        k D.m₀ Y (D.FInv.field t (Y x)) x := by
  have hq := (((forcing D).vectorField (initialData D δ hδ (a • ξ) hs)).raw_smooth t).differentiable
    (by simp)
  have he := (graph_vector_hasFDerivAt
    (fun z => vector D (initialData D δ hδ (a • ξ) hs) (t,z))
    k hk D.m₀ Y _ x hY (hq _)).fderiv
  rw [angular_fderiv D δ hδ ξ hs] at he
  convert! he using 1
  apply congrArg (fun V : Space →L[ℝ] Space => V + _)
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,rankOne_apply,smul_smul,graphMap_apply]
  rw [mul_comm]
  rfl

theorem global_gradient_bound (a k : ℝ) (hk : 0 < k)
    (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hG : ((forcing D).vectorField (initialData D δ hδ (a • ξ) hs)).WordBound 6 R A 0)
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) (hJ : ‖D.FInv.field t (Y x)‖ ≤ C) :
    ‖fderiv ℝ (fun y => k⁻¹ • vector D (initialData D δ hδ (a • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x -
      (a*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity D ξ t (Y x)) (D.normal.field t (Y x))‖ ≤
      (‖coordinateEquiv.symm.toContinuousLinearMap‖*(sobolevEmbeddingConstant period 3*A*R)*C)/k :=
          by
  rw [global_gradient D δ hδ ξ hs a k hk.ne' t Y x hY,add_sub_cancel_left]
  have hd := hG.raw_fderiv_le (by norm_num) t (graphMap k D.m₀ (Y x))
  simp only [majorant,Nat.add_zero,Nat.factorial_one,Nat.cast_one,pow_one,one_pow,mul_one] at hd
  have hn := slowGraphDerivative_norm_le
    (fun z => vector D (initialData D δ hδ (a • ξ) hs) (t,z))
    k D.m₀ Y (D.FInv.field t (Y x)) x
  have hb := sobolevEmbeddingConstant_nonneg period 3
  calc
    _ ≤ |k⁻¹| * ‖fderiv ℝ (fun z => vector D
          (initialData D δ hδ (a • ξ) hs) (t,z)) (graphMap k D.m₀ (Y x))‖ *
        ‖D.FInv.field t (Y x)‖ := hn
    _ ≤ |k⁻¹| * (‖coordinateEquiv.symm.toContinuousLinearMap‖*
        (sobolevEmbeddingConstant period 3*A*R)) * C :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) hJ (norm_nonneg _) (by positivity)
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hk)]; ring

/-- Pressure coefficient, given by `-(2*a*⟪D.normal.field t x,D.M.field t x (canonicalVelocity D
ξ t x)⟫_ℝ)/ ‖D.normal.field t x‖^2`. -/
def pressureCoefficient (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) : ℝ :=
  -(2*a*⟪D.normal.field t x,D.M.field t x (canonicalVelocity D ξ t x)⟫_ℝ)/
    ‖D.normal.field t x‖^2

theorem scalar_hasDerivAt (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt (fun s => scalar D (initialData D δ hδ (a • ξ) hs) (t,(x,s)))
      (pressureCoefficient D ξ a t x * profile δ θ) θ := by
  apply (scalar_angle D (initialData D δ hδ (a • ξ) hs) t x θ).congr_deriv
  rw [vector_factorization D δ hδ ξ hs a t x θ]
  simp only [pressureCoefficient,map_smul,inner_smul_right]
  ring

theorem scalar_deriv (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    deriv (fun s => scalar D (initialData D δ hδ (a • ξ) hs) (t,(x,s))) θ =
      pressureCoefficient D ξ a t x * profile δ θ :=
  (scalar_hasDerivAt D δ hδ ξ hs a t x θ).deriv

theorem scalar_deriv_hasDerivAt (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivAt
      (deriv (fun s => scalar D (initialData D δ hδ (a • ξ) hs) (t,(x,s))))
      (pressureCoefficient D ξ a t x * deriv (profile δ) θ) θ := by
  have he := funext (scalar_deriv D δ hδ ξ hs a t x)
  rw [he]
  exact ((profile_contDiff δ hδ).differentiable (by simp) θ).hasDerivAt.const_mul _

theorem scalar_second_deriv (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    deriv (deriv (fun s => scalar D (initialData D δ hδ (a • ξ) hs) (t,(x,s)))) θ =
      pressureCoefficient D ξ a t x * deriv (profile δ) θ :=
  (scalar_deriv_hasDerivAt D δ hδ ξ hs a t x θ).deriv

theorem scalar_second_deriv_zero (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    deriv (deriv (fun s => scalar D (initialData D δ hδ (a • ξ) hs) (t,(x,s)))) 0 =
      pressureCoefficient D ξ a t x / δ := by
  rw [scalar_second_deriv,profile_deriv_zero δ hδ,div_eq_mul_inv]

/-- Physical pressure, given by `k⁻¹^2 * scalar D (initialData D δ hδ (a • ξ) hs) (t,(Y
x,k*⟪D.m₀,Y x⟫_ℝ))`. -/
def physicalPressure (a k : ℝ) (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space) : ℝ :=
  k⁻¹^2 * scalar D (initialData D δ hδ (a • ξ) hs) (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))

/-- Hessian remainder, given by `lowerHessian (fun z => scalar D (initialData D δ hδ (a • ξ) hs)
(t,z)) k D.m₀ Y (fun y => D.FInv.field t (Y y)) x`. -/
def hessianRemainder (a k : ℝ) (t : Icc (0 : ℝ) D.T) (Y : Space → Space)
    (x : Space) : Space →L[ℝ] Space :=
  lowerHessian (fun z => scalar D (initialData D δ hδ (a • ξ) hs) (t,z))
    k D.m₀ Y (fun y => D.FInv.field t (Y y)) x

theorem physicalPressure_hessian (a k : ℝ) (hk : k ≠ 0) (t : Icc (0 : ℝ) D.T)
    (Y : Space → Space) (hY : ∀ x, HasFDerivAt Y (D.FInv.field t (Y x)) x) (x : Space) :
    fderiv ℝ (gradient (physicalPressure D δ hδ ξ hs a k t Y)) x =
      (pressureCoefficient D ξ a t (Y x) * deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (D.normal.field t (Y x)) (D.normal.field t (Y x)) +
      hessianRemainder D δ hδ ξ hs a k t Y x := by
  let q : LiftTangent → ℝ := fun z => scalar D (initialData D δ hδ (a • ξ) hs) (t,z)
  have hq : ContDiff ℝ ∞ q := pressure_smooth D _ t
  have hJ : DifferentiableAt ℝ (fun y => D.FInv.field t (Y y)) x :=
    ((D.FInv.smooth t).differentiable (by simp) (Y x)).comp x (hY x).differentiableAt
  have hh := hessian_physical hq k hk D.m₀ Y (fun y => D.FInv.field t (Y y)) hY x hJ
  have ha : angularDerivative (angularDerivative q) (graphMap k D.m₀ (Y x)) =
      pressureCoefficient D ξ a t (Y x) * deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ) := by
    rw [angularSecond_eq_deriv hq]
    exact scalar_second_deriv D δ hδ ξ hs a t (Y x) (k*⟪D.m₀,Y x⟫_ℝ)
  rw [ha] at hh
  exact hh

theorem physicalPressure_hessian_of_inverse (a k : ℝ) (hk : k ≠ 0)
    (X Y : Icc (0 : ℝ) D.T → Space → Space)
    (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
    (hXY : ∀ t x, X t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    fderiv ℝ (gradient (physicalPressure D δ hδ ξ hs a k t (Y t))) x =
      (pressureCoefficient D ξ a t (Y t x) * deriv (profile δ) (k*⟪D.m₀,Y t x⟫_ℝ)) •
        rankOne ℝ (D.normal.field t (Y t x)) (D.normal.field t (Y t x)) +
      hessianRemainder D δ hδ ξ hs a k t (Y t) x :=
  physicalPressure_hessian D δ hδ ξ hs a k hk t (Y t)
    (continuousInverse_hasFDerivAt D X Y hX hXY hY t) x

end EulerPacketForwardShear
