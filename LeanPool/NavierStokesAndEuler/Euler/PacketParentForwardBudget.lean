/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentTransverseCosts
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds

/-! The zero-history forward budget has an explicit polynomial source
radius.  Cofactor bounds discharge the Gram inverse cost.  The sole growth
estimate supplied here is the genuine weighted homogeneous propagator H3. -/

@[expose] public section


noncomputable section

namespace EulerPacketParentForwardBudget

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerPacketPiola EulerPacketCofactor EulerPacketParentTransverseCosts
  EulerPacketParentMeanCoercivity EulerGevrey EulerParameterWordGevrey
  EulerSourceForwardCoefficient EulerLinearFundamentalExistence
open scoped ContDiff BoundedContinuousFunction

/-- Radius as an element of `ℝ`. -/
def radius (q : ℕ) (T R C C₁ Cp : ℝ) : ℝ :=
  1+sobolevCoefficientRadius (Fin 4) R +
    sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C) +
    2*forwardCost q T 0 R C C₁ Cp*(sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C)+1)

theorem radius_guards (q : ℕ) (T R C C₁ Cp : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hCp : 0 ≤ Cp) :
    1 ≤ radius q T R C C₁ Cp ∧
    sobolevCoefficientRadius (Fin 4) R ≤ radius q T R C C₁ Cp ∧
    sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C) ≤ radius q T R C C₁ Cp ∧
    2*forwardCost q T 0 R C C₁ Cp*(sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C)+1) ≤
      radius q T R C C₁ Cp := by
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 4) R hR
  have hi := sobolevCoefficientRadius_nonneg (ι := Fin 4) (4*inverseRadius R C)
    (mul_nonneg (by norm_num) (inverseRadius_nonneg R C hR))
  have hf := forwardCost_nonneg q T 0 R C C₁ Cp hT le_rfl hR hC hC₁ hCp
  have hfr := mul_nonneg hf (add_nonneg hi zero_le_one)
  unfold radius
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instPacketParentForwardBudget1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instPacketParentForwardBudget2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- Source forward budget as an element of `EulerTransversePacketForward.Budget D (Fin 4) q`. -/
def sourceForwardBudget (D : Data U) (q : ℕ) (R C C₁ Cp : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hCp : 0 ≤ Cp)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
    (hF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → EndSpace) x‖ ≤ C₁ * majorant R 0 n)
    (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (hg0 : g ⟨0, le_rfl, D.T_pos.le⟩ = 1)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
    (hprop : ∀ t s : Icc (0 : ℝ) D.T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
      ‖((fundamentalPath D.T D.T_pos.le
          (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
              D.frame_lower)).forward t x).comp
        ((fundamentalPath D.T D.T_pos.le
          (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
              D.frame_lower)).backward s x)‖ ≤ Cp*g t/g s) :
    EulerTransversePacketForward.Budget D (Fin 4) q := by
  have hzero : ∀ t x, ‖D.F.field t x‖ ≤ C := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hF 0 t x
  have hi : D.frameLower⁻¹ ≤ gramInverseEnvelope C := by
    simpa only [gramInverseEnvelope,add_comm] using D.frameLower_inv_le_of_frame C hC hdet hzero
  have hr := radius_guards q D.T R C C₁ Cp D.T_pos.le hR hC hC₁ hCp
  have hf := forwardCost_bound q D.T 0 R C C₁ Cp 1 D.T_pos.le hR hC hC₁ hCp (by norm_num)
  have hri : 0 ≤ sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C)+1 :=
    add_nonneg (sobolevCoefficientRadius_nonneg (ι := Fin 4) _
      (mul_nonneg (by norm_num) (inverseRadius_nonneg R C hR))) zero_le_one
  refine {
    g := g
    positive := hg
    initial_one := hg0
    neighborhood := Ω
    neighborhood_measurable := hΩ
    neighborhood_open := hΩo
    support_subset := hsub
    neighborhood_halfball := hΩball
    Rc := R
    C₀ := C
    C₁ := C₁
    C := Cp
    Ri := inverseRadius R C
    R := radius q D.T R C C₁ Cp
    Rc_nonneg := hR
    C₀_nonneg := hC
    C₁_nonneg := hC₁
    C_nonneg := hCp
    frame_bound := hF
    frameDerivative_bound := hF₁
    forward_inverse := inverseRadius_bound R C _ hR hi
    radius_one := hr.1
    frame_radius := hr.2.1
    forcing_radius := hr.2.2.1
    forward_radius := ?_
    propagator := hprop }
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by norm_num)) hri).trans hr.2.2.2

end EulerPacketParentForwardBudget
