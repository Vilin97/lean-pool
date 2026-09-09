/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFullShear
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHomogeneity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra

@[expose] public section

/-! The amplitude in the literal terminal datum gives exactly the
amplitude multiplying the physical primary wave. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerTransversePacketProvider EulerSpatialCutoffs

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

omit [CompleteSpace U] in
theorem terminal_smul (δ : ℝ) (hδ : 0 < δ) (ξ : U) (a : ℝ) :
    terminal δ hδ (a • ξ) = a • terminal δ hδ ξ := by
  apply Lp.ext
  filter_upwards [terminal_ae δ hδ (a • ξ),
    Lp.coeFn_smul a (terminal δ hδ ξ),terminal_ae δ hδ ξ] with x hz hs hy
  rw [hz,hs,Pi.smul_apply,hy]
  simp only [field,smul_smul]
  congr 1
  ring

theorem initialData_value_smul (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (a : ℝ) :
    (initialData D δ hδ (a • ξ) hs).value = a • (initialData D δ hδ ξ hs).value := by
  apply Subtype.ext
  exact terminal_smul δ hδ ξ a

end EulerPacketTerminalDatum

namespace EulerPacketPrimaryShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerCylinderSmoothOrbit EulerPacketCylinderField
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPacketPrimaryFactorization
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

theorem vector_terminal_smul (a : ℝ) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,θ)) =
      a • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ)) := by
  let G := vectorField τ hτ hτT B (initialData D δ hδ ξ hs)
  let H := vectorField τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
  have hp : H.path = (G.smul a).path :=
    velocityPath_eq_smul τ hτ hτT B _ _ a (initialData_value_smul D δ hδ ξ hs a)
  have he := congrFun (pointField_eq_of_slice_eq period H.path (G.smul a).path
    H.orbit (G.smul a).orbit t t (congrArg (fun p => p t) hp)) (x,(θ : AddCircle period))
  exact (H.raw_eq t x θ).trans (he.trans ((G.smul a).raw_eq t x θ).symm)

theorem scaled_terminal_wave_eq (a k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (fun x : Space => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
      (t,(x,k*⟪D.m₀,x⟫_ℝ))) = fullWave τ hτ hτT B δ hδ ξ hs a k t := by
  funext x
  rw [vector_terminal_smul τ hτ hτT B δ hδ ξ hs]
  simp only [fullWave,smul_smul,div_eq_mul_inv,mul_comm]

/-- This derivative belongs to the literal primary used by the initialized
packet, where the amplitude is inserted in its terminal datum. -/
theorem scaled_terminal_physical_gradient (a k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y)=y) :
    fderiv ℝ (fun x => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
      (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))) (X 0) =
      (a/δ) • rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t 0) (D.normal.field t 0) := by
  have he := scaled_terminal_wave_eq τ hτ hτT B δ hδ ξ hs a k t
  change fderiv ℝ ((fun x : Space => k⁻¹ • vector τ hτ hτT B
    (initialData D δ hδ (a • ξ) hs) (t,(x,k*⟪D.m₀,x⟫_ℝ))) ∘ Y) (X 0) = _
  rw [he]
  exact fullWave_physical_canonical_gradient τ hτ hτT B δ hδ ξ hs a k hk t X Y hX hY hleft

end EulerPacketPrimaryShear
