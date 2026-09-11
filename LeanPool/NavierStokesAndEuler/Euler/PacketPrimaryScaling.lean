/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.CylinderSliceRepresentatives
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHomogeneity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
public import LeanPool.NavierStokesAndEuler.Euler.PacketNormalizedPrimary
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryShearIdentity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPiolaData

/-! The amplitude in the literal terminal datum gives exactly the
amplitude multiplying the physical primary wave. -/

section

/-! Exact rank-one primary shear throughout the joined history and forward
interval, obtained from the proved factorization of the actual primary. -/

@[expose] public section

noncomputable section

namespace EulerPacketPrimaryShear

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerGraphPullback EulerPacketNormalizedPrimary
  EulerTransversePacketProvider EulerPacketTerminalDatum EulerTransversePacketPrimary
  EulerSpatialCutoffs EulerPeriodicProfile EulerPacketPrimaryFactorization
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)

/-- Full wave, given by `(α/k) • vector τ hτ hτT B (initialData D δ hδ ξ hs)
(t,(y,k*⟪D.m₀,y⟫_ℝ))`. -/
def fullWave (α k : ℝ) (t : Icc (0 : ℝ) D.T) (y : Space) : Space :=
  (α/k) • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(y,k*⟪D.m₀,y⟫_ℝ))

theorem fullWave_hasFDerivAt (α k : ℝ) (hk : k ≠ 0) (t : Icc (0 : ℝ) D.T) :
    HasFDerivAt (fullWave τ hτ hτT B δ hδ ξ hs α k t)
      ((α/δ) • rankOne ℝ (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0) D.m₀) 0 := by
  let A : Space × ℝ → Space := fun z =>
    vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,z)
  have hA : DifferentiableAt ℝ A (0,0) :=
    ((vectorField τ hτ hτT B (initialData D δ hδ ξ hs)).raw_smooth t).differentiable (by simp) (0,0)
  have hzero : ∀ y, A (y,0)=0 := by
    intro y
    change vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(y,0))=0
    rw [vector_factorization]
    simp [profile]
  have ha : HasDerivAt (fun θ : ℝ => A (0,θ))
      (δ⁻¹ • envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0) 0 := by
    have hp := (profile_hasDerivAt δ hδ 0).differentiableAt.hasDerivAt
    rw [profile_deriv_zero δ hδ] at hp
    have he : (fun θ : ℝ => A (0,θ)) =
        fun θ => profile δ θ • envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0 :=
      funext (vector_factorization τ hτ hτT B δ hδ ξ hs t 0)
    rw [he]
    exact hp.smul_const _
  have h := zero_phase_graph_hasFDerivAt A _ D.m₀ hA hzero ha (α/k) k
  have hc : α/k*k=α := by field_simp
  rw [hc] at h
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,rankOne_apply,smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

theorem fullWave_physical_hasFDerivAt (α k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    HasFDerivAt (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x))
      ((α/δ) • rankOne ℝ (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0)
        (D.normal.field t 0)) (X 0) := by
  have he : (Y ∘ X) = id := funext hleft
  have hdY := EulerLagrangian.derivative_pullback_inverse Y X (D.deformationEquiv t 0) 0 hX hY
  rw [he,fderiv_id,id_comp] at hdY
  have hy : HasFDerivAt Y (D.deformationEquiv t 0).symm.toContinuousLinearMap (X 0) :=
    hdY ▸ hY.hasFDerivAt
  have hp : HasFDerivAt (fullWave τ hτ hτT B δ hδ ξ hs α k t)
      ((α/δ) • rankOne ℝ (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0) D.m₀) (Y (X 0)) := by
    rw [hleft]
    exact fullWave_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t
  convert! hp.comp (X 0) hy using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,comp_apply,rankOne_apply]
  congr 2
  exact (D.FInv.field t 0).adjoint_inner_left v D.m₀

theorem fullWave_physical_norm (α k : ℝ) (hα : 0 ≤ α) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    ‖fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0)‖ =
      (α/δ) * (‖D.normal.field t 0‖ * ‖envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0‖) := by
  rw [(fullWave_physical_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft).fderiv,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hα hδ.le),norm_rankOne,mul_comm
      ‖envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0‖ ‖D.normal.field t 0‖]

/-- The normalized rank-one expression is exactly the one in the source
geometry record, with c=α/δ and the actual primary velocity. -/
theorem fullWave_physical_normalized_gradient (α k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y)
    (hv : envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0 ≠ 0) :
    fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0) =
      ((α/δ)*(‖D.normal.field t 0‖*‖envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0‖)) •
        rankOne ℝ (unit (envelopedVelocity τ hτ hτT B δ hδ ξ hs t 0)) (unit (D.normal.field t 0))
            := by
  rw [(fullWave_physical_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft).fderiv]
  exact rankOne_normalized _ _ _ hv (HistoryData.normal_ne_zero t 0)

theorem fullWave_physical_canonical_gradient (α k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0) =
      (α/δ) • rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t 0) (D.normal.field t 0) := by
  rw [(fullWave_physical_hasFDerivAt τ hτ hτT B δ hδ ξ hs α k hk t X Y hX hY hleft).fderiv,
    envelopedVelocity_independent_profile τ hτ hτT B δ 1 hδ zero_lt_one]
  rfl

theorem fullWave_physical_canonical_norm (α k : ℝ) (hα : 0 ≤ α) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    ‖fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs α k t (Y x)) (X 0)‖ =
      (α/δ) * (‖D.normal.field t 0‖ * ‖canonicalVelocity τ hτ hτT B ξ hs t 0‖) := by
  rw [fullWave_physical_norm τ hτ hτT B δ hδ ξ hs α k hα hk t X Y hX hY hleft,
    envelopedVelocity_independent_profile τ hτ hτT B δ 1 hδ zero_lt_one]
  rfl

/-- The source amplitude choice gives exactly the requested center shear
for the genuine primary, at any chosen target time. The size in this
choice uses the velocity independent of the narrow profile δ. -/
theorem fullWave_target_shear (h k : ℝ) (hh : 0 ≤ h) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) (X Y : Space → Space)
    (hX : HasFDerivAt X (D.F.field t 0) 0)
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y)
    (hv : canonicalVelocity τ hτ hτT B ξ hs t 0 ≠ 0) :
    ‖fderiv ℝ (fun x => fullWave τ hτ hτT B δ hδ ξ hs
      (δ*h/(‖D.normal.field t 0‖*‖canonicalVelocity τ hτ hτT B ξ hs t 0‖)) k t (Y x)) (X 0)‖ = h :=
          by
  have hm : ‖D.normal.field t 0‖ ≠ 0 := norm_ne_zero_iff.mpr (HistoryData.normal_ne_zero t 0)
  have hw : ‖canonicalVelocity τ hτ hτT B ξ hs t 0‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [fullWave_physical_canonical_norm τ hτ hτT B δ hδ ξ hs _ k
    (div_nonneg (mul_nonneg hδ.le hh) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    hk t X Y hX hY hleft]
  field_simp [hδ.ne',hm,hw]

end EulerPacketPrimaryShear

end
end

end

@[expose] public section

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
    (hY : DifferentiableAt ℝ Y (X 0)) (hleft : ∀ y, Y (X y) = y) :
    fderiv ℝ (fun x => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs)
      (t,(Y x,k*⟪D.m₀,Y x⟫_ℝ))) (X 0) =
      (a/δ) • rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t 0) (D.normal.field t 0) := by
  have he := scaled_terminal_wave_eq τ hτ hτT B δ hδ ξ hs a k t
  change fderiv ℝ ((fun x : Space => k⁻¹ • vector τ hτ hτT B
    (initialData D δ hδ (a • ξ) hs) (t,(x,k*⟪D.m₀,x⟫_ℝ))) ∘ Y) (X 0) = _
  rw [he]
  exact fullWave_physical_canonical_gradient τ hτ hτT B δ hδ ξ hs a k hk t X Y hX hY hleft

end EulerPacketPrimaryShear
