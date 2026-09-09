/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedJointDifferentiability
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCoordinateResidual
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPiolaData

@[expose] public section

/-! The actual pointwise equation of the exact packet, expressed with the
prescribed deformation and its genuine time and spatial derivatives. -/

noncomputable section

namespace EulerPacketPhysicalTransform

open Set Filter ContinuousLinearMap EulerSmoothLimit EulerVolterraConvolution
open scoped Topology

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

theorem source_frame_time (F : ℝ × Space → Space →L[ℝ] Space)
    (hmatch : ∀ s : Icc (0 : ℝ) D.T, ∀ x, F (s,x) = D.F.field s x)
    (t : ℝ) (ht : t ∈ Ioo 0 D.T) (x : Space)
    (DF : (ℝ × Space) →L[ℝ] (Space →L[ℝ] Space))
    (hF : HasFDerivAt F DF (t,x)) :
    DF (1,0) = D.F₁.field ⟨t,ht.1.le,ht.2.le⟩ x := by
  have he : (fun s => F (s,x)) =ᶠ[𝓝 t]
      (fun s => extendPath D.T D.T_pos.le D.F.field s x) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    simpa only [extendPath,projIcc_of_mem D.T_pos.le hs] using hmatch ⟨s,hs⟩ x
  have hf := hF.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hd := (D.frame_time t ⟨ht.1.le,ht.2.le⟩ x).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  simpa only [extendPath,projIcc_of_mem D.T_pos.le ⟨ht.1.le,ht.2.le⟩] using
    hf.unique (hd.congr_of_eventuallyEq he)

theorem source_frame_spatial (F : ℝ × Space → Space →L[ℝ] Space)
    (hmatch : ∀ s : Icc (0 : ℝ) D.T, ∀ x, F (s,x) = D.F.field s x)
    (t : Icc (0 : ℝ) D.T) (x v : Space)
    (DF : (ℝ × Space) →L[ℝ] (Space →L[ℝ] Space))
    (hF : HasFDerivAt F DF (t,x)) :
    DF (0,v) = fderiv ℝ (D.F.field t : Space → Space →L[ℝ] Space) x v := by
  have hd := hF.comp x (hasFDerivAt_prodMk_right (t : ℝ) x)
  have he : (fun y => F (t,y)) = (D.F.field t : Space → Space →L[ℝ] Space) :=
    funext (hmatch t)
  change HasFDerivAt (fun y => F (t,y)) (DF.comp (inr ℝ ℝ Space)) x at hd
  rw [he] at hd
  rw [hd.fderiv]
  rfl

end EulerPacketPhysicalTransform

namespace EulerAllOrderDriftCorrection.ExactLiftedPacket

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerPacketCorrectionCoefficients
  EulerPacketCoordinates EulerMetricTransport

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P D.T}
  {B : Budget P D.T_pos (correctionData D P κ hκ Z R)}
  (S : ExactLiftedPacket P D.T_pos (correctionData D P κ hκ Z R) B)

theorem source_equation (t : ℝ) (ht : t ∈ Ioo 0 D.T) (z : LiftTangent) :
    fderiv ℝ S.rawVelocity (t,z) (1,0) +
      (2 : ℝ) • D.FInv.field ⟨t,ht.1.le,ht.2.le⟩ z.1
        (D.F₁.field ⟨t,ht.1.le,ht.2.le⟩ z.1 (S.rawVelocity (t,z))) +
      fderiv ℝ S.rawVelocity (t,z) (0,(κ • S.rawVelocity (t,z),⟪D.m₀,S.rawVelocity (t,z)⟫_ℝ)) +
      κ • D.FInv.field ⟨t,ht.1.le,ht.2.le⟩ z.1
        (fderiv ℝ (D.F.field ⟨t,ht.1.le,ht.2.le⟩ : Space → Space →L[ℝ] Space)
          z.1 (S.rawVelocity (t,z)) (S.rawVelocity (t,z))) +
      D.FInv.field ⟨t,ht.1.le,ht.2.le⟩ z.1
        ((D.FInv.field ⟨t,ht.1.le,ht.2.le⟩ z.1).adjoint (S.rawPressure (t,z))) = 0 := by
  have h := S.raw_normalized_equation t ht z
  simp only [correctionData_linear,correctionData_quadratic,correctionData_metric,
    coveringMap,smul_apply,comp_apply] at h
  have hquad := algebraic_formula D κ S.rawVelocity (t,z)
  simp only [algebraic,rawQuadratic,rawFrame,rawInverse,EulerTransversePacketProvider.Data.clamp,
    projIcc_of_mem D.T_pos.le ⟨ht.1.le,ht.2.le⟩,smul_apply,comp_apply] at hquad
  rw [hquad] at h
  exact h

theorem source_equation_of_frame (F : ℝ × Space → Space →L[ℝ] Space)
    (hmatch : ∀ s : Icc (0 : ℝ) D.T, ∀ x, F (s,x) = D.F.field s x)
    (t : ℝ) (ht : t ∈ Ioo 0 D.T) (z : LiftTangent)
    (DF : (ℝ × Space) →L[ℝ] (Space →L[ℝ] Space))
    (hF : HasFDerivAt F DF (t,z.1)) :
    fderiv ℝ S.rawVelocity (t,z) (1,0) +
      (2 : ℝ) • (D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ z.1).symm
        (DF (1,0) (S.rawVelocity (t,z))) +
      fderiv ℝ S.rawVelocity (t,z) (0,(κ • S.rawVelocity (t,z),⟪D.m₀,S.rawVelocity (t,z)⟫_ℝ)) +
      κ • (D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ z.1).symm
        (DF (0,S.rawVelocity (t,z)) (S.rawVelocity (t,z))) +
      (D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ z.1).symm
        ((D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ z.1).symm.toContinuousLinearMap.adjoint
          (S.rawPressure (t,z))) = 0 := by
  rw [EulerPacketPhysicalTransform.source_frame_time D F hmatch t ht z.1 DF hF,
    EulerPacketPhysicalTransform.source_frame_spatial D F hmatch
      ⟨t,ht.1.le,ht.2.le⟩ z.1 (S.rawVelocity (t,z)) DF hF]
  exact S.source_equation D t ht z

end EulerAllOrderDriftCorrection.ExactLiftedPacket
