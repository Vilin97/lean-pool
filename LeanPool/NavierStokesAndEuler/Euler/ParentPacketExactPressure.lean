/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketExactEuler

@[expose] public section

/-! The actual scalar pressure of the corrected source packet has the
constructed continuous physical pressure force, at every time. -/

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketPhysicalTransform EulerLagrangian
open scoped ContDiff

private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

variable (A : EulerParentPacketFrames.Parent)

theorem transformedForce_continuous
    (Y force g : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) (hforce : Continuous (Function.uncurry force))
    (hg : Continuous (Function.uncurry g)) :
    Continuous (fun q : Icc (0 : ℝ) A.T × Space => force q.1 q.2 +
      A.ell • (A.inverse.field q.1 (A.ell⁻¹ • Y q.1 q.2)).adjoint
        (g q.1 (A.ell⁻¹ • Y q.1 q.2))) := by
  let r : Icc (0 : ℝ) A.T × Space → Space := fun q => A.ell⁻¹ • Y q.1 q.2
  have hr : Continuous r := hY.const_smul A.ell⁻¹
  have hI₀ : Continuous (fun q : Icc (0 : ℝ) A.T × Space => A.inverse.field q.1 q.2) := by
    have hc : Continuous (fun q : Icc (0 : ℝ) A.T × Space => ((q.1 : ℝ),q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have h := (A.inverse.realField_joint_continuous A.T A.T_pos.le).comp
      hc
    simpa only [Function.comp_def,Function.uncurry_def,SmoothTimeField.realField_apply] using h
  have hmap : Continuous (fun q : Icc (0 : ℝ) A.T × Space => (q.1,r q)) :=
    continuous_fst.prodMk hr
  have hIn := hI₀.comp (f := fun q : Icc (0 : ℝ) A.T × Space => (q.1,r q)) hmap
  have ha : Continuous (fun L : Space →L[ℝ] Space => L.adjoint) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous
  have hI := ha.comp (f := fun q : Icc (0 : ℝ) A.T × Space => A.inverse.field q.1 (r q)) hIn
  have hP := hg.comp (f := fun q : Icc (0 : ℝ) A.T × Space => (q.1,r q)) hmap
  have hterm := (hI.clm_apply hP).const_smul A.ell
  exact hforce.add hterm

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)


variable {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos (correctionData (A.transverseData m hm J support
    hSupport) P κ hκ Z R))


def exactPacketForce (k : ℝ) (Y force : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  force t x + A.ell • (A.inverse.field t (A.ell⁻¹ • Y t x)).adjoint
    (((exactPacketOfResidual P B residual)).graphPressure k t (A.ell⁻¹ • Y t x))

theorem exactPacketForce_continuous (k : ℝ) (Y force : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) (hforce : Continuous (Function.uncurry force)) :
    Continuous (Function.uncurry (A.exactPacketForce m hm J support hSupport B residual k Y force))
      := by
  exact A.transformedForce_continuous Y force
    ((exactPacketOfResidual P B residual).graphPressure k) hY hforce
    ((exactPacketOfResidual P B residual).graphPressure_joint_continuous k)

variable (k : ℝ) (hk : k*κ=1) (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hXY : ∀ t x, A.position t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (p : ℝ × Space → ℝ) (force : Icc (0 : ℝ) A.T → Space → Space)
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t,y)) x)
  (hgradient : ∀ (t : Icc (0 : ℝ) A.T) x, gradient (fun y => p (t,y)) x=force t x)

include hk hXY hY hp hgradient in
theorem normalizedExactPressure_gradient (t : Icc (0 : ℝ) A.T) (x : Space) :
    gradient (fun y => A.normalizedExactPressure m hm J support hSupport B residual k Y p (t,y)) x =
      A.ell⁻¹ • force t (A.ell • x) +
        (A.inverse.field t (A.packetInverse Y (t,x))).adjoint
          (((exactPacketOfResidual P B residual)).graphPressure k t (A.packetInverse Y (t,x))) := by
  have hs := exact_physicalPressure_smooth (A.transverseData m hm J support hSupport)
    (exactPacketOfResidual P B residual)
    (fun s y => A.packetPosition (s,y)) (fun s y => A.packetInverse Y (s,y))
    (fun s y => A.packetPosition_spatial s y)
    (fun s y => A.packetInverse_right Y hXY (s,y))
    (A.packetInverse_time_continuous Y hY) k hk (A.packetInverse Y) (fun _ _ => rfl) t
  have hg := exact_physicalPressure_gradient (A.transverseData m hm J support hSupport)
    (exactPacketOfResidual P B residual)
    (fun s y => A.packetPosition (s,y)) (fun s y => A.packetInverse Y (s,y))
    (fun s y => A.packetPosition_spatial s y)
    (fun s y => A.packetInverse_right Y hXY (s,y))
    (A.packetInverse_time_continuous Y hY) k hk (A.packetInverse Y) (fun _ _ => rfl) t x
  have hn := EulerSpatialRescaling.pressure_gradient A.ell⁻¹ (inv_ne_zero A.ell_pos.ne') p (t,x)
    (by simpa only [inv_inv] using hp t (A.ell • x))
  simp only [inv_inv] at hn
  change gradient (fun y => A.normalizedPressure p (t,y)) x =
    A.ell⁻¹ • gradient (fun y => p (t,y)) (A.ell • x) at hn
  change gradient (fun y => A.normalizedPressure p (t,y)+
    physicalPressure (((exactPacketOfResidual P B residual)).rawGraphPotential k) (A.packetInverse
      Y) (t,y)) x=_
  erw [gradient_add _ _ x (A.normalizedPressure_differentiableAt p t x (hp t (A.ell • x)))
    (hs.differentiable (by simp) x),hn,hg,hgradient]
  change A.ell⁻¹ • force t (A.ell • x) + κ •
    (A.inverse.field t (A.packetInverse Y (t,x))).adjoint
      (((exactPacketOfResidual P B residual)).pressure.pointField t
        (EulerGraphPressurePotential.cylinderGraph P k m (A.packetInverse Y (t,x)))) = _
  apply congrArg (fun z => A.ell⁻¹ • force t (A.ell • x) + z)
  exact ((A.inverse.field t (A.packetInverse Y (t,x))).adjoint.map_smul κ
    ((exactPacketOfResidual P B residual).pressure.pointField t
      (EulerGraphPressurePotential.cylinderGraph P k m (A.packetInverse Y (t,x))))).symm

include hk hXY hY hp hgradient in
theorem exactPacketPressure_gradient (t : Icc (0 : ℝ) A.T) (x : Space) :
    gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k Y p (t,y)) x =
      A.exactPacketForce m hm J support hSupport B residual k Y force t x := by
  have hg := EulerSpatialRescaling.pressure_gradient A.ell A.ell_pos.ne'
    (A.normalizedExactPressure m hm J support hSupport B residual k Y p) (t,x)
    (A.normalizedExactPressure_differentiableAt m hm J support hSupport B residual k hk Y hXY hY p
      hp t
      (A.ell⁻¹ • x))
  change gradient (fun y => EulerSpatialRescaling.pressure A.ell
    (A.normalizedExactPressure m hm J support hSupport B residual k Y p) (t,y)) x=_
  rw [hg,A.normalizedExactPressure_gradient m hm J support hSupport B residual k hk Y hXY hY
    p force hp hgradient t (A.ell⁻¹ • x)]
  have hx : A.ell • (A.ell⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  have hy : A.packetInverse Y (t,A.ell⁻¹ • x)=A.ell⁻¹ • Y t x := by
    simp only [packetInverse,projIcc_of_mem A.T_pos.le t.property,hx]
  rw [hx,hy,smul_add,smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  rfl

end EulerParentPacketFrames.Parent
