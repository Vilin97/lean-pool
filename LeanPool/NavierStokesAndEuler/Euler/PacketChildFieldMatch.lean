/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactShearError
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPressureError
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketExactEuler
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketExactEulerianField

/-! Literal rescaling and field identities for a child packet.  The
physical velocity gradient and scalar-pressure Hessian retain the
normalized packet's size: neither receives a negative power of ell. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalLowBounds

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLagrangian


/-- Add velocity, given by `u x+ell • w (ell⁻¹ • x)`. -/
def addVelocity (ell : ℝ) (u w : Space → Space) (x : Space) : Space :=
  u x+ell • w (ell⁻¹ • x)

/-- Add pressure, given by `p x+ell^2*q (ell⁻¹ • x)`. -/
def addPressure (ell : ℝ) (p q : Space → ℝ) (x : Space) : ℝ :=
  p x+ell^2*q (ell⁻¹ • x)

theorem addVelocity_fderiv (ell : ℝ) (hell : ell ≠ 0) (u w : Space → Space)
    (x : Space) (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w (ell⁻¹ • x)) :
    fderiv ℝ (addVelocity ell u w) x=fderiv ℝ u x+fderiv ℝ w (ell⁻¹ • x) := by
  have hd := EulerSpatialRescaling.spatial_derivative ell hell (fun q => w q.2) 0 x hw
  change fderiv ℝ (fun y => ell • w (ell⁻¹ • y)) x=fderiv ℝ w (ell⁻¹ • x) at hd
  have hc : DifferentiableAt ℝ (fun y => ell • w (ell⁻¹ • y)) x :=
    (hw.comp x (ell⁻¹ • ContinuousLinearMap.id ℝ Space).differentiableAt).const_smul ell
  change fderiv ℝ (fun y => u y+ell • w (ell⁻¹ • y)) x = _
  rw [fderiv_fun_add hu hc,hd]

theorem addPressure_gradient (ell : ℝ) (hell : ell ≠ 0) (p q : Space → ℝ)
    (x : Space) (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q (ell⁻¹ • x)) :
    gradient (addPressure ell p q) x = addVelocity ell (gradient p) (gradient q) x := by
  have hg := EulerSpatialRescaling.pressure_gradient ell hell (fun z => q z.2) (0,x) hq
  change gradient (fun y => ell^2*q (ell⁻¹ • y)) x =ell • gradient q (ell⁻¹ • x) at hg
  have hc : DifferentiableAt ℝ (fun y => ell^2*q (ell⁻¹ • y)) x :=
    (hq.comp x (ell⁻¹ • ContinuousLinearMap.id ℝ Space).differentiableAt).const_mul _
  change gradient (fun y => p y+ell^2*q (ell⁻¹ • y)) x = _
  rw [gradient_add _ _ x hp hc,hg]
  rfl

theorem addPressure_hessian (ell : ℝ) (hell : ell ≠ 0) (p q : Space → ℝ)
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) (x : Space)
    (hp1 : DifferentiableAt ℝ (gradient p) x)
    (hq1 : DifferentiableAt ℝ (gradient q) (ell⁻¹ • x)) :
    fderiv ℝ (gradient (addPressure ell p q)) x =
      fderiv ℝ (gradient p) x+fderiv ℝ (gradient q) (ell⁻¹ • x) := by
  have he : gradient (addPressure ell p q)=addVelocity ell (gradient p) (gradient q) :=
    funext (fun y => addPressure_gradient ell hell p q y (hp y) (hq _))
  rw [he]
  exact addVelocity_fderiv ell hell _ _ x hp1 hq1

end EulerPacketPhysicalLowBounds

namespace EulerParentPacketFrames.Parent

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketPhysicalTransform EulerLiftedGradientSpace EulerGraphPressurePotential
  EulerPacketPhysicalLowBounds EulerTransverseFrameCoordinates EulerPacketPhysicalGevrey
  EulerPacketInverseFlowGevrey
open scoped ContDiff

variable (A : Parent)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (k : ℝ) (I : ParticleInverse A)


/-- Normalized packet velocity, constructed using `κ`. -/
def normalizedPacketVelocity (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  κ • A.frame.field t (I.normalized t x)
    ((exactPacketOfResidual P B residual).velocity.pointField t
      (cylinderGraph P k m (I.normalized t x)))

/-- Normalized packet pressure, given by `(exactPacketOfResidual P B residual).graphPotential k
t ∘ I.normalized t`. -/
def normalizedPacketPressure (t : Icc (0 : ℝ) A.T) : Space → ℝ :=
  (exactPacketOfResidual P B residual).graphPotential k t ∘ I.normalized t


theorem normalizedPacketVelocity_smooth (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (A.normalizedPacketVelocity m hm J support hSupport B residual k I t) := by
  have hi := continuousInverse_contDiff (A.transverseData m hm J support hSupport)
    (fun s x => A.packetPosition (s,x)) I.normalized (fun s x => A.packetPosition_spatial s x)
    I.normalized_right I.normalized_continuous t
  exact (graphReconstruction_contDiff (A.transverseData m hm J support hSupport) P κ k
    (exactPacketOfResidual P B residual).velocity.pointField
    (exactPacketOfResidual P B residual).velocity.pointField_smooth t).comp hi


theorem normalizedPacketPressure_smooth (hk : k * κ = 1) (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (A.normalizedPacketPressure m hm J support hSupport B residual k I t) := by
  exact ((exactPacketOfResidual P B residual).graphPotential_smooth k hk t).comp
    (continuousInverse_contDiff (A.transverseData m hm J support hSupport)
      (fun s x => A.packetPosition (s,x)) I.normalized (fun s x => A.packetPosition_spatial s x)
      I.normalized_right I.normalized_continuous t)


theorem exactPacketVelocity_eq_addVelocity (u : ℝ × Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.exactPacketVelocity m hm J support hSupport B residual k I.field u (t,x) =
      addVelocity A.ell (fun y => u (t,y))
        (A.normalizedPacketVelocity m hm J support hSupport B residual k I t) x := by
  change EulerSpatialRescaling.velocity A.ell
    (fun q => A.normalizedVelocity u q+physicalVelocity κ k m A.packetFrame
      (exactPacketOfResidual P B residual).rawVelocity (A.packetInverse I.field) q) (t,x)=_
  rw [A.normalizedVelocity_add_restore]
  change u (t,x)+A.ell • physicalVelocity κ k m A.packetFrame
    (exactPacketOfResidual P B residual).rawVelocity (A.packetInverse I.field) (t,A.ell⁻¹ • x) =
      u (t,x)+A.ell • A.normalizedPacketVelocity m hm J support hSupport B residual k I t (A.ell⁻¹
          • x)
  apply congrArg (fun z => u (t,x)+A.ell • z)
  exact exact_physicalVelocity_eq (A.transverseData m hm J support hSupport)
    (exactPacketOfResidual P B residual) k A.packetFrame (A.packetInverse I.field)
    (A.packetFrame_match m hm J support hSupport) t (A.ell⁻¹ • x)


theorem exactPacketPressure_eq_addPressure (p : ℝ × Space → ℝ)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.exactPacketPressure m hm J support hSupport B residual k I.field p (t,x) =
      addPressure A.ell (fun y => p (t,y))
        (A.normalizedPacketPressure m hm J support hSupport B residual k I t) x := by
  change A.ell^2*(A.normalizedPressure p (t,A.ell⁻¹ • x) +
    physicalPressure ((exactPacketOfResidual P B residual).rawGraphPotential k) (A.packetInverse
        I.field)
      (t,A.ell⁻¹ • x)) = _
  simp only [A.normalizedPressure_apply,smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul,
    physicalPressure,inverseCoordinates,ExactLiftedPacket.rawGraphPotential,
    projIcc_of_mem A.T_pos.le t.property,normalizedPacketPressure,Function.comp_def,
    ParticleInverse.normalized,addPressure]
  field_simp [A.ell_pos.ne']


theorem exactPacketVelocity_fderiv (u : ℝ × Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space)
    (hu : DifferentiableAt ℝ (fun y => u (t, y)) x) :
    fderiv ℝ (fun y => A.exactPacketVelocity m hm J support hSupport B residual k I.field u (t,y))
        x =
      fderiv ℝ (fun y => u (t,y)) x +
      fderiv ℝ (A.normalizedPacketVelocity m hm J support hSupport B residual k I t) (A.ell⁻¹ • x)
          := by
  rw [show (fun y => A.exactPacketVelocity m hm J support hSupport B residual k I.field u (t,y)) =
    addVelocity A.ell (fun y => u (t,y))
      (A.normalizedPacketVelocity m hm J support hSupport B residual k I t) from
        funext (A.exactPacketVelocity_eq_addVelocity m hm J support hSupport B residual k I u t)]
  exact addVelocity_fderiv A.ell A.ell_pos.ne' _ _ x hu
    ((A.normalizedPacketVelocity_smooth m hm J support hSupport B residual k I t).differentiable (by
        simp) _)


theorem exactPacketPressure_hessian (hk : k * κ = 1) (p : ℝ × Space → ℝ)
    (t : Icc (0 : ℝ) A.T) (x : Space)
    (hp : Differentiable ℝ (fun y => p (t, y)))
    (hp1 : DifferentiableAt ℝ (gradient (fun y => p (t, y))) x) :
    fderiv ℝ (gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k I.field
        p (t,y))) x =
      fderiv ℝ (gradient (fun y => p (t,y))) x +
      fderiv ℝ (gradient (A.normalizedPacketPressure m hm J support hSupport B residual k I t))
          (A.ell⁻¹ • x) := by
  rw [show (fun y => A.exactPacketPressure m hm J support hSupport B residual k I.field p (t,y)) =
    addPressure A.ell (fun y => p (t,y))
      (A.normalizedPacketPressure m hm J support hSupport B residual k I t) from
        funext (A.exactPacketPressure_eq_addPressure m hm J support hSupport B residual k I p t)]
  have hq := A.normalizedPacketPressure_smooth m hm J support hSupport B residual k I hk t
  exact addPressure_hessian A.ell A.ell_pos.ne' _ _ hp
    (hq.differentiable (by simp)) x
    hp1
    ((EulerMeanSolenoidal.contDiff_gradient hq).differentiable (by simp) _)

end EulerParentPacketFrames.Parent

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransverseFrameCoordinates
  EulerAllOrderDriftCorrection EulerPacketTerminalDatum

variable (A : Parent) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ support) (α : ℝ)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period A.T_pos
    (initializedCorrectionData (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk))
  (I : ParticleInverse A)

theorem normalizedPacketVelocity_initialized (t : Icc (0 : ℝ) A.T) :
    A.normalizedPacketVelocity m hm J support hSupport Q
      (initializedApproximationResidual (A.meanData H) (A.transverseData m hm J support hSupport)
          rfl
        τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α
        (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I t =
    initializedExactPhysicalVelocity (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk Q t (I.normalized t) := rfl

theorem normalizedPacketPressure_initialized (t : Icc (0 : ℝ) A.T) :
    A.normalizedPacketPressure m hm J support hSupport Q
      (initializedApproximationResidual (A.meanData H) (A.transverseData m hm J support hSupport)
          rfl
        τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α
        (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I t =
    initializedExactPhysicalPressure (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      τ hτ hτT (A.historyOn H m hm J support hSupport τ hτ hτT) δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk Q t (I.normalized t) := rfl

end EulerParentPacketFrames.Parent
