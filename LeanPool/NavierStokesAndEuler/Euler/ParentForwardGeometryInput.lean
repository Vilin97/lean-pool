/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryControlledGrowth
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketForwardInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentPhysicalBudgets

/-! The first normal stage supplies its forward packet budget from the
actual amplification geometry. The large parent shear needs no short-time
assumption of the form CM*T≤1/2. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceGeometry.ForwardGuards

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketSourcePropagator

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (G : ForwardGuards P) (hball : (1 / 2 : ℝ) ≤ G.radius)

/-- Source growth profile, given by `(G.halfBall_controlledGrowth hball).choose`. -/
def sourceGrowthProfile : C(Icc (0 : ℝ) D.T,ℝ) := (G.halfBall_controlledGrowth hball).choose

theorem sourceGrowthProfile_positive (t : Icc (0 : ℝ) D.T) : 0 < G.sourceGrowthProfile hball t :=
  (G.halfBall_controlledGrowth hball).choose_spec.1 t

theorem sourceGrowthProfile_initial : G.sourceGrowthProfile hball ⟨0,le_rfl,D.T_pos.le⟩=1 :=
  (G.halfBall_controlledGrowth hball).choose_spec.2.1

theorem sourceGrowthProfile_propagator :
    PhysicalGrowth D EulerPacketParentPhysicalBudgets.halfBall (G.sourceGrowthProfile hball)
      (560*P.horizon^10/P.epsilon) :=
  (G.halfBall_controlledGrowth hball).choose_spec.2.2.1

theorem sourceGrowthProfile_amplitude (t : Icc (0 : ℝ) D.T) :
    G.primaryAmplitude hball*G.sourceGrowthProfile hball t ≤ 8*Real.exp 6*G.δ*G.hchild :=
  (G.halfBall_controlledGrowth hball).choose_spec.2.2.2 t

theorem primaryAmplitude_bound : G.primaryAmplitude hball ≤ 8*Real.exp 6*G.δ*G.hchild := by
  have h := G.sourceGrowthProfile_amplitude hball ⟨0,le_rfl,D.T_pos.le⟩
  simpa only [G.sourceGrowthProfile_initial hball,mul_one] using h

omit [CompleteSpace U] in
include G in
theorem growth_constant_pos : 0 < 560*P.horizon^10/P.epsilon := by
  exact div_pos (mul_pos (by
      norm_num) (pow_pos (zero_lt_one.trans_le G.horizon_lower) 10)) G.epsilon_pos

end EulerPacketSourceGeometry.ForwardGuards

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketSourceGeometry
  EulerPacketParentLabelBounds

variable {A : Parent} (L : LabelData A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (P : ParentFrame (A.transverseData m hm J support hSupport) 0)
  (G : ForwardGuards P) (hball : (1 / 2 : ℝ) ≤ G.radius)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))

/-- Geometry forward raw, constructed using `EulerPacketParentPhysicalBudgets.forwardBudget`. -/
def geometryForwardRaw :
    EulerTransversePacketForward.Budget (A.transverseData m hm J support hSupport) (Fin 4) 6 :=
  EulerPacketParentPhysicalBudgets.forwardBudget (A.transverseData m hm J support hSupport) 6
    L.displacement L.velocity A.ell L.K (560*P.horizon^10/P.epsilon)
    A.ell_pos.le A.ell_le_one (zero_le_one.trans L.K_one) G.growth_constant_pos.le
    L.displacement_bound L.velocity_bound L.frame_match L.first_match A.frame_det
    (G.sourceGrowthProfile hball) (G.sourceGrowthProfile_positive hball)
        (G.sourceGrowthProfile_initial hball)
    Ω hΩ hΩo hsub hΩball (G.sourceGrowthProfile_propagator hball)

/-- Geometry forward inputs as an element of `ForwardInputs (A.meanData H) (A.transverseData m
hm J support hSupport)`. -/
def geometryForwardInputs (Ti : ℝ) (hT1 : A.T ≤ 1) (hTi : A.T⁻¹ ≤ Ti) :
    ForwardInputs (A.meanData H) (A.transverseData m hm J support hSupport) := by
  let V := L.geometryForwardRaw m hm J support hSupport P G hball Ω hΩ hΩo hsub hΩball
  let N := L.normalBudget m hm J support hSupport 6
  let M := L.meanBudget H 6 Ti hT1 hTi
  let Rn := EulerPacketParentNormalBudget.radius (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K)
  let Rm := EulerPacketParentMeanBudget.radius 6 A.T Ti (coefficientRadius L.K)
    (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K) H.L
  let Rc := max V.R (max Rn Rm)
  exact {
    linear := V.enlargeRadius Rc (le_max_left _ _)
    normal := N.enlargeRadius Rc ((le_max_left Rn Rm).trans (le_max_right _ _))
    mean := M.enlargeRadius Rc ((le_max_right Rn Rm).trans (le_max_right _ _)) }

theorem geometryForwardInputs_growth (Ti : ℝ) (hT1 : A.T ≤ 1) (hTi : A.T⁻¹ ≤ Ti) :
    (L.geometryForwardInputs H m hm J support hSupport P G hball Ω hΩ hΩo hsub hΩball
      Ti hT1 hTi).linear.g=G.sourceGrowthProfile hball := rfl

end EulerParentPacketFrames.LabelData
