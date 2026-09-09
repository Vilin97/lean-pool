/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseSmoothState
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketForwardInput
import LeanPool.NavierStokesAndEuler.Euler.BaseEulerSign

/-! Concrete support, transverse coordinate and short-time source
budgets for the first packet over the compact base Euler solution. -/

@[expose] public section


noncomputable section

namespace EulerPacketSupport

open Set EulerSmoothLimit EulerSpatialCutoffs

/-- Support, given by `tsupport innerCutoff`. -/
def support : Set Space := tsupport innerCutoff

theorem compact : IsCompact support := innerCutoff_compactSupport

theorem subset_halfBall : support ⊆ Metric.ball 0 (1/2 : ℝ) := innerCutoff_support

theorem symmetric (x : Space) : -x ∈ support ↔ x ∈ support := by
  have hf : innerCutoff ∘ Homeomorph.neg Space=innerCutoff := by
    funext y
    exact innerCutoff_even y
  calc
    -x ∈ support ↔ x ∈ tsupport (innerCutoff ∘ Homeomorph.neg Space) := by
      rw [tsupport_comp_eq_preimage]
      rfl
    _ ↔ x ∈ support := by rw [hf]; rfl

theorem norm_lt (x : Space) (hx : x ∈ support) : ‖x‖ < (1/2 : ℝ) := by
  simpa only [Metric.mem_ball,dist_zero_right] using subset_halfBall hx

end EulerPacketSupport

namespace EulerBaseDatum

open Set InnerProductSpace EulerSmoothLimit EulerParentPacketFrames
  EulerTransverseFrameCoordinates EulerBaseEulerGuards EulerPacketSupport

/-- First normal, given by `EuclideanSpace.single 0 1`. -/
def firstNormal : Space := EuclideanSpace.single 0 1

theorem firstNormal_unit : ‖firstNormal‖=1 := by simp [firstNormal]

/-- First plane: an abbreviation for `referencePlane firstNormal`. -/
abbrev FirstPlane := referencePlane firstNormal

/-- First frame, given by `LinearIsometryEquiv.refl ℝ _`. -/
def firstFrame : FirstPlane ≃ₗᵢ[ℝ] referencePlane firstNormal := LinearIsometryEquiv.refl ℝ _

/-- First coordinate as an element of `FirstPlane`. -/
def firstCoordinate : FirstPlane := ⟨EuclideanSpace.single 1 1,by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [firstNormal,EuclideanSpace.inner_single_left]⟩

theorem firstCoordinate_map : (firstFrame firstCoordinate : Space)=EuclideanSpace.single 1 1 := rfl

theorem firstCoordinate_norm : ‖firstCoordinate‖=1 := by
  change ‖(EuclideanSpace.single 1 1 : Space)‖=1
  simp

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

/-- Packet base parent, given by `(initialParent β hβ ell hell hell1).restrictTime T hT hTB`. -/
def packetBaseParent : Parent :=
  (initialParent β hβ ell hell hell1).restrictTime T hT hTB

/-- Packet base state, given by `(initialState β hβ ell hell hell1).restrictTime T hT hTB`. -/
def packetBaseState : SmoothState (packetBaseParent β hβ ell hell hell1 T hT hTB) :=
  (initialState β hβ ell hell hell1).restrictTime T hT hTB

/-- Packet base low bounds, given by `(initialLowBounds β hβ ell hell hell1).restrictTime T hT
hTB`. -/
def packetBaseLowBounds : LowBounds (packetBaseParent β hβ ell hell hell1 T hT hTB) :=
  (initialLowBounds β hβ ell hell hell1).restrictTime T hT hTB

theorem packetBase_label_constant :
    (packetBaseState β hβ ell hell hell1 T hT hTB).labels.K=solutionLabelConstant := rfl

theorem packetBase_boundary_zero :
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB).L=0 := rfl

include hTB in
theorem packetBase_short : initialCoefficientCost*T ≤ 1/2 :=
  ((mul_le_mul_of_nonneg_left hTB initialCoefficientCost_nonneg).trans initialTime_small.1).trans
    (by norm_num)

include hTB in
theorem packetBase_sign_short :
    EulerPacketFirstPressureSign.firstSignRate initialCoefficientCost initialCoefficientCost*T ≤
        1/2 := by
  have hnonneg : 0 ≤ EulerPacketFirstPressureSign.firstSignRate initialCoefficientCost
      initialCoefficientCost := by
    unfold EulerPacketFirstPressureSign.firstSignRate
    positivity [initialCoefficientCost_nonneg]
  exact ((mul_le_mul_of_nonneg_left hTB hnonneg).trans initialTime_small.2).trans (by norm_num)

theorem packetBase_strain_bound (t : Icc (0 : ℝ) T) (x : Space) :
    ‖(packetBaseParent β hβ ell hell hell1 T hT hTB).strain.field t x‖ ≤ initialCoefficientCost :=
        by
  change ‖((initialParent β hβ ell hell hell1).restrictTime T hT hTB).strain.field t x‖ ≤ _
  erw [Parent.restrictTime_strain]
  exact initial_strain_bound β hβ ell hell hell1 _ x

theorem packetBase_curvature_bound (t : Icc (0 : ℝ) T) (x : Space) :
    ‖(packetBaseParent β hβ ell hell hell1 T hT hTB).curvature.field t x‖ ≤ initialCoefficientCost
        := by
  change ‖((initialParent β hβ ell hell hell1).restrictTime T hT hTB).curvature.field t x‖ ≤ _
  erw [Parent.restrictTime_curvature]
  exact initial_curvature_bound β hβ ell hell hell1 _ x

theorem packetBase_initialStrain (x : Space) (hx : x ∈ support) :
    (packetBaseParent β hβ ell hell hell1 T hT hTB).initialStrain.field x=linear β := by
  erw [packetBaseParent,Parent.restrictTime_initialStrain]
  apply initialStrain_plateau β hβ ell hell hell1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hell]
  have hb := mul_le_mul_of_nonneg_right hell1 (norm_nonneg x)
  have hx' := norm_lt x hx
  nlinarith only [hb,hx']

/-- First packet inputs used in base packet setup. -/
def firstPacketInputs :
    ForwardInputs
      ((packetBaseParent β hβ ell hell hell1 T hT hTB).meanData
        (packetBaseLowBounds β hβ ell hell hell1 T hT hTB))
      ((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
        firstNormal firstNormal_unit firstFrame support compact) :=
  (packetBaseState β hβ ell hell hell1 T hT hTB).labels.forwardInputs
    (packetBaseLowBounds β hβ ell hell hell1 T hT hTB)
    firstNormal firstNormal_unit firstFrame support compact
    initialCoefficientCost initialCoefficientCost_nonneg
    (fun t x _ => packetBase_strain_bound β hβ ell hell hell1 T hT hTB t x)
    (Metric.ball 0 (1/2 : ℝ)) Metric.isOpen_ball.measurableSet Metric.isOpen_ball subset_halfBall
    (fun x hx => le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hx))
    (packetBase_short T hTB) T⁻¹ (hTB.trans initialTime_le_one) le_rfl

theorem firstPacketInputs_growth :
    (firstPacketInputs β hβ ell hell hell1 T hT hTB).linear.g=1 := rfl

theorem firstPacket_pressure_numerator (t : Icc (0 : ℝ) T)
    (x : Space) (hx : x ∈ support) :
    1/2 ≤ ⟪((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
      firstNormal firstNormal_unit firstFrame support compact).normal.field t x,
      (packetBaseParent β hβ ell hell hell1 T hT hTB).strain.field t x
        (EulerPacketForwardFactorization.uncutVelocity
          ((packetBaseParent β hβ ell hell hell1 T hT hTB).transverseData
            firstNormal firstNormal_unit firstFrame support compact) firstCoordinate t x)⟫_ℝ := by
  apply source_numerator_pos (packetBaseState β hβ ell hell hell1 T hT hTB).labels
    firstNormal firstNormal_unit firstFrame support compact firstCoordinate firstCoordinate_norm x
  · rw [packetBase_initialStrain β hβ ell hell hell1 T hT hTB x hx,firstCoordinate_map,linear_q]
    simp [firstNormal,EuclideanSpace.inner_single_left,PiLp.add_apply,PiLp.smul_apply]
  · exact packetBase_short T hTB
  · exact packetBase_sign_short T hTB

end EulerBaseDatum
