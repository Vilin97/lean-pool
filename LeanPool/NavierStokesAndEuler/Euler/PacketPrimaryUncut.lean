/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePropagator
public import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointClassical
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryFactorization
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryDynamics
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryScaling
import LeanPool.NavierStokesAndEuler.Euler.TransverseNormalResidual
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory

/-! The uncut primary is the genuine homogeneous physical evolution of
the actual stationary history's initial coordinate.  Its all-time relation
to the compactly supported packet is proved by ODE uniqueness. -/

@[expose] public section


noncomputable section

namespace EulerPacketPrimaryFactorization

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerTransversePacketPrimary EulerPacketTerminalDatum
  EulerPacketSourcePropagator EulerLinearDuhamel EulerVolterraConvolution
  EulerTransverseGramInverse EulerTransverseNormalResidual EulerFixedEndpointClassical
      EulerTimeIntervalRestriction
  EulerTransverseSourceCoefficientPath EulerPacketPrimaryShear EulerPeriodicProfile
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

private theorem physical_homogeneous_unique (T : ℝ) (hT : 0 ≤ T)
    (G : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (f g : ℝ → Space)
    (hf : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt f (G t (f t)) (Icc (0 : ℝ) T) t)
    (hg : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt g (G t (g t)) (Icc (0 : ℝ) T) t)
    (h0 : f 0=g 0) (t : Icc (0 : ℝ) T) : f t=g t := by
  let E := constructedEvolution T hT G
  have he (a : ℝ → Space) (ha : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt a (G t (a t)) (Icc (0 : ℝ) T) t) : a t=E.solution 0 (a 0) t :=
    E.solution_unique 0 (a 0) a
      (fun s => by simpa only [ContinuousMap.zero_apply,add_zero] using ha s) rfl t
  rw [he f hf,he g hg,h0]

theorem historyVelocity_homogeneous {D : Data U} (B : HistoryData D)
    (ξ : U) (x : Space) (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le (B.coefficients.labelVelocity x ξ))
      (physicalGenerator D x t (B.coefficients.labelVelocity x ξ t))
      (Icc (0 : ℝ) D.T) t := by
  let C := B.coefficients
  let a := C.labelCoordinate x ξ t
  let b := acceleration D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
    (C.labelHessian x) C.lower C.lower_pos (C.labelFrame_lower x) (C.labelFrame_derivative x)
    C.potential C.potential_nonneg (C.labelHessian_upper x) C.small ξ t
  have hda := velocity_hasDerivWithinAt D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
    (C.labelHessian x) C.lower C.lower_pos (C.labelFrame_lower x) (C.labelFrame_derivative x)
    C.potential C.potential_nonneg (C.labelHessian_upper x) C.small
    (C.labelFrameSecond x) C.time_pos (C.labelFrame_second_derivative x) (C.labelFrame_equation x)
        ξ t
  have hd := (C.labelFrame_derivative x t).clm_apply hda
  have hnormal : D.normal.field t x ≠ 0 := HistoryData.normal_ne_zero t x
  have he : gram (D.frame.field t x) b =
      (D.frame.field t x).adjoint (0-(2 : ℝ) • D.frameDerivative.field t x a) := by
    have hp := projected_equation D.T D.T_pos.le
      (C.labelFrame x) (C.labelFrameDerivative x) (C.labelHessian x) C.lower C.lower_pos
      (C.labelFrame_lower x) (C.labelFrame_derivative x) C.potential C.potential_nonneg
      (C.labelHessian_upper x) C.small ξ t
    change gram (D.frame.field t x) b = (D.frame.field t x).adjoint ((-2 : ℝ) •
        D.frameDerivative.field t x a) at hp
    simpa only [zero_sub,neg_smul] using hp
  have hb := physical_velocity_balance (D.frame.field t x) (D.frameDerivative.field t x)
    (D.M.field t x) (D.normal.field t x) hnormal (D.frame_tangent t x) (D.frame_range t x)
    (D.frame_strain t x) a b 0 he
  have hd' : HasDerivWithinAt (extendPath D.T D.T_pos.le (C.labelVelocity x ξ))
      (D.frameDerivative.field t x a+D.frame.field t x b) (Icc (0 : ℝ) D.T) t := by
    convert! hd using 1
    simp only [extendPath,projIcc_of_mem D.T_pos.le t.property]
    rfl
  apply hd'.congr_deriv
  rw [physicalGenerator_apply]
  change D.frameDerivative.field t x a+D.frame.field t x b =
    -D.M.field t x (D.frame.field t x a) +
      (2*⟪D.normal.field t x,D.M.field t x (D.frame.field t x a)⟫_ℝ/
        ‖D.normal.field t x‖^2) • D.normal.field t x
  simp only [inner_zero_right,zero_sub,neg_div,neg_smul] at hb
  linear_combination (norm := module) hb

variable {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (ξ : U)

/-- Uncut velocity, given by `physical D ⟨0,le_rfl,D.T_pos.le⟩ x (B.coefficients.labelCoordinate
x ξ ⟨0,le_rfl,hτ.le⟩) t`. -/
def uncutVelocity (t : ℝ) (x : Space) : Space :=
  physical D ⟨0,le_rfl,D.T_pos.le⟩ x
    (B.coefficients.labelCoordinate x ξ ⟨0,le_rfl,hτ.le⟩) t

theorem uncutVelocity_initial (x : Space) :
    uncutVelocity τ hτ hτT B ξ 0 x =
      B.coefficients.labelVelocity x ξ ⟨0,le_rfl,hτ.le⟩ := by
  change physical D ⟨0,le_rfl,D.T_pos.le⟩ x _ ((⟨0,le_rfl,D.T_pos.le⟩ : Icc (0 : ℝ) D.T) : ℝ) = _
  rw [physical_at,propagator_self]
  rfl

theorem uncutVelocity_equation (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => uncutVelocity τ hτ hτT B ξ s x)
      (physicalGenerator D x t (uncutVelocity τ hτ hτT B ξ t x)) (Icc (0 : ℝ) D.T) t := by
  rw [physicalGenerator_apply]
  exact physical_hasDerivWithinAt D ⟨0,le_rfl,D.T_pos.le⟩ t x _

theorem uncutVelocity_tangent (t : Icc (0 : ℝ) D.T) (x : Space) :
    ⟪D.normal.field t x,uncutVelocity τ hτ hτT B ξ t x⟫_ℝ = 0 :=
  physical_tangent D ⟨0,le_rfl,D.T_pos.le⟩ t x _

theorem uncutVelocity_history (t : Icc (0 : ℝ) τ) (x : Space) :
    uncutVelocity τ hτ hτT B ξ t x = B.coefficients.labelVelocity x ξ t := by
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) D.T := fun _ hs => ⟨hs.1,hs.2.trans hτT.le⟩
  have hu (s : Icc (0 : ℝ) τ) :
      HasDerivWithinAt (fun r => uncutVelocity τ hτ hτT B ξ r x)
        (physicalGenerator (D.initial τ hτ hτT.le) x s (uncutVelocity τ hτ hτT B ξ s x))
        (Icc (0 : ℝ) τ) s :=
    (uncutVelocity_equation τ hτ hτT B ξ (initialInclusion D.T τ hτT.le s) x).mono hsub
  have hh (s : Icc (0 : ℝ) τ) :
      HasDerivWithinAt (extendPath τ hτ.le (B.coefficients.labelVelocity x ξ))
        (physicalGenerator (D.initial τ hτ hτT.le) x s
          (extendPath τ hτ.le (B.coefficients.labelVelocity x ξ) s)) (Icc (0 : ℝ) τ) s := by
    apply (historyVelocity_homogeneous B ξ x s).congr_deriv
    dsimp only [extendPath]
    rw [projIcc_of_mem hτ.le s.property]
    rfl
  have h0 : uncutVelocity τ hτ hτT B ξ 0 x =
      extendPath τ hτ.le (B.coefficients.labelVelocity x ξ) 0 := by
    rw [uncutVelocity_initial]
    dsimp only [extendPath]
    rw [projIcc_of_mem hτ.le (show (0 : ℝ) ∈ Icc 0 τ from ⟨le_rfl,hτ.le⟩)]
    rfl
  have he := physical_homogeneous_unique τ hτ.le (physicalGenerator (D.initial τ hτ hτT.le) x)
    (fun s => uncutVelocity τ hτ hτT B ξ s x)
    (extendPath τ hτ.le (B.coefficients.labelVelocity x ξ)) hu hh h0 t
  calc
    _ = extendPath τ hτ.le (B.coefficients.labelVelocity x ξ) t := he
    _ = _ := by
      dsimp only [extendPath]
      rw [projIcc_of_mem hτ.le t.property]
      rfl

theorem canonicalVelocity_eq_cutoff_uncut (hs : tsupport innerCutoff ⊆ D.support)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    canonicalVelocity τ hτ hτT B ξ hs t x = innerCutoff x • uncutVelocity τ hτ hτT B ξ t x := by
  apply physical_homogeneous_unique D.T D.T_pos.le (physicalGenerator D x)
    (fun s => canonicalVelocity τ hτ hτT B ξ hs s x)
    (fun s => innerCutoff x • uncutVelocity τ hτ hτT B ξ s x)
    (fun s => canonicalVelocity_homogeneous_time τ hτ hτT B ξ hs s x) _ _ t
  · intro s
    rw [map_smul]
    exact (uncutVelocity_equation τ hτ hτT B ξ s x).const_smul (innerCutoff x)
  · rw [uncutVelocity_initial]
    exact canonicalVelocity_history τ hτ hτT B ξ hs ⟨0,le_rfl,hτ.le⟩ x

theorem uncutVelocity_ne_zero (hξ : ξ ≠ 0) (t : Icc (0 : ℝ) D.T) (x : Space) :
    uncutVelocity τ hτ hτT B ξ t x ≠ 0 := by
  intro ht
  obtain ⟨s,hs⟩ := B.coefficients.labelVelocity_exists_ne_zero x ξ hξ
  have hz := (constructedEvolution D.T D.T_pos.le (physicalGenerator D x)).homogeneous_zero_at
    (fun r => uncutVelocity τ hτ hτT B ξ r x)
    (fun r => uncutVelocity_equation τ hτ hτT B ξ r x) t
    (initialInclusion D.T τ hτT.le s) ht
  change uncutVelocity τ hτ hτT B ξ s x = 0 at hz
  erw [uncutVelocity_history] at hz
  exact hs hz

theorem vector_uncut_factorization (δ : ℝ) (hδ : 0 < δ) (a : ℝ)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B (initialData D δ hδ (a • ξ) hs) (t,(x,θ)) =
      (a*innerCutoff x*profile δ θ) • uncutVelocity τ hτ hτT B ξ t x := by
  rw [vector_terminal_smul,vector_factorization_canonical,canonicalVelocity_eq_cutoff_uncut]
  simp only [smul_smul]
  congr 1
  ring

end EulerPacketPrimaryFactorization
