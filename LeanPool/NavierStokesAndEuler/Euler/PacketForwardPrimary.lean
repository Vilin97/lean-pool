/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJets
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketInitialRepresentative

@[expose] public section

/-!
The actual compact-wave primary starting at time zero.  It is the genuine
homogeneous forward evolution, has the prescribed initial field, and supplies
the literal homogeneous equation and all primary regularity/parity inputs.
-/

noncomputable section

namespace EulerPacketForwardPrimary

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketCylinderField EulerPacketProfileRecursion EulerTransversePacketProvider
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (Y : InitialData P D)

abbrev forcing : Forcing P D (0 : VectorField) := homogeneousForcing D
abbrev vector : VectorField := (forcing D).vector Y
abbrev scalar : ScalarField := (forcing D).scalar Y
abbrev derivative : VectorField := (forcing D).vectorDerivative Y

omit [CompleteSpace U] in
theorem forcing_path_zero : (forcing (P := P) D).path = 0 := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  rfl

def profile (O : Operators) : Profile := homogeneousPrimary D Y O

def regularity (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P) :
    ProfileRegularity P D.T D.T_pos.le D.support (profile D Y O) :=
  homogeneousPrimaryRegularity D Y O hcorrector

theorem equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) D.T) (vector D Y) (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ))) (pressureJet (scalar D Y) (t,(x,θ))) = 0 :=
  (forcing D).jet_equation Y t x θ

theorem tangent (t : ℝ) (x : Space) (θ : ℝ) :
    inner ℝ (D.normalField (t,(x,θ))) (vector D Y (t,(x,θ))) = 0 :=
  (forcing D).vector_tangent Y t x θ

theorem mean_zero (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, vector D Y (t,(x,θ))) = 0 :=
  (forcing D).vector_mean_zero Y t x

theorem pressure_smooth (t : ℝ) : ContDiff ℝ ∞ (fun y : Space × ℝ => scalar D Y (t,y)) :=
  (forcing D).scalar_spatial_smooth Y t

theorem parity (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U)) :
    ProfileParity D.T (profile D Y O) :=
  homogeneousPrimaryParity D Y O hcorrector hSym hF hM hY

end EulerPacketForwardPrimary

namespace EulerPacketTerminalDatum

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketCylinderField EulerPacketProfileRecursion EulerTransversePacketProvider
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
  EulerSpatialCutoffs EulerPeriodicProfile EulerCylinderSmoothOrbit EulerMetricTransport
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)

def forwardPrimary (O : Operators) : Profile :=
  EulerPacketForwardPrimary.profile D (initialData D δ hδ ξ hs) O

def forwardPrimaryRegularity (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector
  period) :
    ProfileRegularity period D.T D.T_pos.le D.support (forwardPrimary D δ hδ ξ hs O) :=
  EulerPacketForwardPrimary.regularity D (initialData D δ hδ ξ hs) O hcorrector

theorem forwardPrimary_equation (O : Operators) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) D.T) (forwardPrimary D δ hδ ξ hs O).high (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ)))
        (pressureJet (forwardPrimary D δ hδ ξ hs O).highPressure (t,(x,θ))) = 0 :=
  EulerPacketForwardPrimary.equation D (initialData D δ hδ ξ hs) t x θ

theorem forwardPrimary_tangent (O : Operators) (t : ℝ) (x : Space) (θ : ℝ) :
    inner ℝ (D.normalField (t,(x,θ))) ((forwardPrimary D δ hδ ξ hs O).high (t,(x,θ))) = 0 :=
  EulerPacketForwardPrimary.tangent D (initialData D δ hδ ξ hs) t x θ

theorem forwardPrimary_mean_zero (O : Operators) (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..period, (forwardPrimary D δ hδ ξ hs O).high (t,(x,θ))) = 0 :=
  EulerPacketForwardPrimary.mean_zero D (initialData D δ hδ ξ hs) t x

theorem forwardPrimary_parity (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector
  period)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x) :
    ProfileParity D.T (forwardPrimary D δ hδ ξ hs O) :=
  EulerPacketForwardPrimary.parity D (initialData D δ hδ ξ hs) O hcorrector hSym hF hM
    (terminal_reflection δ hδ ξ)

theorem forwardPrimary_initial (O : Operators) (x : Space) (θ : ℝ) :
    (forwardPrimary D δ hδ ξ hs O).high (0,(x,θ)) =
      (innerCutoff x*profile δ θ) • D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ := by
  change (EulerPacketForwardPrimary.forcing D).vector (initialData D δ hδ ξ hs) (0,(x,θ)) = _
  rw [(EulerPacketForwardPrimary.forcing D).vector_initial_of_representative
    (initialData D δ hδ ξ hs) (field δ ξ)
    (smoothField_continuous period _ (field_smooth δ hδ ξ)) (terminal_ae δ hδ ξ),
    field_coe,map_smul]

theorem forwardPrimary_initial_angular (O : Operators) (x : Space) :
    HasDerivAt (fun θ : ℝ => (forwardPrimary D δ hδ ξ hs O).high (0,(x,θ)))
      ((innerCutoff x*δ⁻¹) • D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ) 0 := by
  have he : (fun θ : ℝ => (forwardPrimary D δ hδ ξ hs O).high (0,(x,θ))) =
      fun θ => (innerCutoff x*profile δ θ) • D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ :=
    funext (forwardPrimary_initial D δ hδ ξ hs O x)
  rw [he]
  have hp := (profile_hasDerivAt δ hδ 0).differentiableAt.hasDerivAt
  rw [profile_deriv_zero δ hδ] at hp
  exact (hp.const_mul (innerCutoff x)).smul_const (D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ)

theorem forwardPrimary_initial_angular_norm (O : Operators) :
    ‖deriv (fun θ : ℝ => (forwardPrimary D δ hδ ξ hs O).high (0,(0,θ))) 0‖ =
      δ⁻¹*‖D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ 0 ξ‖ := by
  rw [(forwardPrimary_initial_angular D δ hδ ξ hs O 0).deriv,innerCutoff_zero,one_mul,
    norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]

end EulerPacketTerminalDatum
