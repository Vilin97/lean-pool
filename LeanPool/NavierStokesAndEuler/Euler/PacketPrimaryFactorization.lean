/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHistory
public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath

@[expose] public section

/-! The actual primary retains its angular profile on the entire joined
interval. This follows from uniqueness for its genuine homogeneous linear
ODE, whose coefficients are independent of the angle. -/

noncomputable section

namespace EulerPacketPrimaryFactorization

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerTransversePacketProvider EulerTransversePacketPrimary
  EulerTransverseSourceCoefficientPath EulerPacketTerminalDatum EulerPeriodicProfile
  EulerSpatialCutoffs EulerLinearDuhamel
open scoped ContDiff BoundedContinuousFunction

private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

def physicalGenerator (D : Data U) (x : Space) : C(Icc (0 : ℝ) D.T,Space →L[ℝ] Space) where
  toFun t := -(D.M.field t x)+(2/‖D.normal.field t x‖^2) •
    ((rankOne ℝ (D.normal.field t x) (D.normal.field t x)).comp (D.M.field t x))
  continuous_toFun := by
    have hM : Continuous (fun t => D.M.field t x) := by
      convert! (pointPath D.M x).continuous using 1
      funext t
      exact (pointPath_apply D.M x t).symm
    have hm : Continuous (fun t => D.normal.field t x) := by
      convert! (pointPath D.normal x).continuous using 1
      funext t
      exact (pointPath_apply D.normal x t).symm
    exact hM.neg.add ((continuous_const.div (hm.norm.pow 2)
      (fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr (HistoryData.normal_ne_zero t x)))).smul
        ((((rankOne ℝ).continuous.comp hm).clm_apply hm).clm_comp hM))

theorem physicalGenerator_apply (D : Data U) (x : Space) (t : Icc (0 : ℝ) D.T) (v : Space) :
    physicalGenerator D x t v = -D.M.field t x v+
      (2*⟪D.normal.field t x,D.M.field t x v⟫_ℝ/‖D.normal.field t x‖^2) • D.normal.field t x := by
  simp only [physicalGenerator,ContinuousMap.coe_mk,add_apply,neg_apply,smul_apply,comp_apply,
    rankOne_apply,smul_smul]
  congr 2
  ring

variable [CompleteSpace U] {D : Data U}
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

theorem vector_homogeneous_time {P : ℝ} [Fact (0 < P)] (Y : InitialData P D)
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun s => vector τ hτ hτT B Y (s,(x,θ)))
      (physicalGenerator D x t (vector τ hτ hτT B Y (t,(x,θ)))) (Icc (0 : ℝ) D.T) t := by
  have h := vector_hasDerivWithinAt τ hτ hτT B Y t x θ
  have hb : vectorDerivative τ hτ hτT B Y (t,(x,θ))+
    D.M.field t x (vector τ hτ hτT B Y (t,(x,θ)))+
    (-(2*⟪D.normal.field t x,D.M.field t x (vector τ hτ hτT B Y (t,(x,θ)))⟫_ℝ)/
      ‖D.normal.field t x‖^2) • D.normal.field t x=0 := by
    simpa only [vectorDerivative,vector,normalResidual,Data.clamp_coe] using
      field_balance τ hτ hτT B Y t (x,(θ : AddCircle P))
  have he : vectorDerivative τ hτ hτT B Y (t,(x,θ)) =
      physicalGenerator D x t (vector τ hτ hτT B Y (t,(x,θ))) := by
    rw [physicalGenerator_apply]
    have hh : vectorDerivative τ hτ hτT B Y (t,(x,θ))+
        D.M.field t x (vector τ hτ hτT B Y (t,(x,θ))) =
        (2*⟪D.normal.field t x,D.M.field t x (vector τ hτ hτT B Y (t,(x,θ)))⟫_ℝ/
          ‖D.normal.field t x‖^2) • D.normal.field t x :=
      sub_eq_zero.mp (by simpa only [neg_div,neg_smul,sub_eq_add_neg] using hb)
    exact (eq_sub_of_add_eq hh).trans (by abel)
  rwa [he] at h

private theorem homogeneous_unique (T : ℝ) (hT : 0 ≤ T)
    (G : C(Icc (0 : ℝ) T,Space →L[ℝ] Space)) (f g : ℝ → Space)
    (hf : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt f (G t (f t)) (Icc (0 : ℝ) T) t)
    (hg : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt g (G t (g t)) (Icc (0 : ℝ) T) t)
    (h0 : f 0=g 0) (t : Icc (0 : ℝ) T) : f t=g t := by
  let E := constructedEvolution T hT G
  have he (a : ℝ → Space) (ha : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt a (G t (a t)) (Icc (0 : ℝ) T) t) :
      a t=E.solution 0 (a 0) t :=
    E.solution_unique 0 (a 0) a (fun s => by simpa only [ContinuousMap.zero_apply,add_zero] using
      ha s) rfl t
  rw [he f hf,he g hg,h0]

theorem angular_proportional (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) D.T)
    (x : Space) (θ φ : ℝ) :
    profile δ φ • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ)) =
      profile δ θ • vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,φ)) := by
  apply homogeneous_unique D.T D.T_pos.le (physicalGenerator D x)
    (fun s => profile δ φ • vector τ hτ hτT B (initialData D δ hδ ξ hs) (s,(x,θ)))
    (fun s => profile δ θ • vector τ hτ hτT B (initialData D δ hδ ξ hs) (s,(x,φ))) _ _ _ t
  · intro s
    rw [map_smul]
    convert! (vector_homogeneous_time τ hτ hτT B
      (initialData D δ hδ ξ hs) s x θ).const_smul (profile δ φ) using 1
  · intro s
    rw [map_smul]
    convert! (vector_homogeneous_time τ hτ hτT B
      (initialData D δ hδ ξ hs) s x φ).const_smul (profile δ θ) using 1
  · have hθ := vector_compact_wave_history τ hτ hτT B δ hδ ξ hs ⟨0,le_rfl,hτ.le⟩ x θ
    have hφ := vector_compact_wave_history τ hτ hτT B δ hδ ξ hs ⟨0,le_rfl,hτ.le⟩ x φ
    dsimp only at hθ hφ
    rw [hθ,hφ,smul_smul,smul_smul]
    congr 1
    ring

def referenceValue (δ : ℝ) : ℝ := profile δ (Real.pi/2)

theorem referenceValue_pos (δ : ℝ) (hδ : 0 < δ) : 0 < referenceValue δ := by
  simp only [referenceValue,profile,Real.sin_pi_div_two,Real.cos_pi_div_two,sub_zero]
  exact Real.arctan_pos.mpr (div_pos zero_lt_one (by linarith))

/-- The envelope is retained in this actual velocity. On the core it agrees
with the unmultiplied history, and its definition is valid for every time. -/
def envelopedVelocity (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : ℝ) (x : Space) : Space :=
  (referenceValue δ)⁻¹ •
    vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,Real.pi/2))

theorem vector_factorization (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) D.T)
    (x : Space) (θ : ℝ) :
    vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ)) =
      profile δ θ • envelopedVelocity τ hτ hτT B δ hδ ξ hs t x := by
  have h := congrArg (fun v : Space => (referenceValue δ)⁻¹ • v)
    (angular_proportional τ hτ hτT B δ hδ ξ hs t x θ (Real.pi/2))
  change (referenceValue δ)⁻¹ • (referenceValue δ • _) = _ at h
  rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (referenceValue_pos δ hδ)),one_smul] at h
  simpa only [envelopedVelocity,smul_smul,mul_comm] using h

theorem envelopedVelocity_history (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) τ) (x : Space) :
    envelopedVelocity τ hτ hτT B δ hδ ξ hs t x =
      innerCutoff x • B.coefficients.labelVelocity x ξ t := by
  rw [envelopedVelocity,vector_compact_wave_history,smul_smul]
  change ((referenceValue δ)⁻¹*(innerCutoff x*referenceValue δ)) • _ = _
  have he : (referenceValue δ)⁻¹*(innerCutoff x*referenceValue δ)=innerCutoff x := by
    field_simp [ne_of_gt (referenceValue_pos δ hδ)]
  rw [he]

theorem envelopedVelocity_homogeneous_time (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => envelopedVelocity τ hτ hτT B δ hδ ξ hs s x)
      (physicalGenerator D x t (envelopedVelocity τ hτ hτT B δ hδ ξ hs t x))
      (Icc (0 : ℝ) D.T) t := by
  simp only [envelopedVelocity,map_smul]
  convert! (vector_homogeneous_time τ hτ hτT B
    (initialData D δ hδ ξ hs) t x (Real.pi/2)).const_smul (referenceValue δ)⁻¹ using 1

/-- The recovered velocity is independent of the narrow angular profile.
In particular its construction does not introduce a dependence on δ into
the geometric amplitude or the homogeneous propagation estimate. -/
theorem envelopedVelocity_independent_profile (δ δ' : ℝ) (hδ : 0 < δ) (hδ' : 0 < δ')
    (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    envelopedVelocity τ hτ hτT B δ hδ ξ hs t x =
      envelopedVelocity τ hτ hτT B δ' hδ' ξ hs t x := by
  apply homogeneous_unique D.T D.T_pos.le (physicalGenerator D x)
    (fun s => envelopedVelocity τ hτ hτT B δ hδ ξ hs s x)
    (fun s => envelopedVelocity τ hτ hτT B δ' hδ' ξ hs s x)
    (fun s => envelopedVelocity_homogeneous_time τ hτ hτT B δ hδ ξ hs s x)
    (fun s => envelopedVelocity_homogeneous_time τ hτ hτT B δ' hδ' ξ hs s x) _ t
  exact (envelopedVelocity_history τ hτ hτT B δ hδ ξ hs ⟨0,le_rfl,hτ.le⟩ x).trans
    (envelopedVelocity_history τ hτ hτT B δ' hδ' ξ hs ⟨0,le_rfl,hτ.le⟩ x).symm

def canonicalVelocity (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)
    (t : ℝ) (x : Space) : Space :=
  envelopedVelocity τ hτ hτT B 1 zero_lt_one ξ hs t x

theorem vector_factorization_canonical (δ : ℝ) (hδ : 0 < δ) (ξ : U)
    (hs : tsupport innerCutoff ⊆ D.support) (t : Icc (0 : ℝ) D.T)
    (x : Space) (θ : ℝ) :
    vector τ hτ hτT B (initialData D δ hδ ξ hs) (t,(x,θ)) =
      profile δ θ • canonicalVelocity τ hτ hτT B ξ hs t x := by
  rw [vector_factorization,envelopedVelocity_independent_profile τ hτ hτT B δ 1 hδ zero_lt_one]
  rfl

theorem canonicalVelocity_history (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)
    (t : Icc (0 : ℝ) τ) (x : Space) :
    canonicalVelocity τ hτ hτT B ξ hs t x = innerCutoff x • B.coefficients.labelVelocity x ξ t :=
  envelopedVelocity_history τ hτ hτT B 1 zero_lt_one ξ hs t x

theorem canonicalVelocity_homogeneous_time (ξ : U) (hs : tsupport innerCutoff ⊆ D.support)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun s => canonicalVelocity τ hτ hτT B ξ hs s x)
      (physicalGenerator D x t (canonicalVelocity τ hτ hτT B ξ hs t x))
      (Icc (0 : ℝ) D.T) t :=
  envelopedVelocity_homogeneous_time τ hτ hτT B 1 zero_lt_one ξ hs t x

end EulerPacketPrimaryFactorization
