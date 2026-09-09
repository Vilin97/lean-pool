/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerParent
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
public import LeanPool.NavierStokesAndEuler.Euler.LpParameterIntegral
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets

@[expose] public section

/-! Actual ordinary L² displacement, material velocity and acceleration
for the base flow. The displacement estimate integrates the real spatial
jets of the flow, and the other two estimates use volume preservation. -/

noncomputable section

namespace EulerBaseEulerParent

open Set MeasureTheory Filter EulerSmoothLimit EulerSmoothBanachFlow
  EulerSmoothFlowGevrey EulerLpTranslation EulerGevrey EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction Interval

private local instance (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space)) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space)) := inferInstance

structure L2Data (I : Input) where
  velocity : Icc (0 : ℝ) I.T → SmoothL2Field Space
  derivative : Icc (0 : ℝ) I.T → SmoothL2Field Space
  velocity_match : ∀ t x, (velocity t).field x=I.field.field t x
  derivative_match : ∀ t x, (derivative t).field x=I.derivative.field t x
  C : ℝ
  S : ℝ
  C₁ : ℝ
  S₁ : ℝ
  C_nonneg : 0 ≤ C
  S_nonneg : 0 ≤ S
  C₁_nonneg : 0 ≤ C₁
  S₁_nonneg : 0 ≤ S₁
  velocity_bound : ∀ t, (velocity t).HasJetBound C S
  derivative_bound : ∀ t, (derivative t).HasJetBound C₁ S₁

namespace L2Data

variable {I : Input} (L : L2Data I)

def velocityRadius : ℝ := flowRadius I.B I.R I.T L.S

theorem velocityRadius_nonneg : 0 ≤ L.velocityRadius := by
  have hb := I.B_nonneg
  have hr := I.R_pos
  have ht := I.T_pos
  have hs := L.S_nonneg
  dsimp [velocityRadius,flowRadius]
  positivity

def velocityField (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.composeField ((flowData I.T I.T_pos.le I.field).forward t)
    (forward_contDiff I.T I.T_pos.le I.field t)
    (forward_measurePreserving I.T I.T_pos.le I.field I.divergence volume t)
    (1+I.B*I.T) (4*I.R+1)
    (add_nonneg zero_le_one (mul_nonneg I.B_nonneg I.T_pos.le))
    (add_nonneg (mul_nonneg (by norm_num) I.R_pos.le) zero_le_one)
    (fun n hn => forward_positive_bound I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
      I.small I.bound n hn t)
    (L.velocity t) L.C L.S L.C_nonneg L.S_nonneg (L.velocity_bound t)

theorem velocityField_bound (t : Icc (0 : ℝ) I.T) :
    (L.velocityField t).HasJetBound L.C L.velocityRadius := by
  unfold velocityField velocityRadius
  apply SmoothL2Field.composeField_bound

theorem velocityField_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    (L.velocityField t).field x=I.velocity.field t x := by
  change (L.velocity t).field ((flowData I.T I.T_pos.le I.field).forward t x)=_
  rw [L.velocity_match,I.velocity_apply]
  rfl

theorem velocityField_jet (n : ℕ) (t : Icc (0 : ℝ) I.T) :
    iteratedFDeriv ℝ n (L.velocityField t).field =
      fun x => I.velocity.jet n t x := by
  rw [show (L.velocityField t).field = (I.velocity.field t : Space → Space) from
    funext (L.velocityField_apply t)]
  exact funext (fun x => (I.velocity.jet_eq n t x).symm)

theorem displacement_jet_integral (n : ℕ) (t : Icc (0 : ℝ) I.T) (x : Space) :
    I.displacement.jet n t x =
      ∫ s in (0 : ℝ)..(t : ℝ), extendPath I.T I.T_pos.le (I.velocity.jet n) s x := by
  let f : C(Icc (0 : ℝ) I.T,Space [×n]→L[ℝ] Space) :=
    ⟨fun s => I.velocity.jet n s x,
      (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp (I.velocity.jet n).continuous⟩
  have h := EulerContinuousTimeIntegral.eq_initial_add_integral I.T I.T_pos.le f
    (fun s => extendPath I.T I.T_pos.le (I.displacement.jet n) s x)
    (fun s => SmoothTimeField.TimeDerivative.jet_pointwise I.T I.T_pos.le
      I.displacement I.velocity I.displacement_time n x s) t
  have hz : I.displacement.jet n ⟨0,le_rfl,I.T_pos.le⟩ x=0 := by
    rw [I.displacement.jet_eq]
    have he : (I.displacement.field ⟨0,le_rfl,I.T_pos.le⟩ : Space → Space)=0 :=
      funext I.displacement_initial
    rw [he,iteratedFDeriv_zero]
    rfl
  simp only [extendPath,projIcc_of_mem I.T_pos.le t.property,
    projIcc_of_mem I.T_pos.le (show (0 : ℝ) ∈ Icc 0 I.T from ⟨le_rfl,I.T_pos.le⟩),hz,
    zero_add,EulerContinuousTimeIntegral.integral_apply,EulerContinuousTimeIntegral.realIntegral]
      at h
  exact h

theorem displacement_memLp_and_bound (n : ℕ) (t : Icc (0 : ℝ) I.T) :
    MemLp (iteratedFDeriv ℝ n (I.displacement.field t : Space → Space)) 2 volume ∧
      (eLpNorm (iteratedFDeriv ℝ n (I.displacement.field t : Space → Space)) 2 volume).toReal ≤
        I.T*L.C*L.velocityRadius^n*(n.factorial : ℝ)^2 := by
  let f : ℝ × Space → Space [×n]→L[ℝ] Space :=
    fun p => extendPath I.T I.T_pos.le (I.velocity.jet n) p.1 p.2
  have hc : Continuous f := by
    have ht := extendPath_continuous I.T I.T_pos.le (I.velocity.jet n)
    dsimp [f]
    fun_prop
  have hb : ∀ s : ℝ, MemLp (fun x => f (s,x)) 2 volume ∧
      (eLpNorm (fun x => f (s,x)) 2 volume).toReal ≤
        L.C*L.velocityRadius^n*(n.factorial : ℝ)^2 := by
    intro s
    have he : (fun x => f (s,x)) =
        iteratedFDeriv ℝ n (L.velocityField (projIcc 0 I.T I.T_pos.le s)).field :=
      (L.velocityField_jet n (projIcc 0 I.T I.T_pos.le s)).symm
    rw [he]
    exact ⟨(L.velocityField _).integrable n,by
      rw [← SmoothL2Field.norm_jetLp]
      exact L.velocityField_bound _ n⟩
  have hp := EulerLpParameterIntegral.intervalIntegral_memLp_and_bound (t : ℝ) t.property.1
    volume f hc.aestronglyMeasurable (L.C*L.velocityRadius^n*(n.factorial : ℝ)^2)
    (mul_nonneg (mul_nonneg L.C_nonneg (pow_nonneg L.velocityRadius_nonneg n)) (sq_nonneg _))
    (Eventually.of_forall hb)
  have he : (fun x => ∫ s in (0 : ℝ)..(t : ℝ), f (s,x)) =
      iteratedFDeriv ℝ n (I.displacement.field t : Space → Space) := by
    funext x
    exact (displacement_jet_integral (I := I) n t x).symm.trans (I.displacement.jet_eq n t x)
  rw [he] at hp
  refine ⟨hp.1,hp.2.trans ?_⟩
  have ht := mul_le_mul_of_nonneg_right t.property.2
    (mul_nonneg (mul_nonneg L.C_nonneg (pow_nonneg L.velocityRadius_nonneg n))
      (sq_nonneg (n.factorial : ℝ)))
  exact ht.trans_eq (by ring)

def displacementField (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space where
  field := I.displacement.field t
  smooth := I.displacement.smooth t
  integrable n := (L.displacement_memLp_and_bound n t).1

theorem displacementField_bound (t : Icc (0 : ℝ) I.T) :
    (L.displacementField t).HasJetBound (I.T*L.C) L.velocityRadius := by
  intro n
  rw [SmoothL2Field.norm_jetLp]
  exact (L.displacement_memLp_and_bound n t).2

def accelerationSourceRadius : ℝ := 4*I.R+L.S+L.S₁

theorem accelerationSourceRadius_nonneg : 0 ≤ L.accelerationSourceRadius := by
  have hr := I.R_pos
  have hs := L.S_nonneg
  have hs₁ := L.S₁_nonneg
  dsimp [accelerationSourceRadius]
  positivity

theorem field_derivative_bound (t : Icc (0 : ℝ) I.T) :
    HasSupBound (fderiv ℝ (I.field.field t : Space → Space)) (I.B*I.R) L.accelerationSourceRadius
      := by
  have h : HasSupBound (I.field.field t : Space → Space) I.B I.R :=
    fun n x => field_jet_bound I.T I.field I.B I.R I.bound n t x
  exact (h.derivative I.B_nonneg I.R_pos.le).mono (mul_nonneg I.B_nonneg I.R_pos.le)
    (mul_nonneg (by norm_num) I.R_pos.le) le_rfl
    (by dsimp [accelerationSourceRadius]; linarith [L.S_nonneg,L.S₁_nonneg])

def accelerationProduct (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.productField (fderiv ℝ (I.field.field t : Space → Space))
    ((I.field.smooth t).fderiv_right (m := ∞) (by simp)) (L.velocity t)
    (I.B*I.R) L.C L.accelerationSourceRadius (mul_nonneg I.B_nonneg I.R_pos.le) L.C_nonneg
    L.accelerationSourceRadius_nonneg (L.field_derivative_bound t)
    ((L.velocity_bound t).mono L.C_nonneg L.S_nonneg le_rfl
      (by dsimp [accelerationSourceRadius]; linarith [I.R_pos,L.S₁_nonneg]))

def accelerationSource (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.addField (L.derivative t) (L.accelerationProduct t)

def accelerationAmplitude : ℝ := L.C₁+3*(I.B*I.R)*L.C

theorem accelerationAmplitude_nonneg : 0 ≤ L.accelerationAmplitude := by
  have hb := I.B_nonneg
  have hr := I.R_pos
  have hc := L.C_nonneg
  have hc₁ := L.C₁_nonneg
  dsimp [accelerationAmplitude]
  positivity

theorem accelerationSource_bound (t : Icc (0 : ℝ) I.T) :
    (L.accelerationSource t).HasJetBound L.accelerationAmplitude L.accelerationSourceRadius := by
  apply SmoothL2Field.HasJetBound.add
  · exact (L.derivative_bound t).mono L.C₁_nonneg L.S₁_nonneg le_rfl
      (by dsimp [accelerationSourceRadius]; linarith [I.R_pos,L.S_nonneg])
  · exact SmoothL2Field.productField_bound _ _ _ _ _ _ _ _ _ _ _

def accelerationRadius : ℝ := flowRadius I.B I.R I.T L.accelerationSourceRadius

theorem accelerationRadius_nonneg : 0 ≤ L.accelerationRadius := by
  have hb := I.B_nonneg
  have hr := I.R_pos
  have ht := I.T_pos
  have hs := L.accelerationSourceRadius_nonneg
  dsimp [accelerationRadius,flowRadius]
  positivity

def accelerationField (t : Icc (0 : ℝ) I.T) : SmoothL2Field Space :=
  SmoothL2Field.composeField ((flowData I.T I.T_pos.le I.field).forward t)
    (forward_contDiff I.T I.T_pos.le I.field t)
    (forward_measurePreserving I.T I.T_pos.le I.field I.divergence volume t)
    (1+I.B*I.T) (4*I.R+1)
    (add_nonneg zero_le_one (mul_nonneg I.B_nonneg I.T_pos.le))
    (add_nonneg (mul_nonneg (by norm_num) I.R_pos.le) zero_le_one)
    (fun n hn => forward_positive_bound I.T I.T_pos.le I.field I.B I.R I.B_nonneg I.R_pos
      I.small I.bound n hn t)
    (L.accelerationSource t) L.accelerationAmplitude L.accelerationSourceRadius
    L.accelerationAmplitude_nonneg L.accelerationSourceRadius_nonneg (L.accelerationSource_bound t)

theorem accelerationField_bound (t : Icc (0 : ℝ) I.T) :
    (L.accelerationField t).HasJetBound L.accelerationAmplitude L.accelerationRadius := by
  unfold accelerationField accelerationRadius
  apply SmoothL2Field.composeField_bound

theorem accelerationField_apply (t : Icc (0 : ℝ) I.T) (x : Space) :
    (L.accelerationField t).field x=I.acceleration.field t x := by
  change (L.derivative t).field ((flowData I.T I.T_pos.le I.field).forward t x) +
    fderiv ℝ (I.field.field t : Space → Space) ((flowData I.T I.T_pos.le I.field).forward t x)
      ((L.velocity t).field ((flowData I.T I.T_pos.le I.field).forward t x)) = _
  rw [L.derivative_match,L.velocity_match,I.acceleration_apply,accelerationFamily_apply]

end L2Data
end EulerBaseEulerParent
