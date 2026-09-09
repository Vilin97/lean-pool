/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.ODE.Gronwall

/-! Actual L² stability of two ordinary Euler solutions.  The pressure
and the entire transport term cancel before estimating the remaining
reference-gradient term.  All time derivatives are genuine one-sided
derivatives at the endpoints. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution Finset
open scoped ContDiff Topology

theorem advection_norm_gradient (W U : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ U.field x‖ ≤ K) :
    ‖(advectionField W U).toLp‖ ≤ K*‖W.toLp‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(advectionField W U).toLp_ae,W.toLp_ae] with x ha hw
  rw [ha,hw,advectionField_field]
  exact ((fderiv ℝ U.field x).le_opNorm (W.field x)).trans
    (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))

theorem differenceRhs_l2_bound (U W P : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ U.field x‖ ≤ K)
    (hdiv : ∀ x, divergence (addField U W).field x = 0)
    (hW : W.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    2*⟪W.toLp,(differenceRhs U W P).toLp⟫_ℝ ≤ 2*K*‖W.toLp‖^2 := by
  have he := differenceRhs_pairing U W P hdiv hW hP (Fin.elim0 : Fin 0 → Fin 3)
  simp only [wordField_zero,transportCommutator_zero,inner_zero_left,neg_zero,
    zero_sub] at he
  rw [he]
  calc
    _ ≤ 2*|⟪(advectionField W U).toLp,W.toLp⟫_ℝ| := by
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by norm_num)
    _ ≤ 2*(‖(advectionField W U).toLp‖*‖W.toLp‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
    _ ≤ 2*((K*‖W.toLp‖)*‖W.toLp‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (advection_norm_gradient W U K hK) (norm_nonneg _))
      (by norm_num)
    _ = _ := by ring

theorem linear_stability_within (X X' : ℝ → ℝ) (C T : ℝ)
    (hcont : ContinuousOn X (Icc 0 T))
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hineq : ∀ t ∈ Ico 0 T, X' t ≤ C * X t) :
    ∀ t ∈ Icc 0 T, X t ≤ X 0*Real.exp (C*t) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le (K := C) (ε := 0) hcont
    (fun t ht r hr => ((hder t ht).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)).liminf_right_slope_le hr) (le_refl (X 0))
    (fun t ht => by simpa only [add_zero] using hineq t ht)
  simpa only [gronwallBound_ε0,sub_zero] using h

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

/-- Velocity path, given by `ordinaryWordPath U.velocity U.velocity_continuous (Fin.elim0 : Fin
0 → Fin 3)`. -/
def velocityPath (U : Evolution T hT) : C(Icc (0 : ℝ) T,L2) :=
  ordinaryWordPath U.velocity U.velocity_continuous (Fin.elim0 : Fin 0 → Fin 3)

@[simp] theorem velocityPath_apply (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    U.velocityPath t=(U.velocity t).toLp := by
  simp only [velocityPath,ordinaryWordPath_apply,wordField_zero]

/-- L2 energy path as an element of `C(Icc (0 : ℝ) T,ℝ)`. -/
def l2EnergyPath (U V : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => ‖(U.difference V t).toLp‖^2,by
    have h := (ordinaryWordPath (U.difference V) (U.difference_continuous V)
      (Fin.elim0 : Fin 0 → Fin 3)).continuous
    simpa only [Function.comp_def,ordinaryWordPath_apply,wordField_zero] using
      (continuous_pow 2).comp h.norm⟩

/-- L2 energy derivative, given by `2*⟪(U.difference V t).toLp,(U.differenceDerivative V
t).toLp⟫_ℝ`. -/
def l2EnergyDerivative (U V : Evolution T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  2*⟪(U.difference V t).toLp,(U.differenceDerivative V t).toLp⟫_ℝ

theorem l2Energy_hasDerivWithinAt (U V : Evolution T hT) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.l2EnergyPath V)) (U.l2EnergyDerivative V t)
      (Icc (0 : ℝ) T) t := by
  have hd := (ordinaryWord_hasDerivWithinAt T hT (U.difference V)
    (U.differenceDerivative V) (U.difference_continuous V)
    (U.differenceDerivative_continuous V) (U.difference_time_law V)
    (Fin.elim0 : Fin 0 → Fin 3) t).norm_sq
  change HasDerivWithinAt (fun r => ‖(U.difference V (projIcc 0 T hT r)).toLp‖^2)
    (2*⟪(U.difference V t).toLp,(U.differenceDerivative V t).toLp⟫_ℝ)
    (Icc (0 : ℝ) T) t
  simpa only [wordField_zero,projIcc_of_mem hT t.property] using hd

theorem l2EnergyDerivative_bound (U V : Evolution T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    U.l2EnergyDerivative V t ≤ 2*K*U.l2EnergyPath V t := by
  rw [l2EnergyDerivative,differenceDerivative_eq]
  apply differenceRhs_l2_bound _ _ _ K (hK t)
  · have he : (addField (U.velocity t) (U.difference V t)).field=(V.velocity t).field := by
      funext x
      simp only [addField_field,difference,fieldSub_field]
      abel
    rw [he]
    exact solenoidal_representative_divergence _ (V.solenoidal t) _ (V.velocity t).smooth
      (V.velocity t).toLp_ae
  · rw [difference,toLp_fieldSub]
    exact solenoidalSpace.sub_mem (V.solenoidal t) (U.solenoidal t)
  · rw [pressureDifference,toLp_fieldSub]
    exact gradientSpace.sub_mem (V.gradient t) (U.gradient t)

theorem l2_energy_bound (U V : Evolution T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    ‖(U.difference V t).toLp‖^2 ≤
      ‖(U.difference V ⟨0,le_rfl,hT⟩).toLp‖^2*Real.exp (2*K*t) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.l2EnergyPath V))
        (U.l2EnergyDerivative V (projIcc 0 T hT r)) (Icc 0 T) r := by
    have h := U.l2Energy_hasDerivWithinAt V ⟨r,hr.1,hr.2.le⟩
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using h
  have hb (r : ℝ) (hr : r ∈ Ico 0 T) :
      U.l2EnergyDerivative V (projIcc 0 T hT r) ≤
        (2*K)*extendPath T hT (U.l2EnergyPath V) r :=
    U.l2EnergyDerivative_bound V K hK (projIcc 0 T hT r)
  have h := linear_stability_within (extendPath T hT (U.l2EnergyPath V))
    (fun r => U.l2EnergyDerivative V (projIcc 0 T hT r)) (2*K) T
    ((U.l2EnergyPath V).continuous.comp continuous_projIcc).continuousOn hd hb t t.property
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    l2EnergyPath,ContinuousMap.coe_mk] using h

theorem l2_stability (U V : Evolution T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    ‖(U.difference V t).toLp‖ ≤
      ‖(U.difference V ⟨0,le_rfl,hT⟩).toLp‖*Real.exp (K*t) := by
  have h := U.l2_energy_bound V K hK t
  rw [show 2*K*(t : ℝ)=K*t+K*t by ring,Real.exp_add] at h
  have hp : 0 ≤ ‖(U.difference V ⟨0,le_rfl,hT⟩).toLp‖*Real.exp (K*t) := by positivity
  nlinarith [norm_nonneg (U.difference V t).toLp]

theorem velocityPath_norm_sub_le (U V : Evolution T hT) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) :
    ‖V.velocityPath-U.velocityPath‖ ≤
      ‖V.velocityPath ⟨0,le_rfl,hT⟩-U.velocityPath ⟨0,le_rfl,hT⟩‖*Real.exp (K*T) := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have h := U.l2_stability V K hK t
  simp only [difference,toLp_fieldSub] at h
  simpa only [ContinuousMap.sub_apply,velocityPath_apply] using h.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left t.property.2 hK0)) (norm_nonneg _))

theorem l2_stability_of_h3 (U V : Evolution T hT) (M : ℝ)
    (hM : ∀ t, tensorNorm 3 (U.velocity t) ≤ M) (t : Icc (0 : ℝ) T) :
    ‖(U.difference V t).toLp‖ ≤ ‖(U.difference V ⟨0,le_rfl,hT⟩).toLp‖*
      Real.exp ((9*EulerSmoothSobolev.smoothEmbeddingConstant*M)*t) := by
  apply U.l2_stability V
  intro s x
  have hb := EulerSmoothSobolev.real_smooth_fderiv_le_H3 3 (U.velocity s).field
    (U.velocity s).smooth (fun j _ => (U.velocity s).integrable j) x
  rw [← tensorNorm_eq] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hM s)
    (mul_nonneg (by norm_num) EulerSmoothSobolev.smoothEmbeddingConstant_nonneg))

end Evolution
end EulerOrdinarySobolev
