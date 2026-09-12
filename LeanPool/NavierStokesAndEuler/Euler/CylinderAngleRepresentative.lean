/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAnglePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointEvaluation
public import LeanPool.NavierStokesAndEuler.Euler.AngleMeanZeroPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The genuine cylinder L² angular operator represents the literal classical primitive. -/

section

/-! A translation-kernel formula for the literal normalized periodic primitive. -/

@[expose] public section

noncomputable section

namespace EulerAngleMeanZeroPrimitive

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- This formula realizes the angular primitive as an integral of translations. -/
theorem primitive_eq_translation_kernel (P : ℝ) (hP : P ≠ 0) (f : ℝ → E)
    (hf : Continuous f) (hper : Function.Periodic f P)
    (hmean : (∫ s in (0 : ℝ)..P, f s) = 0) (θ : ℝ) :
    primitive P f θ = P⁻¹ • (∫ s in (0 : ℝ)..P, s • f (θ+s)) := by
  let q := primitive P f
  have hq : Continuous q := primitive_continuous P f hf
  have hqp : Function.Periodic q P := primitive_periodic P f hf hper hmean
  have hd (s : ℝ) : HasDerivAt (fun r => r • q (θ+r))
      (q (θ+s)+s • f (θ+s)) s := by
    have hq' := (primitive_hasDerivAt P f hf (θ+s)).scomp s ((hasDerivAt_id s).const_add θ)
    simpa only [Function.comp_def, id_eq, one_smul, Pi.smul_def', q, add_comm] using
      (hasDerivAt_id s).smul hq'
  have hqc : Continuous (fun s => q (θ+s)) := hq.comp (continuous_const.add continuous_id)
  have hfc : Continuous (fun s => s • f (θ+s)) :=
    continuous_id.smul (hf.comp (continuous_const.add continuous_id))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((hqc.add hfc).intervalIntegrable 0 P)
  rw [intervalIntegral.integral_add (hqc.intervalIntegrable 0 P) (hfc.intervalIntegrable 0 P)] at hi
  have hzero : (∫ s in (0 : ℝ)..P, q (θ+s))=0 := by
    rw [intervalIntegral.integral_comp_add_left]
    have hp := hqp.intervalIntegral_add_eq θ 0
    rw [zero_add] at hp
    rw [add_zero, hp]
    exact primitive_mean_zero P hP f hf
  rw [hzero, zero_add, hqp θ, zero_smul, sub_zero] at hi
  change q θ = _
  rw [hi, smul_smul, inv_mul_cancel₀ hP, one_smul]

end EulerAngleMeanZeroPrimitive

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderAnglePrimitive

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevPointEvaluation EulerSpatialSobolevInverse EulerPressureSpatialRegularity

variable (P : ℝ) [Fact (0 < P)]

theorem sobolevKernel_continuous {q : ℕ} (u : SobolevSpace P q) :
    Continuous (fun s : ℝ => s • sobolevTranslation P q (angleShift P s) u) :=
  continuous_id.smul ((sobolevTranslation_continuous P u).comp (angleShift_continuous P))

/-- The lifted operator is also the actual Bochner integral in the Sobolev space. -/
theorem sobolevPrimitive_eq_integral {q : ℕ} (u : SobolevSpace P q) :
    sobolevPrimitive P q u = P⁻¹ • (∫ s in (0 : ℝ)..P, s • sobolevTranslation P q (angleShift P s)
        u) := by
  apply value_injective P
  change primitive P (value P u) = (valueOperator P q)
    (P⁻¹ • (∫ s in (0 : ℝ)..P, s • sobolevTranslation P q (angleShift P s) u))
  rw [map_smul, ← (valueOperator P q).intervalIntegral_comp_comm
    ((sobolevKernel_continuous P u).intervalIntegrable 0 P)]
  change P⁻¹ • (∫ s in (0 : ℝ)..P, kernelCurve P (value P u) s) = _
  congr 1

theorem pointEvaluation_translation (u : SobolevSpace P 3) (a x : LiftDomain P) :
    pointEvaluation P x (sobolevTranslation P 3 a u) = representative P u (x+a) := by
  apply pointEvaluation_eq P x (sobolevTranslation P 3 a u)
    (fun y => representative P u (y+a))
    ((representative_continuous P u).comp (continuous_id.add continuous_const))
  filter_upwards [translation_ae P a (value P u),
    (measurePreserving_translation P a).quasiMeasurePreserving.ae (representative_ae P u)] with y
        hy hr
  change translation P a (value P u) y = _
  exact hy.trans hr

theorem pointEvaluation_primitive_kernel (u : SobolevSpace P 3) (x : LiftDomain P) :
    pointEvaluation P x (sobolevPrimitive P 3 u) =
      P⁻¹ • (∫ s in (0 : ℝ)..P, s • representative P u (x+angleShift P s)) := by
  rw [sobolevPrimitive_eq_integral, map_smul,
    ← (pointEvaluation P x).intervalIntegral_comp_comm
      ((sobolevKernel_continuous P u).intervalIntegrable 0 P)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change pointEvaluation P x (s • sobolevTranslation P 3 (angleShift P s) u) =
    s • representative P u (x+angleShift P s)
  rw [map_smul, pointEvaluation_translation]

/-- Evaluation of the constructed L² operator gives the actual normalized integral. -/
theorem pointEvaluation_primitive_classical (u : SobolevSpace P 3)
    (f : LiftDomain P → Vector3) (hf : Continuous f)
    (hrep : (value P u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f)
    (hmean : ∀ y, (∫ s in (0 : ℝ)..P, f (y, (s : AddCircle P))) = 0)
    (y : Vector3) (θ : ℝ) :
    pointEvaluation P (y,(θ : AddCircle P)) (sobolevPrimitive P 3 u) =
      EulerAngleMeanZeroPrimitive.primitive P (fun s => f (y,(s : AddCircle P))) θ := by
  rw [pointEvaluation_primitive_kernel, representative_eq P u f hf hrep]
  have hp : Function.Periodic (fun s : ℝ => f (y,(s : AddCircle P))) P := by
    intro s
    change f (y,((s+P : ℝ) : AddCircle P)) = f (y,(s : AddCircle P))
    rw [AddCircle.coe_add_period]
  have h := EulerAngleMeanZeroPrimitive.primitive_eq_translation_kernel P
    (ne_of_gt (Fact.out : 0 < P)) (fun s => f (y,(s : AddCircle P)))
    (hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P))) hp (hmean y) θ
  simpa only [angleShift, Prod.mk_add_mk, add_zero, AddCircle.coe_add] using h.symm

/-- Classical identification holds as equality of actual L² representatives. -/
theorem primitive_ae_classical (u : SobolevSpace P 3)
    (f q : LiftDomain P → Vector3) (hf : Continuous f)
    (hrep : (value P u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f)
    (hmean : ∀ y, (∫ s in (0 : ℝ)..P, f (y, (s : AddCircle P))) = 0)
    (hq : ∀ (y : Vector3) (θ : ℝ), q (y, (θ : AddCircle P)) =
      EulerAngleMeanZeroPrimitive.primitive P (fun s => f (y, (s : AddCircle P))) θ) :
    (primitive P (value P u) : LiftDomain P → Vector3)=ᵐ[liftMeasure P] q := by
  have he (x : LiftDomain P) : representative P (sobolevPrimitive P 3 u) x = q x := by
    obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective x.2
    have hx : x=(x.1,(θ : AddCircle P)) := by
      apply Prod.ext
      · rfl
      · exact hθ.symm
    rw [hx]
    exact (pointEvaluation_primitive_classical P u f hf hrep hmean x.1 θ).trans (hq x.1 θ).symm
  filter_upwards [representative_ae P (sobolevPrimitive P 3 u)] with x hx
  exact hx.trans (he x)

end EulerCylinderAnglePrimitive
