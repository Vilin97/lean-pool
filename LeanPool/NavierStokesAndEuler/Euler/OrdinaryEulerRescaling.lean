/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldScaling
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerGradientControl
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRestriction

@[expose] public section

/-! The genuine time/amplitude symmetry of ordinary Euler, including
restriction to a shorter closed time interval. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVolterraConvolution
open scoped Topology

def scaleTimeMap (S T c : ℝ) (hc : 0 ≤ c) (hct : c*T ≤ S) :
    C(Icc (0 : ℝ) T,Icc (0 : ℝ) S) where
  toFun t := ⟨c*t,mul_nonneg hc t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 hc).trans hct⟩
  continuous_toFun := (continuous_subtype_val.const_mul c).subtype_mk _

@[simp] theorem scaleTimeMap_val (S T c : ℝ) (hc : 0 ≤ c) (hct : c*T ≤ S)
    (t : Icc (0 : ℝ) T) : ((scaleTimeMap S T c hc hct t) : ℝ)=c*t := rfl

namespace Evolution

variable {S : ℝ} {hS : 0 ≤ S}

def rescale (U : Evolution S hS) (T : ℝ) (hT : 0 ≤ T)
    (c : ℝ) (hc : 0 < c) (hct : c*T ≤ S) : Evolution T hT where
  velocity t := scaleField c (U.velocity (scaleTimeMap S T c hc.le hct t))
  pressureForce t := scaleField (c*c) (U.pressureForce (scaleTimeMap S T c hc.le hct t))
  velocity_continuous n := scaleField_continuous c _
    (fun n => (U.velocity_continuous n).comp (scaleTimeMap S T c hc.le hct).continuous) n
  pressure_continuous n := scaleField_continuous (c*c) _
    (fun n => (U.pressure_continuous n).comp (scaleTimeMap S T c hc.le hct).continuous) n
  solenoidal t := by
    rw [scaleField_toLp]
    exact solenoidalSpace.smul_mem c (U.solenoidal _)
  gradient t := by
    rw [scaleField_toLp]
    exact gradientSpace.smul_mem (c*c) (U.gradient _)
  time_law t ht x := by
    have hcs : c*t ∈ Ioo (0 : ℝ) S :=
      ⟨mul_pos hc ht.1,(mul_lt_mul_of_pos_left ht.2 hc).trans_le hct⟩
    have hi : HasDerivAt (fun r : ℝ => c*r) c t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul c
    have hd := ((U.time_law (c*t) hcs x).scomp t hi).const_smul c
    have he : (fun r => scaleField c
        (U.velocity (scaleTimeMap S T c hc.le hct (projIcc 0 T hT r))) |>.field x)
        =ᶠ[𝓝 t] (fun r => c • (U.velocity (projIcc 0 S hS (c*r))).field x) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le,hr.2.le⟩
      have hrS : c*r ∈ Icc (0 : ℝ) S :=
        ⟨mul_nonneg hc.le hr.1.le,(mul_le_mul_of_nonneg_left hr.2.le hc.le).trans hct⟩
      simp only [scaleField_field,projIcc_of_mem hT hrT,projIcc_of_mem hS hrS]
      rfl
    have hrhs :
        -fderiv ℝ (scaleField c (U.velocity (scaleTimeMap S T c hc.le hct
          ⟨t,ht.1.le,ht.2.le⟩))).field x
          ((scaleField c (U.velocity (scaleTimeMap S T c hc.le hct
            ⟨t,ht.1.le,ht.2.le⟩))).field x)-
          (scaleField (c*c) (U.pressureForce (scaleTimeMap S T c hc.le hct
            ⟨t,ht.1.le,ht.2.le⟩))).field x =
        c • (c • (-fderiv ℝ (U.velocity ⟨c*t,hcs.1.le,hcs.2.le⟩).field x
          ((U.velocity ⟨c*t,hcs.1.le,hcs.2.le⟩).field x)-
            (U.pressureForce ⟨c*t,hcs.1.le,hcs.2.le⟩).field x)) := by
      have heq : scaleTimeMap S T c hc.le hct ⟨t,ht.1.le,ht.2.le⟩ =
          ⟨c*t,hcs.1.le,hcs.2.le⟩ := rfl
      rw [heq]
      simp only [scaleField_fderiv,scaleField_field,smul_apply,map_smul,
        smul_sub,smul_neg,smul_smul]
    rw [hrhs]
    exact hd.congr_of_eventuallyEq he

@[simp] theorem rescale_velocity (U : Evolution S hS) (T : ℝ) (hT : 0 ≤ T)
    (c : ℝ) (hc : 0 < c) (hct : c*T ≤ S) (t : Icc (0 : ℝ) T) :
    (U.rescale T hT c hc hct).velocity t =
      scaleField c (U.velocity (scaleTimeMap S T c hc.le hct t)) := rfl

theorem rescale_initial (U : Evolution S hS) (T : ℝ) (hT : 0 ≤ T)
    (c : ℝ) (hc : 0 < c) (hct : c*T ≤ S) :
    (U.rescale T hT c hc hct).velocity ⟨0,le_rfl,hT⟩ =
      scaleField c (U.velocity ⟨0,le_rfl,hS⟩) := by
  rw [rescale_velocity]
  congr 2
  apply Subtype.ext
  exact mul_zero c

end Evolution
end EulerOrdinarySobolev
