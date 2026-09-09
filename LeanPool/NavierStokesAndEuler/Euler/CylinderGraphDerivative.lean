/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphAffine
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A genuine cylinder L² time derivative, together with its genuine angular
derivative, remains a genuine spatial L² derivative on every fixed phase graph. -/

@[expose] public section


noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory Filter EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ContDiff Topology

variable (P : ℝ) [Fact (0 < P)]

theorem graph_hasDerivWithinAt
    (u v : ℝ → LiftL2 P) (f : ℝ → LiftDomain P → Vector3)
    (hf : ∀ r x, ContDiff ℝ ∞ (localFieldLift P (f r) x))
    (hu : ∀ r, (u r : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f r)
    (hv : ∀ r, (v r : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      fieldDerivative P (0, 1) (f r))
    (θ : Vector3 → AddCircle P) (hθ : Continuous θ)
    (w : ℝ → Lp Vector3 2 (volume : Measure Vector3))
    (hw : ∀ r, (w r : Vector3 → Vector3) =ᵐ[volume] fun x => f r (x, θ x))
    (g : LiftDomain P → Vector3) (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift P g x))
    (u' v' : LiftL2 P)
    (hu' : (u' : LiftDomain P → Vector3) =ᵐ[liftMeasure P] g)
    (hv' : (v' : LiftDomain P → Vector3) =ᵐ[liftMeasure P] fieldDerivative P (0, 1) g)
    (w' : Lp Vector3 2 (volume : Measure Vector3))
    (hw' : (w' : Vector3 → Vector3) =ᵐ[volume] fun x => g (x, θ x))
    (s : Set ℝ) (t : ℝ)
    (hdu : HasDerivWithinAt u u' s t) (hdv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt w w' s t := by
  have hb (r : ℝ) : ‖slope w t r-w'‖^2 ≤
      (2/P)*‖slope u t r-u'‖^2+(2*P)*‖slope v t r-v'‖^2 := by
    simpa only [slope_def_module,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def,
      Matrix.cons_val_succ] using graph_affine_norm_sq_le P ![f t,f r,g]
      (by
        intro i x
        fin_cases i
        · exact hf t x
        · exact hf r x
        · exact hg x)
      ![u t,u r,u'] ![v t,v r,v']
      (by
        intro i
        fin_cases i
        · exact hu t
        · exact hu r
        · exact hu')
      (by
        intro i
        fin_cases i
        · exact hv t
        · exact hv r
        · exact hv') θ hθ
      ![w t,w r,w']
      (by
        intro i
        fin_cases i
        · exact hw t
        · exact hw r
        · exact hw') (r-t)⁻¹
  have huLim := (hasDerivWithinAt_iff_tendsto_slope.mp hdu).sub_const u'
  have hvLim := (hasDerivWithinAt_iff_tendsto_slope.mp hdv).sub_const v'
  have hlim : Tendsto (fun r => (2/P)*‖slope u t r-u'‖^2+(2*P)*‖slope v t r-v'‖^2)
      (𝓝[s \ {t}] t) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero,add_zero] using
      ((huLim.norm.pow 2).const_mul (2/P)).add ((hvLim.norm.pow 2).const_mul (2*P))
  have hsq := squeeze_zero (fun r => sq_nonneg ‖slope w t r-w'‖) hb hlim
  rw [hasDerivWithinAt_iff_tendsto_slope,tendsto_iff_norm_sub_tendsto_zero]
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hr

end EulerCylinderGraphTrace
