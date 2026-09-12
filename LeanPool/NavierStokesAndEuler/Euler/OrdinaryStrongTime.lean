/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFieldSobolevTime
import LeanPool.NavierStokesAndEuler.Euler.InjectivePathDerivativeWithin

/-! A genuine L² evolution lifts to every ordinary Sobolev order when
the proposed derivative has continuous actual spatial jets. Bounded
Sobolev evaluation then supplies the classical pointwise time law. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
  EulerSmoothFieldSobolevTime EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerVolterraConvolution
open scoped ContDiff

local instance instOrdinaryStrongTime1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable (T : ℝ) (hT : 0 ≤ T)
  (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
  (hd : ∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp) (B ⟨t, ht.1.le, ht.2.le⟩).toLp t)

include hd in
theorem sobolev_derivative_of_l2 (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath A hA q))
      (sobolevPath B hB q t) (Icc (0 : ℝ) T) t := by
  apply EulerInjectivePathDerivative.hasDerivWithinAt_of_injective_map
    (valueOperator 1 q) (value_injective 1) T hT (sobolevPath A hA q) (sobolevPath B hB q)
  intro r hr
  have h := ordinaryLift.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r (hd r hr)
  have he : (fun s => valueOperator 1 q (extendPath T hT (sobolevPath A hA q) s)) =
      fun s => ordinaryLift (A (projIcc 0 T hT s)).toLp := by
    funext s
    exact ordinarySobolev_value q _ _
  rw [he]
  have hb : valueOperator 1 q (extendPath T hT (sobolevPath B hB q) r) =
      ordinaryLift (B ⟨r,hr.1.le,hr.2.le⟩).toLp := by
    change value 1 (ordinarySobolev q (B (projIcc 0 T hT r)).toLp _)=_
    erw [ordinarySobolev_value,projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
  rw [hb]
  exact h

include hA hB hd in
theorem pointwise_derivative_of_l2 (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun r => (A (projIcc 0 T hT r)).field x)
      ((B t).field x) (Icc (0 : ℝ) T) t := by
  let L := observation 3 (le_refl 3) (x,(0 : AddCircle (1 : ℝ)))
  have hs := sobolev_derivative_of_l2 T hT A B hA hB hd 3 t
  have h := L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hs
  have he : (fun r => L (extendPath T hT (sobolevPath A hA 3) r)) =
      fun r => (A (projIcc 0 T hT r)).field x := by
    funext r
    exact observation_apply 3 (le_refl 3) (x,(0 : AddCircle (1 : ℝ))) _
  have hb : L (sobolevPath B hB 3 t)=(B t).field x :=
    observation_apply 3 (le_refl 3) (x,(0 : AddCircle (1 : ℝ))) _
  simpa only [Function.comp_def,he,hb] using h

end EulerOrdinarySobolev
