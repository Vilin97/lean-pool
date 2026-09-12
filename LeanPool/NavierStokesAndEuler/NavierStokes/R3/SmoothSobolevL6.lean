/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import LeanPool.NavierStokesAndEuler.ForMathlib.SobolevThreeDimensional
import Mathlib.Algebra.Order.Ring.Star

/-!
# Homogeneous Sobolev bounds for smooth square-integrable functions

Spatial cutoffs extend the compactly supported Sobolev inequality to a smooth
function whose value and derivative belong to `L²`. The derivative of the
cutoff contributes an error tending to zero; Fatou's lemma passes to the limit.
-/

@[expose] public section



noncomputable section

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace NavierStokesR3.RieszTestOperators

open ProblemStatement ComparisonCutoffs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The product rule with a uniformly bounded spatial cutoff. -/
theorem norm_fderiv_cutoff_smul_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fun y => cutoff R y • f y) x‖ ≤
      ‖fderiv ℝ f x‖ + (derivativeConstant 1 / R) * ‖f x‖ :=
  NavierStokesAndEuler.SobolevThreeDimensional.norm_fderiv_cutoff_smul_le hf hR x

/-- The cutoff derivative has a vanishing `L²` error. -/
theorem eLpNorm_fderiv_cutoff_smul_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) :
    eLpNorm (fderiv ℝ (fun y => cutoff R y • f y)) 2 volume ≤
      eLpNorm (fderiv ℝ f) 2 volume +
        ENNReal.ofReal (derivativeConstant 1 / R) * eLpNorm f 2 volume :=
  NavierStokesAndEuler.SobolevThreeDimensional.eLpNorm_fderiv_cutoff_smul_le hf hR

/-- The homogeneous `H¹ → L⁶` inequality without a support assumption.
Only the function itself must have finite `L²` norm for this extended-norm
inequality; the right side may be infinite. -/
theorem smooth_eLpNorm_six_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume :=
  NavierStokesAndEuler.SobolevThreeDimensional.eLpNorm_six_le hf h2

/-- A smooth function with square-integrable value and derivative belongs to
`L⁶`, with no support hypothesis. -/
theorem smooth_memLp_six {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    MemLp f 6 volume :=
  NavierStokesAndEuler.SobolevThreeDimensional.memLp_six hf h2 hD2

/-- The real-valued homogeneous Sobolev bound when both `L²` norms are finite. -/
theorem smooth_eLpNorm_six_toReal_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    (eLpNorm f 6 volume).toReal ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        (eLpNorm (fderiv ℝ f) 2 volume).toReal :=
  NavierStokesAndEuler.SobolevThreeDimensional.toReal_eLpNorm_six_le hf h2 hD2

end NavierStokesR3.RieszTestOperators
