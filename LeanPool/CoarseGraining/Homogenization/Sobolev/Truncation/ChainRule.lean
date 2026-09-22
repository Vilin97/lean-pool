/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Definitions
import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import Mathlib.Analysis.Calculus.MeanValue

/-! # Chain Rule -/

namespace Homogenization

open Homogenization MeasureTheory

/-!
# C¹ chain-rule building blocks for `H¹`

Reusable sub-lemmas for the mollification chain rule: the pointwise `fderiv`
chain-rule identity in coordinate form, the `L²` bound on a Lipschitz
composition, and Lipschitz continuity from a derivative bound.  These are the
pieces the chain-rule argument threads together with the `L²` convergence of
`convexApproxSmoothing`.
-/

/-- Lipschitz continuity of a real function from a bound on its derivative. -/
theorem lipschitzWith_of_abs_deriv_le {G : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hG : Differentiable ℝ G) (hderiv : ∀ t, |deriv G t| ≤ M) :
    LipschitzWith M.toNNReal G := by
  apply lipschitzWith_of_nnnorm_deriv_le hG
  intro t
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM, Real.norm_eq_abs]
  exact hderiv t

/-- Coordinate form of the chain rule: the `i`-th partial of `G ∘ w` is
`G'(w)·∂ᵢw`. -/
theorem fderiv_comp_basisVec {d : ℕ} {G : ℝ → ℝ} {w : Vec d → ℝ} {x : Vec d}
    {i : Fin d} (hG : DifferentiableAt ℝ G (w x)) (hw : DifferentiableAt ℝ w x) :
    (fderiv ℝ (fun y => G (w y)) x) (basisVec i)
      = deriv G (w x) * (fderiv ℝ w x) (basisVec i) := by
  have hcomp : HasFDerivAt (fun y => G (w y))
      ((fderiv ℝ G (w x)).comp (fderiv ℝ w x)) x :=
    (hG.hasFDerivAt).comp x hw.hasFDerivAt
  rw [hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, mul_comm]

/-- The unconditional integral `L²` bound for a Lipschitz composition: `‖G∘f − G∘g‖_{L²} ≤ M‖f − g‖_{L²}`. -/
theorem eLpNormPrime_comp_sub_le_of_lipschitz {d : ℕ} {U : Set (Vec d)} {G : ℝ → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hLip : LipschitzWith M.toNNReal G) (f g : Vec d → ℝ) :
    eLpNorm' (fun x => G (f x) - G (g x)) 2 (volumeMeasureOn U)
      ≤ ENNReal.ofReal M * eLpNorm' (fun x => f x - g x) 2 (volumeMeasureOn U) := by
  have hpt : ∀ x, ‖G (f x) - G (g x)‖ ≤ ‖M • (f x - g x)‖ := by
    intro x
    have hd := hLip.dist_le_mul (f x) (g x)
    rw [norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg hM]
    simpa [Real.dist_eq, Real.coe_toNNReal M hM] using hd
  calc eLpNorm' (fun x => G (f x) - G (g x)) 2 (volumeMeasureOn U)
      ≤ eLpNorm' (fun x => M • (f x - g x)) 2 (volumeMeasureOn U) :=
        eLpNorm'_mono_ae (by norm_num) (Filter.Eventually.of_forall hpt)
    _ = ENNReal.ofReal M * eLpNorm' (fun x => f x - g x) 2 (volumeMeasureOn U) := by
        rw [show (fun x => M • (f x - g x)) = (M • fun x => f x - g x) from rfl,
          eLpNorm'_const_smul M (by norm_num)]
        simp [Real.enorm_eq_ofReal hM]

/-- The same Lipschitz bound in Mathlib's measurable `L²` convention. -/
theorem eLpNorm_comp_sub_le_of_lipschitz {d : ℕ} {U : Set (Vec d)} {G : ℝ → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hLip : LipschitzWith M.toNNReal G) (f g : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volumeMeasureOn U))
    (hg : AEStronglyMeasurable g (volumeMeasureOn U)) :
    eLpNorm (fun x => G (f x) - G (g x)) 2 (volumeMeasureOn U)
      ≤ ENNReal.ofReal M * eLpNorm (fun x => f x - g x) 2 (volumeMeasureOn U) := by
  have hcomp : AEStronglyMeasurable (fun x => G (f x) - G (g x)) (volumeMeasureOn U) :=
    (hLip.continuous.comp_aestronglyMeasurable hf).sub
      (hLip.continuous.comp_aestronglyMeasurable hg)
  have hsub : AEStronglyMeasurable (fun x => f x - g x) (volumeMeasureOn U) := hf.sub hg
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hcomp,
    eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hsub]
  simpa only [ENNReal.toReal_ofNat] using
    eLpNormPrime_comp_sub_le_of_lipschitz hM hLip f g

end Homogenization
