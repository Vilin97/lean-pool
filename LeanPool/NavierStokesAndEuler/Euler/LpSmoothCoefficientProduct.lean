/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPathMap
public import LeanPool.NavierStokesAndEuler.Euler.LpOperatorField
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual smooth L² multiplication by bounded smooth coefficients

The coefficient derivatives are genuine uniform-norm jets. The product
derivatives are actual Fréchet derivatives, proved square integrable by the
Leibniz estimate. The derivative identity remains a literal function equality.
-/

@[expose] public section


noncomputable section

namespace EulerLpSmoothCoefficientProduct

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLpTranslation EulerLpTranslation.SmoothL2Field Filter
open scoped ContDiff BoundedContinuousFunction

universe u v
variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
  {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem product_memLp (A : SmoothCoefficientPath K (V →L[ℝ] W)) (t : K)
    (f : SmoothL2Field V) (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n (fun x => A.field t x (f.field x))) 2 volume := by
  let g : ℕ → Space → ℝ := fun i x =>
    ((n.choose i : ℝ)*‖A.jet i t‖)*‖iteratedFDeriv ℝ (n-i) f.field x‖
  have hg (i : ℕ) : MemLp (g i) 2 volume :=
    (f.integrable (n-i)).norm.const_mul _
  have hsum : MemLp (∑ i ∈ Finset.range (n+1), g i) 2 volume :=
    memLp_finsetSum' _ (fun i _ => hg i)
  have hm : AEStronglyMeasurable
      (iteratedFDeriv ℝ n (fun x => A.field t x (f.field x))) volume :=
    (((A.smooth t).clm_apply f.smooth).continuous_iteratedFDeriv (m := n) (by
        simp)).aestronglyMeasurable
  apply hsum.mono' hm
  apply Eventually.of_forall
  intro x
  apply (norm_iteratedFDeriv_clm_apply (A.smooth t) f.smooth x (by simp : (n : ℕ∞ω) ≤ ∞)).trans
  simp only [Finset.sum_apply, g]
  apply Finset.sum_le_sum
  intro i _
  have hA : ‖iteratedFDeriv ℝ i (A.field t : Space → V →L[ℝ] W) x‖ ≤ ‖A.jet i t‖ := by
    rw [← A.jet_eq]
    exact (A.jet i t).norm_coe_le_norm x
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)) (norm_nonneg
      _)

/-- Product, bundling `field`, `smooth`, `integrable`. -/
def product (A : SmoothCoefficientPath K (V →L[ℝ] W)) (t : K)
    (f : SmoothL2Field V) : SmoothL2Field W where
  field x := A.field t x (f.field x)
  smooth := (A.smooth t).clm_apply f.smooth
  integrable := product_memLp A t f

@[simp] theorem product_field (A : SmoothCoefficientPath K (V →L[ℝ] W)) (t : K)
    (f : SmoothL2Field V) (x : Space) : (product A t f).field x = A.field t x (f.field x) := rfl

theorem product_toLp (A : SmoothCoefficientPath K (V →L[ℝ] W)) (t : K)
    (f : SmoothL2Field V) :
    (product A t f).toLp = EulerLpOperatorField.full volume (A.field t) f.toLp := by
  apply Lp.ext
  filter_upwards [(product A t f).toLp_ae,
    EulerLpOperatorField.full_ae volume (A.field t) f.toLp, f.toLp_ae] with x h₁ h₂ h₃
  exact h₁.trans ((congrArg (A.field t x) h₃).symm.trans h₂.symm)

/-- Left derivative, given by `SmoothCoefficientPath.map (flipₗᵢ ℝ Space V
W).toContinuousLinearEquiv.toContinuousLinearMap A.derivative`. -/
def leftDerivative (A : SmoothCoefficientPath K (V →L[ℝ] W)) :
    SmoothCoefficientPath K (V →L[ℝ] (Space →L[ℝ] W)) :=
  SmoothCoefficientPath.map (flipₗᵢ ℝ Space V W).toContinuousLinearEquiv.toContinuousLinearMap
      A.derivative

/-- Right derivative, given by `SmoothCoefficientPath.map (compL ℝ Space V W) A`. -/
def rightDerivative (A : SmoothCoefficientPath K (V →L[ℝ] W)) :
    SmoothCoefficientPath K ((Space →L[ℝ] V) →L[ℝ] (Space →L[ℝ] W)) :=
  SmoothCoefficientPath.map (compL ℝ Space V W) A

theorem product_derivative_field (A : SmoothCoefficientPath K (V →L[ℝ] W)) (t : K)
    (f : SmoothL2Field V) :
    (product A t f).derivative.field =
      (addField (product (rightDerivative A) t f.derivative)
        (product (leftDerivative A) t f)).field := by
  funext x
  have hd := ((A.smooth t).differentiable (by simp) x).hasFDerivAt.clm_apply
    (f.smooth.differentiable (by simp) x).hasFDerivAt
  apply ContinuousLinearMap.ext
  intro w
  have he := congrArg (fun D : Space →L[ℝ] W => D w) hd.fderiv
  have hflip (D : Space →L[ℝ] V →L[ℝ] W) (v : V) (a : Space) :
      (flipₗᵢ ℝ Space V W).toContinuousLinearEquiv.toContinuousLinearMap D v a = D a v := rfl
  simpa only [product, addField_field, SmoothL2Field.derivative,
    leftDerivative, rightDerivative, SmoothCoefficientPath.map_apply,
    SmoothCoefficientPath.derivative, SmoothCoefficientPath.derivativeField_eq,
    hflip, flip_apply, compL_apply, comp_apply, add_apply] using he

theorem jetLp_congr (f g : SmoothL2Field V) (h : f.field = g.field) (n : ℕ) :
    f.jetLp n = g.jetLp n := by
  apply Lp.ext
  filter_upwards [f.jetLp_ae n, g.jetLp_ae n] with x h₁ h₂
  rw [h₁, h₂, h]

theorem product_derivative_jetLp (A : SmoothCoefficientPath K (V →L[ℝ] W)) (t : K)
    (f : SmoothL2Field V) (n : ℕ) :
    (product A t f).derivative.jetLp n =
      (product (rightDerivative A) t f.derivative).jetLp n +
        (product (leftDerivative A) t f).jetLp n :=
  (jetLp_congr _ _ (product_derivative_field A t f) n).trans (jetLp_addField _ _ n)

end EulerLpSmoothCoefficientProduct
