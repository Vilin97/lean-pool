/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientProduct

@[expose] public section

/-!
# Continuity of actual L² product jets

The ordinary derivative product rule reduces each spatial order to lower
orders with differentiated bounded coefficients. This proves continuity of
the genuine L² jets, including for operator-valued derivatives.
-/

noncomputable section

namespace EulerLpSmoothCoefficientProduct

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLpTranslation EulerLpTranslation.SmoothL2Field Filter
open scoped ContDiff BoundedContinuousFunction

universe u v
variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
  {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem jetLp_zero_from_value (f : SmoothL2Field V) :
    f.jetLp 0 =
      (continuousMultilinearCurryFin0 ℝ Space
        V).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
        2 volume f.toLp := by
  let L : V →L[ℝ] (Space [×0]→L[ℝ] V) :=
    (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  apply Lp.ext
  filter_upwards [f.jetLp_ae 0, L.coeFn_compLpL f.toLp, f.toLp_ae] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, iteratedFDeriv_zero_eq_comp]
  rfl

theorem jetLp_succ_from_derivative (f : SmoothL2Field V) (n : ℕ) :
    f.jetLp (n+1) =
      (continuousMultilinearCurryRightEquiv' ℝ n Space
        V).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
        2 volume (f.derivative.jetLp n) := by
  let L : (Space [×n]→L[ℝ] (Space →L[ℝ] V)) →L[ℝ] (Space [×(n+1)]→L[ℝ] V) :=
    (continuousMultilinearCurryRightEquiv' ℝ n Space
      V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  apply Lp.ext
  filter_upwards [f.jetLp_ae (n+1),
    ContinuousLinearMap.coeFn_compLpL (𝕜 := ℝ) (𝕜' := ℝ)
      (E := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (F := Space [×(n+1)]→L[ℝ] V)
      (σ := RingHom.id ℝ) L (f.derivative.jetLp n), f.derivative.jetLp_ae n] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, iteratedFDeriv_succ_eq_comp_right]
  rfl

theorem continuous_product_value (A : SmoothCoefficientPath K (V →L[ℝ] W))
    (f : K → SmoothL2Field V) (hf : Continuous (fun t => (f t).jetLp 0)) :
    Continuous (fun t => (product A t (f t)).toLp) := by
  have hm : Continuous (fun t => EulerLpOperatorField.full volume (A.field t)) :=
    (EulerLpOperatorField.fullMap (E := V) (F := W) volume).continuous.comp A.field.continuous
  have he : (fun t => (product A t (f t)).toLp) =
      fun t => EulerLpOperatorField.full volume (A.field t) (f t).toLp :=
    funext (fun t => product_toLp A t (f t))
  rw [he]
  exact hm.clm_apply (continuous_toLp f hf)

private theorem continuous_product_jet_aux (n : ℕ) :
    ∀ (V W : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W]
      (A : SmoothCoefficientPath K (V →L[ℝ] W)) (f : K → SmoothL2Field V),
      (∀ k, Continuous (fun t => (f t).jetLp k)) →
      Continuous (fun t => (product A t (f t)).jetLp n) := by
  induction n with
  | zero =>
    intro V W _ _ _ _ A f hf
    have he : (fun t => (product A t (f t)).jetLp 0) =
        fun t => (continuousMultilinearCurryFin0 ℝ Space
          W).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
          2 volume (product A t (f t)).toLp :=
      funext (fun t => jetLp_zero_from_value (product A t (f t)))
    rw [he]
    exact ContinuousLinearMap.continuous _ |>.comp (continuous_product_value A f (hf 0))
  | succ n ih =>
    intro V W _ _ _ _ A f hf
    have hright := ih (Space →L[ℝ] V) (Space →L[ℝ] W) (rightDerivative A)
      (fun t => (f t).derivative) (continuous_jetLp_derivative f hf)
    have hleft := ih V (Space →L[ℝ] W) (leftDerivative A) f hf
    have hd : Continuous (fun t => (product A t (f t)).derivative.jetLp n) := by
      have he : (fun t => (product A t (f t)).derivative.jetLp n) =
          (fun t => (product (rightDerivative A) t (f t).derivative).jetLp n)+
            (fun t => (product (leftDerivative A) t (f t)).jetLp n) :=
        funext (fun t => product_derivative_jetLp A t (f t) n)
      rw [he]
      exact hright.add hleft
    have he : (fun t => (product A t (f t)).jetLp (n+1)) =
        fun t => (continuousMultilinearCurryRightEquiv' ℝ n Space
          W).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
          2 volume ((product A t (f t)).derivative.jetLp n) :=
      funext (fun t => jetLp_succ_from_derivative (product A t (f t)) n)
    rw [he]
    exact ContinuousLinearMap.continuous _ |>.comp hd

/-- Every actual product jet is continuous in L², with no product-regularity hypothesis. -/
theorem continuous_product_jet (A : SmoothCoefficientPath K (V →L[ℝ] W))
    (f : K → SmoothL2Field V) (hf : ∀ n, Continuous (fun t => (f t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (product A t (f t)).jetLp n) :=
  continuous_product_jet_aux n V W A f hf

end EulerLpSmoothCoefficientProduct
