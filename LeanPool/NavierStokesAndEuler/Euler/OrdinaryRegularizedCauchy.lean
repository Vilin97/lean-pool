/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizationError
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryPerturbedEnergy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import Mathlib.Algebra.Order.Star.Real

/-! The true smooth regularized Euler flows are Cauchy in continuous
L² on the common energy-controlled interval. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerSmoothSobolev EulerVolterraConvolution Finset
open scoped ContDiff Topology

/-- Regularized comparison cost, given by `regularizationCost M*Real.sqrt (Real.exp
((2*((360*smoothEmbeddingConstant)*M)+1)*T))`. -/
def regularizedComparisonCost (T M : ℝ) : ℝ :=
  regularizationCost M*Real.sqrt (Real.exp ((2*((360*smoothEmbeddingConstant)*M)+1)*T))

theorem regularizedComparisonCost_nonneg (T M : ℝ) : 0 ≤ regularizedComparisonCost T M :=
  mul_nonneg (regularizationCost_nonneg M) (Real.sqrt_nonneg _)

theorem regularized_l2_comparison {T : ℝ} {hT : 0 ≤ T} {j k : ℕ}
    (U : RegularizedEvolution (regularizer j) T hT)
    (V : RegularizedEvolution (regularizer k) T hT)
    (M : ℝ) (hU : ∀ t, WordBound 4 M (U.velocity t))
    (hV : ∀ t, WordBound 4 M (V.velocity t))
    (hinit : (V.velocity ⟨0, le_rfl, hT⟩).toLp = (U.velocity ⟨0, le_rfl, hT⟩).toLp) :
    ‖fieldPath V.velocity V.velocity_continuous-fieldPath U.velocity U.velocity_continuous‖ ≤
      (regularizerError j+regularizerError k)*regularizedComparisonCost T M := by
  let G := (360*smoothEmbeddingConstant)*M
  let C := 2*G+1
  let E := (regularizerError j+regularizerError k)*regularizationCost M
  have hM : 0 ≤ M := wordBound_nonneg (hU ⟨0,le_rfl,hT⟩)
  have hG : 0 ≤ G := mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hE : 0 ≤ E := mul_nonneg (add_nonneg (regularizerError_nonneg j) (regularizerError_nonneg k))
    (regularizationCost_nonneg M)
  let X (r : ℝ) := ‖(V.velocity (projIcc 0 T hT r)).toLp-(U.velocity (projIcc 0 T hT r)).toLp‖^2
  let X' (r : ℝ) := 2*⟪(V.velocity (projIcc 0 T hT r)).toLp-(U.velocity (projIcc 0 T hT r)).toLp,
    (V.derivative (projIcc 0 T hT r)).toLp-(U.derivative (projIcc 0 T hT r)).toLp⟫_ℝ
  have hc : ContinuousOn X (Icc 0 T) := by
    exact ((((fieldPath V.velocity V.velocity_continuous).continuous.sub
      (fieldPath U.velocity U.velocity_continuous).continuous).comp continuous_projIcc).norm.pow
          2).continuousOn
  have hx0 : X 0=0 := by
    simp only [X,projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
      hinit,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt X (X' r) (Icc 0 T) r := by
    have h := ((V.l2_time ⟨r,hr⟩).sub (U.l2_time ⟨r,hr⟩)).norm_sq
    simpa only [X,X',Pi.sub_apply,projIcc_of_mem hT hr] using h
  have hb (r : ℝ) (_hr : r ∈ Icc 0 T) : X' r ≤ C*X r+E^2 := by
    have h := perturbed_difference_energy (U.velocity (projIcc 0 T hT r))
      (V.velocity (projIcc 0 T hT r)) (U.solenoidal _) (V.solenoidal _)
      (U.derivative (projIcc 0 T hT r)).toLp (V.derivative (projIcc 0 T hT r)).toLp
      G (regularizerError j*regularizationCost M) (regularizerError k*regularizationCost M)
      (wordBound_gradient (wordBound_mono (hU _) (by omega)))
      (regularized_rhs_error j _ (U.solenoidal _) M (hU _))
      (regularized_rhs_error k _ (V.solenoidal _) M (hV _))
    simpa only [X,X',C,E,add_mul] using h
  have hnorm (t : Icc (0 : ℝ) T) :
      ‖(V.velocity t).toLp-(U.velocity t).toLp‖ ≤ E*Real.sqrt (Real.exp (C*T)) := by
    have h := forced_linear_zero_bound T C E hC X X' hc hx0 hd hb t t.property
    simp only [X,projIcc_of_mem hT t.property] at h
    have hs := Real.sq_sqrt ((Real.exp_pos (C*T)).le)
    have he : 0 ≤ E*Real.sqrt (Real.exp (C*T)) := mul_nonneg hE (Real.sqrt_nonneg _)
    nlinarith [norm_nonneg ((V.velocity t).toLp-(U.velocity t).toLp)]
  apply (ContinuousMap.norm_le _ (mul_nonneg
    (add_nonneg (regularizerError_nonneg j) (regularizerError_nonneg k))
    (regularizedComparisonCost_nonneg T M))).mpr
  intro t
  exact (hnorm t).trans_eq (by dsimp [E,C,G,regularizedComparisonCost]; ring)

theorem regularized_cauchy {T : ℝ} {hT : 0 ≤ T}
    (U : ∀ n, RegularizedEvolution (regularizer n) T hT)
    (M : ℝ) (hM : ∀ n t, WordBound 4 M ((U n).velocity t))
    (hinit : ∀ j k, ((U k).velocity ⟨0, le_rfl, hT⟩).toLp = ((U j).velocity ⟨0, le_rfl, hT⟩).toLp) :
    CauchySeq (fun n => fieldPath (U n).velocity (U n).velocity_continuous) := by
  have he : Tendsto (fun n => regularizerError n*regularizedComparisonCost T M) atTop (𝓝 (0 : ℝ))
      := by
    simpa only [zero_mul] using regularizerError_tendsto.mul_const (regularizedComparisonCost T M)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hh : ∀ᶠ n in atTop, regularizerError n*regularizedComparisonCost T M < ε/2 :=
    (tendsto_order.mp he).2 _ (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N,fun j hj k hk => ?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  apply (regularized_l2_comparison (U j) (U k) M (hM j) (hM k) (hinit j k)).trans_lt
  have hj' := hN j hj
  have hk' := hN k hk
  nlinarith

end EulerOrdinarySobolev
