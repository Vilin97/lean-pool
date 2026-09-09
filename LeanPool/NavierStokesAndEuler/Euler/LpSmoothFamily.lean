/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpDominatedDerivative
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Smooth parameter dependence in actual L² from square-integrable fiberwise jets. -/

noncomputable section


namespace EulerLpSmoothFamily

open MeasureTheory Filter EulerLpDerivative
open scoped ContDiff Topology

universe u v w

variable {X : Type u} [MeasurableSpace X] {P : Type v}
  [NormedAddCommGroup P] [NormedSpace ℝ P] {V : Type w}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual parameter jets on almost every fiber, with one L² majorant per derivative order. -/
structure SmoothFamily (μ : Measure X) (P : Type v) (V : Type w)
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : P → X → V
  smooth : ∀ᵐ x ∂μ, ContDiff ℝ ∞ (fun a => field a x)
  jet : (n : ℕ) → P → Lp (P [×n]→L[ℝ] V) 2 μ
  jet_ae : ∀ n a, jet n a =ᵐ[μ] fun x => iteratedFDeriv ℝ n (fun b => field b x) a
  bound : ℕ → Lp ℝ 2 μ
  bounded : ∀ n, ∀ᵐ x ∂μ, ∀ a, ‖iteratedFDeriv ℝ n (fun b => field b x) a‖ ≤ bound n x

namespace SmoothFamily

variable {μ : Measure X}

def value (A : SmoothFamily μ P V) (a : P) : Lp V 2 μ :=
  (continuousMultilinearCurryFin0 ℝ P V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 μ (A.jet 0 a)

theorem value_ae (A : SmoothFamily μ P V) (a : P) : A.value a =ᵐ[μ] A.field a := by
  filter_upwards [(continuousMultilinearCurryFin0 ℝ P
    V).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
    (A.jet 0 a), A.jet_ae 0 a] with x hx hj
  rw [show A.value a x = continuousMultilinearCurryFin0 ℝ P V (A.jet 0 a x) from hx, hj]
  rw [iteratedFDeriv_zero_eq_comp]
  exact (continuousMultilinearCurryFin0 ℝ P V).apply_symm_apply _

def derivative (A : SmoothFamily μ P V) : SmoothFamily μ P (P →L[ℝ] V) where
  field a x := fderiv ℝ (fun b => A.field b x) a
  smooth := A.smooth.mono (fun _ hx => hx.fderiv_right (m := ∞) (by simp))
  jet n a := (continuousMultilinearCurryRightEquiv' ℝ n P
    V).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 μ (A.jet (n+1) a)
  jet_ae n a := by
    let L : (P [×(n+1)]→L[ℝ] V) →L[ℝ] (P [×n]→L[ℝ] (P →L[ℝ] V)) :=
      (continuousMultilinearCurryRightEquiv' ℝ n P V).toContinuousLinearEquiv.toContinuousLinearMap
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (𝕜 := ℝ) (𝕜' := ℝ)
      (E := P [×(n+1)]→L[ℝ] V) (F := P [×n]→L[ℝ] (P →L[ℝ] V))
      (σ := RingHom.id ℝ) L (A.jet (n+1) a), A.jet_ae (n+1) a] with x hx hj
    rw [hx, hj, iteratedFDeriv_succ_eq_comp_right]
    exact (continuousMultilinearCurryRightEquiv' ℝ n P V).apply_symm_apply _
  bound n := A.bound (n+1)
  bounded n := (A.bounded (n+1)).mono (fun x hx a => by
    simpa only [norm_iteratedFDeriv_fderiv] using hx a)

theorem bound_nonneg (A : SmoothFamily μ P V) (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ A.bound n x :=
  (A.bounded n).mono (fun _ hx => (norm_nonneg _).trans (hx 0))

theorem hasFDerivAt_value (A : SmoothFamily μ P V) (a : P) :
    HasFDerivAt A.value (derivativeMap μ (A.derivative.value a)) a := by
  have hshift : HasFDerivAt (fun b => A.value (b+a))
      (derivativeMap μ (A.derivative.value a)) 0 := by
    apply EulerLpDerivative.hasFDerivAt_of_dominated μ
      (fun b => A.value (b+a)) (fun b x => A.field (b+a) x)
      (fun b => A.value_ae (b+a)) (A.derivative.value a) _ (A.bound 1)
      (Lp.memLp (A.bound 1)) (A.bound_nonneg 1)
    · apply Eventually.of_forall
      intro b
      filter_upwards [A.smooth, A.bounded 1] with x hx hb
      have hd (c : P) : ‖fderiv ℝ (fun d => A.field d x) c‖ ≤ A.bound 1 x := by
        simpa only [norm_iteratedFDeriv_one] using hb c
      have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ) (f := fun c => A.field c x) (s := Set.univ)
        (fun c _ => hx.differentiable (by simp) c) (fun c _ => hd c)
        (convex_univ : Convex ℝ (Set.univ : Set P)) (Set.mem_univ a) (Set.mem_univ (b+a))
      simpa only [zero_add, add_sub_cancel_right] using hh
    · filter_upwards [A.smooth, A.derivative.value_ae a] with x hx hd
      rw [hd]
      change HasFDerivAt (fun b => A.field (b+a) x)
        (fderiv ℝ (fun b => A.field b x) a) (0 : P)
      apply (hasFDerivAt_comp_add_right (f := fun b => A.field b x) a).mpr
      simpa only [zero_add] using (hx.differentiable (by simp) a).hasFDerivAt
  simpa only [zero_add] using (hasFDerivAt_comp_add_right a).mp hshift

theorem fderiv_value (A : SmoothFamily μ P V) :
    fderiv ℝ A.value = fun a => derivativeBundling μ (A.derivative.value a) :=
  funext (fun a => (A.hasFDerivAt_value a).fderiv)

end SmoothFamily

end EulerLpSmoothFamily
