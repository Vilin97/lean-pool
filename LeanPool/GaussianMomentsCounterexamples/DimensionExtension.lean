/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import LeanPool.GaussianMomentsCounterexamples.GaussianMeasure
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.MvPolynomial.Rename

/-! Marginal compatibility for any injective selection of real Gaussian coordinates. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory

namespace GaussianMomentsCounterexamples

theorem continuous_realEval {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    Continuous (realEval P) := by
  exact P.continuous_eval.comp (by fun_prop)

/-- Any injective coordinate selection preserves the standard Gaussian law. -/
theorem gaussianMeasure_marginal {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => x (e i))
      (gaussianMeasure n) (gaussianMeasure k) := by
  have hi : iIndepFun (fun i (x : Fin n → ℝ) => x i) (gaussianMeasure n) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  refine ⟨by fun_prop, ?_⟩
  rw [(hi.precomp he).map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  simp only [gaussianMeasure,
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) _).map_eq]

/-- Renaming into distinct Gaussian coordinates preserves every polynomial expectation. -/
theorem expectation_rename {k n : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (P : MvPolynomial (Fin k) ℂ) :
    expectation (MvPolynomial.rename e P) = expectation P := by
  unfold expectation
  conv_rhs => rw [← (gaussianMeasure_marginal e he).map_eq]
  rw [integral_map (gaussianMeasure_marginal e he).measurable.aemeasurable
    (continuous_realEval P).aestronglyMeasurable]
  simp only [realEval, MvPolynomial.eval_rename, Function.comp_def]

/-- Failure in a smaller dimension propagates to every larger dimension. -/
theorem not_GMC_of_le {k n : ℕ} (hkn : k ≤ n) (hk : ¬ GMC k) : ¬ GMC n := by
  intro hn
  apply hk
  intro P hP Q
  let e : Fin k → Fin n := Fin.castLE hkn
  have he : Function.Injective e := Fin.castLE_injective hkn
  obtain ⟨N, hN⟩ := hn (MvPolynomial.rename e P) (by
    intro m hm
    rw [← map_pow, expectation_rename e he]
    exact hP m hm) (MvPolynomial.rename e Q)
  refine ⟨N, fun m hm => ?_⟩
  have h := hN m hm
  rwa [← map_pow, ← map_mul, expectation_rename e he] at h

end GaussianMomentsCounterexamples
