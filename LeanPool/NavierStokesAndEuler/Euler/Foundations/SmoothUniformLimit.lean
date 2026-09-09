/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Smooth Uniform Limit
-/

@[expose] public section

noncomputable section

namespace EulerSmoothUniformLimit

open Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]

/-- An infinite compatible derivative tower is smooth at every level. -/
theorem contDiff_of_derivative_tower (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hJ : ∀ n x, HasFDerivAt (J n) (L n (J (n + 1) x)) x) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  have hfinite : ∀ k : ℕ, ∀ n, ContDiff ℝ k (J n) := by
    intro k
    induction k with
    | zero =>
      intro n
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun x => (hJ n x).continuousAt))
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hJ n x).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (J n) = fun x => L n (J (n + 1) x) :=
        funext (fun x => (hJ n x).fderiv)
      rw [he]
      exact (L n).contDiff.comp (ih (n + 1))
  intro n
  exact contDiff_infty.mpr (fun k => hfinite k n)

/-- Uniform limits of a compatible smooth derivative tower are again smooth.
This is the completion step for Sobolev mollifications. -/
theorem contDiff_of_uniform_derivative_limits
    (f : ∀ n, ℕ → E → F n) (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hlim : ∀ n, TendstoUniformly (f n) (J n) atTop) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  apply contDiff_of_derivative_tower J L
  intro n x
  have hd := (L n).uniformContinuous.comp_tendstoUniformly (hlim (n + 1))
  exact hasFDerivAt_of_tendstoUniformly hd (hf n) (fun y => (hlim n).tendsto_at y) x

/-- Completeness constructs every limit in a uniformly Cauchy derivative tower;
the limit and all of its compatible derivatives are smooth. -/
theorem exists_smooth_limit_of_uniform_cauchy_tower [∀ n, CompleteSpace (F n)]
    (f : ∀ n, ℕ → E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hC : ∀ n, UniformCauchySeqOn (f n) atTop Set.univ) :
    ∃ J : ∀ n, E → F n,
      (∀ n, TendstoUniformly (f n) (J n) atTop) ∧ (∀ n, ContDiff ℝ ∞ (J n)) := by
  have hp : ∀ n x, ∃ v : F n, Tendsto (fun k => f n k x) atTop (nhds v) := by
    intro n x
    exact cauchy_map_iff_exists_tendsto.mp ((hC n).cauchy_map (Set.mem_univ x))
  choose J hJ using hp
  have hlim : ∀ n, TendstoUniformly (f n) (J n) atTop := by
    intro n
    rw [← tendstoUniformlyOn_univ]
    exact (hC n).tendstoUniformlyOn_of_tendsto (fun x _ => hJ n x)
  exact ⟨J, hlim, contDiff_of_uniform_derivative_limits f J L hf hlim⟩

end EulerSmoothUniformLimit
