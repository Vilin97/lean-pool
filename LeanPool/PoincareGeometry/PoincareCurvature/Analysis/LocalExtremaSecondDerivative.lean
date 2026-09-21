/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Second derivatives at local extrema

This file records the non-strict second-derivative test in a form suited to
maximum-principle arguments.  Mathlib's strict derivative test proves that a
negative second derivative and a vanishing first derivative force a local
maximum.  Combining that theorem with a local minimum shows that the function
is locally constant and hence that its second derivative cannot be negative.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped Laplacian

/-- The second derivative of a continuous real function is nonnegative at a
local minimum.  No differentiability assumption is needed: Lean's total
`deriv` is zero when the relevant derivative does not exist. -/
theorem IsLocalMin.deriv_deriv_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hcont : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra hnonneg
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge hnonneg
  have hfirst : deriv f x = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax f x :=
    isLocalMax_of_deriv_deriv_neg hneg hfirst hcont
  have hconst : f =ᶠ[nhds x] fun _ : ℝ => f x := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hderiv : deriv f =ᶠ[nhds x] deriv (fun _ : ℝ => f x) := hconst.deriv
  have hzero : deriv (deriv f) x = 0 := by
    calc
      deriv (deriv f) x = deriv (deriv (fun _ : ℝ => f x)) x :=
        Filter.EventuallyEq.deriv_eq hderiv
      _ = 0 := by simp
  linarith

/-- Every diagonal value of the second Fréchet derivative of a `C²` real
function is nonnegative at a local minimum. -/
theorem IsLocalMin.iteratedFDeriv_two_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hmin : IsLocalMin f x)
    (hf : ContDiff ℝ 2 f) (v : E) :
    0 ≤ iteratedFDeriv ℝ 2 f x ![v, v] := by
  let line : ℝ → E := fun t => x + t • v
  have hlineMin : IsLocalMin (f ∘ line) 0 := by
    have hbase : IsLocalMin f (line 0) := by simpa [line] using hmin
    apply hbase.comp_continuous
    fun_prop
  have hlineCont : ContinuousAt (f ∘ line) 0 := by
    exact hf.continuous.continuousAt.comp (by fun_prop)
  have hlineSecond : 0 ≤ deriv (deriv (f ∘ line)) 0 :=
    hlineMin.deriv_deriv_nonneg hlineCont
  let L : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have hshift : ContDiff ℝ 2 (fun y : E => f (x + y)) := by
    fun_prop
  have hcomp := L.iteratedFDeriv_comp_right hshift (0 : ℝ) (i := 2) le_rfl
  have hlineEq :
      iteratedFDeriv ℝ 2 (f ∘ line) 0 ![1, 1] =
        iteratedFDeriv ℝ 2 f x ![v, v] := by
    have happ := congrArg (fun A => A ![1, 1]) hcomp
    simp only [L, Function.comp_def,
      iteratedFDeriv_comp_add_left] at happ
    have harr : (fun i : Fin 2 => ![(1 : ℝ), 1] i • v) = ![v, v] := by
      funext i
      fin_cases i <;> simp
    simpa [line, L, Function.comp_def,
      iteratedFDeriv_comp_add_left, harr] using happ
  rw [← hlineEq]
  have hiter : 0 ≤ iteratedDeriv 2 (f ∘ line) 0 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ,
      show iteratedDeriv 1 (f ∘ line) = deriv (f ∘ line) by
        rw [show (1 : ℕ) = 0 + 1 by decide, iteratedDeriv_succ,
          iteratedDeriv_zero]]
    exact hlineSecond
  rw [iteratedDeriv_eq_iteratedFDeriv] at hiter
  have hone : (fun _ : Fin 2 => (1 : ℝ)) = ![1, 1] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hone] using hiter

/-- The Euclidean Laplacian is nonnegative at a local minimum of a `C²`
real function. -/
theorem IsLocalMin.laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}
    (hmin : IsLocalMin f x) (hf : ContDiff ℝ 2 f) :
    0 ≤ (Δ f) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f]
  exact Finset.sum_nonneg fun i _ =>
    hmin.iteratedFDeriv_two_nonneg hf ((stdOrthonormalBasis ℝ E) i)
