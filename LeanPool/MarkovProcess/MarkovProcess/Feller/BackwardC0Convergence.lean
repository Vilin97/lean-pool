/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.BackwardC0Integral
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.StrongOperatorLimit

/-!
# Convergence of the backward `C₀` recursion along a family of semigroups

The backward recursion of `Feller/BackwardC0Recursion.lean` evolves a nonempty ordered family of
one-coordinate `C₀` factors through the transitions of one Feller kernel semigroup.  Here the
family of times and the factors are held fixed and the *semigroup* varies along a filter: if the
`C₀` semigroups converge strongly, so does the backward recursion, in the `C₀` norm.  The
induction is one line per step: contractivity makes the outer transition insensitive to the
error accumulated by the inner one.

Since the `C₀` norm is the supremum norm, this is exactly convergence of the coordinate-product
integrals against the finite-time kernels, uniformly in the starting point.

Main results: `tendsto_backwardC0_of_tendsto_c0Semigroup`,
`tendstoUniformly_integral_coordinateProduct_finiteTimeKernel`.

The factors and the observation times are fixed; nothing is asserted when they vary along the
filter as well, and no rate of convergence is claimed.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess

section Uniform

variable {alpha : Type*} [TopologicalSpace alpha] {iota : Type*} {l : Filter iota}

/-- Convergence in the `C₀` norm is uniform convergence of the evaluated functions. -/
theorem tendstoUniformly_apply_of_tendsto {F : iota → C₀(alpha, ℝ)} {f : C₀(alpha, ℝ)}
    (h : Tendsto F l (nhds f)) : TendstoUniformly (fun i x ↦ F i x) (fun x ↦ f x) l :=
  ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.mp h

end Uniform

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- **Strong convergence of the `C₀` semigroups propagates through the backward recursion.**
For a fixed nonempty ordered family of times and fixed one-coordinate factors, the backward
recursions of a family of Feller kernel semigroups converge in the `C₀` norm to the backward
recursion of the limit semigroup. -/
theorem tendsto_backwardC0_of_tendsto_c0Semigroup
    {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hQ : Q.IsFellerKernelSemigroup)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun i ↦ (hP i).backwardC0 times factors) l
      (nhds (hQ.backwardC0 times factors)) := by
  induction n with
  | zero =>
      simpa only [IsFellerKernelSemigroup.backwardC0_zero] using hconv (times 0) (factors 0)
  | succ n ih =>
      simp only [IsFellerKernelSemigroup.backwardC0_succ]
      exact Semigroup.tendsto_apply_of_opNorm_le_one
        (fun i ↦ (hP i).c0Semigroup (times 0)) (hQ.c0Semigroup (times 0))
        (fun i ↦ factors 0 * (hP i).backwardC0 times.relativeTail (Fin.tail factors))
        (factors 0 * hQ.backwardC0 times.relativeTail (Fin.tail factors))
        (fun i ↦ ((hP i).c0Semigroup).norm_operator_le_one _) (hconv (times 0) _)
        (tendsto_const_nhds.mul (ih times.relativeTail (Fin.tail factors)))

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- **Uniform convergence of the coordinate-product integrals.**  Strong convergence of the `C₀`
semigroups makes the finite-time integral of a product of one-coordinate `C₀` functions converge
uniformly in the starting point. -/
theorem tendstoUniformly_integral_coordinateProduct_finiteTimeKernel
    {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hQ : Q.IsFellerKernelSemigroup)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    TendstoUniformly
      (fun i x ↦ ∫ path, ∏ j, factors j (path j) ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, ∏ j, factors j (path j) ∂finiteTimeKernel Q times x) l := by
  have h := tendstoUniformly_apply_of_tendsto
    (tendsto_backwardC0_of_tendsto_c0Semigroup hP hQ hconv times factors)
  simpa only [IsFellerKernelSemigroup.backwardC0_apply_eq_integral_finiteTimeKernel] using h

end SubMarkovKernelSemigroup

end MarkovProcess
