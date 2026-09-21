/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.FiniteTimeKernelContinuity
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.Kernel

/-!
# Backward `C₀` recursion for finite Feller transitions

An ordered nonempty family of one-coordinate `C₀` factors determines a backward semigroup
recursion: evolve the last factors relative to the first time, multiply by the first factor, and
then evolve from the starting state to the first time.  The recursion varies continuously in the
`C₀` norm when every ordered observation time converges.

This file contains only the analytic recursion and its continuity.  Its identification with an
integral against a finite-time kernel is in `Feller/BackwardC0Integral.lean`; no statement about
path space is proved here.
-/

open Filter Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- Backward semigroup recursion for a nonempty ordered family of coordinatewise `C₀` factors. -/
noncomputable def IsFellerKernelSemigroup.backwardC0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup) :
    {n : ℕ} → FiniteOrderedTimes (n + 1) →
      (Fin (n + 1) → C₀(alpha, ℝ)) → C₀(alpha, ℝ)
  | 0, times, factors => hP.c0Semigroup (times 0) (factors 0)
  | _n + 1, times, factors =>
      hP.c0Semigroup (times 0)
        (factors 0 * hP.backwardC0 times.relativeTail (Fin.tail factors))

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- The backward recursion for a singleton family is one Feller-semigroup application. -/
@[simp]
theorem IsFellerKernelSemigroup.backwardC0_zero
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    (times : FiniteOrderedTimes 1) (factors : Fin 1 → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0) (factors 0) :=
  rfl

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- At a successor length, the backward recursion multiplies the first factor by the recursively
evolved relative tail before applying the first transition. -/
@[simp]
theorem IsFellerKernelSemigroup.backwardC0_succ
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {n : ℕ} (times : FiniteOrderedTimes (n + 2))
    (factors : Fin (n + 2) → C₀(alpha, ℝ)) :
    hP.backwardC0 times factors = hP.c0Semigroup (times 0)
      (factors 0 * hP.backwardC0 times.relativeTail (Fin.tail factors)) :=
  rfl

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- The backward recursion is continuous in the `C₀` norm under coordinatewise convergence of a
nonempty ordered time family. -/
theorem IsFellerKernelSemigroup.tendsto_backwardC0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes (n + 1)}
    {times0 : FiniteOrderedTimes (n + 1)}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun a ↦ hP.backwardC0 (times a) factors) l
      (nhds (hP.backwardC0 times0 factors)) := by
  induction n with
  | zero =>
      simp only [backwardC0_zero]
      exact hP.c0Semigroup.tendsto_apply_of_tendsto (ht 0) tendsto_const_nhds
  | succ n ih =>
      have htail : ∀ i, Tendsto (fun a ↦ (times a).relativeTail i) l
          (nhds (times0.relativeTail i)) := by
        intro i
        simpa only [FiniteOrderedTimes.relativeTail_apply] using
          (ht i.succ).sub (ht 0)
      have hinner := ih htail (Fin.tail factors)
      simp only [backwardC0_succ]
      exact hP.c0Semigroup.tendsto_apply_of_tendsto (ht 0)
        (tendsto_const_nhds.mul hinner)

end SubMarkovKernelSemigroup
end MarkovProcess
