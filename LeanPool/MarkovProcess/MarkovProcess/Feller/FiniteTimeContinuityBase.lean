/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Feller.FiniteTimeKernelContinuity
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.Kernel


/-!
# Singleton finite-time Feller continuity

For a one-coordinate finite-time kernel, evaluation at the unique coordinate recovers the
transition kernel at that time.  Feller continuity therefore gives convergence of its `C₀` test
integrals as the observation time varies.  This is the base case for a recursive finite-time
continuity argument; no higher-dimensional continuity is asserted here.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha X : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- Kernel integrals of `C₀` tests against singleton finite-time laws vary continuously with the
unique observation time. -/
theorem IsFellerKernelSemigroup.tendsto_kernelIntegral_finiteTimeKernel_one_map_eval
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {l : Filter X} {times : X → FiniteOrderedTimes 1}
    {times0 : FiniteOrderedTimes 1}
    (ht : Tendsto (fun a ↦ times a 0) l (nhds (times0 0)))
    (f : C₀(alpha, ℝ)) (x : alpha) :
    Tendsto (fun a ↦ kernelIntegral
        ((finiteTimeKernel P (times a)).map (fun path ↦ path 0)) f x)
      l (nhds (kernelIntegral
        ((finiteTimeKernel P times0).map (fun path ↦ path 0)) f x)) := by
  simp_rw [finiteTimeKernel_one_map_eval]
  exact hP.tendsto_kernelIntegral_c0 ht tendsto_const_nhds x

end SubMarkovKernelSemigroup
end MarkovProcess
