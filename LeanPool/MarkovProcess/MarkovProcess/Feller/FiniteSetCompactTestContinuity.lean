/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Feller.FiniteTimeJointCompactTestContinuity
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.FiniteSetKernelCompactTestTransport


/-!
# Continuity of finite-set compact-test integrals

Compact-test integrals against a conservative Feller semigroup's finite-set kernel vary
continuously with the starting point. The proof transports the test to increasing coordinates
and applies fixed-time finite-kernel continuity. The empty finite set is included without a
separate nonemptiness assumption.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- A compact-test integral against a finite-set kernel is continuous in the starting point. -/
theorem IsFellerKernelSemigroup.continuous_integral_compactlySupported_finiteSetKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (I : Finset NNReal) (f : C_c(I → alpha, ℝ)) :
    Continuous fun x ↦ ∫ path, f path ∂finiteSetKernel P I x := by
  have h := hFeller.continuous_integral_compactlySupported_finiteTimeKernel hP
    (finiteSetTimes I) (pullbackFiniteSetCompactTest I f)
  simpa only [integral_finiteSetKernel_eq_integral_pullbackFiniteSetCompactTest P I f]
    using h

end MarkovProcess.SubMarkovKernelSemigroup
