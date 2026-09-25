/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.StrictStatements
public import LeanPool.ParameterFreeGradient.V7.LowerBoundStatements
public import LeanPool.ParameterFreeGradient.V7.ControllerStatements

/-!
The regime-dependent query rate and the main parameter-free convergence statement.
-/

@[expose] public section

namespace V7

/-- The regime-dependent main complexity rate, including the logarithmic smoothness-search cost. -/
noncomputable def CurrentMainRate (p Cp C Kbar L M0 : ℝ) : ℝ :=
  if p < 2 then
    Cp * Kbar ^ (1 / 2 : ℝ) + Cp * Real.log (Real.exp 1 + L / M0)
  else if p = 2 then
    C * Kbar ^ (1 / 2 : ℝ) + C * Real.log (Real.exp 1 + L / M0)
  else
    Cp * Kbar ^ (p / (p + 2)) + Cp * Real.log (Real.exp 1 + L / M0)

/-- G03 and `thm:main`: one runtime-`p` method family is selected first;
the universal Euclidean constant precedes `p`, while `Cp` is selected after
`p` and before dimension or instance data. -/
noncomputable def MainStatement : Prop :=
  ∃ family : RuntimeMethodFamily,
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℝ), 1 < p →
        ∃ Cp : ℝ, 0 < Cp ∧
          ∀ (d : ℕ) (input : MethodInput d),
            input.p = p → 0 < input.eps → 0 < input.M0 →
            ∀ inst : PositiveInstance p d input.x0,
              SecantInitialization input inst.oracle →
              input.M0 ≤ inst.L →
              ∃ run : PairRunResult d,
                let Kbar := conditionBar inst input.eps
                Executes (family d) input inst.oracle run ∧
                TraceExact inst.oracle run.trace ∧
                run.trace ≠ [] ∧
                run.trace.head?.map O3.Observation.point = some input.x0 ∧
                run.returnedWasQueried ∧
                lpNorm (conjugateExponent p) (inst.oracle.gradient run.returned) ≤ input.eps ∧
                (run.postInitializationCallCount : ℝ) ≤
                  CurrentMainRate p Cp C Kbar inst.L input.M0

end V7
