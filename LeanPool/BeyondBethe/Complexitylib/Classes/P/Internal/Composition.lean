/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics.PolynomialComposition
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Internal.NormalForm
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition

/-!
# Closure of FP under composition — proof internals

This module combines the sequential machine construction with polynomial
normal forms for its two component computations. The public theorem is in
`Complexitylib.Classes.P.Composition`.
-/


public section

namespace Complexity

/-- Internal proof that polynomial-time string functions are closed under
function composition. -/
theorem mem_FP_comp_internal {f g : List Bool → List Bool}
    (hf : f ∈ FP) (hg : g ∈ FP) : (g ∘ f) ∈ FP := by
  obtain ⟨nf, tmF, p, hfComp⟩ :=
    mem_FP_iff_computesInTime_polynomial_internal.mp hf
  obtain ⟨ng, tmG, q, hgComp⟩ :=
    mem_FP_iff_computesInTime_polynomial_internal.mp hg
  refine ⟨(Polynomial.C 4 * p + Polynomial.C 11 + q.comp p).natDegree,
    TM.compositionTapeCount nf ng, TM.compositionTM tmF tmG,
    (fun n => 4 * p.eval n + 11 + q.eval (p.eval n)), ?_, ?_⟩
  · exact TM.compositionTM_computesInTime hfComp hgComp
      (polynomial_eval_mono_nat q)
  · exact BigO.polynomial_composition_time p q

end Complexity
