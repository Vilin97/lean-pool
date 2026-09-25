/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Internal.NormalForm
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Composition

/-!
# Closure of P under FP preimages — proof internals

The preprocessing function and target decider are first normalized to
natural-polynomial time bounds. Their executable sequential composition then
decides the preimage language within the polynomial obtained by composing
those bounds.
-/


@[expose] public section

namespace Complexity

/-- Internal proof that polynomial-time languages are closed under preimages
of polynomial-time string functions. -/
theorem mem_P_preimage_internal {f : List Bool → List Bool} {L : Language}
    (hf : f ∈ FP) (hL : L ∈ P) : f ⁻¹' L ∈ P := by
  obtain ⟨nf, tmF, p, hF⟩ :=
    mem_FP_iff_computesInTime_polynomial_internal.mp hf
  obtain ⟨ng, tmG, q, hG⟩ :=
    mem_P_iff_decidesInTime_polynomial_internal.mp hL
  let r := Polynomial.C 4 * p + Polynomial.C 11 + q.comp p
  apply mem_P_iff_decidesInTime_polynomial_internal.mpr
  refine ⟨TM.compositionTapeCount nf ng, TM.compositionTM tmF tmG, r, ?_⟩
  simpa [r, Polynomial.eval_comp] using
    TM.compositionTM_decidesInTime hF hG (polynomial_eval_mono_nat q)

end Complexity
