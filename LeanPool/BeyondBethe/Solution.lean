/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Main
public import LeanPool.BeyondBethe.BeyondBethe.PalomarComplexity
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham

/-!
# Proved solution for the Palomar statement

Comparator checks that `Palomar.beyond_bethe_permanent` has exactly the same
type as its counterpart in `Challenge.lean`.  The proof below extracts the
concrete algorithm and its finite-word Turing-machine implementation from the
fully internal theorem `BeyondBethe.theoremOne`, then applies Complexitylib's
formal proof of Cobham's characterization of polynomial time.
-/

@[expose] public section

namespace Palomar

theorem beyond_bethe_permanent :
    ∃ (c : ℝ)
      (alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ)
      (F : List Bool → List Bool),
      BeyondBethe.ApproximationGuarantee alg c ∧
        F ∈ BeyondBethe.PalomarComplexity.CobhamFP ∧
        BeyondBethe.StringRealizes F alg := by
  obtain ⟨spec⟩ := BeyondBethe.theoremOne
  obtain ⟨F, hF, hrealizes⟩ := spec.polynomialTime
  refine ⟨spec.c, spec.alg, F, spec.guarantee, ?_, hrealizes⟩
  apply BeyondBethe.PalomarComplexity.cobhamFP_of_complexity
  rw [Complexity.CobhamFP_eq_FP]
  exact hF

end Palomar
