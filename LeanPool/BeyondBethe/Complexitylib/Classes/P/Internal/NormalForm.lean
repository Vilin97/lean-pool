/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Defs

/-!
# Polynomial-time normal forms — proof internals

The definitions of `P` and `FP` permit arbitrary time functions with Big-O
power bounds. This module replaces either witness by the evaluation of one
polynomial over the naturals, giving everywhere-valid monotone time bounds.

The public theorem is in `Complexitylib.Classes.P.NormalForm`.
-/


@[expose] public section

namespace Complexity

/-- Internal proof that `P` membership is equivalent to decision within the
evaluation of a natural-coefficient polynomial. -/
theorem mem_P_iff_decidesInTime_polynomial_internal {L : Language} :
    L ∈ P ↔ ∃ (k : ℕ) (tm : TM k) (p : Polynomial ℕ),
      tm.DecidesInTime L p.eval := by
  constructor
  · intro hL
    obtain ⟨d, k, tm, T, hdec, hbig⟩ := Set.mem_iUnion.mp hL
    obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hbig
    exact ⟨k, tm, p, hdec.mono hp⟩
  · rintro ⟨k, tm, p, hdec⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p.natDegree, k, tm, p.eval, hdec, ?_⟩
    exact BigO.of_polynomial_bound p fun _ => le_rfl

/-- Internal proof that `FP` membership is equivalent to computation within
the evaluation of a natural-coefficient polynomial. -/
theorem mem_FP_iff_computesInTime_polynomial_internal
    {f : List Bool → List Bool} :
    f ∈ FP ↔ ∃ (k : ℕ) (tm : TM k) (p : Polynomial ℕ),
      tm.ComputesInTime f p.eval := by
  constructor
  · rintro ⟨d, k, tm, T, hcomp, hbig⟩
    obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hbig
    exact ⟨k, tm, p, hcomp.mono hp⟩
  · rintro ⟨k, tm, p, hcomp⟩
    refine ⟨p.natDegree, k, tm, p.eval, hcomp, ?_⟩
    exact BigO.of_polynomial_bound p fun _ => le_rfl

end Complexity
