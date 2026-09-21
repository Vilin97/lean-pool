/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Containment.Internal

/-!
# TM-to-RAM time-class containment

The fixed sparse simulator transfers deterministic Turing deciders to
logarithmic-cost RAM deciders through the public input/output ABI. Polynomial
Turing time is therefore contained in polynomial RAM time.
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- A deterministic TM time bound transfers to the fixed compiled sparse RAM
simulator through the complete public input/output ABI. -/
theorem compiledDecision_decidesInTime
    {tm : TM n} {L : Language} {T : ℕ → ℕ}
    (hdecides : tm.DecidesInTime L T) :
    (compiledDecision tm).DecidesInTime L
      (fun inputLength => decisionTimeBound tm inputLength (T inputLength)) :=
  compiledDecision_decidesInTime_internal hdecides

/-- The explicit transferred bound packages the fixed simulator as a member of
the corresponding RAM time class. -/
theorem mem_DTIME_of_decidesInTime
    {tm : TM n} {L : Language} {T : ℕ → ℕ}
    (hdecides : tm.DecidesInTime L T) :
    L ∈ RAM.DTIME (fun inputLength =>
      decisionTimeBound tm inputLength (T inputLength)) :=
  mem_DTIME_of_decidesInTime_internal hdecides

/-- Every polynomial-time Turing language is decidable in polynomial
logarithmic-cost RAM time. -/
theorem P_subset_RAM_P : Complexity.P ⊆ RAM.P :=
  P_subset_internal

/-- Every fixed polynomial Turing-time class embeds into polynomial RAM time. -/
theorem DTIME_pow_subset_RAM_P (degree : ℕ) :
    Complexity.DTIME (· ^ degree) ⊆ RAM.P := by
  intro L hL
  apply P_subset_RAM_P
  exact Set.mem_iUnion.mpr ⟨degree, hL⟩

end Sparse

end TMConfig

end RAM

end Complexity
