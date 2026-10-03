/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine

/-!
# Exact-run decomposition — proof internals

These small deterministic-run lemmas expose configurations at chosen time
indices. They support the finite reduced-configuration argument without adding
execution choices to the machine model.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Split an exact run at a prescribed prefix length. -/
theorem reachesIn_split_internal {tm : TM n} {a b : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn (a + b) c c') :
    ∃ d, tm.reachesIn a c d ∧ tm.reachesIn b d c' := by
  induction a generalizing c with
  | zero =>
      exact ⟨c, .zero, by simpa using hreach⟩
  | succ a ih =>
      have hlength : Nat.succ a + b = (a + b) + 1 := by omega
      rw [hlength] at hreach
      cases hreach with
      | step hstep hrest =>
          obtain ⟨d, hprefix, hsuffix⟩ := ih hrest
          exact ⟨d, .step hstep hprefix, hsuffix⟩

/-- Expose the configuration at time `i` of an exact `t`-step run. -/
theorem reachesIn_prefix_internal {tm : TM n} {t i : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') (hi : i ≤ t) :
    ∃ d, tm.reachesIn i c d ∧ tm.reachesIn (t - i) d c' := by
  have hlength : i + (t - i) = t := Nat.add_sub_of_le hi
  rw [← hlength] at hreach
  exact reachesIn_split_internal hreach

end TM

end Complexity
