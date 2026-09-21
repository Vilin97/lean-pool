/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Incidence.Fibers

/-!
# Small-prime counterexamples to the printed incidence threshold

These kernel-checked examples show that the paper's claim for every prime `p > 10` is false for
the exact admissible auxiliary-point statement used by its diameter-two argument.
-/

namespace BGS.Markoff

local instance {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    Decidable (IsAdmissibleCoordinate a) := by
  unfold IsAdmissibleCoordinate
  infer_instance

local instance {K : Type*} [Field K] [DecidableEq K] (a b y lambda mu : K) :
    Decidable (IncidenceAux a b y lambda mu) := by
  unfold IncidenceAux
  infer_instance

section Prime13

local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem no_admissible_incidenceAux_point_at_thirteen :
    IsAdmissibleCoordinate (1 : ZMod 13) ∧
      IsAdmissibleCoordinate (4 : ZMod 13) ∧
      (1 : ZMod 13) ^ 2 ≠ (4 : ZMod 13) ^ 2 ∧
      ¬ ∃ y lambda mu : ZMod 13,
          IsAdmissibleCoordinate y ∧ IncidenceAux 1 4 y lambda mu := by
  decide

end Prime13

section Prime17

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem no_admissible_incidenceAux_point_at_seventeen :
    IsAdmissibleCoordinate (1 : ZMod 17) ∧
      IsAdmissibleCoordinate (6 : ZMod 17) ∧
      (1 : ZMod 17) ^ 2 ≠ (6 : ZMod 17) ^ 2 ∧
      ¬ ∃ y lambda mu : ZMod 17,
          IsAdmissibleCoordinate y ∧ IncidenceAux 1 6 y lambda mu := by
  decide

end Prime17

end BGS.Markoff
