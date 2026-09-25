/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.EvenSignOrbitDivisibility
public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.NonparabolicComplementFrontier

/-!
# Even-sign divisibility for component complements

This file specializes the free even-sign action to the finite complement used
by the nonparabolic complement frontier.
-/

@[expose] public section

namespace BGS.Markoff

/-- An even-sign-invariant component complement has cardinality divisible by
four. The hypothesis is stated in the same form as the complement frontier's
`hsign` input. -/
theorem four_dvd_puncturedComponentComplementFinset_card_of_evenSign_invariant
    (p : ℕ) [Fact p.Prime] (hpThree : 3 < p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hsign : ∀ (s : EvenSign)
        (x : PuncturedMarkoffSurface (ZMod p)),
      s • x ∈ puncturedComponentComplementFinset p c ↔
        x ∈ puncturedComponentComplementFinset p c) :
    4 ∣ (puncturedComponentComplementFinset p c).card := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hpDvd
  exact four_dvd_finset_card_of_evenSign_invariant htwo
    (puncturedComponentComplementFinset p c)
    (fun s x hx => (hsign s x).2 hx)

end BGS.Markoff
