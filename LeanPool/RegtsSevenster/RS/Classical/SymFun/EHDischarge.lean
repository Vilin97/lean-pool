/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.HInsert
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.HSubZ

/-!
# Discharge of the `hSub` recurrence hypothesis

The bialternant development is stated over a recurrence for the
guarded complete-homogeneous polynomials; `HInsert.lean` proves it,
so the resolvent identity and the shifted forms hold
unconditionally.
-/

@[expose] public section

namespace RS

/-- The add-one-variable recurrence, discharging the hypothesis the
bialternant development is stated over. -/
theorem hSubRec (k : ℕ) : HSubRec k :=
  fun hj m => hSub_insert hj m

/-- The guarded resolvent, unconditionally. -/
theorem sum_fin_resolvent' {k : ℕ} {A : Finset (Fin k)}
    {j : Fin k} (hj : j ∉ A) (hcard : A.card + 1 = k) (m : ℕ) :
    ∑ r : Fin k,
      (-1 : MvPolynomial (Fin k) ℂ) ^ (r : ℕ) *
        (eSub A r * hSubZ (insert j A) ((m : ℤ) - (r : ℕ))) =
      MvPolynomial.X j ^ m :=
  sum_fin_resolvent (hSubRec k) hj hcard m

end RS
