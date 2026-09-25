/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.PrivateFamily
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface

/-!
# The curve base case

This file implements blueprint node **C08** of the lower-bound side of the sharp finite-field
Nikodym exponent.

Let `P : PrivateFamily F d E` be a private family of lines over the finite field `F`, with line
ideals `P.lineIdeal e` in `P_d = MvPolynomial (Fin d) K` for a field extension `K` of `F`, and let
`I` be a prime ideal of quotient dimension at most one containing every line of the family
(`∀ e, I ≤ P.lineIdeal e`). Then

* `PrivateFamily.eq_lineIdeal_of_quotDim_le_one`: `I` is the ideal of each line of the family;
* `PrivateFamily.card_le_one_of_quotDim_le_one`: the family has at most one line, `L ≤ 1`;
* `PrivateFamily.degree_eq_one_of_quotDim_le_one`: if the family is nonempty, `deg I = 1`;
* `PrivateFamily.card_le_degree_of_quotDim_le_one`: `L ≤ deg I`.

The algebraic input is `eq_lineIdeal_of_le_of_quotDim_le_one` (a prime of quotient dimension at
most one containing a line ideal is that line ideal), proved unconditionally in
`Nikodym.LowerBound.Algebra.Interface`; no `AlgebraInterface` hypothesis is needed. The
combinatorial input is the injectivity of `e ↦ P.lineIdeal e` (node F05).
-/

@[expose] public section

namespace Nikodym.LowerBound

namespace PrivateFamily

variable {K : Type*} [Field K] {d : ℕ}
variable {F : Type*} [Field F] {E : Type*} [Fintype E] [Algebra F K] (P : PrivateFamily F d E)

/-- Blueprint C08: a prime `I` of quotient dimension at most one containing the `e`-th line of
the family is the ideal of that line. -/
theorem eq_lineIdeal_of_quotDim_le_one {I : Ideal (MvPolynomial (Fin d) K)} [I.IsPrime]
    (hdim : quotDim I ≤ 1) (e : E) (hle : I ≤ P.lineIdeal (K := K) e) : I = P.lineIdeal e :=
  eq_lineIdeal_of_le_of_quotDim_le_one hdim (liftPt_ne_zero (P.v_ne_zero e)) hle

/-- Blueprint C08: a private family of lines contained in a prime of quotient dimension at most
one has at most one line: all its line ideals equal `I`, and `e ↦ P.lineIdeal e` is injective. -/
theorem card_le_one_of_quotDim_le_one {I : Ideal (MvPolynomial (Fin d) K)} [I.IsPrime]
    (hdim : quotDim I ≤ 1) (hI : ∀ e, I ≤ P.lineIdeal (K := K) e) : Fintype.card E ≤ 1 :=
  Fintype.card_le_one_iff.mpr fun e f ↦ P.lineIdeal_injective (K := K) <|
    (P.eq_lineIdeal_of_quotDim_le_one hdim e (hI e)).symm.trans
      (P.eq_lineIdeal_of_quotDim_le_one hdim f (hI f))

/-- Blueprint C08: a prime of quotient dimension at most one containing a nonempty private family
of lines has degree one, being the ideal of a line. -/
theorem degree_eq_one_of_quotDim_le_one {I : Ideal (MvPolynomial (Fin d) K)} [I.IsPrime]
    (hdim : quotDim I ≤ 1) [Nonempty E] (hI : ∀ e, I ≤ P.lineIdeal (K := K) e) :
    degree I = 1 := by
  obtain ⟨e⟩ := ‹Nonempty E›
  rw [P.eq_lineIdeal_of_quotDim_le_one hdim e (hI e)]
  exact degree_lineIdeal _ (liftPt_ne_zero (P.v_ne_zero e))

/-- Blueprint C08: for a prime `I` of quotient dimension at most one containing a private family
of `L = Fintype.card E` lines, `L ≤ deg I`. -/
theorem card_le_degree_of_quotDim_le_one {I : Ideal (MvPolynomial (Fin d) K)} [I.IsPrime]
    (hdim : quotDim I ≤ 1) (hI : ∀ e, I ≤ P.lineIdeal (K := K) e) :
    Fintype.card E ≤ degree I := by
  rcases isEmpty_or_nonempty E with hE | hE
  · rw [Fintype.card_eq_zero_iff.mpr hE]
    exact Nat.zero_le _
  · rw [P.degree_eq_one_of_quotDim_le_one hdim hI]
    exact P.card_le_one_of_quotDim_le_one hdim hI

end PrivateFamily

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
