/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralBivariateAffineHasseWeil
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExceptionalPrimeCount

/-!
# Unconditional BGS assembly

The closed function-field Hasse--Weil theorem now supplies the general affine
plane-curve estimate used by the split, nonsplit, and cage arguments.  These
short wrappers close the final parameter of the existing BGS assembly.
-/

namespace BGS.Markoff

/-- **BGS Theorem 1**, with both Corvaja--Zannier and affine Hasse--Weil
discharged in the repository. -/
theorem theoremOneStatement : TheoremOneStatement :=
  theoremOneStatement_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

/-- The eventual form of BGS Conjecture 1: strong approximation holds at
every sufficiently large prime. -/
theorem eventually_strongApproximationAt :
    ∃ p0 : ℕ, ∀ (p : ℕ), p.Prime → p0 ≤ p → StrongApproximationAt p :=
  eventually_strongApproximationAt_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

/-- **BGS Theorem 2**, obtained from the unconditional Theorem 1 and Chen's
orbit-divisibility theorem, using Martin's later elementary proof. -/
theorem theoremTwoStatement : TheoremTwoStatement :=
  theoremTwoStatement_of_generalHasseWeil
    BGS.HasseWeil.generalBivariateAffineHasseWeilTheorem

end BGS.Markoff
