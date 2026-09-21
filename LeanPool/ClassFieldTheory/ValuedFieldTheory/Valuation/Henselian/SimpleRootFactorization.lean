/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.CoprimeFactorLifting
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion
/-!
# From simple-root Hensel lifting to valuation factorization

The Henselian ring assumption now supplies the actual coprime factors.
The valuation factorization criterion then extends the monic result to
all primitive polynomials, with the prescribed reductions and degree bounds.
-/

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField

variable {K : Type*} [Field K] (V : ValuationSubring K)
  [HenselianRing V (IsLocalRing.maximalIdeal V)]

/-- The simple-root Henselian condition supplies monic coprime-factor lifting. -/
theorem monicResidualCoprimeFactorLifting_of_henselianRing :
    MonicResidualCoprimeFactorLifting V := by
  intro f gbar hbar hf hgbar hhbar hfac hcop
  obtain ⟨g, h, hg, hh, hgh, _, _, hgmap, hhmap, _⟩ :=
    ValuationTheory.Henselian.exists_coprime_factor_lift
      (I := IsLocalRing.maximalIdeal V) f gbar hbar hf hgbar hhbar hfac hcop
  exact ⟨g, h, hg, hh, hgh, hgmap, hhmap⟩

/-- A Henselian valuation ring satisfies the full primitive factorization
form of Hensel's lemma, without completeness or rank assumptions. -/
theorem henselFactorization_of_henselianRing : HenselFactorizationProperty V :=
  henselianValuationExtension V (monicResidualCoprimeFactorLifting_of_henselianRing V)

end DiscreteValuationField
