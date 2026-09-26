/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OmnificFactorization
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinementProof
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayNormalForm

/-!
# Proofs of factorisation statements for omnific integers

The normal-form equivalence identifies this presentation of `Oz` with the omnific integer
subring. Primality and factorisation therefore pass across the equivalence.
-/

universe u

public noncomputable section

namespace ConwayRefinement.Standalone.Oz

namespace NormalFormIdentifiesOmnificIntegers

/-- Conway's cut definition and the normal-form definition determine the same subring. -/
theorem of_normalForm : Oz.NormalFormIdentifiesOmnificIntegers.{u} := by
  exact normalFormIdentifiesOmnificIntegers

end NormalFormIdentifiesOmnificIntegers

namespace EveryOmnificIntegerIsPrimal

/-- Conway's refinement conjecture implies that every normal-form omnific integer is primal. -/
theorem of_refinement : Oz.EveryOmnificIntegerIsPrimal.{u} := by
  intro x
  have hnative : IsPrimal
      (normalFormRingEquiv x) :=
    (conwayConjecture_iff_forall_isPrimal.mp ConwayConjecture.proof) _
  exact (RingEquiv.isPrimal_iff
    normalFormRingEquiv x).mp hnative

end EveryOmnificIntegerIsPrimal

namespace IrreducibleIsPrime

/-- Every irreducible omnific integer is prime. -/
theorem of_primality : Oz.IrreducibleIsPrime.{u} := by
  intro x hx
  exact hx.prime_of_isPrimal (EveryOmnificIntegerIsPrimal.of_refinement x)

end IrreducibleIsPrime

namespace IrreducibleFactorizationsAreUnique

/-- Irreducible factorisations in `Oz` are unique up to order and units. -/
theorem of_primality : Oz.IrreducibleFactorizationsAreUnique.{u} := by
  intro f g hf hg hfg
  exact prime_factors_unique
    (fun x hx ↦ IrreducibleIsPrime.of_primality x (hf x hx))
    (fun x hx ↦ IrreducibleIsPrime.of_primality x (hg x hx))
    hfg

end IrreducibleFactorizationsAreUnique

end ConwayRefinement.Standalone.Oz
