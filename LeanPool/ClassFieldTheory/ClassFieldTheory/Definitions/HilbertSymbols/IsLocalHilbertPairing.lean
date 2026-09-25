/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingLaws
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingNormResidueCriterion
/-!
# Local Hilbert pairings
-/

@[expose] public section

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The algebraic laws and Kummer norm-residue criterion required of a local
Hilbert pairing.  These properties do not fix the value normalization of the
symbol; that requires a comparison with a normalized Artin map. -/
def IsLocalHilbertPairing
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  B.IsSteinberg ∧ B.IsSkewSymmetric ∧ B.IsNondegenerate ∧
    B.SatisfiesNormResidueCriterion

end ClassFieldTheory.HilbertPairing
