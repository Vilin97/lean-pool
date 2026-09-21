/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
import Mathlib.Algebra.Group.Hom.Basic
/-!
# Inverting the values of a local Hilbert pairing

The algebraic laws and norm-vanishing criterion are invariant under inversion
of every value. Thus these conditions alone do not distinguish the value
convention used by a normalized local Artin map. This theorem does not assert
that a pairing and its inverse are distinct.
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- Inverting every value preserves the local Hilbert-pairing axioms. -/
theorem IsLocalHilbertPairing.inv
    {K : Type u} [Field K] {n : ℕ+}
    {B : HilbertPairing K n}
    (hB : B.IsLocalHilbertPairing) :
    (B⁻¹).IsLocalHilbertPairing := by
  rcases hB with ⟨hsteinberg, hskew, hnondegenerate, hnorm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    simpa only [symbol, MonoidHom.inv_apply, inv_eq_one] using hsteinberg a ha
  · intro a b
    simpa only [MonoidHom.inv_apply] using
      congrArg (fun z : rootsOfUnity (n : ℕ) K => z⁻¹) (hskew a b)
  · constructor
    · intro a ha
      apply hnondegenerate.1 a
      intro b
      simpa only [MonoidHom.inv_apply, inv_eq_one] using ha b
    · intro b hb
      apply hnondegenerate.2 b
      intro a
      simpa only [MonoidHom.inv_apply, inv_eq_one] using hb a
  · intro a b
    simpa only [symbol, MonoidHom.inv_apply, inv_eq_one] using hnorm a b

end ClassFieldTheory.HilbertPairing
