/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFiniteFactor
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
/-!
# Locality and support conditions for global Hilbert pairing families
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory.GlobalHilbertPairingFamily

universe u

/-- Every finite-place member of the family is a local Hilbert pairing. -/
def IsLocallyHilbert
    (F : Type u) [Field F] [NumberField F]
    {n : ℕ+} (B : GlobalHilbertPairingFamily F n) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F),
    HilbertPairing.IsLocalHilbertPairing (B v)

/-- For each pair of nonzero elements of the number field, only finitely many
finite-place factors are nontrivial. -/
def HasFiniteSupport
    (F : Type u) [Field F] [NumberField F]
    {n : ℕ+} (B : GlobalHilbertPairingFamily F n)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) : Prop :=
  ∀ a b : Fˣ,
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) ↦
      finiteFactor F B hmu v a b)

end ClassFieldTheory.GlobalHilbertPairingFamily
