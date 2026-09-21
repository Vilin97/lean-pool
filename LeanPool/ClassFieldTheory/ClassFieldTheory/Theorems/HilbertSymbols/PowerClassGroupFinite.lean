/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
/-!
# Finiteness of local power classes

The nonzero residue of the exponent in a nonarchimedean local field makes its
multiplicative `n`-th-power quotient finite. This is the finiteness input for
turning a nondegenerate Hilbert pairing into a perfect pairing.
-/

namespace ClassFieldTheory

universe u

/-- The power-class group of a nonarchimedean local field is finite when
the exponent is nonzero in the field. -/
theorem powerClassGroup_finite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) :
    Finite (PowerClassGroup K n) := by
  let : Small.{0} K := LocalFieldTheory.nonarchimedeanLocalField_small K
  let S := Shrink.{0} K
  let : ValuativeRel S := LocalFieldTheory.shrinkLocalFieldValuativeRel K
  let : IsNonarchimedeanLocalField S :=
    LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField K
  let e : S ≃+* K := Shrink.ringEquiv K
  have hnS : ((n : ℕ) : S) ≠ 0 := by
    intro hz
    apply hnK
    have hzK := congrArg e hz
    simpa [e] using hzK
  let : Finite (PowerClassGroup S n) := by
    change Finite (Sˣ ⧸ (powMonoidHom (n : ℕ) : Sˣ →* Sˣ).range)
    exact LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero
      S (n : ℕ) hnS
  exact Finite.of_equiv (PowerClassGroup S n)
    (powerClassGroupEquivOfRingEquiv e n).toEquiv

end ClassFieldTheory
