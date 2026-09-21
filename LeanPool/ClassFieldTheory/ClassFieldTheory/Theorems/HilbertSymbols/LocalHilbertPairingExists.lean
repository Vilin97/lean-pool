/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
import Mathlib.NumberTheory.LocalField.Basic
/-!
# Existence of the local Hilbert pairing

Let `K` be a nonarchimedean local field containing the `n`-th roots of
unity, with `n` nonzero in `K`.  The local Hilbert symbol descends to a
bimultiplicative pairing

`Kˣ / (Kˣ)^n × Kˣ / (Kˣ)^n → μₙ(K)`.

The theorem below records the pairing laws without naming a particular
implementation of local reciprocity in its statement. Its proof imports the
implementation layer. The witness satisfies the
Steinberg relation, skew-symmetry, nondegeneracy in both variables, and the
Kummer norm-residue vanishing criterion.  Multiplicativity is already part
of the type `HilbertPairing K n`.  These properties still leave the harmless
choice of a normalization of the values in `μₙ` explicit.
-/

namespace ClassFieldTheory

universe u

/-- A nonarchimedean local field containing the `n`-th roots of unity admits
a nondegenerate, skew-symmetric Hilbert pairing satisfying the Steinberg and
Kummer norm-residue laws. -/
theorem exists_localHilbertPairing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ B : HilbertPairing K n,
      HilbertPairing.IsLocalHilbertPairing B := by
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
  have hmuS : (primitiveRoots (n : ℕ) S).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    refine ⟨e.symm ζ, ?_⟩
    exact (mem_primitiveRoots n.pos).2
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective e.symm.injective)
  let B : HilbertPairing S n := localHilbertPairing S n hnS hmuS
  exact ⟨hilbertPairingOfRingEquiv e n hmuS B,
    hilbertPairingOfRingEquiv_isLocalHilbertPairing e n hmuS B
      (localHilbertPairing_isLocalHilbertPairing S n hnS hmuS)⟩

end ClassFieldTheory
