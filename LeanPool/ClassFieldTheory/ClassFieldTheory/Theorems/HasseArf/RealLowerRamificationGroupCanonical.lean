/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
/-!
# Canonical real lower ramification groups

The real-index filtration is decreasing directly from the antitonicity of
powers of the maximal ideal. No choice of a local extension is needed.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The public real lower groups of a finite Abelian local extension form a
decreasing filtration of its canonical decomposition group. -/
theorem realLowerRamificationGroup_canonical_antitone
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [ValuativeRel L] [TopologicalSpace L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Antitone (ClassFieldTheory.realLowerRamificationGroup K
      (ValuativeRel.valuation L).valuationSubring) := by
  intro s t hst σ hσ x
  have hexp : (Int.ceil (s + 1)).toNat ≤ (Int.ceil (t + 1)).toNat :=
    Int.toNat_le_toNat (Int.ceil_le_ceil (add_le_add_left hst 1))
  exact (Ideal.pow_le_pow_right
    (I := IsLocalRing.maximalIdeal (ValuativeRel.valuation L).valuationSubring)
    hexp) (hσ x)

end ClassFieldTheory
