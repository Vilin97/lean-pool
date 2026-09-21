/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import Mathlib.FieldTheory.Galois.Abelian
/-!
# Conductors of finite abelian local extensions

For a finite abelian extension `L / K`, define its conductor exponent as the
least `n ≥ 0` for which the `n`-th principal-unit group of
`K` lies in the norm subgroup.  The conductor itself is the corresponding
power of the maximal ideal of the valuation ring of `K`.

The existence of this least exponent is not an extra hypothesis here.  It
follows from openness of the norm subgroup of the actual finite extension and
the principal-unit neighbourhood basis.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory

/-- The field-level principal-unit filtration is antitone in its exponent. -/
theorem fieldPrincipalUnits_antitone
    (K : Type) [Field K] [ValuativeRel K]
    {m n : ℕ} (hmn : m ≤ n) :
    LocalFieldTheory.fieldPrincipalUnits K n ≤ LocalFieldTheory.fieldPrincipalUnits K m :=
  Subgroup.map_mono (principalUnits_antitone K hmn)

/-- For an actual finite abelian local extension, some principal-unit group
is contained in its norm subgroup. This supplies the least conductor
exponent. -/
theorem exists_fieldPrincipalUnits_le_normSubgroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ n : ℕ, LocalFieldTheory.fieldPrincipalUnits K n ≤ localNormSubgroup K L := by
  obtain ⟨n, _hn, hle⟩ :=
    LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpen K (localNormSubgroup K L)
      (LocalClassFieldTheory.localNormSubgroup_isOpen K L)
  exact ⟨n, hle⟩

/-- The least principal-unit depth contained in the norm subgroup of the
finite abelian extension `L / K`. -/
def localConductorExponent
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : ℕ := by
  classical
  exact Nat.find (exists_fieldPrincipalUnits_le_normSubgroup K L)

/-- The principal-unit group at the conductor exponent is contained in the
norm subgroup. -/
theorem localConductorExponent_spec
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    LocalFieldTheory.fieldPrincipalUnits K (localConductorExponent K L) ≤
      localNormSubgroup K L := by
  classical
  exact Nat.find_spec (exists_fieldPrincipalUnits_le_normSubgroup K L)

/-- Minimality of the conductor exponent. -/
theorem localConductorExponent_min
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {n : ℕ} (hn : LocalFieldTheory.fieldPrincipalUnits K n ≤ localNormSubgroup K L) :
    localConductorExponent K L ≤ n := by
  classical
  exact Nat.find_min' (exists_fieldPrincipalUnits_le_normSubgroup K L) hn

/-- A depth contains the conductor depth exactly when its principal units are
already norms.  This records both the defining property and its minimality. -/
theorem localConductorExponent_le_iff
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) :
    localConductorExponent K L ≤ n ↔
      LocalFieldTheory.fieldPrincipalUnits K n ≤ localNormSubgroup K L := by
  constructor
  · intro hn
    exact (fieldPrincipalUnits_antitone K hn).trans
      (localConductorExponent_spec K L)
  · exact localConductorExponent_min K L

/-- The conductor ideal `p_K ^ n`, where `n` is the least principal-unit
depth contained in the norm subgroup. -/
def localConductorIdeal
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Ideal 𝒪[K] :=
  𝓂[K] ^ localConductorExponent K L

/-- The conductor exponent is zero exactly when the whole unit group
`U_K = U_K^(0)` is contained in the norm subgroup. -/
theorem localConductorExponent_eq_zero_iff
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localConductorExponent K L = 0 ↔
      LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L := by
  simpa using (localConductorExponent_le_iff K L 0)

/-- The conductor ideal is `1` exactly when its exponent is zero. -/
theorem localConductorIdeal_eq_one_iff_exponent_eq_zero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localConductorIdeal K L = 1 ↔ localConductorExponent K L = 0 := by
  simp [localConductorIdeal, Ideal.pow_eq_top_iff,
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top]

/-- The conductor-one criterion stated directly in terms of the norm subgroup
and `U_K = U_K^(0)`. -/
theorem localConductorIdeal_eq_one_iff
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localConductorIdeal K L = 1 ↔
      LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L :=
  (localConductorIdeal_eq_one_iff_exponent_eq_zero K L).trans
    (localConductorExponent_eq_zero_iff K L)

end LocalClassFieldTheory
