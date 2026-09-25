/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
/-!
# Canonical ramification invariants

The ramification index and residue degree are the ideal-theoretic invariants of
the chosen valuation rings.  Every theorem below is stated directly in the
ambient valued-extension context; there are no compatibility aliases or
extension-marker arguments.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  moduleFinite_target_valuationSubring_of_finite_separable →
    moduleFinite_target_valuationSubring_of_finite_separable

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  moduleIsTorsionFree_target_valuationSubring_of_finite_separable →
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  ramificationIndex_mul_residueDegree_eq_degree →
    ramificationIndex_mul_residueDegree_eq_degree

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable →
    ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable


noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The local fundamental identity for a finite extension of valuation rings. -/
theorem degree_eq_ramificationIndex_mul_residueDegree
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF :=
  (ramificationIndex_mul_residueDegree_eq_degree
    base target).symm

/--
Establishes the inequality
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
≠ 0`.
-/
theorem ramificationIndex_ne_zero
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF ≠ 0 :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zero
    base target

/--
Establishes the strict bound `0 <
ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF`.
-/
theorem ramificationIndex_pos
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    0 < ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF :=
  Nat.pos_of_ne_zero (ramificationIndex_ne_zero base target)

/--
Establishes the inequality `ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
base.toDVF target.toDVF ≠ 0`.
-/
theorem residueDegree_ne_zero
    [Module.Finite base.valuationSubring target.valuationSubring] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
      base.toDVF target.toDVF ≠ 0 :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree_ne_zero
    base target

/--
Establishes the strict bound `0 <
ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF`.
-/
theorem residueDegree_pos
    [Module.Finite base.valuationSubring target.valuationSubring] :
    0 < ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
      base.toDVF target.toDVF :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree_pos
    base target

/--
Proves the bound `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
base.toDVF target.toDVF ≤ ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem ramificationIndex_le_degree
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF ≤
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  rw [degree_eq_ramificationIndex_mul_residueDegree base target]
  nth_rw 1 [← mul_one
    (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF)]
  exact Nat.mul_le_mul_left _
    (Nat.succ_le_of_lt (residueDegree_pos base target))

/--
Proves the bound `ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF
target.toDVF ≤ ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem residueDegree_le_degree
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF ≤
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  rw [degree_eq_ramificationIndex_mul_residueDegree base target]
  calc
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF ≤
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
            base.toDVF target.toDVF *
          ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
            base.toDVF target.toDVF := by
      nth_rw 1 [← mul_one
        (ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF)]
      exact Nat.mul_le_mul_left _
        (Nat.succ_le_of_lt (ramificationIndex_pos base target))
    _ = _ := Nat.mul_comm _ _

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF = 1` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
= 1 ∧ ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF
= 1`.
-/
theorem degree_eq_one_iff_ramificationIndex_eq_one_and_residueDegree_eq_one
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
          base.toDVF target.toDVF = 1 ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF = 1 ∧
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF = 1 := by
  constructor
  · intro hdegree
    have hprod :
        ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
              base.toDVF target.toDVF *
            ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
              base.toDVF target.toDVF = 1 := by
      rw [← degree_eq_ramificationIndex_mul_residueDegree base target, hdegree]
    exact ⟨Nat.eq_one_of_mul_eq_one_right hprod,
      Nat.eq_one_of_mul_eq_one_left hprod⟩
  · rintro ⟨he, hf⟩
    rw [degree_eq_ramificationIndex_mul_residueDegree base target,
      he, hf, one_mul]

/--
Establishes the identity `ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
base.toDVF target.toDVF = ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem residueDegree_eq_degree_of_ramificationIndex_eq_one
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (h :
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF = 1) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  rw [degree_eq_ramificationIndex_mul_residueDegree base target, h, one_mul]

/--
Establishes the identity `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
base.toDVF target.toDVF = ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem ramificationIndex_eq_degree_of_residueDegree_eq_one
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (h :
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF = 1) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  rw [degree_eq_ramificationIndex_mul_residueDegree base target, h, mul_one]

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
= 1`.
-/
@[simp] theorem isUnramified_iff_ramificationIndex_eq_one :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF = 1 :=
  Iff.rfl

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF =
1`.
-/
@[simp] theorem isTotallyRamified_iff_residueDegree_eq_one :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF = 1 :=
  Iff.rfl

variable [FiniteDimensional K L]

/--
Establishes the identity `ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF = ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF
target.toDVF * ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF
target.toDVF`.
-/
theorem degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF :=
  (ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable
      base target).symm

/-- A finite separable extension of the discrete valued fields is defectless. -/
theorem isDefectless_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsDefectless
      base.toDVF target.toDVF :=
  degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable base target

/--
Proves the bound `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
base.toDVF target.toDVF ≤ ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem ramificationIndex_le_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF ≤
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable
      base target
  exact ramificationIndex_le_degree base target

/--
Proves the bound `ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF
target.toDVF ≤ ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem residueDegree_le_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF ≤
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable
      base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base target
  exact residueDegree_le_degree base target

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF
target.toDVF = 1` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF =
ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF target.toDVF`.
-/
theorem ramificationIndex_eq_one_iff_residueDegree_eq_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF = 1 ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF =
        ValuationTheory.DiscreteValuationField.ValuedExtension.degree
          base.toDVF target.toDVF := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable
      base target
  constructor
  · exact residueDegree_eq_degree_of_ramificationIndex_eq_one base target
  · intro hf
    have hdegree :=
      degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
        base target
    have hpos := residueDegree_pos base target
    apply Nat.eq_of_mul_eq_mul_right hpos
    simpa [hf] using hdegree.symm

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF
target.toDVF = 1` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
= ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF target.toDVF`.
-/
theorem residueDegree_eq_one_iff_ramificationIndex_eq_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF = 1 ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF =
        ValuationTheory.DiscreteValuationField.ValuedExtension.degree
          base.toDVF target.toDVF := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable
      base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base target
  constructor
  · exact ramificationIndex_eq_degree_of_residueDegree_eq_one base target
  · intro he
    have hdegree :=
      degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
        base target
    have hpos := ramificationIndex_pos base target
    apply Nat.eq_of_mul_eq_mul_left hpos
    simpa [he] using hdegree.symm

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree base.toDVF target.toDVF =
ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF target.toDVF`.
-/
theorem isUnramified_iff_residueDegree_eq_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsUnramified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF =
        ValuationTheory.DiscreteValuationField.ValuedExtension.degree
          base.toDVF target.toDVF :=
  ramificationIndex_eq_one_iff_residueDegree_eq_degree_of_finite_separable
    base target

/--
Characterizes `ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified base.toDVF
target.toDVF` by the equivalent condition
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
= ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF target.toDVF`.
-/
theorem isTotallyRamified_iff_ramificationIndex_eq_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsTotallyRamified
          base.toDVF target.toDVF ↔
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF =
        ValuationTheory.DiscreteValuationField.ValuedExtension.degree
          base.toDVF target.toDVF :=
  residueDegree_eq_one_iff_ramificationIndex_eq_degree_of_finite_separable
    base target

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
