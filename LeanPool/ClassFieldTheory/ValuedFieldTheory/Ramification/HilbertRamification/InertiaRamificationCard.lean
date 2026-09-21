/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.ValuedGalois
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF
/-!
# Inertia cardinality and the ramification index

For a finite Galois extension of complete discrete valuation fields, the
decomposition-side inertia subgroup has cardinality equal to the canonical
ramification index.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification.CompleteDVF

open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- In a finite Galois extension of complete discrete valued fields, the
decomposition-side inertia subgroup has cardinality equal to the canonical
ramification index. -/
theorem natCard_decompositionInertiaSubgroup_eq_ramificationIndex
    [IsGalois K L]
    [Algebra.IsSeparable
      (base.valuationSubring ⧸ base.maximalIdeal)
      (target.valuationSubring ⧸ target.maximalIdeal)] :
    Nat.card (target.valuation.valuationSubring.inertiaSubgroup K) =
      ValuedExtension.ramificationIndex base.toDVF target.toDVF := by
  let : IsScalarTower base.valuationSubring target.valuationSubring L :=
    Valuation.valuationSubring_isScalarTower_of_hasExtension
      base.valuation target.valuation
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
      base target
  let : MulSemiringAction (L ≃ₐ[K] L) target.valuationSubring := by
    change MulSemiringAction (L ≃ₐ[K] L) target.valuation.valuationSubring
    exact MulSemiringAction.compHom (R := target.valuation.valuationSubring)
      (galEquivDecompositionGroup
        (base := base) (target := target)).toMonoidHom
  let : SMulDistribClass (L ≃ₐ[K] L) target.valuationSubring L :=
    { smul_distrib_smul := by
        intro sigma r z
        change sigma ((r : L) * z) = sigma (r : L) * sigma z
        rw [map_mul] }
  let : IsGaloisGroup (L ≃ₐ[K] L)
      base.valuationSubring target.valuationSubring :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L)
      base.valuationSubring target.valuationSubring K L
  have hIdealInertia :
      target.maximalIdeal.toAddSubgroup.inertia (L ≃ₐ[K] L) =
        inertiaGroup (K := K) (base := base) (target := target) := by
    ext sigma
    rw [mem_inertiaGroup_iff]
    rw [← maximalIdealInertia_eq_decompositionInertia
      (K := K) (target := target)]
    rfl
  have hFullCard :
      Nat.card (inertiaGroup (K := K) (base := base) (target := target)) =
        ValuedExtension.ramificationIndex base.toDVF target.toDVF := by
    rw [← hIdealInertia]
    exact
      ValuedExtension.card_inertia_eq_ramificationIndex_of_finite_separable
        base target (L ≃ₐ[K] L)
  have hMap :=
    inertiaGroup_map_galEquivDecompositionGroup
      (K := K) (base := base) (target := target)
  calc
    Nat.card (target.valuation.valuationSubring.inertiaSubgroup K) =
        Nat.card
          (Subgroup.map
            (galEquivDecompositionGroup
              (base := base) (target := target)).toMonoidHom
            (inertiaGroup (K := K) (base := base) (target := target))) := by
      rw [hMap]
    _ = Nat.card
        (inertiaGroup (K := K) (base := base) (target := target)) :=
      Subgroup.card_map_of_injective
        (galEquivDecompositionGroup
          (base := base) (target := target)).injective
    _ = ValuedExtension.ramificationIndex base.toDVF target.toDVF := hFullCard

end RamificationTheory.HilbertRamification.CompleteDVF

end
