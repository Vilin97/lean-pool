/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
/-!
# Norm quotients for unramified local extensions

For a finite unramified Galois extension, the field-norm subgroup is exactly
the subgroup of elements whose normalized valuation is divisible by the
extension degree. The inclusion is the normalized norm formula; the reverse
inclusion follows from finite local reciprocity because the norm quotient and
the valuation quotient have the same finite cardinality.
-/

noncomputable section


namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
  [Module.Finite 𝒪[K] 𝒪[L]]
  [IsUnramifiedValuedExtension K L]

/-- Every field norm has normalized valuation divisible by the degree. -/
theorem localNormSubgroup_le_unramifiedNormSubgroup :
    localNormSubgroup K L ≤
      unramifiedNormSubgroup K (Module.finrank K L) := by
  intro x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  apply (mem_unramifiedNormSubgroup_iff K (Module.finrank K L) _).2
  rw [valuationMap_apply]
  change (Module.finrank K L : Int) ∣
    v K (Additive.ofMul
      (LocalFieldTheory.normUnits K L y))
  rw [v_normUnits_eq_residue_finrank_mul_of_isGalois K L,
    unramifiedValuation_residue_finrank_eq_finrank K L]
  exact dvd_mul_right _ _

/-- The canonical map from the norm quotient to the valuation quotient. -/
noncomputable def normQuotientToUnramifiedNormQuotient :
    NormQuotient K L →*
      Kˣ ⧸ unramifiedNormSubgroup K (Module.finrank K L) :=
  normQuotientLift
    (unramifiedNormClass K (Module.finrank K L))
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2
        (localNormSubgroup_le_unramifiedNormSubgroup K L hx))

/-- The comparison map sends a norm class to the corresponding unramified valuation class. -/
@[simp]
theorem normQuotientToUnramifiedNormQuotient_mk (x : Kˣ) :
    normQuotientToUnramifiedNormQuotient K L
        (normClass K L x) =
      unramifiedNormClass K (Module.finrank K L) x :=
  rfl

/-- Every unramified valuation class is represented by an actual norm quotient class. -/
theorem normQuotientToUnramifiedNormQuotient_surjective :
    Function.Surjective
      (normQuotientToUnramifiedNormQuotient K L) :=
  normQuotientLift_surjective
    (unramifiedNormClass K (Module.finrank K L))
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2
        (localNormSubgroup_le_unramifiedNormSubgroup K L hx))
    (unramifiedNormClass_surjective K (Module.finrank K L))

/-- Cyclicity identifies the unramified Galois group with its abelianization. -/
noncomputable def galoisGroupEquivAbelianizationOfUnramifiedValuation :
    Gal(L / K) ≃* Abelianization (Gal(L / K)) := by
  letI : IsCyclic (Gal(L / K)) :=
    isCyclic_galoisGroup_of_unramifiedValuation K L
  letI : CommGroup (Gal(L / K)) :=
    IsCyclic.commGroup (α := Gal(L / K))
  exact Abelianization.equivOfComm (H := Gal(L / K))

/-- The cyclic Galois-group equivalence is the canonical map to the abelianization. -/
@[simp]
theorem galoisGroupEquivAbelianizationOfUnramifiedValuation_apply
    (σ : Gal(L/K)) :
    galoisGroupEquivAbelianizationOfUnramifiedValuation K L σ =
      Abelianization.of σ :=
  rfl

noncomputable local instance unramifiedNormComparisonNormQuotientFinite :
    Finite (NormQuotient K L) :=
  Finite.of_equiv (Gal(L / K))
    ((galoisGroupEquivAbelianizationOfUnramifiedValuation K L).toEquiv.trans
      (abelianizationEquivNormQuotient K L).toEquiv)

private theorem normQuotient_card_eq_finrank :
    Nat.card (NormQuotient K L) = Module.finrank K L := by
  let : Finite (Abelianization (Gal(L / K))) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  calc
    Nat.card (NormQuotient K L) =
        Nat.card (Abelianization (Gal(L / K))) :=
      Nat.card_congr (abelianizationEquivNormQuotient K L).symm.toEquiv
    _ = Nat.card (Gal(L / K)) :=
      (Nat.card_congr
        (galoisGroupEquivAbelianizationOfUnramifiedValuation K L).toEquiv).symm
    _ = Module.finrank K L :=
      galoisGroup_card_eq_finrank_of_unramifiedValuation K L

/-- The comparison from the actual norm quotient to the valuation quotient is injective. -/
theorem normQuotientToUnramifiedNormQuotient_injective :
    Function.Injective
      (normQuotientToUnramifiedNormQuotient K L) := by
  let : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  let : Finite (NormQuotient K L) :=
    Finite.of_equiv (Gal(L / K))
      ((galoisGroupEquivAbelianizationOfUnramifiedValuation K L).trans
        (abelianizationEquivNormQuotient K L)).toEquiv
  have hcard :
      Nat.card (NormQuotient K L) =
        Nat.card
          (Kˣ ⧸ unramifiedNormSubgroup K (Module.finrank K L)) := by
    rw [normQuotient_card_eq_finrank K L]
    exact
      (unramifiedNormQuotient_card_eq_degree
        K (Module.finrank K L)).symm
  have hbij : Function.Bijective
      (normQuotientToUnramifiedNormQuotient K L) :=
    (Nat.bijective_iff_surjective_and_card
      (normQuotientToUnramifiedNormQuotient K L)).2
        ⟨normQuotientToUnramifiedNormQuotient_surjective K L,
          hcard⟩
  exact hbij.1

/-- The actual norm subgroup is the valuation-divisibility subgroup. -/
theorem normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure :
    localNormSubgroup K L =
      unramifiedNormSubgroup K (Module.finrank K L) := by
  apply le_antisymm
  · exact localNormSubgroup_le_unramifiedNormSubgroup K L
  · intro x hx
    apply (normClass_eq_one_iff_mem K L x).1
    apply normQuotientToUnramifiedNormQuotient_injective K L
    rw [map_one]
    rw [normQuotientToUnramifiedNormQuotient_mk]
    exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2 hx

/-- The actual unramified norm quotient is the normalized valuation quotient. -/
noncomputable def normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure :
    NormQuotient K L ≃*
      Multiplicative (ZMod (Module.finrank K L)) :=
  (normQuotientEquivOfSubgroupEq K L
    (unramifiedNormSubgroup K (Module.finrank K L))
    (normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure K L)).trans
    (unramifiedNormQuotientEquivZMod K (Module.finrank K L))

/-- The unramified norm-quotient equivalence sends a unit class to its reduced valuation. -/
@[simp]
theorem normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk
    (x : Kˣ) :
    normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
        (normClass K L x) =
      valuationModDegreeMulHom K (Module.finrank K L) x := by
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure,
    MulEquiv.trans_apply, normQuotientEquivOfSubgroupEq_normClass,
    unramifiedNormQuotientEquivZMod_mk]

end LocalClassFieldTheory
