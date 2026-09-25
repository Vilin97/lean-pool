/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
/-!
# Exact norm quotients in a cyclic tower

For a tower of cyclic Galois extensions, the first map in the concrete
idele-class norm-quotient sequence is injective.  Together with the
already available right exactness, this gives the short exact norm
sequence and its exact cardinal factorization.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open RelativeIdeleGroup.Cohomology

private theorem cyclicNormTower_relativeClassGroupIsMulCommutative
    (A B : Type) [Field A] [NumberField A] [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] cyclicNormTower_relativeClassGroupIsMulCommutative

private theorem cyclicNormTower_ideleClassGroupIsMulCommutative
    (A : Type) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] cyclicNormTower_ideleClassGroupIsMulCommutative

variable
    (K M L : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M] [IsGalois M L] [IsGalois K L]
    [IsCyclic (M ≃ₐ[K] M)]
    [IsCyclic (L ≃ₐ[M] L)]
    [IsCyclic (L ≃ₐ[K] L)]

/-- In a cyclic Galois tower, the norm-induced map

`C_M / N_{L/M} C_L → C_K / N_{L/K} C_L`

is injective. -/
theorem intermediateToCompositeNormQuotient_injective_of_cyclicTower :
    Function.Injective
      (intermediateToCompositeNormQuotient K M L) := by
  let A := IntermediateClassNormQuotient K M L
  let B := TowerCompositeClassNormQuotient K M L
  let C := IdeleClassNormQuotient K M
  let f : A →* B :=
    intermediateToCompositeNormQuotient K M L
  let g : B →* C :=
    compositeToBaseNormQuotient K M L
  have hA :
      Nat.card A = Module.finrank M L := by
    calc
      Nat.card A =
          Nat.card (IdeleClassNormQuotient M L) :=
        Nat.card_congr
          (intermediateClassNormQuotientBaseChangeMulEquiv
            K M L).toEquiv
      _ =
          (RelativeIdeleGroup.Cohomology.ideleClassNorm
            M L).range.index := by
        rw [Subgroup.index_eq_card]
      _ = Module.finrank M L :=
        GlobalClassFieldTheory.ClassFieldAxiom.relativeIdeleClassNorm_index_eq_finrank_cyclic
          M L
  have hB :
      Nat.card B = Module.finrank K L := by
    calc
      Nat.card B =
          Nat.card (IdeleClassNormQuotient K L) :=
        Nat.card_congr
          (towerCompositeClassNormQuotientEquiv
            K M L).toEquiv
      _ =
          (RelativeIdeleGroup.Cohomology.ideleClassNorm
            K L).range.index := by
        rw [Subgroup.index_eq_card]
      _ = Module.finrank K L :=
        GlobalClassFieldTheory.ClassFieldAxiom.relativeIdeleClassNorm_index_eq_finrank_cyclic
          K L
  have hC :
      Nat.card C = Module.finrank K M := by
    calc
      Nat.card C =
          (RelativeIdeleGroup.Cohomology.ideleClassNorm
            K M).range.index := by
        rw [Subgroup.index_eq_card]
      _ = Module.finrank K M :=
        GlobalClassFieldTheory.ClassFieldAxiom.relativeIdeleClassNorm_index_eq_finrank_cyclic
          K M
  let : Finite A :=
    Nat.finite_of_card_ne_zero (by
      rw [hA]
      exact Nat.ne_of_gt Module.finrank_pos)
  let : Finite B :=
    Nat.finite_of_card_ne_zero (by
      rw [hB]
      exact Nat.ne_of_gt Module.finrank_pos)
  let : Finite C :=
    Nat.finite_of_card_ne_zero (by
      rw [hC]
      exact Nat.ne_of_gt Module.finrank_pos)
  have hgSurjective : Function.Surjective g :=
    compositeToBaseNormQuotient_surjective K M L
  have hquotient :
      Nat.card (B ⧸ g.ker) = Nat.card C :=
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective
        g hgSurjective).toEquiv
  have hfactor :
      Nat.card B =
        Nat.card C * Nat.card f.range := by
    calc
      Nat.card B =
          Nat.card (B ⧸ g.ker) *
            Nat.card g.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup
          g.ker
      _ = Nat.card C * Nat.card f.range := by
        rw [hquotient]
        change
          Nat.card C *
              Nat.card (compositeToBaseNormQuotient K M L).ker =
            Nat.card C *
              Nat.card (intermediateToCompositeNormQuotient K M L).range
        rw [← intermediateToCompositeNormQuotient_range_eq_ker K M L]
  have hmul :
      Module.finrank K M * Nat.card f.range =
        Module.finrank K M * Module.finrank M L := by
    calc
      Module.finrank K M * Nat.card f.range =
          Nat.card C * Nat.card f.range := by
        rw [hC]
      _ = Nat.card B := hfactor.symm
      _ = Module.finrank K L := hB
      _ =
          Module.finrank K M * Module.finrank M L :=
        (Module.finrank_mul_finrank K M L).symm
  have hRangeDegree :
      Nat.card f.range = Module.finrank M L :=
    Nat.mul_left_cancel Module.finrank_pos hmul
  have hRangeCard :
      Nat.card f.range = Nat.card A :=
    hRangeDegree.trans hA.symm
  have hfRangeBijective :
      Function.Bijective f.rangeRestrict :=
    f.rangeRestrict_surjective.bijective_of_nat_card_le
      hRangeCard.symm.le
  intro x y hxy
  apply hfRangeBijective.1
  apply Subtype.ext
  exact hxy

/-- The concrete norm-quotient sequence of a cyclic Galois tower is
short exact: its first map is injective, its middle image is the final
kernel, and its last map is surjective. -/
theorem cyclicTowerNormQuotient_shortExact :
    Function.Injective
        (intermediateToCompositeNormQuotient K M L) ∧
      MonoidHom.range
          (intermediateToCompositeNormQuotient K M L) =
        MonoidHom.ker
          (compositeToBaseNormQuotient K M L) ∧
      Function.Surjective
        (compositeToBaseNormQuotient K M L) := by
  exact
    ⟨intermediateToCompositeNormQuotient_injective_of_cyclicTower
        K M L,
      intermediateToCompositeNormQuotient_range_eq_ker
        K M L,
      compositeToBaseNormQuotient_surjective K M L⟩

/-- Orders in the cyclic tower norm sequence multiply exactly. -/
theorem cyclicTowerNormQuotient_card_eq_mul :
    Nat.card (TowerCompositeClassNormQuotient K M L) =
      Nat.card (IntermediateClassNormQuotient K M L) *
        Nat.card (IdeleClassNormQuotient K M) := by
  calc
    Nat.card (TowerCompositeClassNormQuotient K M L) =
        Nat.card (IdeleClassNormQuotient K L) :=
      Nat.card_congr
        (towerCompositeClassNormQuotientEquiv
          K M L).toEquiv
    _ =
        (RelativeIdeleGroup.Cohomology.ideleClassNorm
          K L).range.index := by
      rw [Subgroup.index_eq_card]
    _ = Module.finrank K L :=
      GlobalClassFieldTheory.ClassFieldAxiom.relativeIdeleClassNorm_index_eq_finrank_cyclic
        K L
    _ =
        Module.finrank K M * Module.finrank M L :=
      (Module.finrank_mul_finrank K M L).symm
    _ =
        Nat.card (IdeleClassNormQuotient K M) *
          Nat.card (IdeleClassNormQuotient M L) := by
      rw [←
          GlobalClassFieldTheory.ClassFieldAxiom.relativeIdeleClassNorm_index_eq_finrank_cyclic
            K M,
        ←
          GlobalClassFieldTheory.ClassFieldAxiom.relativeIdeleClassNorm_index_eq_finrank_cyclic
            M L,
        Subgroup.index_eq_card,
        Subgroup.index_eq_card]
    _ =
        Nat.card (IdeleClassNormQuotient M L) *
          Nat.card (IdeleClassNormQuotient K M) := by
      rw [Nat.mul_comm]
    _ =
        Nat.card (IntermediateClassNormQuotient K M L) *
          Nat.card (IdeleClassNormQuotient K M) := by
      rw [Nat.card_congr
        (intermediateClassNormQuotientBaseChangeMulEquiv
          K M L).toEquiv]
      rfl

end GlobalClassFields
end GlobalClassFieldTheory
