/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.CyclotomicKummerDescent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupSurjectivity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Local existence theorem in characteristic zero

Kummer theory supplies a finite Galois norm subgroup inside the power
subgroup attached to any finite-index subgroup of `Kˣ`.  Consequently the
ordinary norm-subgroup order embedding is surjective, hence an order
isomorphism.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

/-- In characteristic zero, every native open finite-index subgroup of
`Kˣ` is the norm subgroup of a finite abelian extension. -/
theorem finiteAbelianNormSubgroupMap_surjective_of_charZero :
    Function.Surjective (finiteAbelianNormSubgroupMap K) := by
  apply finiteAbelianNormSubgroupMap_surjective_of_normOpen K
  intro H _hH
  have hindex : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  let n : ℕ+ := ⟨H.index, Nat.pos_of_ne_zero hindex⟩
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  obtain ⟨F, hnormF⟩ :=
    exists_finiteGalois_normSubgroup_le_powMonoidHom_range K n hnK
  let E : IntermediateField K (SeparableClosure K) := F
  let : FiniteDimensional K E := F.finiteDimensional
  let : IsGalois K E := F.isGalois
  apply finiteIndexSubgroup_isNormOpen_of_normSubgroup_le K E H
  intro x hx
  have hxPower : x ∈ (powMonoidHom H.index : Kˣ →* Kˣ).range := by
    simpa [E, n] using hnormF hx
  obtain ⟨y, rfl⟩ :=
    (MonoidHom.mem_range (G := Kˣ)).1 hxPower
  exact H.pow_index_mem y

/-- Characteristic-zero local existence as an order isomorphism: finite
abelian subextensions, ordered by inclusion, correspond to native open
finite-index subgroups of `Kˣ` with the opposite inclusion order. -/
noncomputable def finiteAbelianNormSubgroupOrderIsoOfCharZero :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃o
      (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := Equiv.ofBijective (finiteAbelianNormSubgroupMap K)
    ⟨finiteAbelianNormSubgroupMap_injective K,
      finiteAbelianNormSubgroupMap_surjective_of_charZero K⟩
  map_rel_iff' := by
    intro L₁ L₂
    change finiteAbelianNormSubgroup K L₂ ≤
        finiteAbelianNormSubgroup K L₁ ↔ L₁ ≤ L₂
    exact (finiteAbelianSubextension_le_iff_normSubgroup_le K L₁ L₂).symm

/-- Underlying equivalence of the characteristic-zero local existence
order isomorphism. -/
noncomputable def finiteAbelianNormSubgroupEquivOfCharZero :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃
      OpenFiniteIndexSubgroup K :=
  (finiteAbelianNormSubgroupOrderIsoOfCharZero K).toEquiv

/-- States the theorem `finiteAbelianNormSubgroupOrderIso_of_charZero_apply`. -/
@[simp]
theorem finiteAbelianNormSubgroupOrderIso_of_charZero_apply
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianNormSubgroupOrderIsoOfCharZero K L =
      finiteAbelianNormSubgroupMap K L := by
  rfl

end LocalClassFieldTheory

end
