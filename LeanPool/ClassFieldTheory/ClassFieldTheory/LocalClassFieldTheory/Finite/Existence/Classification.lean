/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.CharacteristicZero
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.EqualCharacteristic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
/-!
# Classification by open finite-index norm subgroups

Combining the mixed- and equal-characteristic existence arguments gives the
unconditional order isomorphism between finite abelian subextensions of the
fixed separable closure and open finite-index subgroups of the local
multiplicative group.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every native open finite-index subgroup of `Kˣ` is the norm subgroup of
a finite abelian subextension of the fixed separable closure. -/
theorem finiteAbelianNormSubgroupMap_surjective :
    Function.Surjective (finiteAbelianNormSubgroupMap K) := by
  classical
  by_cases hcharZero : CharZero K
  · let : CharZero K := hcharZero
    exact finiteAbelianNormSubgroupMap_surjective_of_charZero K
  · obtain ⟨p, hp, hKp⟩ := (CharP.exists' K).resolve_left hcharZero
    let : Fact p.Prime := hp
    let : CharP K p := hKp
    exact finiteAbelianNormSubgroupMap_surjective_of_charP K p

/-- **Finite local existence theorem.** Finite abelian subextensions,
ordered by field inclusion, correspond to native open finite-index subgroups
of `Kˣ` with the opposite inclusion order. -/
noncomputable def finiteAbelianNormSubgroupOrderIso :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃o
      (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := Equiv.ofBijective (finiteAbelianNormSubgroupMap K)
    ⟨finiteAbelianNormSubgroupMap_injective K,
      finiteAbelianNormSubgroupMap_surjective K⟩
  map_rel_iff' := by
    intro L₁ L₂
    change finiteAbelianNormSubgroup K L₂ ≤
        finiteAbelianNormSubgroup K L₁ ↔ L₁ ≤ L₂
    exact (finiteAbelianSubextension_le_iff_normSubgroup_le K L₁ L₂).symm

/-- Underlying equivalence of the finite local existence order isomorphism. -/
noncomputable def finiteAbelianNormSubgroupEquiv :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃
      OpenFiniteIndexSubgroup K :=
  (finiteAbelianNormSubgroupOrderIso K).toEquiv

/-- States the theorem `finiteAbelianNormSubgroupOrderIso_apply`. -/
@[simp]
theorem finiteAbelianNormSubgroupOrderIso_apply
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianNormSubgroupOrderIso K L =
      finiteAbelianNormSubgroupMap K L :=
  rfl

end LocalClassFieldTheory
