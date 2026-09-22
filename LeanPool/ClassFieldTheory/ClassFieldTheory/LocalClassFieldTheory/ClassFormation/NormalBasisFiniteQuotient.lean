/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower
/-! Provides the public declarations in the
  `LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient` Lean module. -/

namespace LocalClassFieldTheory
open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter IsNonarchimedeanLocalField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Module.Finite 𝒪[K] 𝒪[L]]

/-- Since the normal-basis lattices `π_K^n M` are open for high `n`, each
corresponding `V^n` contains an ordinary principal-unit subgroup. -/
theorem exists_principalUnits_le_chosenNormalBasisPrincipalUnitSet :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ m : Nat, (principalUnits L m : Set 𝒪[L]ˣ) ⊆
        chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn
  let S : Set L :=
    (chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) : Set L)
  have hS : S ∈ nhds (0 : L) := hc n hcn
  have hSO : {x : 𝒪[L] | (x : L) ∈ S} ∈ nhds (0 : 𝒪[L]) := by
    exact continuous_subtype_val.continuousAt hS
  rcases exists_maximalIdeal_pow_subset_nhds_zero L
      {x : 𝒪[L] | (x : L) ∈ S} hSO with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro a ha
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  change
    (((((a : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)) ∈ S
  exact hm ((mem_principalUnits_iff L a m).1 ha)

/-- The canonical map from `𝒪_Lˣ/U_L^m` onto `𝒪_Lˣ/V` whenever
`U_L^m ≤ V`. -/
def integerUnitsModPrincipalUnitsToSubgroupQuotient
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    IntegerUnitsModPrincipalUnitsAtLevel L m →* (𝒪[L]ˣ ⧸ V) :=
  integerUnitsModPrincipalUnitsAtLevelLift m (QuotientGroup.mk' V)
    (by
      intro a ha
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk a : 𝒪[L]ˣ ⧸ V) = 1
      exact (QuotientGroup.eq_one_iff a).2 (h ha))

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- States the theorem `integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective`. -/
theorem integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    Function.Surjective
      (integerUnitsModPrincipalUnitsToSubgroupQuotient L m V h) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  refine ⟨integerUnitsModPrincipalUnitsAtLevelMk L m a, ?_⟩
  rfl

/-- A quotient by a subgroup containing an ordinary principal-unit level is
finite. -/
theorem finite_chosenNormalBasisIntegerUnitsQuotient_of_principalUnits_le
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    Finite (𝒪[L]ˣ ⧸ V) := by
  let : Finite (IntegerUnitsModPrincipalUnitsAtLevel L m) :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L m
  exact Finite.of_surjective
    (integerUnitsModPrincipalUnitsToSubgroupQuotient L m V h)
    (integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective L m V h)

/-- Finite-index boundary for the local class-field axiom: for sufficiently large `n`, every
actual subgroup with carrier `V^n` has finite quotient in `𝒪_Lˣ`. -/
theorem exists_finite_chosenNormalBasisIntegerUnitsQuotient :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ (V : Subgroup 𝒪[L]ˣ),
        (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n →
          Finite (𝒪[L]ˣ ⧸ V) := by
  rcases exists_principalUnits_le_chosenNormalBasisPrincipalUnitSet
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn V hV
  rcases hc n hcn with ⟨m, hm⟩
  have hle : principalUnits L m ≤ V := by
    intro a ha
    change (a : 𝒪[L]ˣ) ∈ (V : Set 𝒪[L]ˣ)
    rw [hV]
    exact hm ha
  exact finite_chosenNormalBasisIntegerUnitsQuotient_of_principalUnits_le
    (L := L) m V hle

end
end LocalClassFieldTheory
