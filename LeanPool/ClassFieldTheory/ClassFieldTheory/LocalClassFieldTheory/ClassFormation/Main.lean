/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FieldUnitsHerbrand
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.IntegerUnitsHerbrand
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisCohomology

/-! # Main -/
namespace LocalClassFieldTheory
open CyclicCohomology

open LocalFieldTheory

/-!
# The local class-field axiom

For a cyclic extension of nonarchimedean local fields, the actual Tate
cohomology of `Lˣ` has cardinalities `[L : K]` in degree zero and `1` in
degree minus one.
-/

noncomputable section

open scoped ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

/-- The integer-unit Herbrand witness used by the local class-field axiom,
including the proof that its Herbrand quotient is one. -/
theorem exists_localIntegerUnitsHerbrandDefinedAndEqOne
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
      @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
        (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
        g hU.1 hU.2 = 1 := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroup
      (K := K) (L := L) with ⟨cV, hcV⟩
  rcases exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton
      (K := K) (L := L) g hg with ⟨cH, hcH⟩
  rcases exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel
      (K := K) (L := L) with ⟨cU, hcU⟩
  let n : Nat := max cV (max cH cU)
  have hcVn : cV ≤ n := le_max_left cV (max cH cU)
  have hrest : max cH cU ≤ n := le_max_right cV (max cH cU)
  have hcHn : cH ≤ n := le_trans (le_max_left cH cU) hrest
  have hcUn : cU ≤ n := le_trans (le_max_right cH cU) hrest
  rcases hcV n hcVn with ⟨V, hV, _hVprincipal⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  have hcoh := hcH n hcHn V hV
  rcases hcU n hcUn V hV g hg hcoh.1 hcoh.2 with ⟨hU, hUone⟩
  exact ⟨hU, hUone⟩

/-- Canonical choice of the integer-unit finiteness witness constructed by
the local normal-basis argument. -/
private theorem localIntegerUnitsHerbrandDefined
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g :=
  Classical.choose (exists_localIntegerUnitsHerbrandDefinedAndEqOne K L g hg)

private theorem localIntegerUnitsHerbrandQuotient_eq_one
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
      (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L) g
      (localIntegerUnitsHerbrandDefined K L g hg).1
      (localIntegerUnitsHerbrandDefined K L g hg).2 = 1 :=
  Classical.choose_spec (exists_localIntegerUnitsHerbrandDefinedAndEqOne K L g hg)

/-- Finiteness of actual unit Tate `H⁰`, produced from the same local
normal-basis witness as the cardinality theorem. -/
theorem localFieldUnitsTateH0FiniteOfGenerator
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) :=
  unitsTateH0FiniteOfIntegerUnitsHerbrand K L g hg
    (localIntegerUnitsHerbrandDefined K L g hg)

/-- The local class-field-axiom theorem for a specified generator of the cyclic Galois group. -/
theorem localFieldUnits_tate_card_of_generator
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    letI := localFieldUnitsTateH0FiniteOfGenerator K L g hg
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  exact fieldUnits_tate_card_of_integerUnits_herbrand_eq_one
    K L g hg (localIntegerUnitsHerbrandDefined K L g hg)
      (localIntegerUnitsHerbrandQuotient_eq_one K L g hg)

/-- States the theorem `localFieldUnitsTateH0FiniteOfIsCyclic`. -/
theorem localFieldUnitsTateH0FiniteOfIsCyclic
    [IsCyclic (Gal(L / K))] :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) := by
  obtain ⟨g, hg⟩ := (IsCyclic.exists_generator :
    ∃ g : Gal(L / K), ∀ sigma : Gal(L / K),
      sigma ∈ Subgroup.zpowers g)
  exact localFieldUnitsTateH0FiniteOfGenerator K L g hg

/-- Generator-free form of the local class-field-axiom theorem.  Both Tate
cohomology objects are canonical and independent of the generator used in the proof. -/
theorem localFieldUnits_tate_card_of_isCyclic [IsCyclic (Gal(L / K))] :
    letI := localFieldUnitsTateH0FiniteOfIsCyclic K L
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  rcases (IsCyclic.exists_generator :
    ∃ g : Gal(L / K), ∀ sigma : Gal(L / K),
      sigma ∈ Subgroup.zpowers g) with ⟨g, hg⟩
  exact localFieldUnits_tate_card_of_generator K L g hg

end
end LocalClassFieldTheory
