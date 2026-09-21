/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisRecursiveLifting

/-! # Normal Basis Cohomology -/
namespace LocalClassFieldTheory
open CyclicCohomology

open LocalFieldTheory

/-!
# Low-degree cohomology of a deep normal-basis unit subgroup

The recursive norm and coboundary constructions are converted here into the
actual quotient statements `H⁰(G,V)=H⁻¹(G,V)=1` used in the local class-field-axiom theorem.
-/

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

/-- The local class-field-axiom theorem: for every sufficiently deep chosen normal-basis subgroup
`V`, both low-degree Herbrand quotients are trivial. -/
theorem exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton
    (g : Gal(L/K))
    (hgen : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ (V : Subgroup 𝒪[L]ˣ)
        (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n),
        letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
          K L n V hV
        Subsingleton (HerbrandH0 (Gal(L / K)) V) ∧
          Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g) := by
  rcases exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNorm
      (K := K) (L := L) with ⟨c0, hc0⟩
  rcases exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOne
      (K := K) (L := L) g hgen with ⟨cm, hcm⟩
  refine ⟨max c0 cm, ?_⟩
  intro n hn V hV
  have hc0n : c0 ≤ n := le_trans (le_max_left c0 cm) hn
  have hcmn : cm ≤ n := le_trans (le_max_right c0 cm) hn
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n V hV
  have hfixed : fixedSubgroup (Gal(L / K)) V ≤
      tateNormSubgroup (Gal(L / K)) V := by
    intro a ha
    have haSet : ((a : V) : 𝒪[L]ˣ) ∈ (V : Set 𝒪[L]ˣ) := (a : V).2
    have haLevel : ((a : V) : 𝒪[L]ˣ) ∈
        chosenNormalBasisPrincipalUnitSet K L n := by
      rw [← hV]
      exact haSet
    have haFixed : ∀ sigma : Gal(L / K),
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        sigma • ((a : V) : 𝒪[L]ˣ) = ((a : V) : 𝒪[L]ˣ) := by
      intro sigma
      exact congrArg (fun z : V => (z : 𝒪[L]ˣ)) (ha sigma)
    rcases hc0 n hc0n ((a : V) : 𝒪[L]ˣ) haLevel haFixed with
      ⟨b, hb, hab⟩
    let bv : V := ⟨b, by
      change b ∈ (V : Set 𝒪[L]ˣ)
      rw [hV]
      exact hb⟩
    refine ⟨bv, ?_⟩
    apply Subtype.ext
    rw [tateNormHom_apply,
      chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe K L n V hV]
    exact hab.symm
  have hkernel : normKernelSubgroup (Gal(L / K)) V ≤
      augmentationSubgroup (Gal(L / K)) V g := by
    intro a ha
    have haLevel : ((a : V) : 𝒪[L]ˣ) ∈
        chosenNormalBasisPrincipalUnitSet K L n := by
      rw [← hV]
      exact (a : V).2
    have haNorm :
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        tateNorm (Gal(L / K)) 𝒪[L]ˣ ((a : V) : 𝒪[L]ˣ) = 1 := by
      rw [← chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe K L n V hV]
      exact congrArg (fun z : V => (z : 𝒪[L]ˣ)) ha
    rcases hcm n hcmn ((a : V) : 𝒪[L]ˣ) haLevel haNorm with
      ⟨b, hb, hab⟩
    let bv : V := ⟨b, by
      change b ∈ (V : Set 𝒪[L]ˣ)
      rw [hV]
      exact hb⟩
    refine ⟨bv, ?_⟩
    apply Subtype.ext
    rw [sigmaMinusOneHom_apply,
      chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe K L n V hV]
    exact hab.symm
  exact ⟨
    herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup hfixed,
    herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup
      g hkernel⟩

end
end LocalClassFieldTheory
