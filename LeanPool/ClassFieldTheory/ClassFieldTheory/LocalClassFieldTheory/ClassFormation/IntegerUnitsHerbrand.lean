/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient

/-! # Integer Units Herbrand -/

@[expose] public section
namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

/-!
# The Herbrand quotient of the integer-unit group

This file proves the final integer-unit Herbrand-quotient calculation.  For a
sufficiently deep normal-basis neighbourhood
`V = 1 + π_K^n M`, the exact sequence

`1 → V → 𝒪_Lˣ → 𝒪_Lˣ / V → 1`

has the actual `Gal(L / K)` actions.  Vanishing of the two low-degree
Herbrand groups of `V`, together with finiteness of the quotient, gives
`h(G, 𝒪_Lˣ) = 1` by the Herbrand-quotient multiplicativity theorem.
-/

noncomputable
section

open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand
open IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The normal-basis subgroup sequence is short exact and equivariant for
the actual actions used in the local class-field-axiom argument. -/
theorem chosenNormalBasisIntegerUnitsHerbrand_shortExact
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
    (∀ (sigma : Gal(L/K)) (a : V),
        chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V (sigma • a) =
          sigma • chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a) ∧
      (∀ (sigma : Gal(L/K)) (a : 𝒪[L]ˣ),
        chosenNormalBasisIntegerUnitsQuotientMap (L := L) V (sigma • a) =
          sigma • chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a) ∧
      (∀ a : 𝒪[L]ˣ,
        chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a = 1 ↔
          ∃ v : V,
            chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V v = a) ∧
      Function.Injective
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) ∧
      Function.Surjective
        (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  refine ⟨chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant K L n V hV,
    chosenNormalBasisIntegerUnitsQuotientMap_equivariant K L n V hV, ?_,
    chosenNormalBasisPrincipalUnitSubgroupInclusion_injective (L := L) V,
    chosenNormalBasisIntegerUnitsQuotientMap_surjective (L := L) V⟩
  intro a
  have hrange :=
    chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotient
      (L := L) V
  constructor
  · intro ha
    have ha' : a ∈ MonoidHom.ker
        (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V) := ha
    rw [← hrange] at ha'
    exact ha'
  · rintro ⟨v, rfl⟩
    have hv :
        chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V v ∈
          MonoidHom.range
            (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) :=
      ⟨v, rfl⟩
    rw [hrange] at hv
    exact hv

/-- Integer-unit Herbrand calculation at one chosen normal-basis
level.  The only low-degree cohomology input is the proved vanishing of
`H⁰(G,V)` and `H⁻¹(G,V)`; finiteness of `𝒪_Lˣ/V` is the other honest
input. -/
theorem integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasis
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hfinite : Finite (𝒪[L]ˣ ⧸ V))
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L/K), sigma ∈ Subgroup.zpowers g)
    (hH0 :
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
      Subsingleton (HerbrandH0 (Gal(L/K)) V))
    (hHminusOne :
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
      Subsingleton (HerbrandHMinusOne (Gal(L/K)) V g)) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
    ∃ _ : HerbrandQuotientDefined (Gal(L/K)) 𝒪[L]ˣ g,
      @herbrandQuotient (Gal(L/K)) 𝒪[L]ˣ _ _ _
        (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
        g = 1 := by
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  let : Finite (𝒪[L]ˣ ⧸ V) := hfinite
  let : Subsingleton (HerbrandH0 (Gal(L/K)) V) := hH0
  let : Subsingleton (HerbrandHMinusOne (Gal(L/K)) V g) := hHminusOne
  let hVdefined : HerbrandQuotientDefined (Gal(L/K)) V g :=
    ⟨inferInstance, inferInstance⟩
  let hQdefined : HerbrandQuotientDefined (Gal(L/K)) (𝒪[L]ˣ ⧸ V) g :=
    ⟨inferInstance, inferInstance⟩
  let hseq := chosenNormalBasisIntegerUnitsHerbrand_shortExact K L n V hV
  have hsurj : ∀ c : 𝒪[L]ˣ ⧸ V, ∃ b : 𝒪[L]ˣ,
      chosenNormalBasisIntegerUnitsQuotientMap (L := L) V b = c := by
    intro c
    exact hseq.2.2.2.2 c
  let hU := herbrandQuotientDefined_middle_of_left_right
    (G := Gal(L/K)) (A := V) (B := 𝒪[L]ˣ) (C := 𝒪[L]ˣ ⧸ V)
    (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V)
    (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V)
    hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hsurj
    g hg hVdefined hQdefined
  refine ⟨hU, ?_⟩
  let : Finite (HerbrandH0 (Gal(L/K)) 𝒪[L]ˣ) := hU.1
  let : Finite (HerbrandHMinusOne (Gal(L/K)) 𝒪[L]ˣ g) := hU.2
  have hVone : herbrandQuotient (G := Gal(L/K)) (A := V) g = 1 := by
    exact herbrandQuotient_eq_one_of_card_eq
      (G := Gal(L/K)) (A := V) g
      (by simp only [Nat.card_unique])
  have hQone :
      herbrandQuotient (G := Gal(L/K)) (A := 𝒪[L]ˣ ⧸ V) g = 1 := by
    exact herbrandQuotient_eq_one_of_finite_module
      (G := Gal(L/K)) (A := 𝒪[L]ˣ ⧸ V) g hg
  have hmul : herbrandQuotient (G := Gal(L/K)) (A := 𝒪[L]ˣ) g =
      herbrandQuotient (G := Gal(L/K)) (A := V) g *
        herbrandQuotient (G := Gal(L/K)) (A := 𝒪[L]ˣ ⧸ V) g :=
    herbrandQuotient_multiplicative_of_shortExact
      (G := Gal(L/K)) (A := V) (B := 𝒪[L]ˣ) (C := 𝒪[L]ˣ ⧸ V)
      (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V)
      (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V)
      hseq.1 hseq.2.1 hseq.2.2.1 hseq.2.2.2.1 hsurj g hg
  exact hmul.trans (by rw [hVone, hQone, one_mul])

variable [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Module.Finite 𝒪[K] 𝒪[L]]

/-- At all sufficiently deep chosen normal-basis levels:
`H⁰(G,V)=H⁻¹(G,V)=1` implies that the integer-unit Herbrand quotient is
defined and equals `1`. -/
theorem exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ (V : Subgroup 𝒪[L]ˣ)
        (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
        (g : Gal(L/K)),
        (∀ sigma : Gal(L/K), sigma ∈ Subgroup.zpowers g) →
        (letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV;
          Subsingleton (HerbrandH0 (Gal(L/K)) V)) →
        (letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV;
          Subsingleton (HerbrandHMinusOne (Gal(L/K)) V g)) →
        letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
        letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
        letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
        ∃ _ : HerbrandQuotientDefined (Gal(L/K)) 𝒪[L]ˣ g,
          @herbrandQuotient (Gal(L/K)) 𝒪[L]ˣ _ _ _
            (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
            g = 1 := by
  rcases exists_finite_chosenNormalBasisIntegerUnitsQuotient
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro n hcn V hV g hg hH0 hHminusOne
  exact integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasis
    K L n V hV (hc n hcn V hV) g hg hH0 hHminusOne

end
end LocalClassFieldTheory
