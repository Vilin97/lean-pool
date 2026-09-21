/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FilteredLiftingSequence
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting

/-! # Normal Basis Recursive Lifting -/
namespace LocalClassFieldTheory
open CyclicCohomology

open LocalFieldTheory

/-!
# Infinite lifting on the normal-basis principal-unit filtration

This is the recursive core of the local class-field-axiom theorem.  The one-step graded
lifting is iterated, its correction factors are multiplied, and completeness
of the local field turns the resulting formal recursion into an actual norm
or coboundary in the initial subgroup.
-/

noncomputable section

universe u

open scoped ValuativeRel
open Filter IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

omit [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L] in
private theorem filteredCorrectionProduct_eq_chosenNormalBasisProduct
    (z : Nat → 𝒪[L]ˣ) (d : Nat) :
    filteredCorrectionProduct z d =
      chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [filteredCorrectionProduct_succ,
        chosenNormalBasisPrincipalUnitCorrectionProduct_succ, ih]

/-- Recursive `H⁰` lifting.  At every sufficiently deep
normal-basis level, an actually fixed unit is the norm of a unit at the same
level. -/
theorem exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNorm :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L n →
      (∀ sigma : Gal(L / K), sigma • a = a) →
      ∃ b : 𝒪[L]ˣ, b ∈ chosenNormalBasisPrincipalUnitSet K L n ∧
        a = tateNorm (Gal(L / K)) 𝒪[L]ˣ b := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnit_h0_oneStep_lifting
      (K := K) (L := L) with ⟨cStep, hStep⟩
  rcases exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct
      (K := K) (L := L) with ⟨cProd, hProd⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
      (K := K) (L := L) with ⟨b, hb⟩
  refine ⟨max cStep (max cProd (b + 1)), ?_⟩
  intro n hn a ha hfixed
  have hcStep : cStep ≤ n :=
    le_trans (le_max_left cStep (max cProd (b + 1))) hn
  have hrest : max cProd (b + 1) ≤ max cStep (max cProd (b + 1)) :=
    le_max_right cStep (max cProd (b + 1))
  have hcProd : cProd ≤ n :=
    le_trans (le_trans (le_max_left cProd (b + 1)) hrest) hn
  have hbn : b + 1 ≤ n :=
    le_trans (le_trans (le_max_right cProd (b + 1)) hrest) hn
  let P : Nat → 𝒪[L]ˣ → Prop := fun k x =>
    x ∈ chosenNormalBasisPrincipalUnitSet K L k
  let R : 𝒪[L]ˣ → Prop := fun x =>
    ∀ sigma : Gal(L / K), sigma • x = x
  let F : 𝒪[L]ˣ →* 𝒪[L]ˣ :=
    tateNormHom (G := Gal(L / K)) (A := 𝒪[L]ˣ)
  let initial : FilteredLiftState 𝒪[L]ˣ P R n 0 :=
    ⟨a, by simpa [P] using ha, hfixed⟩
  let step : ∀ i (s : FilteredLiftState 𝒪[L]ˣ P R n i),
      Nonempty (FilteredLiftStep 𝒪[L]ˣ P R F n i s) := by
    intro i s
    have hlevel : cStep ≤ n + i :=
      le_trans hcStep (Nat.le_add_right n i)
    rcases hStep (n + i) hlevel s.value (by simpa [P] using s.mem)
        (by simpa [R] using s.stable) with
      ⟨z, a', hz, ha', hfixed', heq⟩
    refine ⟨⟨z, ?_, ⟨a', ?_, ?_⟩, ?_⟩⟩
    · simpa [P] using hz
    · simpa [P, Nat.add_assoc] using ha'
    · simpa [R] using hfixed'
    · simpa [F] using heq
  let states : (i : Nat) → FilteredLiftState 𝒪[L]ˣ P R n i :=
    chosenFilteredLiftStateSequence 𝒪[L]ˣ P R F n initial step
  let z : Nat → 𝒪[L]ˣ :=
    chosenFilteredLiftCorrectionSequence 𝒪[L]ˣ P R F n initial step
  have hz (i : Nat) : z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) := by
    exact chosenFilteredLiftCorrectionSequence_mem
      𝒪[L]ˣ P R F n initial step i
  rcases hProd n hcProd z hz with ⟨x, hx, hxmem⟩
  have hstates (i : Nat) :
      (states i).value ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) := by
    exact (states i).mem
  have hrem : Tendsto
      (fun i : Nat => (((states i).value : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds (1 : 𝒪[L])) :=
    tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound
      (K := K) (L := L) hb hbn (fun i => (states i).value) hstates
  have hnorm := tendsto_galoisGroupIntegerUnits_tateNorm_of_tendsto
    (K := K) (L := L)
    (fun d => chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) x hx
  have hrec (d : Nat) :
      a = tateNorm (Gal(L / K)) 𝒪[L]ˣ
          (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) *
        (states d).value := by
    have h := filteredLift_initial_eq_correctionProduct_mul_state
      𝒪[L]ˣ P R F n initial step d
    rw [filteredCorrectionProduct_eq_chosenNormalBasisProduct
      (L := L) z d] at h
    simpa [initial, states, F] using h
  have hmul : Tendsto
      (fun d : Nat =>
        ((tateNorm (Gal(L / K)) 𝒪[L]ˣ
            (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) :
          𝒪[L]ˣ) : 𝒪[L]) * (((states d).value : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds (((tateNorm (Gal(L / K)) 𝒪[L]ˣ x : 𝒪[L]ˣ) : 𝒪[L]) * 1)) :=
    hnorm.mul hrem
  have hconst : Tendsto (fun _d : Nat => ((a : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((a : 𝒪[L]ˣ) : 𝒪[L])) := tendsto_const_nhds
  have heqO : ((a : 𝒪[L]ˣ) : 𝒪[L]) =
      ((tateNorm (Gal(L / K)) 𝒪[L]ˣ x : 𝒪[L]ˣ) : 𝒪[L]) * 1 := by
    apply tendsto_nhds_unique hconst
    exact hmul.congr' (Eventually.of_forall (fun d => by
      simpa using congrArg (fun q : 𝒪[L]ˣ => (q : 𝒪[L])) (hrec d).symm))
  refine ⟨x, hxmem, ?_⟩
  apply Units.ext
  simpa using heqO

/-- Recursive `H⁻¹` lifting.  For a chosen generator,
every sufficiently deep norm-one unit is an actual coboundary from the same
normal-basis level. -/
theorem exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOne
    (g : Gal(L / K)) (hgen : ∀ sigma : Gal(L / K),
      sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L n →
      tateNorm (Gal(L / K)) 𝒪[L]ˣ a = 1 →
      ∃ b : 𝒪[L]ˣ, b ∈ chosenNormalBasisPrincipalUnitSet K L n ∧
        a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g b := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_lifting
      (K := K) (L := L) g hgen with ⟨cStep, hStep⟩
  rcases exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct
      (K := K) (L := L) with ⟨cProd, hProd⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
      (K := K) (L := L) with ⟨b, hb⟩
  refine ⟨max cStep (max cProd (b + 1)), ?_⟩
  intro n hn a ha hnorma
  have hcStep : cStep ≤ n :=
    le_trans (le_max_left cStep (max cProd (b + 1))) hn
  have hrest : max cProd (b + 1) ≤ max cStep (max cProd (b + 1)) :=
    le_max_right cStep (max cProd (b + 1))
  have hcProd : cProd ≤ n :=
    le_trans (le_trans (le_max_left cProd (b + 1)) hrest) hn
  have hbn : b + 1 ≤ n :=
    le_trans (le_trans (le_max_right cProd (b + 1)) hrest) hn
  let P : Nat → 𝒪[L]ˣ → Prop := fun k x =>
    x ∈ chosenNormalBasisPrincipalUnitSet K L k
  let R : 𝒪[L]ˣ → Prop := fun x =>
    tateNorm (Gal(L / K)) 𝒪[L]ˣ x = 1
  let F : 𝒪[L]ˣ →* 𝒪[L]ˣ :=
    sigmaMinusOneHom (G := Gal(L / K)) (A := 𝒪[L]ˣ) g
  let initial : FilteredLiftState 𝒪[L]ˣ P R n 0 :=
    ⟨a, by simpa [P] using ha, hnorma⟩
  let step : ∀ i (s : FilteredLiftState 𝒪[L]ˣ P R n i),
      Nonempty (FilteredLiftStep 𝒪[L]ˣ P R F n i s) := by
    intro i s
    have hlevel : cStep ≤ n + i :=
      le_trans hcStep (Nat.le_add_right n i)
    rcases hStep (n + i) hlevel s.value (by simpa [P] using s.mem)
        (by simpa [R] using s.stable) with
      ⟨z, a', hz, ha', hnorm', heq⟩
    refine ⟨⟨z, ?_, ⟨a', ?_, ?_⟩, ?_⟩⟩
    · simpa [P] using hz
    · simpa [P, Nat.add_assoc] using ha'
    · simpa [R] using hnorm'
    · simpa [F] using heq
  let states : (i : Nat) → FilteredLiftState 𝒪[L]ˣ P R n i :=
    chosenFilteredLiftStateSequence 𝒪[L]ˣ P R F n initial step
  let z : Nat → 𝒪[L]ˣ :=
    chosenFilteredLiftCorrectionSequence 𝒪[L]ˣ P R F n initial step
  have hz (i : Nat) : z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) := by
    exact chosenFilteredLiftCorrectionSequence_mem
      𝒪[L]ˣ P R F n initial step i
  rcases hProd n hcProd z hz with ⟨x, hx, hxmem⟩
  have hstates (i : Nat) :
      (states i).value ∈ chosenNormalBasisPrincipalUnitSet K L (n + i) :=
    (states i).mem
  have hrem : Tendsto
      (fun i : Nat => (((states i).value : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds (1 : 𝒪[L])) :=
    tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound
      (K := K) (L := L) hb hbn (fun i => (states i).value) hstates
  have hcob := tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendsto
    (K := K) (L := L) g
    (fun d => chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) x hx
  have hrec (d : Nat) :
      a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g
          (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) *
        (states d).value := by
    have h := filteredLift_initial_eq_correctionProduct_mul_state
      𝒪[L]ˣ P R F n initial step d
    rw [filteredCorrectionProduct_eq_chosenNormalBasisProduct
      (L := L) z d] at h
    simpa [initial, states, F] using h
  have hmul : Tendsto
      (fun d : Nat =>
        ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g
            (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d) :
          𝒪[L]ˣ) : 𝒪[L]) * (((states d).value : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds (((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g x : 𝒪[L]ˣ) : 𝒪[L]) * 1)) :=
    hcob.mul hrem
  have hconst : Tendsto (fun _d : Nat => ((a : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((a : 𝒪[L]ˣ) : 𝒪[L])) := tendsto_const_nhds
  have heqO : ((a : 𝒪[L]ˣ) : 𝒪[L]) =
      ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g x : 𝒪[L]ˣ) : 𝒪[L]) * 1 := by
    apply tendsto_nhds_unique hconst
    exact hmul.congr' (Eventually.of_forall (fun d => by
      simpa using congrArg (fun q : 𝒪[L]ˣ => (q : 𝒪[L])) (hrec d).symm))
  refine ⟨x, hxmem, ?_⟩
  apply Units.ext
  simpa using heqO

end
end LocalClassFieldTheory
