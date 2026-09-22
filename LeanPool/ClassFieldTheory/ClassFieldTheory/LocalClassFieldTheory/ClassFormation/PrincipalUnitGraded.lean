/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients
/-! Provides the public declarations in the
  `LocalClassFieldTheory.ClassFormation.PrincipalUnitGraded` Lean module. -/

namespace LocalClassFieldTheory

open CyclicCohomology LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open IsNonarchimedeanLocalField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in

/-- The map `u ↦ u - 1` on successive normal-basis principal-unit quotients
is injective.  Its kernel calculation is exactly the statement that
`u - 1 ∈ π_K^(n+1)M` if and only if `u ∈ V^(n+1)`. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_injective
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    Function.Injective
      (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro q hq
    rw [Subgroup.mem_bot]
    revert hq
    refine
      chosenNormalBasisPrincipalUnitSuccQuot.inductionOn
        (L := L) hV
        (motive := fun q =>
          q ∈ (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
            K L n hVn hVsucc hV hmul_error).ker → q = 1)
        q ?_
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    change chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) = 1 at hu
    rw [chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_mk] at hu
    have hu_n : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ u.2
    have hzero :
        chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 := by
      have h := congrArg
        (fun x : Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) => x.toAdd) hu
      change
        chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 at h
      exact h
    have hu_succ :
        (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) :=
      (chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff
        (K := K) (L := L) (u : 𝒪[L]ˣ) hu_n).1 hzero
    change chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u = 1
    rw [chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff]
    change (u : 𝒪[L]ˣ) ∈ (Vsucc : Set 𝒪[L]ˣ)
    rw [hVsucc]
    exact hu_succ
  · exact bot_le

/-- If the high normal-basis lattice lies in the maximal ideal, every additive
successive-quotient class is represented by a unit `1 + x`; hence the
map `u ↦ u - 1` is surjective. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_surjective_of_le_maximalIdeal
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (hle : chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L) :
    Function.Surjective
      (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error) := by
  intro y
  let yadd : chosenNormalBasisLatticeSuccQuot K L n := Multiplicative.toAdd y
  suffices ∃ q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV,
      chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
          K L n hVn hVsucc hV hmul_error q = Multiplicative.ofAdd yadd by
    simpa [yadd] using this
  refine chosenNormalBasisLatticeSuccQuot.inductionOn K L n
    (motive := fun yadd =>
      ∃ q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV,
        chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
            K L n hVn hVsucc hV hmul_error q =
          Multiplicative.ofAdd yadd)
    yadd ?_
  intro x
  have hxmax : (x : L) ∈ maximalIdealFieldSubmodule K L := hle x.2
  rcases (mem_maximalIdealFieldSubmodule_iff
      (K := K) (L := L) (x : L)).1 hxmax with ⟨a, ha, hax⟩
  have ha_pow : a ∈ (𝓂[L] ^ (1 : Nat) : Ideal 𝒪[L]) := by
    simpa using ha
  let hunit : IsUnit (1 + a) :=
    isUnit_one_add_of_mem_maximalIdeal_pow L (n := 1) (by rfl) a ha_pow
  let u : 𝒪[L]ˣ := hunit.unit
  have huval : ((u : 𝒪[L]ˣ) : 𝒪[L]) = 1 + a := by
    exact IsUnit.unit_spec hunit
  have hu_sub_one :
      (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) = (x : L)) := by
    rw [huval]
    simpa using hax
  have hu_set : u ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    rw [mem_chosenNormalBasisPrincipalUnitSet_iff, hu_sub_one]
    exact x.2
  have huVn : u ∈ Vn := by
    change u ∈ (Vn : Set 𝒪[L]ˣ)
    rw [hVn]
    exact hu_set
  let ux : Vn := ⟨u, huVn⟩
  refine ⟨chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV ux, ?_⟩
  rw [chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_mk]
  change Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n u hu_set) =
    Multiplicative.ofAdd (chosenNormalBasisLatticeSuccQuotMk K L n x)
  congr 1
  rw [chosenNormalBasisPrincipalUnitLatticeClass]
  exact congrArg (chosenNormalBasisLatticeSuccQuotMk K L n)
    (Subtype.ext hu_sub_one)

/-- The actual isomorphism
`V^n/V^(n+1) ≃ π_K^nM/π_K^(n+1)M` once the high-lattice bound and
multiplicative-error estimate hold. -/
noncomputable def chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (hle : chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) :=
  MulEquiv.ofBijective
    (chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
      K L n hVn hVsucc hV hmul_error)
    ⟨chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_injective
        (K := K) (L := L) hVn hVsucc hV hmul_error,
      chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_surjective_of_le_maximalIdeal
        (K := K) (L := L) hVn hVsucc hV hmul_error hle⟩

/-- States the theorem `chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot_mk`. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot_mk
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (hle : chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
        K L hVn hVsucc hV hmul_error hle
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
      Multiplicative.ofAdd
        (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
          (by exact hVn ▸ u.2)) :=
  rfl

/-- Existential high-degree boundary used in the proof of the local class-field-axiom theorem:
for every sufficiently large `n`, the actual successive principal-unit
quotient is isomorphic to the corresponding normal-basis lattice quotient. -/
theorem exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ Vn Vsucc : Subgroup 𝒪[L]ˣ,
        ∃ hV : Vsucc ≤ Vn,
          ∃ hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n,
            (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1) ∧
              ∃ Φ : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
                  Multiplicative (chosenNormalBasisLatticeSuccQuot K L n),
                Vn ≤ principalUnits L 1 ∧
                  ∀ u : Vn,
                    Φ (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
                      Multiplicative.ofAdd
                        (chosenNormalBasisPrincipalUnitLatticeClass K L n
                          (u : 𝒪[L]ˣ) (by exact hVn ▸ u.2)) := by
  rcases exists_chosenNormalBasisPrincipalUnitSubgroupSuccPair
      (K := K) (L := L) with ⟨c₁, hc₁⟩
  rcases exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ
      (K := K) (L := L) with ⟨c₂, hc₂⟩
  rcases
    exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed
      (K := K) (L := L) with ⟨c₃, hc₃⟩
  refine ⟨max c₁ (max c₂ c₃), ?_⟩
  intro n hn
  have hc₁n : c₁ ≤ n :=
    le_trans (le_max_left c₁ (max c₂ c₃)) hn
  have hcrest : max c₂ c₃ ≤ max c₁ (max c₂ c₃) :=
    le_max_right c₁ (max c₂ c₃)
  have hc₂n : c₂ ≤ n :=
    le_trans (le_trans (le_max_left c₂ c₃) hcrest) hn
  have hc₃n : c₃ ≤ n :=
    le_trans (le_trans (le_max_right c₂ c₃) hcrest) hn
  rcases hc₁ n hc₁n with ⟨Vn, Vsucc, hVn, hVsucc, hV, hVnle⟩
  let hmul_error := hc₂ n hc₂n
  let hle := (hc₃ n hc₃n).1
  let Φ : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) :=
    chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
      K L hVn hVsucc hV hmul_error hle
  refine ⟨Vn, Vsucc, hV, hVn, hVsucc, Φ, hVnle, ?_⟩
  intro u
  rfl

end
end LocalClassFieldTheory
