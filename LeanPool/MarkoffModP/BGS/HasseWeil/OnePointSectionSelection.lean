/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointIncrement
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStepanovGrid
import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceConstants
import Mathlib.Data.Fintype.EquivFin

/-!
# Selecting one-point sections with distinct pole orders

The local jump bound converts a Riemann-space dimension lower bound into
many strict levels of the pole filtration.  Choosing one section at each
strict level, and adjoining the constant section, produces a linearly
independent family with distinct pole-order digits in a prescribed range.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance sectionSelectionConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance sectionSelectionConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- With exact constants, the initial one-point Riemann space has dimension
one. -/
theorem finiteExtensionOnePointRiemannSpace_zero_finrank
    (P : FiniteExtensionPlace K L)
    (hconstants : algebraicClosure K L = ⊥) :
    Module.finrank K (finiteExtensionOnePointRiemannSpace K L P 0) = 1 := by
  classical
  change Module.finrank K
    (finiteExtensionRiemannSpace K L (Finsupp.single P (0 : ℤ))) = 1
  have hzero : Finsupp.single P (0 : ℤ) =
      (0 : FiniteExtensionDivisor K L) := by
    ext v
    by_cases hv : v = P <;> simp [hv]
  rw [hzero]
  exact finiteExtensionRiemannSpace_zero_finrank K L hconstants

/-- A final dimension lower bound forces the stated number of strict levels
in the one-point filtration. -/
theorem le_card_onePointStrictLevels_of_finrank_lower
    (P : FiniteExtensionPlace K L) (N m : ℕ)
    (hconstants : algebraicClosure K L = ⊥)
    (hlower :
      1 + finiteExtensionPlaceDegree K L P * m ≤
        Module.finrank K (finiteExtensionOnePointRiemannSpace K L P N)) :
    m ≤ (strictFiltrationLevels
      (fun n => finiteExtensionOnePointRiemannSpace K L P n) N).card := by
  apply le_card_strictFiltrationLevels_of_initial_add_mul_le_finrank
    (R := fun n => finiteExtensionOnePointRiemannSpace K L P n)
    (d := finiteExtensionPlaceDegree K L P)
  · exact finiteExtensionPlaceDegree_pos K L P
  · intro n
    exact finiteExtensionOnePointRiemannSpace_mono K L P (by omega)
  · intro n
    exact finiteExtensionOnePointRiemannSpace_finrank_succ_le K L P n
  · rw [finiteExtensionOnePointRiemannSpace_zero_finrank K L P hconstants]
    exact hlower

/-- Select a prescribed number of positive-pole sections from the strict
levels below `N`. -/
theorem exists_onePointSections_of_le_card_strictLevels
    (P : FiniteExtensionPlace K L) (N m : ℕ)
    (hm : m ≤ (strictFiltrationLevels
      (fun n => finiteExtensionOnePointRiemannSpace K L P n) N).card) :
    ∃ (f : Fin m → L) (d : Fin m → ℕ),
      (∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P N) ∧
      (∀ i, f i ≠ 0) ∧
      (∀ i, finiteExtensionPrincipalDivisor K L (f i) P = -(d i : ℤ)) ∧
      Function.Injective d ∧
      (∀ i, 0 < d i ∧ d i ≤ N) ∧
      LinearIndependent K f := by
  classical
  let I := {n // n ∈ strictFiltrationLevels
    (fun r => finiteExtensionOnePointRiemannSpace K L P r) N}
  obtain ⟨F, hF, hFinjective⟩ :=
    exists_onePointRiemannSpace_sections_indexed_by_strictLevels K L P N
  have hcard : Fintype.card (Fin m) ≤ Fintype.card I := by
    rw [Fintype.card_fin]
    simpa only [I, Fintype.card_coe] using hm
  let e : Fin m ↪ I :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let f : Fin m → L := fun i => F (e i)
  let d : Fin m → ℕ := fun i => (e i).1 + 1
  have hdPositive (i : Fin m) : 0 < d i := by
    simp [d]
  have hdLe (i : Fin m) : d i ≤ N := by
    have hiRange : (e i).1 ∈ Finset.range N :=
      (Finset.mem_filter.mp (e i).2).1
    have hiLt : (e i).1 < N := Finset.mem_range.mp hiRange
    simp only [d]
    omega
  have hfMem (i : Fin m) :
      f i ∈ finiteExtensionOnePointRiemannSpace K L P N := by
    apply finiteExtensionOnePointRiemannSpace_mono K L P (hdLe i)
    exact (hF (e i)).1
  have hfNotMem (i : Fin m) :
      f i ∉ finiteExtensionOnePointRiemannSpace K L P (e i).1 :=
    (hF (e i)).2.1
  have hfNe (i : Fin m) : f i ≠ 0 := by
    intro hzero
    apply hfNotMem i
    rw [hzero]
    exact Submodule.zero_mem _
  have hfOrder (i : Fin m) :
      finiteExtensionPrincipalDivisor K L (f i) P = -(d i : ℤ) := by
    simpa only [f, d] using (hF (e i)).2.2
  have hdInjective : Function.Injective d := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    simp only [d] at hij
    omega
  have horderInjective : Function.Injective
      (fun i => finiteExtensionPrincipalDivisor K L (f i) P) := by
    intro i j hij
    apply hdInjective
    have hcast : -(d i : ℤ) = -(d j : ℤ) := by
      rw [← hfOrder i, ← hfOrder j]
      exact hij
    exact_mod_cast (neg_inj.mp hcast)
  refine ⟨f, d, hfMem, hfNe, hfOrder, hdInjective,
    fun i => ⟨hdPositive i, hdLe i⟩, ?_⟩
  exact linearIndependent_of_injective_finiteExtensionPrincipalDivisor_order
    K L P f hfNe horderInjective

/-- Adjoin the constant section to a selected positive-pole family.  The
resulting pole digits start at zero and remain pairwise distinct. -/
theorem exists_onePointSectionsWithConstant_of_le_card_strictLevels
    (P : FiniteExtensionPlace K L) (N m : ℕ)
    (hm : m ≤ (strictFiltrationLevels
      (fun n => finiteExtensionOnePointRiemannSpace K L P n) N).card) :
    ∃ (f : Option (Fin m) → L) (d : Option (Fin m) → ℕ),
      (∀ i, f i ∈ finiteExtensionOnePointRiemannSpace K L P N) ∧
      (∀ i, f i ≠ 0) ∧
      (∀ i, finiteExtensionPrincipalDivisor K L (f i) P = -(d i : ℤ)) ∧
      Function.Injective d ∧
      (∀ i, d i ≤ N) ∧
      LinearIndependent K f := by
  classical
  obtain ⟨f₀, d₀, hf₀Mem, hf₀Ne, hf₀Order, hd₀Injective,
      hd₀Range, hf₀LI⟩ :=
    exists_onePointSections_of_le_card_strictLevels K L P N m hm
  let f : Option (Fin m) → L
    | none => 1
    | some i => f₀ i
  let d : Option (Fin m) → ℕ
    | none => 0
    | some i => d₀ i
  have hfMem : ∀ i, f i ∈
      finiteExtensionOnePointRiemannSpace K L P N := by
    intro i
    cases i with
    | none =>
        simpa [f] using
          algebraMap_mem_finiteExtensionOnePointRiemannSpace K L P N (1 : K)
    | some i => simpa [f] using hf₀Mem i
  have hfNe : ∀ i, f i ≠ 0 := by
    intro i
    cases i with
    | none => simp [f]
    | some i => simpa [f] using hf₀Ne i
  have hfOrder : ∀ i,
      finiteExtensionPrincipalDivisor K L (f i) P = -(d i : ℤ) := by
    intro i
    cases i with
    | none =>
        simp [f, d, finiteExtensionPrincipalDivisor_one]
    | some i => simpa [f, d] using hf₀Order i
  have hdInjective : Function.Injective d := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j =>
            exfalso
            have hj := (hd₀Range j).1
            simp [d] at hij
            omega
    | some i =>
        cases j with
        | none =>
            exfalso
            have hi := (hd₀Range i).1
            simp [d] at hij
            omega
        | some j =>
            congr 1
            exact hd₀Injective (by simpa [d] using hij)
  have horderInjective : Function.Injective
      (fun i => finiteExtensionPrincipalDivisor K L (f i) P) := by
    intro i j hij
    apply hdInjective
    have hcast : -(d i : ℤ) = -(d j : ℤ) := by
      rw [← hfOrder i, ← hfOrder j]
      exact hij
    exact_mod_cast (neg_inj.mp hcast)
  refine ⟨f, d, hfMem, hfNe, hfOrder, hdInjective, ?_, ?_⟩
  · intro i
    cases i with
    | none => simp [d]
    | some i => simpa [d] using (hd₀Range i).2
  · exact linearIndependent_of_injective_finiteExtensionPrincipalDivisor_order
      K L P f hfNe horderInjective

end

end BGS.HasseWeil
