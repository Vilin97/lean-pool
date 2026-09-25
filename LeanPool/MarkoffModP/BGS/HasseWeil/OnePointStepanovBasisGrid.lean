/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FrobeniusRestriction
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStepanovGrid
public import Mathlib.Tactic

/-!
# One-point Stepanov grids from a full Riemann-space basis

The usual mixed-order grid chooses both tensor factors at distinct strict
levels.  For a place of degree greater than one, that discards most of the
second Riemann space.  This file proves that the second family may instead
be any linearly independent family.

Group a relation by the first index.  Frobenius linearity turns each row
into `u i * Frobenius (row i)`.  Every nonzero such term has order

`-d i + (#K) * order (row i)`.

The digits `d i < #K` are distinct, so these orders remain distinct modulo
`#K`, independently of the orders of the rows.  A unique least-order term
then rules out a nontrivial relation.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial BigOperators

noncomputable section

section FrobeniusInjectivity

variable (K A : Type*) [Field K] [Fintype K]
  [Field A] [Algebra K A]

/-- Frobenius iteration is injective on a field. -/
theorem powCardLinearMap_injective (n : ℕ) :
    Function.Injective (powCardLinearMap K A n) := by
  exact (powCardAlgHom K A n).injective

end FrobeniusInjectivity

private theorem digit_eq_of_neg_add_mul_eq
    {s d e : ℕ} (hd : d < s) (he : e < s)
    {a b : ℤ}
    (h : -(d : ℤ) + (s : ℤ) * a = -(e : ℤ) + (s : ℤ) * b) :
    d = e := by
  have hdiv : (s : ℤ) ∣ (d : ℤ) - (e : ℤ) := by
    refine ⟨a - b, ?_⟩
    linarith
  have habs : |(d : ℤ) - (e : ℤ)| < (s : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero := Int.eq_zero_of_abs_lt_dvd hdiv habs
  exact_mod_cast (sub_eq_zero.mp hzero)

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance basisGridConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance basisGridConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A bounded distinct first pole-order digit and an arbitrary linearly
independent second family produce a linearly independent Frobenius product
grid. -/
theorem onePointStepanovBasisGrid_linearIndependent
    {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteExtensionPlace K L)
    (u : α → L) (d : α → ℕ) (v : β → L)
    (hu : ∀ i, u i ≠ 0)
    (huOrder : ∀ i,
      finiteExtensionPrincipalDivisor K L (u i) P = -(d i : ℤ))
    (hdInjective : Function.Injective d)
    (hdigit : ∀ i, d i < Fintype.card K)
    (hvLI : LinearIndependent K v) :
    LinearIndependent K
      (fun ij : α × β => u ij.1 * (v ij.2) ^ Fintype.card K) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hrelation ij
  by_contra hcZero
  let row : α → L := fun i => ∑ j, c (i, j) • v j
  have hrowNe : row ij.1 ≠ 0 := by
    intro hzero
    have hcoeff := (Fintype.linearIndependent_iff.mp hvLI)
      (fun j => c (ij.1, j)) hzero ij.2
    exact hcZero hcoeff
  let S : Finset α := Finset.univ.filter (fun i => row i ≠ 0)
  have hijS : ij.1 ∈ S := by simp [S, hrowNe]
  have hSnonempty : S.Nonempty := ⟨ij.1, hijS⟩
  let term : α → L := fun i =>
    u i * powCardLinearMap K L 1 (row i)
  have htermNe : ∀ i ∈ S, term i ≠ 0 := by
    intro i hi
    have hpowNe : powCardLinearMap K L 1 (row i) ≠ 0 := by
      intro hzero
      apply (Finset.mem_filter.mp hi).2
      apply powCardLinearMap_injective K L 1
      simpa using hzero
    exact mul_ne_zero (hu i) hpowNe
  have htermOrder (i : α) (hi : i ∈ S) :
      finiteExtensionPrincipalDivisor K L (term i) P =
        -(d i : ℤ) + (Fintype.card K : ℤ) *
          finiteExtensionPrincipalDivisor K L (row i) P := by
    change finiteExtensionPrincipalDivisor K L
      (u i * powCardLinearMap K L 1 (row i)) P = _
    have hpowNe : powCardLinearMap K L 1 (row i) ≠ 0 := by
      intro hzero
      apply (Finset.mem_filter.mp hi).2
      apply powCardLinearMap_injective K L 1
      simpa using hzero
    rw [finiteExtensionPrincipalDivisor_mul K L _ _ (hu i) hpowNe]
    simp only [Finsupp.add_apply]
    rw [finiteExtensionPrincipalDivisor_powCardLinearMap_apply K L
        (row i) ((Finset.mem_filter.mp hi).2) 1 P,
      huOrder i]
    simp
  have htermOrderInjective : ∀ i ∈ S, ∀ j ∈ S,
      finiteExtensionPrincipalDivisor K L (term i) P =
        finiteExtensionPrincipalDivisor K L (term j) P → i = j := by
    intro i hi j hj hij
    apply hdInjective
    apply digit_eq_of_neg_add_mul_eq (hdigit i) (hdigit j)
    rw [← htermOrder i hi, ← htermOrder j hj]
    exact hij
  have hsumRelation : ∑ i ∈ S, term i = 0 := by
    calc
      ∑ i ∈ S, term i = ∑ i, term i := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        have hrowZero : row i = 0 := by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and,
            not_ne_iff] using hi
        simp [term, hrowZero]
      _ = ∑ i, ∑ j, c (i, j) •
          (u i * (v j) ^ Fintype.card K) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [term, row, map_sum, map_smul,
          powCardLinearMap_apply, pow_one, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Algebra.smul_def]
        ring
      _ = ∑ p : α × β, c p •
          (u p.1 * (v p.2) ^ Fintype.card K) := by
        rw [Fintype.sum_prod_type]
      _ = 0 := hrelation
  obtain ⟨i, hiS, hileast⟩ := S.exists_min_image
    (fun j => finiteExtensionPrincipalDivisor K L (term j) P) hSnonempty
  have htermMin : ∀ j ∈ S, j ≠ i →
      finiteExtensionPrincipalDivisor K L (term i) P <
        finiteExtensionPrincipalDivisor K L (term j) P := by
    intro j hj hji
    exact lt_of_le_of_ne (hileast j hj)
      (fun heq => hji (htermOrderInjective j hj i hiS heq.symm))
  exact False.elim ((finiteExtensionPrincipalDivisor_sum_eq_of_unique_min
    K L P S term i hiS htermNe htermMin).1 hsumRelation)

end

end BGS.HasseWeil
