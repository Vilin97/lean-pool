/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.KStatistic

/-!
# Mean-one two-point systems

This file develops the two-point reduction used in the formal proof of
Theorem 2.1.  It records the canonical parametrization

`Yᵢ ∈ {1 - γᵢ, 1 + βᵢ}`,  `P(Yᵢ = 1 + βᵢ) = γᵢ / (γᵢ + βᵢ)`

and proves the required Boolean-lattice monotonicity.  The latter is obtained
directly from the coordinatewise antitonicity of the exponential Dirichlet
statistic.
-/

open MeasureTheory ProbabilityTheory Set

namespace Feige

section Parameters

/-- Probability of the high value in a mean-one two-point law. -/
noncomputable def highProbability (γ β : ℝ) : ℝ :=
  γ / (γ + β)

/-- The low value in the mean-one two-point parametrization. -/
def lowValue (γ : ℝ) : ℝ := 1 - γ

/-- The high value in the mean-one two-point parametrization. -/
def highValue (β : ℝ) : ℝ := 1 + β

theorem highProbability_nonneg {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    0 ≤ highProbability γ β := by
  exact div_nonneg hγ (add_pos_of_nonneg_of_pos hγ hβ).le

theorem highProbability_le_one {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    highProbability γ β ≤ 1 := by
  rw [highProbability, div_le_one (add_pos_of_nonneg_of_pos hγ hβ)]
  linarith

/-- The complementary probability in symmetric form. -/
theorem one_sub_highProbability {γ β : ℝ} (h : γ + β ≠ 0) :
    1 - highProbability γ β = β / (γ + β) := by
  rw [highProbability]
  field_simp
  ring

/-- The parametrized two-point law has mean exactly one. -/
theorem twoPoint_mean_one {γ β : ℝ} (h : γ + β ≠ 0) :
    highProbability γ β * highValue β +
        (1 - highProbability γ β) * lowValue γ = 1 := by
  rw [one_sub_highProbability h]
  simp only [highProbability, highValue, lowValue]
  field_simp
  ring

end Parameters

section BooleanLattice

variable {ι : Type*} [Fintype ι]

/-- The vector encoded by a high set `S`: coordinates in `S` take their
high value, and all remaining coordinates take their low value. -/
noncomputable def twoPointVector (γ β : ι → ℝ) (S : Set ι) (i : ι) : ℝ :=
  by
    classical
    exact if i ∈ S then highValue (β i) else lowValue (γ i)

/-- The Dirichlet statistic at the two-point vector encoded by `S`. -/
noncomputable def twoPointK (γ β : ι → ℝ) (S : Set ι) : ℝ :=
  dirichletK (twoPointVector γ β S)

/-- At the bottom of the Boolean lattice every coefficient in the internal
exponential event is nonpositive, so the defining event is certain. -/
theorem twoPointK_empty (γ β : ι → ℝ) (hγ : ∀ i, 0 ≤ γ i) :
    twoPointK γ β ∅ = 1 := by
  classical
  have hevent : kEvent (twoPointVector γ β ∅) = Set.univ := by
    ext e
    simp only [kEvent, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have hsum :
        (∑ i, (twoPointVector γ β ∅ i - 1) * (e (some i) : ℝ)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      simp only [twoPointVector, Set.mem_empty_iff_false, ite_false, lowValue]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hγ i])
        (e (some i)).coe_nonneg
    exact hsum.trans (e none).coe_nonneg
  rw [twoPointK, dirichletK, hevent]
  exact probReal_univ

omit [Fintype ι] in
theorem twoPointVector_mono {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i) :
    Monotone (twoPointVector γ β : Set ι → ι → ℝ) := by
  classical
  intro A B hAB i
  by_cases hiA : i ∈ A
  · have hiB : i ∈ B := hAB hiA
    simp [twoPointVector, hiA, hiB]
  · by_cases hiB : i ∈ B
    · simp only [twoPointVector, ite_eq_right hiA, ite_eq_left hiB, lowValue, highValue]
      linarith [hγ i, hβ i]
    · simp [twoPointVector, hiA, hiB]

/-- Moving upward in the Boolean lattice can only decrease the Dirichlet
statistic. -/
theorem twoPointK_antitone {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i) :
    Antitone (twoPointK γ β : Set ι → ℝ) := by
  intro A B hAB
  exact dirichletK_antitone (twoPointVector_mono hγ hβ hAB)

section ProductHighSet

variable [DecidableEq ι]

/-- Product-law mass of a high set. -/
def highSetMass (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ Finset.univ \ S, (1 - p i)

theorem highSetMass_nonneg {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι) :
    0 ≤ highSetMass p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i _ ↦ hp0 i
  · exact Finset.prod_nonneg fun i _ ↦ sub_nonneg.mpr (hp1 i)

/-- The product masses over all Boolean-lattice states sum to one. -/
theorem sum_highSetMass (p : ι → ℝ) :
    (∑ S ∈ Finset.univ.powerset, highSetMass p S) = 1 := by
  simp only [highSetMass]
  rw [← Finset.prod_add]
  simp

/-- Finset-indexed version of `Kₘ(S)`, convenient for finite products and
maximal-chain constructions. -/
noncomputable def twoPointKFinset (γ β : ι → ℝ) (S : Finset ι) : ℝ :=
  twoPointK γ β (S : Set ι)

omit [DecidableEq ι] in
theorem twoPointKFinset_antitone {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i) :
    Antitone (twoPointKFinset γ β : Finset ι → ℝ) := by
  intro A B hAB
  exact twoPointK_antitone hγ hβ (by simpa using hAB)

/-- Coordinatewise high probabilities in the two-point parametrization. -/
noncomputable def twoPointHighProbability (γ β : ι → ℝ) (i : ι) : ℝ :=
  highProbability (γ i) (β i)

/-- Rejection probability under the independent two-point product law,
written as a finite sum over high sets. -/
noncomputable def twoPointRejectionMass
    (γ β : ι → ℝ) (α : ℝ) : ℝ := by
  classical
  exact ∑ S ∈ Finset.univ.powerset.filter
      (fun S ↦ twoPointKFinset γ β S ≤ α),
    highSetMass (twoPointHighProbability γ β) S

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointHighProbability_nonneg {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) (i : ι) :
    0 ≤ twoPointHighProbability γ β i :=
  highProbability_nonneg (hγ i) (hβ i)

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointHighProbability_le_one {γ β : ι → ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) (i : ι) :
    twoPointHighProbability γ β i ≤ 1 :=
  highProbability_le_one (hγ i) (hβ i)

theorem twoPointRejectionMass_nonneg {γ β : ι → ℝ} {α : ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) :
    0 ≤ twoPointRejectionMass γ β α := by
  classical
  unfold twoPointRejectionMass
  exact Finset.sum_nonneg fun S _ ↦ highSetMass_nonneg
    (twoPointHighProbability_nonneg hγ hβ)
    (twoPointHighProbability_le_one hγ hβ) S

theorem twoPointRejectionMass_le_one {γ β : ι → ℝ} {α : ℝ}
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i) :
    twoPointRejectionMass γ β α ≤ 1 := by
  classical
  unfold twoPointRejectionMass
  calc
    (∑ S ∈ Finset.univ.powerset.filter
          (fun S ↦ twoPointKFinset γ β S ≤ α),
        highSetMass (twoPointHighProbability γ β) S) ≤
        ∑ S ∈ Finset.univ.powerset,
          highSetMass (twoPointHighProbability γ β) S := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro S _ _
        exact highSetMass_nonneg
          (twoPointHighProbability_nonneg hγ hβ)
          (twoPointHighProbability_le_one hγ hβ) S
    _ = 1 := sum_highSetMass _

end ProductHighSet

end BooleanLattice

end Feige
