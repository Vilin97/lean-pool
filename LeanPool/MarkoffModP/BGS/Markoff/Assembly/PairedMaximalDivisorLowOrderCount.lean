/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.MaximalDivisorLowOrderCount

/-!
# Small-order trace counts after inversion pairing

The trace maps on both rotation tori identify an eigenvalue with its
inverse. Applying this before the maximal-divisor union removes the factor
two that is lost by counting eigenvalues instead of traces.
-/

namespace BGS.Markoff

open BGS.NumberTheory

noncomputable section

section InvolutionImage

variable {G T : Type*} [Group G] [Fintype G] [DecidableEq G]
  [DecidableEq T] [IsCyclic G]

/-- An inversion-invariant map has at most half as many values as inputs,
apart from the at most two elements satisfying `x² = 1`. -/
theorem two_mul_card_image_le_card_add_two_of_inv_invariant
    (s : Finset G) (f : G → T)
    (hsinv : ∀ x ∈ s, x⁻¹ ∈ s)
    (hfinv : ∀ x, f x⁻¹ = f x) :
    2 * (s.image f).card ≤ s.card + 2 := by
  classical
  let fixed : Finset G := s.filter fun x => x⁻¹ = x
  have hfixedSubset :
      fixed ⊆ BGS.NumberTheory.elementsWithPowOne G 2 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [BGS.NumberTheory.mem_elementsWithPowOne_iff]
    have hmul := congrArg (fun y : G => y * x) hx.2
    simpa [pow_two] using hmul.symm
  have hfixedCard : fixed.card ≤ 2 :=
    (Finset.card_le_card hfixedSubset).trans
      (IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num))
  have hcardFibers :
      s.card =
        ∑ y ∈ s.image f, (s.filter fun x => f x = y).card :=
    Finset.card_eq_sum_card_fiberwise
      (s := s) (t := s.image f) (f := f) (by
        intro x hx
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hfiber :
      ∀ y ∈ s.image f,
        2 ≤ (s.filter fun x => f x = y).card +
          if y ∈ fixed.image f then 1 else 0 := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    by_cases hyfixed : y ∈ fixed.image f
    · rw [ite_eq_left hyfixed]
      have hxFiber : x ∈ s.filter fun z => f z = y :=
        Finset.mem_filter.mpr ⟨hx, hxy⟩
      have hpositive : 1 ≤ (s.filter fun z => f z = y).card :=
        Finset.one_le_card.mpr ⟨x, hxFiber⟩
      omega
    · rw [ite_eq_right hyfixed]
      have hfix : x⁻¹ ≠ x := by
        intro h
        apply hyfixed
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩, hxy⟩
      have hxFiber : x ∈ s.filter fun z => f z = y :=
        Finset.mem_filter.mpr ⟨hx, hxy⟩
      have hxInvFiber : x⁻¹ ∈ s.filter fun z => f z = y := by
        refine Finset.mem_filter.mpr ⟨hsinv x hx, ?_⟩
        rw [hfinv, hxy]
      have hpair :
          ({x, x⁻¹} : Finset G) ⊆ s.filter fun z => f z = y := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxFiber
        · exact hxInvFiber
      have hne : x ≠ x⁻¹ := Ne.symm hfix
      have htwo : 2 ≤ (s.filter fun z => f z = y).card := by
        simpa [hne] using Finset.card_le_card hpair
      simpa using htwo
  have hfixedImageSubset : fixed.image f ⊆ s.image f := by
    apply Finset.image_subset_iff.mpr
    intro x hx
    exact Finset.mem_image.mpr
      ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  have hconditional :
      (∑ y ∈ s.image f, if y ∈ fixed.image f then 1 else 0) =
        (fixed.image f).card := by
    calc
      (∑ y ∈ s.image f, if y ∈ fixed.image f then 1 else 0) =
          ((s.image f).filter fun y => y ∈ fixed.image f).card := by
        simp
      _ = (fixed.image f).card := by
        congr 1
        ext y
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨hfixedImageSubset h, h⟩
  calc
    2 * (s.image f).card =
        ∑ _y ∈ s.image f, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ y ∈ s.image f,
        ((s.filter fun x => f x = y).card +
          if y ∈ fixed.image f then 1 else 0) := by
      gcongr with y hy
      exact hfiber y hy
    _ = s.card + (fixed.image f).card := by
      rw [Finset.sum_add_distrib, ← hcardFibers, hconditional]
    _ ≤ s.card + 2 := Nat.add_le_add_left
      (Finset.card_image_le.trans hfixedCard) _

end InvolutionImage

end

end BGS.Markoff
