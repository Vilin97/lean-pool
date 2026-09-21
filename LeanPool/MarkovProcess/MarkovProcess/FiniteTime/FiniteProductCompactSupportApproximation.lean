/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.FiniteProductStoneWeierstrass

/-!
# Compactly supported approximation on a finite product

This file upgrades compact-set Stone--Weierstrass approximation to a uniform approximation on the
whole product.  The key device is a product of one-coordinate compactly supported cutoffs.  Each
coordinate cutoff is one on the corresponding projection of the target's compact support.
-/

open Topology
open scoped CompactlySupported ZeroAtInfty

namespace MarkovProcess.PiContinuousMap

variable {I α : Type*} [Fintype I] [TopologicalSpace α]

/-- Coordinatewise compactly supported cutoffs for a compactly supported function.  The product
cutoff is one on the target's topological support, and its natural product box is compact. -/
theorem exists_coordinate_cutoffs_of_hasCompactSupport
    [T3Space α] [LocallyCompactSpace α] (f : C_c(I → α, ℝ)) :
    ∃ (φ : I → C₀(α, ℝ)) (B : Set (I → α)),
      IsCompact B ∧
      (∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
      Set.EqOn (∏ i, coordinate i ((φ i : C₀(α, ℝ)) : C(α, ℝ))) 1 (tsupport f) ∧
      tsupport f ⊆ B ∧
      Set.EqOn (∏ i, coordinate i ((φ i : C₀(α, ℝ)) : C(α, ℝ))) 0 Bᶜ := by
  classical
  have hprojection (i : I) : IsCompact ((fun x : I → α ↦ x i) '' tsupport f) :=
    f.hasCompactSupport.image (continuous_apply i)
  have hcutoff (i : I) :
      ∃ φ : C₀(α, ℝ),
        Set.EqOn φ 1 ((fun x : I → α ↦ x i) '' tsupport f) ∧
          HasCompactSupport φ ∧
          ∀ x, 0 ≤ φ x ∧ φ x ≤ 1 := by
    obtain ⟨u, huone, -, hucompact, hurange⟩ :=
      exists_continuous_one_zero_of_isCompact (hprojection i) isClosed_empty
        (Set.disjoint_empty _)
    exact ⟨⟨u, HasCompactSupport.is_zero_at_infty hucompact⟩, huone, hucompact, hurange⟩
  choose φ hφone hφcompact hφrange using hcutoff
  let B : Set (I → α) := Set.pi Set.univ (fun i ↦ tsupport (φ i))
  refine ⟨φ, B, isCompact_univ_pi hφcompact, hφrange, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.prod_apply, coordinate_apply, Pi.one_apply]
    apply Finset.prod_eq_one
    intro i hi
    exact hφone i ⟨x, hx, rfl⟩
  · intro x hx i hi
    apply subset_tsupport
    show φ i (x i) ≠ 0
    rw [hφone i ⟨x, hx, rfl⟩]
    exact one_ne_zero
  · intro x hx
    simp only [Finset.prod_apply, coordinate_apply, Pi.zero_apply]
    simp only [B, Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

/-- A compactly supported continuous function on a finite product can be approximated uniformly on
the whole product by the coordinate `C₀` algebra. -/
theorem exists_coordinateC0Subalgebra_near_compactlySupported
    [T3Space α] [LocallyCompactSpace α]
    (f : C_c(I → α, ℝ)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ h ∈ coordinateC0Subalgebra (I := I) (α := α),
      ∀ x, ‖h x - f x‖ < epsilon := by
  classical
  obtain ⟨φ, B, hBcompact, hφrange, hcutoff_one, hsupport_subset, hcutoff_zero⟩ :=
    exists_coordinate_cutoffs_of_hasCompactSupport f
  let q : C(I → α, ℝ) := ∏ i, coordinate i (((φ i : C₀(α, ℝ)) : C(α, ℝ)))
  obtain ⟨g, hgmem, hgnear⟩ :=
    exists_coordinateC0Subalgebra_near_on_isCompact (f := f.toContinuousMap) hBcompact hepsilon
  refine ⟨q * g, ?_, fun x ↦ ?_⟩
  · have hqmem : q ∈ coordinateC0Subalgebra (I := I) (α := α) := by
      dsimp only [q]
      have hprod (s : Finset I) :
          (∏ i ∈ s, coordinate i (((φ i : C₀(α, ℝ)) : C(α, ℝ)))) ∈
            coordinateC0Subalgebra (I := I) (α := α) := by
        induction s using Finset.induction_on with
        | empty => exact (coordinateC0Subalgebra (I := I) (α := α)).one_mem
        | @insert i s hi ih =>
            rw [Finset.prod_insert hi]
            exact (coordinateC0Subalgebra (I := I) (α := α)).mul_mem
              (coordinate_c0_mem_coordinateC0Subalgebra (I := I) i (φ i)) ih
      exact hprod Finset.univ
    exact (coordinateC0Subalgebra (I := I) (α := α)).mul_mem hqmem hgmem
  · by_cases hxB : x ∈ B
    · have hq_nonneg : 0 ≤ q x := by
        dsimp only [q]
        simp only [ContinuousMap.prod_apply, coordinate_apply]
        exact Finset.prod_nonneg fun i _ ↦ (hφrange i (x i)).1
      have hq_le_one : q x ≤ 1 := by
        dsimp only [q]
        simp only [ContinuousMap.prod_apply, coordinate_apply]
        exact Finset.prod_le_one (fun i _ ↦ (hφrange i (x i)).1)
          (fun i _ ↦ (hφrange i (x i)).2)
      have hqf : q x * f x = f x := by
        by_cases hxsupport : x ∈ tsupport f
        · have hqone : q x = 1 := by
            dsimp only [q]
            simpa only [ContinuousMap.prod_apply, Finset.prod_apply, coordinate_apply,
              Pi.one_apply] using hcutoff_one hxsupport
          rw [hqone, one_mul]
        · rw [image_eq_zero_of_notMem_tsupport hxsupport, mul_zero]
      rw [ContinuousMap.mul_apply, ← hqf, ← mul_sub]
      calc
        ‖q x * (g x - f x)‖ = ‖q x‖ * ‖g x - f x‖ := norm_mul _ _
        _ ≤ 1 * ‖g x - f x‖ := mul_le_mul_of_nonneg_right
          (by simpa only [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hq_le_one)
          (norm_nonneg _)
        _ < 1 * epsilon := mul_lt_mul_of_pos_left (hgnear x hxB) zero_lt_one
        _ = epsilon := one_mul _
    · have hqzero : q x = 0 := by
        dsimp only [q]
        simp only [ContinuousMap.prod_apply, coordinate_apply]
        simpa only [Finset.prod_apply, coordinate_apply, Pi.zero_apply] using hcutoff_zero hxB
      have hxfzero : f x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx ↦ hxB (hsupport_subset hx))
      rw [ContinuousMap.mul_apply, hqzero, zero_mul, hxfzero, sub_zero, norm_zero]
      exact hepsilon

end MarkovProcess.PiContinuousMap
