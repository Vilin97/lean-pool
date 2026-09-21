/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Convolution

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointWellOrdered
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The multi-factor convolution formula

Berarducci, Remark 7.6: the two-factor convolution formula extends by induction to a product of
finitely many series. The germ of the product of a list of series at a cutoff is the finite sum,
over the exponent lists summing to that cutoff, of the products of the germs of the factors at
those exponents.

The index set is built by the same recursion as the formula. At a cons the two-factor index set
selects the exponent of the head, and the exponent lists of the tail are taken at the shifted
cutoff; the resulting families are pairwise disjoint because they have distinct heads, and the
cons map is injective, so the double sum collapses to a single sum. The empty list contributes the
unit exactly at cutoff zero, since the support of one is the single exponent zero and its germ
vanishes elsewhere.
-/

universe v

public noncomputable section

open HahnSeries

namespace Berarducci

variable {K : Type v} [Field K]

/-- The product of the germs of a list of series at a list of exponents. -/
def germListProd : List K⟦ℝ⟧ → List ℝ → Germ K
  | [], [] => 1
  | b :: l, β :: f => germAt b β * germListProd l f
  | _, _ => 0

@[simp]
theorem germListProd_nil : germListProd ([] : List K⟦ℝ⟧) [] = 1 :=
  (rfl)

@[simp]
theorem germListProd_cons (b : K⟦ℝ⟧) (l : List K⟦ℝ⟧) (β : ℝ) (f : List ℝ) :
    germListProd (b :: l) (β :: f) = germAt b β * germListProd l f :=
  (rfl)

/-- The finite index set of the multi-factor convolution formula. -/
def convolutionIndexList : List K⟦ℝ⟧ → ℝ → Finset (List ℝ)
  | [], γ => if γ = 0 then {[]} else ∅
  | b :: l, γ =>
      (convolutionIndex b l.prod γ).biUnion
        fun β ↦ (convolutionIndexList l (γ - β)).image (β :: ·)

@[simp]
theorem convolutionIndexList_nil (γ : ℝ) :
    convolutionIndexList ([] : List K⟦ℝ⟧) γ = if γ = 0 then {[]} else ∅ :=
  (rfl)

@[simp]
theorem convolutionIndexList_cons (b : K⟦ℝ⟧) (l : List K⟦ℝ⟧) (γ : ℝ) :
    convolutionIndexList (b :: l) γ =
      (convolutionIndex b l.prod γ).biUnion
        fun β ↦ (convolutionIndexList l (γ - β)).image (β :: ·) :=
  (rfl)

theorem length_of_mem_convolutionIndexList :
    ∀ (l : List K⟦ℝ⟧) (γ : ℝ) {f : List ℝ}, f ∈ convolutionIndexList l γ →
      f.length = l.length
  | [], γ, f, hf => by
      rw [convolutionIndexList_nil] at hf
      by_cases hγ : γ = 0
      · rw [if_pos hγ, Finset.mem_singleton] at hf
        rw [hf]
        rfl
      · rw [if_neg hγ] at hf
        exact absurd hf (Finset.notMem_empty f)
  | b :: t, γ, f, hf => by
      rw [convolutionIndexList_cons, Finset.mem_biUnion] at hf
      obtain ⟨β, _, hβ⟩ := hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hβ
      rw [List.length_cons, List.length_cons,
        length_of_mem_convolutionIndexList t (γ - β) hg]

theorem sum_of_mem_convolutionIndexList :
    ∀ (l : List K⟦ℝ⟧) (γ : ℝ) {f : List ℝ},
      f ∈ convolutionIndexList l γ → f.sum = γ
  | [], γ, f, hf => by
      rw [convolutionIndexList_nil] at hf
      by_cases hγ : γ = 0
      · rw [if_pos hγ, Finset.mem_singleton] at hf
        rw [hf, List.sum_nil, hγ]
      · rw [if_neg hγ] at hf
        exact absurd hf (Finset.notMem_empty f)
  | b :: t, γ, f, hf => by
      rw [convolutionIndexList_cons, Finset.mem_biUnion] at hf
      obtain ⟨β, _, hβ⟩ := hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hβ
      rw [List.sum_cons, sum_of_mem_convolutionIndexList t (γ - β) hg]
      ring

private theorem germAt_one_of_ne_zero {γ : ℝ} (hγ : γ ≠ 0) :
    germAt (1 : K⟦ℝ⟧) γ = 0 := by
  refine germAt_eq_zero_of_not_mem_closure_support ?_
  have hsupp : (1 : K⟦ℝ⟧).support = {(0 : ℝ)} := by
    change (HahnSeries.single (0 : ℝ) (1 : K)).support = _
    exact HahnSeries.support_single_of_ne one_ne_zero
  rw [hsupp, closure_singleton]
  simpa using hγ

/-- Berarducci, Remark 7.6: the germ of a product of a list of series at a cutoff is the finite
sum, over the exponent lists summing to that cutoff, of the products of the germs of the factors
at those exponents. -/
theorem germAt_listProd (l : List K⟦ℝ⟧) (γ : ℝ) :
    germAt l.prod γ = ∑ f ∈ convolutionIndexList l γ, germListProd l f := by
  induction l generalizing γ with
  | nil =>
    rw [List.prod_nil, convolutionIndexList_nil]
    by_cases hγ : γ = 0
    · subst hγ
      rw [if_pos rfl, Finset.sum_singleton, germListProd_nil]
      change germAt ((1 : Series K) : K⟦ℝ⟧) 0 = 1
      rw [germAt_apply, translatedTruncation_zero]
      exact map_one toGerm
    · rw [if_neg hγ, Finset.sum_empty]
      exact germAt_one_of_ne_zero hγ
  | cons b t ih =>
    rw [List.prod_cons, germAt_mul, convolutionIndexList_cons]
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun β _ ↦ ?_
      rw [Finset.sum_image (fun _ _ _ _ h ↦ (List.cons_inj_right β).mp h), ih (γ - β),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun f _ ↦ rfl
    · intro x _ y _ hxy
      refine Finset.disjoint_left.mpr fun g hg hg' ↦ hxy ?_
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨f', _, hf'⟩ := Finset.mem_image.mp hg'
      exact (List.cons.injEq _ _ _ _ ▸ hf').1.symm

end Berarducci
