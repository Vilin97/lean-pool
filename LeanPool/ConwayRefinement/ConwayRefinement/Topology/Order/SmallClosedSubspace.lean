/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.OrderedAddGroup
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.SetTheory.Cardinal.Finsupp
public import Mathlib.SetTheory.Cardinal.Rat
public import Mathlib.Topology.Algebra.Module.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Supports in closed rational subspaces

Density of a rational span in its closure bounds every well-ordered subset of the closure by the
cardinality of the original span. This keeps supports produced by Cantor–Bendixson germ refinement
below a prescribed cardinal without bounding the whole closed subspace.
-/

open Set
open Cardinal

universe u

public noncomputable section

namespace Submodule

variable {C : Type u} [AddCommGroup C] [LinearOrder C] [IsOrderedAddMonoid C]
  [Module ℚ C] [PosSMulMono ℚ C]
  [TopologicalSpace C] [OrderTopology C] [IsTopologicalAddGroup C]
  [DenselyOrdered C]

local instance : PosSMulStrictMono ℚ C := PosSMulMono.toPosSMulStrictMono

omit [IsOrderedAddMonoid C] in
/-- Rational scalar multiplication is continuous in the order topology of an ordered rational
vector space. -/
theorem continuous_rat_smul (q : ℚ) : Continuous fun x : C ↦ q • x := by
  rcases lt_trichotomy q 0 with hq | hq | hq
  · have hpos : 0 < -q := neg_pos.mpr hq
    have hcont : Continuous fun x : C ↦ (-q) • x := by
      apply Monotone.continuous_of_surjective
      · intro x y hxy
        exact smul_le_smul_of_nonneg_left hxy hpos.le
      · intro y
        refine ⟨(-q)⁻¹ • y, ?_⟩
        change (-q) • ((-q)⁻¹ • y) = y
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    convert continuous_neg.comp hcont using 1
    funext x
    simp
  · subst q
    simpa using (continuous_const : Continuous fun _ : C ↦ (0 : C))
  · apply Monotone.continuous_of_surjective
    · intro x y hxy
      exact smul_le_smul_of_nonneg_left hxy hq.le
    · intro y
      refine ⟨q⁻¹ • y, ?_⟩
      change q • (q⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul]

instance instContinuousConstSMulRat : ContinuousConstSMul ℚ C :=
  ⟨continuous_rat_smul⟩

/-- Distinct points in the closed rational span are separated by a point of the original span. -/
theorem exists_span_between_of_ne (S : Set C)
    (x y : (span ℚ S).topologicalClosure) (hxy : x ≠ y) :
    ∃ z : span ℚ S, (x : C) < z ∧ (z : C) < y ∨
      (y : C) < z ∧ (z : C) < x := by
  let P := span ℚ S
  rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hxy) with hxy' | hyx'
  · let m : C := (2 : ℚ)⁻¹ • ((x : C) + (y : C))
    have hm : m ∈ closure (P : Set C) := by
      have hm' : m ∈ P.topologicalClosure := by
        simpa [m] using P.topologicalClosure.smul_mem ((2 : ℚ)⁻¹)
          (P.topologicalClosure.add_mem x.2 y.2)
      rw [← topologicalClosure_coe]
      exact hm'
    have hxm : (x : C) < m := by
      dsimp [m]
      calc
        (x : C) = (2 : ℚ)⁻¹ • ((x : C) + (x : C)) := by
          rw [smul_add, ← add_smul]
          norm_num
        _ < (2 : ℚ)⁻¹ • ((x : C) + (y : C)) :=
          smul_lt_smul_of_pos_left
            (add_lt_add_left hxy' (x : C) |>.trans_eq (add_comm _ _)) (by norm_num)
    have hmy : m < (y : C) := by
      dsimp [m]
      calc
        (2 : ℚ)⁻¹ • ((x : C) + (y : C)) <
            (2 : ℚ)⁻¹ • ((y : C) + (y : C)) :=
          smul_lt_smul_of_pos_left
            (by simpa [add_comm] using (add_lt_add_left hxy' (y : C))) (by norm_num)
        _ = (y : C) := by
          rw [smul_add, ← add_smul]
          norm_num
    obtain ⟨z, hzI, hzP⟩ :=
      mem_closure_iff.mp hm (Ioo (x : C) (y : C)) isOpen_Ioo ⟨hxm, hmy⟩
    exact ⟨⟨z, hzP⟩, Or.inl hzI⟩
  · let m : C := (2 : ℚ)⁻¹ • ((y : C) + (x : C))
    have hm : m ∈ closure (P : Set C) := by
      have hm' : m ∈ P.topologicalClosure := by
        simpa [m] using P.topologicalClosure.smul_mem ((2 : ℚ)⁻¹)
          (P.topologicalClosure.add_mem y.2 x.2)
      rw [← topologicalClosure_coe]
      exact hm'
    have hym : (y : C) < m := by
      dsimp [m]
      calc
        (y : C) = (2 : ℚ)⁻¹ • ((y : C) + (y : C)) := by
          rw [smul_add, ← add_smul]
          norm_num
        _ < (2 : ℚ)⁻¹ • ((y : C) + (x : C)) :=
          smul_lt_smul_of_pos_left
            (add_lt_add_left hyx' (y : C) |>.trans_eq (add_comm _ _)) (by norm_num)
    have hmx : m < (x : C) := by
      dsimp [m]
      calc
        (2 : ℚ)⁻¹ • ((y : C) + (x : C)) <
            (2 : ℚ)⁻¹ • ((x : C) + (x : C)) :=
          smul_lt_smul_of_pos_left
            (by simpa [add_comm] using (add_lt_add_left hyx' (x : C))) (by norm_num)
        _ = (x : C) := by
          rw [smul_add, ← add_smul]
          norm_num
    obtain ⟨z, hzI, hzP⟩ :=
      mem_closure_iff.mp hm (Ioo (y : C) (x : C)) isOpen_Ioo ⟨hym, hmx⟩
    exact ⟨⟨z, hzP⟩, Or.inr hzI⟩

/-- Every well-ordered subset of the closed rational span of a small nonempty set is small. -/
@[blueprint "lem:well-ordered-subset-closed-rational-span-cardinality"
  (phase := "Refinement over Archimedean classes")
  (title := "Well-ordered subsets of closed rational spans")
  (statement := /--
    Let $C$ be a densely ordered rational vector space with its order topology,
    let $\kappa>\aleph_0$, and let $S\subseteq C$ be nonempty with
    $\#S<\kappa$.  Every well-ordered subset of the topological closure of
    $\operatorname{span}_{\mathbb Q}(S)$ has cardinality less than $\kappa$.
  -/)
  (proof := /--
    For each nonmaximal point $x$ of the well-ordered subset, let $x^+$ be its
    successor and choose a point of $\operatorname{span}_{\mathbb Q}(S)$
    strictly between $x$ and $x^+$.  The resulting intervals are disjoint, so
    this choice is injective; the possible maximum accounts for one additional
    point.  Hence the subset has cardinality at most
    $\#\operatorname{span}_{\mathbb Q}(S)+1$.  Finite rational linear
    combinations identify the latter span with a subset of
    $S\to_0\mathbb Q$, whose cardinality is
    $\max\{\#S,\aleph_0\}<\kappa$.
  -/)]
theorem mk_lt_of_isPWO_topologicalClosure_span
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
    (S : Set C) (hS : #S < κ) (hSne : S.Nonempty)
    (W : Set (span ℚ S).topologicalClosure) (hW : W.IsPWO) :
    #W < κ := by
  let upper (x : W) : Set (span ℚ S).topologicalClosure := W ∩ Set.Ioi x
  have upperWF (x : W) : (upper x).IsWF := hW.isWF.mono Set.inter_subset_left
  let next (x : W) (h : (upper x).Nonempty) : W :=
    ⟨(upperWF x).min h, ((upperWF x).min_mem h).1⟩
  have lt_next (x : W) (h : (upper x).Nonempty) : x < next x h :=
    ((upperWF x).min_mem h).2
  have exists_between_span (x : W) (h : (upper x).Nonempty) :
      ∃ z : span ℚ S, (x : C) < z ∧ (z : C) < next x h := by
    have hne :
        (x : (span ℚ S).topologicalClosure) ≠
          (next x h : (span ℚ S).topologicalClosure) := by
      intro hxy
      exact (lt_next x h).ne (Subtype.ext hxy)
    obtain ⟨z, hz | hz⟩ := exists_span_between_of_ne S x (next x h) hne
    · exact ⟨z, hz⟩
    · exact ((show (x : C) < next x h by exact lt_next x h).asymm
        (hz.1.trans hz.2)).elim
  let between (x : W) (h : (upper x).Nonempty) : span ℚ S :=
    Classical.choose (exists_between_span x h)
  have between_spec (x : W) (h : (upper x).Nonempty) :
      (x : C) < between x h ∧ (between x h : C) < next x h := by
    exact Classical.choose_spec (exists_between_span x h)
  classical
  let f : W → (span ℚ S) ⊕ Unit := fun x ↦
    if h : (upper x).Nonempty then Sum.inl (between x h) else Sum.inr ()
  have hf : Function.Injective f := by
    have f_ne_of_lt {x y : W} (hxy : x < y) : f x ≠ f y := by
      have hx : (upper x).Nonempty := ⟨y, y.2, hxy⟩
      by_cases hy : (upper y).Nonempty
      · intro heq
        have heq' : between x hx = between y hy := by
          simpa only [f, dite_eq_left hx, dite_eq_left hy, Sum.inl.injEq] using heq
        have hnle : next x hx ≤ y := (upperWF x).min_le hx ⟨y.2, hxy⟩
        have hlt : (between x hx : C) < between y hy := by
          calc
            (between x hx : C) < next x hx := (between_spec x hx).2
            _ ≤ y := hnle
            _ < between y hy := (between_spec y hy).1
        exact hlt.ne (congrArg Subtype.val heq')
      · simp [f, hx, hy]
    intro x y hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact f_ne_of_lt hlt hxy
    · exact f_ne_of_lt hgt hxy.symm
  have hspan : #(span ℚ S) < κ := by
    letI : Nonempty S := hSne.to_subtype
    have hinj : Function.Injective (Span.repr ℚ S) := by
      intro x y hxy
      apply Subtype.ext
      have := congrArg (Finsupp.linearCombination ℚ ((↑) : S → C)) hxy
      simpa using this
    calc
      #(span ℚ S) ≤ #(S →₀ ℚ) := Cardinal.mk_le_of_injective hinj
      _ = max #S ℵ₀ := by
        simp
      _ < κ := max_lt hS Fact.out
  calc
    #W ≤ #(span ℚ S) + 1 := by
      simpa using Cardinal.mk_le_of_injective hf
    _ < κ := Cardinal.add_lt_of_lt (Fact.out : ℵ₀ < κ).le hspan
      (Cardinal.one_lt_aleph0.trans Fact.out)

end Submodule
