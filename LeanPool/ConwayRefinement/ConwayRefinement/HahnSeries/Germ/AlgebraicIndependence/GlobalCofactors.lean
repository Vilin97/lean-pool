/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Derivative
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Boundary
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TranslatedTruncationInterpolation

/-!
# Global cofactors from local data of fixed rank

Consider a nonpositive Hahn series whose translated truncation at every nonpositive cutoff,
including zero, has degree at most `β`. Its exact rank-`β` cutoffs accumulate nowhere. Suppose a
finite family of homogeneous lifts is given, each with a degree bound and strictly smaller proper
translated truncations, and at every exact rank-`β` cutoff local cofactors are prescribed that
correct the truncation below degree `β`. Interpolating those local cofactors produces global
cofactors with the same pointwise degree bounds, whose combination with the lifts corrects the
series below degree `β` at every nonpositive cutoff simultaneously. The subtracted term is an exact
finite combination of the lifts, so this step preserves membership in the ideal they generate.
-/

public noncomputable section

open Set Filter Topology
open scoped NatOrdinal

universe u v w

namespace HahnSeries.Nonpositive

variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

open Classical in
/-- Local cofactors at every exact top-rank cutoff interpolate to global cofactors. They keep the
prescribed pointwise degree bounds, and subtracting their products with the generators leaves a
series whose translated truncations have degree strictly below `β` at every nonpositive cutoff,
including zero. -/
theorem exists_forall_degree_translatedTruncLE_sub_sum_mul_lt (β : NatOrdinal.{u})
    {ι : Type w} [Fintype ι] (V : ι → Nonpositive G R) (ρ σ : ι → NatOrdinal.{u})
    (hgrade : ∀ j, ρ j + σ j ≤ β)
    (hV : ∀ j, ν (V j) ≤ σ j)
    (hVcut : ∀ j, ∀ x : G, x < 0 → ν (translatedTruncLE x (V j)) < σ j)
    (u : Nonpositive G R)
    (hu : ∀ x : G, x ≤ 0 → ν (translatedTruncLE x u) ≤ β)
    (w : {x // x ∈ (u : HahnSeries G R).closedSupport ∧
      (u : HahnSeries G R).closedSupport.cantorBendixsonRank
        (u : HahnSeries G R).closedSupport_isPWO x = β.val} → ι → Nonpositive G R)
    (hw : ∀ i j, ν (w i j) ≤ ρ j)
    (hcorr : ∀ i : {x // x ∈ (u : HahnSeries G R).closedSupport ∧
        (u : HahnSeries G R).closedSupport.cantorBendixsonRank
          (u : HahnSeries G R).closedSupport_isPWO x = β.val},
      ν (translatedTruncLE (i : G) u - ∑ j, w i j * V j) < β) :
    ∃ c : ι → Nonpositive G R,
      (∀ j, ∀ x : G, x ≤ 0 → ν (translatedTruncLE x (c j)) ≤ ρ j) ∧
      ∀ x : G, x ≤ 0 → ν (translatedTruncLE x (u - ∑ j, c j * V j)) < β := by
  classical
  have hassemble : ∀ j : ι, ∃ c : Nonpositive G R,
      (∀ i : {x // x ∈ (u : HahnSeries G R).closedSupport ∧
          (u : HahnSeries G R).closedSupport.cantorBendixsonRank
            (u : HahnSeries G R).closedSupport_isPWO x = β.val},
        ν (translatedTruncLE (i : G) c - w i j) = ⊥) ∧
      ∀ y : G, y ≤ 0 →
        ¬(y ∈ (u : HahnSeries G R).closedSupport ∧
          (u : HahnSeries G R).closedSupport.cantorBendixsonRank
            (u : HahnSeries G R).closedSupport_isPWO y = β.val) →
        ν (translatedTruncLE y c) < ρ j := fun j ↦
    exists_prescribed_truncations_on_topRankLevel β (ρ j) u hu (fun i ↦ w i j) (fun i ↦ hw i j)
  choose c hcenter hnon using hassemble
  have hcb : ∀ j, ∀ x : G, x ≤ 0 → ν (translatedTruncLE x (c j)) ≤ ρ j := by
    intro j x hx
    by_cases hxl : x ∈ (u : HahnSeries G R).closedSupport ∧
        (u : HahnSeries G R).closedSupport.cantorBendixsonRank
          (u : HahnSeries G R).closedSupport_isPWO x = β.val
    · have hsplit : translatedTruncLE x (c j) =
          (translatedTruncLE x (c j) - w ⟨x, hxl⟩ j) + w ⟨x, hxl⟩ j := by abel
      rw [hsplit]
      refine ((ν).map_add_le_max _ _).trans (max_le ?_ (hw ⟨x, hxl⟩ j))
      rw [hcenter j ⟨x, hxl⟩]
      exact bot_le
    · exact (hnon j x hx hxl).le
  have hbot : (⊥ : WithBot NatOrdinal.{u}) < (β : WithBot NatOrdinal) := WithBot.bot_lt_coe β
  have hsep : ∀ j, ∀ θ, θ < σ j → ρ j + θ < β := by
    intro j θ hθ
    calc
      ρ j + θ < ρ j + σ j := add_lt_add_of_le_of_lt le_rfl hθ
      _ ≤ β := hgrade j
  have hsep' : ∀ j, ∀ θ, θ < ρ j → σ j + θ < β := by
    intro j θ hθ
    calc
      σ j + θ < σ j + ρ j := add_lt_add_of_le_of_lt le_rfl hθ
      _ ≤ β := by rw [add_comm]; exact hgrade j
  have hbound : ∀ j, ∀ x : G, x ≤ 0 →
      ν (translatedTruncLE x (c j * V j) - translatedTruncLE x (c j) * V j) < β := by
    intro j x hx
    rcases eq_or_lt_of_le hx with hx0 | hxneg
    · subst hx0
      simp only [translatedTruncLE_zero, sub_self, (ν).map_zero]
      exact hbot
    · apply degree_translatedTruncLE_mul_sub_mul_lt_of_pointwise_bounds (c j) (V j)
        (ρ j) (σ j) β ?_ ?_ (hVcut j) (hsep j) hxneg
      · simpa only [translatedTruncLE_zero] using hcb j 0 le_rfl
      · exact fun y hy ↦ hcb j y hy.le
  refine ⟨c, hcb, ?_⟩
  intro x hx
  by_cases hxl : x ∈ (u : HahnSeries G R).closedSupport ∧
      (u : HahnSeries G R).closedSupport.cantorBendixsonRank
        (u : HahnSeries G R).closedSupport_isPWO x = β.val
  · have hkey : translatedTruncLE x (u - ∑ j, c j * V j) =
        (translatedTruncLE x u - ∑ j, w ⟨x, hxl⟩ j * V j)
          - (∑ j, (translatedTruncLE x (c j * V j) - translatedTruncLE x (c j) * V j))
          - (∑ j, (translatedTruncLE x (c j) - w ⟨x, hxl⟩ j) * V j) := by
      rw [map_sub, map_sum]
      simp only [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      abel
    rw [hkey]
    refine ((ν).map_sub_le_max _ _).trans_lt (max_lt (((ν).map_sub_le_max _ _).trans_lt
      (max_lt (hcorr ⟨x, hxl⟩) ?_)) ?_)
    · exact (ν).map_sum_lt_of_forall_lt _ _ hbot fun j _ ↦ hbound j x hx
    · apply (ν).map_sum_lt_of_forall_lt _ _ hbot
      intro j _
      apply lt_of_le_of_lt _ hbot
      have hmul := (ν).map_mul_le_add (translatedTruncLE x (c j) - w ⟨x, hxl⟩ j) (V j)
      rw [hcenter j ⟨x, hxl⟩, WithBot.bot_add] at hmul
      exact hmul
  · have hu' : ν (translatedTruncLE x u) < β := by
      by_cases hxm : x ∈ (u : HahnSeries G R).closedSupport
      · refine lt_of_le_of_ne (hu x hx) ?_
        rw [degree_translatedTruncLE_eq, if_pos hxm]
        intro he
        apply hxl
        refine ⟨hxm, ?_⟩
        have hval := congrArg NatOrdinal.val (WithBot.coe_injective he)
        rw [NatOrdinal.val_of, cantorBendixsonRank_eq] at hval
        exact hval
      · rw [degree_translatedTruncLE_eq, if_neg hxm]
        exact hbot
    rw [map_sub, map_sum]
    refine ((ν).map_sub_le_max _ _).trans_lt (max_lt hu' ?_)
    apply (ν).map_sum_lt_of_forall_lt _ _ hbot
    intro j _
    have hsplit : translatedTruncLE x (c j * V j) =
        (translatedTruncLE x (c j * V j) - translatedTruncLE x (c j) * V j)
          + translatedTruncLE x (c j) * V j := by abel
    rw [hsplit]
    refine ((ν).map_add_le_max _ _).trans_lt (max_lt (hbound j x hx) ?_)
    rw [mul_comm]
    exact degree_mul_lt_of_le_of_lt_of_separated (V j) (translatedTruncLE x (c j))
      (σ j) (ρ j) β (hV j) (hnon j x hx hxl) (hsep' j)

end HahnSeries.Nonpositive
