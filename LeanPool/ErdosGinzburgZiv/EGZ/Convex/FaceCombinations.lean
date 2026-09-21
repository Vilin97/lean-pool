/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FiniteHull

/-!
# Convex combinations and minimal faces of rational polytopes

This file develops the order-theoretic face API needed by the canonical
face flag.  Positivity in an exposed face forces every positive summand into
that face.  Relative-interior membership consequently implies that the face
is the least face containing the point.  Independently, finiteness of the
face poset constructs such a least face for every point of the polytope.
-/

open scoped BigOperators

namespace EGZ.RationalPolytope.Face

/-- If a convex combination belongs to an exposed face, every input with
strictly positive weight belongs to that face. -/
theorem mem_of_pos_of_eq_convexCombination {d : ℕ}
    {P : RationalPolytope d} (F : P.Face) {I : Type*} [Fintype I]
    (points : I → RealCoord d) (weight : I → ℝ) (q : RealCoord d)
    (hpoints : ∀ i, points i ∈ P.carrier)
    (hweight0 : ∀ i, 0 ≤ weight i) (hweightsum : (∑ i, weight i) = 1)
    (hbary : q = ∑ i, weight i • points i) (hqF : q ∈ F.carrier)
    {i : I} (hi : 0 < weight i) : points i ∈ F.carrier := by
  classical
  obtain ⟨functional, level, hle, hcarrier⟩ := F.is_exposed
  have hqlevel : functional q = level := by
    rw [hcarrier] at hqF
    exact hqF.2
  have hfunbar : functional q = ∑ j, weight j • functional (points j) := by
    rw [hbary, ← Finset.affineCombination_eq_linear_combination
      Finset.univ points weight (by simpa using hweightsum)]
    rw [(Finset.univ.map_affineCombination points weight hweightsum functional)]
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hweightsum]
    rfl
  have hfunbar' : functional q =
      ∑ j, weight j * functional (points j) := by
    simpa only [smul_eq_mul] using hfunbar
  let gap : I → ℝ := fun j ↦ weight j * (level - functional (points j))
  have hgap0 : ∀ j, 0 ≤ gap j := by
    intro j
    exact mul_nonneg (hweight0 j) (sub_nonneg.mpr (hle _ (hpoints j)))
  have hgapsum : (∑ j, gap j) = 0 := by
    calc
      (∑ j, gap j) = level * (∑ j, weight j) -
          ∑ j, weight j * functional (points j) := by
        simp only [gap]
        rw [Finset.mul_sum]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by
        rw [hweightsum, ← hfunbar', hqlevel]
        ring
  have hgapi : gap i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ hgap0 j)).mp hgapsum i (Finset.mem_univ i)
  have hleveli : functional (points i) = level := by
    have : level - functional (points i) = 0 := by
      apply (mul_eq_zero.mp hgapi).resolve_left
      exact hi.ne'
    linarith
  rw [hcarrier]
  exact ⟨hpoints i, hleveli⟩

/-- A point in the relative interior of a face belongs to no smaller face:
the relative-interior face lies below every face containing the point. -/
theorem le_of_mem_relInterior {d : ℕ} {P : RationalPolytope d}
    {F G : P.Face} {q : RealCoord d} (hqF : q ∈ F.relInterior)
    (hqG : q ∈ G.carrier) : F ≤ G := by
  intro x hxF
  by_cases hxq : x = q
  · simpa [hxq] using hqG
  · obtain ⟨z, hzF, a, b, ha, hb, hab, haxb⟩ :=
      EGZ.exists_openSegment_of_mem_intrinsicInterior hqF hxF (Ne.symm hxq)
    let points : Fin 2 → RealCoord d := ![x, z]
    let weight : Fin 2 → ℝ := ![a, b]
    apply G.mem_of_pos_of_eq_convexCombination points weight q (i := 0)
    · intro i
      fin_cases i <;> simp [points, F.subset_polytope hxF,
        F.subset_polytope hzF]
    · intro i
      fin_cases i <;> simp [weight, ha.le, hb.le]
    · simp [weight, hab]
    · simpa [points, weight] using haxb.symm
    · exact hqG
    · simpa [weight] using ha

/-- Relative interiors of distinct faces are disjoint. -/
theorem eq_of_mem_relInterior {d : ℕ} {P : RationalPolytope d}
    {F G : P.Face} {q : RealCoord d} (hqF : q ∈ F.relInterior)
    (hqG : q ∈ G.relInterior) : F = G := by
  apply le_antisymm
  · exact le_of_mem_relInterior hqF (intrinsicInterior_subset hqG)
  · exact le_of_mem_relInterior hqG (intrinsicInterior_subset hqF)

/-- Order-theoretic minimality among the faces which contain a point. -/
def IsLeastFaceAt {d : ℕ} (P : RationalPolytope d)
    (q : RealCoord d) (F : P.Face) : Prop :=
  q ∈ F.carrier ∧ ∀ G : P.Face, q ∈ G.carrier → F ≤ G

/-- Every point of a rational polytope has a least containing face.  This is
purely finite: choose a containing face with the fewest generators, then
intersect it with any competing containing face. -/
theorem exists_isLeastFaceAt {d : ℕ} (P : RationalPolytope d)
    {q : RealCoord d} (hq : q ∈ P.carrier) :
    ∃ F : P.Face, IsLeastFaceAt P q F := by
  classical
  have hex : ∃ k : ℕ, ∃ F : P.Face,
      q ∈ F.carrier ∧ F.generatorFinset.card = k := by
    exact ⟨(⊤ : P.Face).generatorFinset.card, ⊤, hq, rfl⟩
  let m : ℕ := Nat.find hex
  obtain ⟨F, hqF, hFcard⟩ := Nat.find_spec hex
  refine ⟨F, hqF, ?_⟩
  intro G hqG
  by_contra hFG
  let I : P.Face := interOfNonempty F G ⟨q, hqF, hqG⟩
  have hqI : q ∈ I.carrier := ⟨hqF, hqG⟩
  have hgen_subset : I.generatorFinset ⊆ F.generatorFinset := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, hx'.2.1⟩
  have hgen_ne : I.generatorFinset ≠ F.generatorFinset := by
    intro heq
    apply hFG
    intro x hxF
    have hxI : x ∈ I.carrier := by
      rw [I.carrier_eq_convexHull_generatorFinset, heq,
        ← F.carrier_eq_convexHull_generatorFinset]
      exact hxF
    exact hxI.2
  have hcard_lt : I.generatorFinset.card < F.generatorFinset.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hgen_subset, hgen_ne⟩)
  have hmin : m ≤ I.generatorFinset.card :=
    Nat.find_min' hex ⟨I, hqI, rfl⟩
  dsimp [m] at hmin
  rw [hFcard] at hcard_lt
  exact (Nat.not_lt_of_ge hmin) hcard_lt

/-- Relative-interior membership implies order-theoretic minimality. -/
theorem isLeastFaceAt_of_mem_relInterior {d : ℕ}
    {P : RationalPolytope d} {q : RealCoord d} {F : P.Face}
    (hq : q ∈ F.relInterior) : IsLeastFaceAt P q F := by
  exact ⟨intrinsicInterior_subset hq,
    fun G hqG ↦ le_of_mem_relInterior hq hqG⟩

/-- Order-theoretic least faces are unique. -/
theorem IsLeastFaceAt.unique {d : ℕ} {P : RationalPolytope d}
    {q : RealCoord d} {F G : P.Face}
    (hF : IsLeastFaceAt P q F) (hG : IsLeastFaceAt P q G) : F = G :=
  le_antisymm (hF.2 G hG.1) (hG.2 F hF.1)

end EGZ.RationalPolytope.Face
