/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.DistanceGeometry.Defs
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Geometry.Euclidean.PerpBisector
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Data.Set.Card

/-!
# Trilateration: sphere intersections of codimension-one center families

A family of centers whose affine span is a hyperplane (the orthogonal complement of
the center span is one-dimensional) localizes a point to at most two candidates: the
intersection of the spheres `{p | ∀ i, dist p (c i) = r i}` has at most two elements.

This is the higher-dimensional analog of
`EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two` (two circles
meet in at most two points), and the combinatorial heart of the branch-and-prune
algorithm for the Discretizable Molecular Distance Geometry Problem: a new vertex
localized against enough already-placed neighbours has at most two placements, so the
search tree has bounded branching.

The proof: for any two solutions `p₁`, `p₂`, equal distances to each center give
`⟪c i -ᵥ c i₀, p₂ -ᵥ p₁⟫ = 0` (`inner_vsub_vsub_of_dist_eq_of_dist_eq`), so the
difference vector lies in `Wᗮ`, where `W = vectorSpan ℝ (range c)`. When `Wᗮ` is
one-dimensional it cannot contain two linearly independent vectors, so any third
solution's difference vector is a scalar multiple of `p₂ -ᵥ p₁`; feeding that into the
distance equation through the quadratic `dist_smul_vadd_eq_dist` forces the third
solution to coincide with `p₁` or `p₂`.

## Main results

* `DistanceGeometry.encard_setOf_forall_dist_eq_le_two` : the general codimension-one
  statement.
* `DistanceGeometry.trilateration_le_two` : the specialization to three affinely
  independent centers in `EuclideanSpace ℝ (Fin 3)`.
-/

@[expose] public section

namespace DistanceGeometry

open scoped RealInnerProductSpace
open EuclideanGeometry Module Submodule

section General

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
  {ι : Type*} {c : ι → P} {r : ι → ℝ}

/-- The intersection of the spheres of real-valued radii `r` about the centers `c`.
If some `r i` is negative, the intersection is empty because distances are
nonnegative. -/
def sphereIntersection (c : ι → P) (r : ι → ℝ) : Set P :=
  {p | ∀ i, dist p (c i) = r i}

@[simp]
theorem mem_sphereIntersection {p : P} :
    p ∈ sphereIntersection c r ↔ ∀ i, dist p (c i) = r i := Iff.rfl

omit [FiniteDimensional ℝ V] in
/-- For two solutions `p₁`, `p₂`, the difference vector is orthogonal to every center
difference `c i -ᵥ c i₀`, hence lies in `(vectorSpan ℝ (range c))ᗮ`. -/
private theorem vsub_mem_orthogonal [Nonempty ι] {p₁ p₂ : P}
    (h₁ : p₁ ∈ sphereIntersection c r) (h₂ : p₂ ∈ sphereIntersection c r) :
    (p₂ -ᵥ p₁) ∈ (vectorSpan ℝ (Set.range c))ᗮ := by
  -- It suffices to be orthogonal to each generator `c i -ᵥ c i₀` of the span.
  rw [vectorSpan_range_eq_span_range_vsub_right ℝ c (Classical.arbitrary ι)]
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact inner_vsub_vsub_of_dist_eq_of_dist_eq
      (by rw [h₁ _, h₂ _]) (by rw [h₁ i, h₂ i])
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- The geometric heart: when the center span has codimension one, among any three
solutions two coincide. The disjunction covers `p₁ = p₂` (the degenerate choice)
explicitly. -/
private theorem eq_or_eq_or_eq_of_finrank_orthogonal_eq_one [Nonempty ι]
    (hc : finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1) {p p₁ p₂ : P}
    (hp : p ∈ sphereIntersection c r) (h₁ : p₁ ∈ sphereIntersection c r)
    (h₂ : p₂ ∈ sphereIntersection c r) : p = p₁ ∨ p = p₂ ∨ p₁ = p₂ := by
  -- If the two reference solutions coincide, the third disjunct holds.
  by_cases hp12 : p₁ = p₂
  · exact Or.inr (Or.inr hp12)
  refine Or.imp_right Or.inl ?_
  -- `p₁ ≠ p₂`, so `p₂ -ᵥ p₁` is a nonzero vector in the 1-dimensional `Wᗮ`.
  have hw2 : (p₂ -ᵥ p₁) ∈ (vectorSpan ℝ (Set.range c))ᗮ := vsub_mem_orthogonal h₁ h₂
  have hw2ne : (p₂ -ᵥ p₁ : V) ≠ 0 := vsub_ne_zero.mpr (fun h => hp12 h.symm)
  have hwp : (p -ᵥ p₁) ∈ (vectorSpan ℝ (Set.range c))ᗮ := vsub_mem_orthogonal h₁ hp
  -- `Wᗮ` is 1-dimensional and contains the nonzero `p₂ -ᵥ p₁`, hence `Wᗮ = span{p₂ -ᵥ p₁}`.
  have hspan : (vectorSpan ℝ (Set.range c))ᗮ = ℝ ∙ (p₂ -ᵥ p₁) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]; exact hw2
    · rw [finrank_span_singleton hw2ne, hc]
  -- So `p -ᵥ p₁` is a scalar multiple of `p₂ -ᵥ p₁`.
  rw [hspan, Submodule.mem_span_singleton] at hwp
  obtain ⟨t, ht⟩ := hwp
  -- `p = t • (p₂ -ᵥ p₁) +ᵥ p₁`.
  have hpval : p = t • (p₂ -ᵥ p₁) +ᵥ p₁ := by rw [ht, vsub_vadd]
  -- Distance of `p` to `c i₀` is `r i₀ = dist p₁ (c i₀)`; feed into the quadratic.
  have hd : dist (t • (p₂ -ᵥ p₁) +ᵥ p₁) (c (Classical.arbitrary ι))
      = dist p₁ (c (Classical.arbitrary ι)) := by
    rw [← hpval, hp _, h₁ _]
  rw [dist_smul_vadd_eq_dist _ _ hw2ne] at hd
  -- The other root `t = 1` corresponds to `p₂` (which also satisfies the equation).
  have hd2 : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) (c (Classical.arbitrary ι))
      = dist p₁ (c (Classical.arbitrary ι)) := by
    rw [one_smul, vsub_vadd, h₂ _, h₁ _]
  rw [dist_smul_vadd_eq_dist _ _ hw2ne] at hd2
  -- `hd2 : 1 = 0 ∨ 1 = root`; the second disjunct pins down the nonzero root.
  have hroot : (1 : ℝ)
      = -2 * ⟪p₂ -ᵥ p₁, p₁ -ᵥ c (Classical.arbitrary ι)⟫ / ⟪p₂ -ᵥ p₁, p₂ -ᵥ p₁⟫ :=
    hd2.resolve_left one_ne_zero
  rcases hd with h | h
  · -- `t = 0` ⇒ `p = p₁`.
    left; rw [hpval, h, zero_smul, zero_vadd]
  · -- `t = root = 1` ⇒ `p = p₂`.
    right
    have ht1 : t = 1 := by rw [h, ← hroot]
    rw [hpval, ht1, one_smul, vsub_vadd]

/-- If the center span has codimension one, all solutions lie in a set of at
most two explicitly chosen points. -/
private theorem sphereIntersection_subset_pair [Nonempty ι]
    (hc : finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1) (r : ι → ℝ) :
    ∃ p₁ p₂ : P, sphereIntersection c r ⊆ {p₁, p₂} := by
  by_cases hnonempty : (sphereIntersection c r).Nonempty
  · obtain ⟨p₁, hp₁⟩ := hnonempty
    by_cases hsecond : ∃ p₂ ∈ sphereIntersection c r, p₂ ≠ p₁
    · obtain ⟨p₂, hp₂, hp₂ne⟩ := hsecond
      refine ⟨p₁, p₂, ?_⟩
      intro p hp
      rcases eq_or_eq_or_eq_of_finrank_orthogonal_eq_one hc hp hp₁ hp₂ with
        hpEq | hpEq | hp₁Eq
      · exact Set.mem_insert_iff.mpr (Or.inl hpEq)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hpEq))
      · exact (hp₂ne hp₁Eq.symm).elim
    · push Not at hsecond
      refine ⟨p₁, p₁, ?_⟩
      intro p hp
      have hpEq : p = p₁ := hsecond p hp
      exact Set.mem_insert_iff.mpr (Or.inl hpEq)
  · let p₀ := c (Classical.arbitrary ι)
    refine ⟨p₀, p₀, ?_⟩
    intro p hp
    exact (hnonempty ⟨p, hp⟩).elim

/-- If the orthogonal complement of the center span is one-dimensional (the centers
span a hyperplane), the intersection of the spheres `{p | ∀ i, dist p (c i) = r i}`
has at most two elements. -/
theorem encard_setOf_forall_dist_eq_le_two [Nonempty ι]
    (hc : finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1) (r : ι → ℝ) :
    Set.encard {p : P | ∀ i, dist p (c i) = r i} ≤ 2 := by
  change (sphereIntersection c r).encard ≤ 2
  obtain ⟨p₁, p₂, hsubset⟩ := sphereIntersection_subset_pair hc r
  calc
    (sphereIntersection c r).encard ≤ ({p₁, p₂} : Set P).encard :=
      Set.encard_mono hsubset
    _ ≤ ({p₂} : Set P).encard + 1 := Set.encard_insert_le {p₂} p₁
    _ = 2 := by norm_num

end General

/-! ### Specialization: three affinely independent centers in `EuclideanSpace ℝ (Fin 3)` -/

/-- The localization set of three centers `c` and real-valued radii `r` in
`EuclideanSpace ℝ (Fin 3)`: the intersection of the three spheres. A negative radius
makes the set empty. -/
def trilaterationSet (c : Fin 3 → EuclideanSpace ℝ (Fin 3)) (r : Fin 3 → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {p : EuclideanSpace ℝ (Fin 3) | ∀ i, dist p (c i) = r i}

variable {c : Fin 3 → EuclideanSpace ℝ (Fin 3)}

/-- Three affinely independent centers and three radii localize a point in
`EuclideanSpace ℝ (Fin 3)` to at most two candidates: the intersection of the three
spheres has at most two elements. The `d = 3` analog of
`EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two`. -/
theorem trilateration_le_two (hc : AffineIndependent ℝ c) (r : Fin 3 → ℝ) :
    (trilaterationSet c r).encard ≤ 2 := by
  -- the centers span a plane, so the orthogonal complement is a line
  have hW : Module.finrank ℝ (vectorSpan ℝ (Set.range c)) = 2 := hc.finrank_vectorSpan (by simp)
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hperp : Module.finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal
      (K := vectorSpan ℝ (Set.range c))
    rw [hW, h3] at hsum
    omega
  exact encard_setOf_forall_dist_eq_le_two hperp r

end DistanceGeometry
