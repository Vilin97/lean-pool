/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FaceCombinations
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.VertexHull

/-!
# Finite convex combinations of polytope vertices

This file packages membership in the convex hull of the vertex set as a
finite family of real weights.  Real weights are necessary for an arbitrary
real point of a rational polytope: even an interval with rational endpoints
contains points which admit no rational convex coefficients.

The support lemmas record the two properties needed by reductions to finite
vertex families.  A positive summand of a combination lying on an exposed
face lies on that face, and a positive summand of a combination equal to a
vertex must be that vertex.
-/

open scoped BigOperators

namespace EGZ.RationalPolytope

/-- The finite set of actual vertices of a rational polytope. -/
noncomputable def vertexFinset {d : ℕ} (P : RationalPolytope d) :
    Finset (RealCoord d) :=
  P.finite_vertexSet.toFinset

@[simp]
theorem coe_vertexFinset {d : ℕ} (P : RationalPolytope d) :
    (↑P.vertexFinset : Set (RealCoord d)) = P.vertexSet := by
  exact P.finite_vertexSet.coe_toFinset

@[simp]
theorem mem_vertexFinset {d : ℕ} (P : RationalPolytope d)
    {v : RealCoord d} : v ∈ P.vertexFinset ↔ v ∈ P.vertexSet := by
  rw [← P.coe_vertexFinset]
  rfl

theorem vertexFinset_subset_carrier {d : ℕ} (P : RationalPolytope d) :
    ∀ {v : RealCoord d}, v ∈ P.vertexFinset → v ∈ P.carrier := by
  intro v hv
  exact extremePoints_subset (P.mem_vertexFinset.mp hv)

/-- A convex combination indexed by the complete finite vertex set of `P`.

The weight is stored on the ambient coordinate type because this is the form
returned by `Finset.mem_convexHull'` and is convenient when a later argument
supplies coefficients vertex by vertex.  Only its values on `vertexFinset`
enter the data. -/
structure VertexWeights {d : ℕ} (P : RationalPolytope d)
    (q : RealCoord d) where
  weight : RealCoord d → ℝ
  nonnegative : ∀ v ∈ P.vertexFinset, 0 ≤ weight v
  sum_eq_one : ∑ v ∈ P.vertexFinset, weight v = 1
  weighted_sum_eq : ∑ v ∈ P.vertexFinset, weight v • v = q

/-- Every point of a rational polytope has a finite convex-combination
representation using all of its vertices (with zero weights permitted). -/
theorem exists_vertexWeights {d : ℕ} (P : RationalPolytope d)
    {q : RealCoord d} (hq : q ∈ P.carrier) :
    Nonempty (P.VertexWeights q) := by
  classical
  have hqHull := P.mem_convexHull_vertexSet hq
  rw [← P.coe_vertexFinset] at hqHull
  obtain ⟨weight, hnonnegative, hsum, hbary⟩ :=
    Finset.mem_convexHull'.mp hqHull
  exact ⟨{
    weight := weight
    nonnegative := hnonnegative
    sum_eq_one := hsum
    weighted_sum_eq := hbary
  }⟩

/-- In any finite convex combination equal to an extreme point of `P`, a
strictly positive summand is that extreme point.  The inputs need only lie
in `P`; they need not themselves be vertices.

This indexed form is convenient for zero-sum reductions, whose coefficients
are naturally indexed by the original finite family. -/
theorem eq_of_pos_of_eq_convexCombination_of_mem_vertexSet
    {d : ℕ} {P : RationalPolytope d} {I : Type*} [Fintype I]
    (points : I → RealCoord d) (weight : I → ℝ) (q : RealCoord d)
    (hpoints : ∀ i, points i ∈ P.carrier)
    (hweight0 : ∀ i, 0 ≤ weight i)
    (hweightsum : (∑ i, weight i) = 1)
    (hbary : q = ∑ i, weight i • points i)
    (hq : q ∈ P.vertexSet) {i : I} (hi : 0 < weight i) :
    points i = q := by
  classical
  let t : Finset I := Finset.univ.erase i
  let c : ℝ := ∑ j ∈ t, weight j
  have hc_nonnegative : 0 ≤ c := by
    exact Finset.sum_nonneg fun j _ ↦ hweight0 j
  have hc_add : c + weight i = 1 := by
    calc
      c + weight i = ∑ j ∈ (Finset.univ : Finset I), weight j := by
        exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
      _ = 1 := hweightsum
  by_cases hc0 : c = 0
  · have hrestWeight : ∀ j ∈ t, weight j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ hweight0 j)).mp hc0
    have hrestVector : (∑ j ∈ t, weight j • points j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hrestWeight j hj, zero_smul]
    have hiOne : weight i = 1 := by linarith
    calc
      points i = weight i • points i := by rw [hiOne, one_smul]
      _ = (∑ j ∈ t, weight j • points j) + weight i • points i := by
        rw [hrestVector, zero_add]
      _ = ∑ j, weight j • points j := by
        exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
      _ = q := hbary.symm
  · have hcpos : 0 < c := lt_of_le_of_ne hc_nonnegative (Ne.symm hc0)
    let normalized : I → ℝ := fun j ↦ weight j / c
    have hnormalized_nonnegative : ∀ j ∈ t, 0 ≤ normalized j := by
      intro j hj
      exact div_nonneg (hweight0 j) hcpos.le
    have hnormalized_sum : (∑ j ∈ t, normalized j) = 1 := by
      calc
        (∑ j ∈ t, normalized j) = (∑ j ∈ t, weight j) * c⁻¹ := by
          simp only [normalized, div_eq_mul_inv, Finset.sum_mul]
        _ = c * c⁻¹ := rfl
        _ = 1 := mul_inv_cancel₀ hc0
    let r : RealCoord d := ∑ j ∈ t, normalized j • points j
    have hrP : r ∈ P.carrier := by
      dsimp only [r]
      exact P.convex.sum_mem hnormalized_nonnegative hnormalized_sum
        (fun j _ ↦ hpoints j)
    have hc_r : c • r = ∑ j ∈ t, weight j • points j := by
      dsimp only [r]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul]
      have hcoeff : c * normalized j = weight j := by
        dsimp only [normalized]
        field_simp
      rw [hcoeff]
    have hbarySplit : q = weight i • points i + c • r := by
      calc
        q = ∑ j, weight j • points j := hbary
        _ = (∑ j ∈ t, weight j • points j) + weight i • points i := by
          exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
        _ = weight i • points i + c • r := by rw [hc_r]; ac_rfl
    have hqsegment : q ∈ openSegment ℝ (points i) r := by
      exact ⟨weight i, c, hi, hcpos, by linarith, hbarySplit.symm⟩
    rw [vertexSet, mem_extremePoints] at hq
    exact (hq.2 (points i) (hpoints i) r hrP hqsegment).1

namespace VertexWeights

/-- If the represented point lies in an exposed face, every vertex carrying
positive weight lies in that face. -/
theorem mem_face_of_pos {d : ℕ} {P : RationalPolytope d}
    {q : RealCoord d} (W : P.VertexWeights q) (F : P.Face)
    (hqF : q ∈ F.carrier) {v : RealCoord d}
    (hv : v ∈ P.vertexFinset) (hpos : 0 < W.weight v) :
    v ∈ F.carrier := by
  classical
  let points : {x // x ∈ P.vertexFinset} → RealCoord d := fun x ↦ x.1
  let weight : {x // x ∈ P.vertexFinset} → ℝ := fun x ↦ W.weight x.1
  apply F.mem_of_pos_of_eq_convexCombination points weight q
      (i := ⟨v, hv⟩)
  · intro i
    exact P.vertexFinset_subset_carrier i.2
  · intro i
    exact W.nonnegative i.1 i.2
  · change (∑ i : {x // x ∈ P.vertexFinset}, W.weight i.1) = 1
    calc
      (∑ i : {x // x ∈ P.vertexFinset}, W.weight i.1) =
          ∑ x ∈ P.vertexFinset, W.weight x := by
            rw [← Finset.attach_eq_univ, Finset.sum_attach]
      _ = 1 := W.sum_eq_one
  · change q = ∑ i : {x // x ∈ P.vertexFinset}, W.weight i.1 • i.1
    symm
    calc
      (∑ i : {x // x ∈ P.vertexFinset}, W.weight i.1 • i.1) =
          ∑ x ∈ P.vertexFinset, W.weight x • x := by
            rw [← Finset.attach_eq_univ]
            exact Finset.sum_attach P.vertexFinset
              (fun x ↦ W.weight x • x)
      _ = q := W.weighted_sum_eq
  · exact hqF
  · exact hpos

/-- In a convex representation of an extreme point of `P`, every vertex with
positive weight is the represented point itself. -/
theorem eq_of_pos_of_mem_vertexSet {d : ℕ} {P : RationalPolytope d}
    {q : RealCoord d} (W : P.VertexWeights q) (hq : q ∈ P.vertexSet)
    {v : RealCoord d} (hv : v ∈ P.vertexFinset)
    (hpos : 0 < W.weight v) : v = q := by
  classical
  by_contra hvq
  let s := P.vertexFinset
  let c : ℝ := ∑ x ∈ s.erase q, W.weight x
  have hqs : q ∈ s := P.mem_vertexFinset.mpr hq
  have hvs : v ∈ s := hv
  have hve : v ∈ s.erase q := Finset.mem_erase.mpr ⟨hvq, hvs⟩
  have hcpos : 0 < c := by
    apply Finset.sum_pos'
    · intro x hx
      exact W.nonnegative x (Finset.mem_of_mem_erase hx)
    · exact ⟨v, hve, hpos⟩
  have hcsum : c + W.weight q = 1 := by
    calc
      c + W.weight q = ∑ x ∈ s, W.weight x := by
        exact Finset.sum_erase_add _ _ hqs
      _ = 1 := W.sum_eq_one
  have hc : c = 1 - W.weight q := by linarith
  have hbaryErase :
      (∑ x ∈ s.erase q, W.weight x • x) = c • q := by
    have hdecomp :
        (∑ x ∈ s.erase q, W.weight x • x) + W.weight q • q = q := by
      calc
        (∑ x ∈ s.erase q, W.weight x • x) + W.weight q • q =
            ∑ x ∈ s, W.weight x • x := Finset.sum_erase_add _ _ hqs
        _ = q := W.weighted_sum_eq
    calc
      (∑ x ∈ s.erase q, W.weight x • x) =
          q - W.weight q • q := (eq_sub_iff_add_eq).2 hdecomp
      _ = (1 - W.weight q) • q := by rw [sub_smul, one_smul]
      _ = c • q := by rw [hc]
  let normalized : RealCoord d → ℝ := fun x ↦ c⁻¹ * W.weight x
  have hnormalized_nonnegative :
      ∀ x ∈ s.erase q, 0 ≤ normalized x := by
    intro x hx
    exact mul_nonneg (inv_nonneg.mpr hcpos.le)
      (W.nonnegative x (Finset.mem_of_mem_erase hx))
  have hnormalized_sum :
      (∑ x ∈ s.erase q, normalized x) = 1 := by
    calc
      (∑ x ∈ s.erase q, normalized x) =
          c⁻¹ * ∑ x ∈ s.erase q, W.weight x := by
            simp only [normalized, Finset.mul_sum]
      _ = c⁻¹ * c := rfl
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  have hnormalized_bary :
      (∑ x ∈ s.erase q, normalized x • x) = q := by
    calc
      (∑ x ∈ s.erase q, normalized x • x) =
          ∑ x ∈ s.erase q, c⁻¹ • (W.weight x • x) := by
            apply Finset.sum_congr rfl
            intro x hx
            change (c⁻¹ * W.weight x) • x = c⁻¹ • W.weight x • x
            rw [mul_smul]
      _ = c⁻¹ • ∑ x ∈ s.erase q, W.weight x • x := by
            rw [Finset.smul_sum]
      _ = c⁻¹ • (c • q) := by rw [hbaryErase]
      _ = q := inv_smul_smul₀ hcpos.ne' q
  have hqHullErase :
      q ∈ convexHull ℝ (↑(s.erase q) : Set (RealCoord d)) :=
    Finset.mem_convexHull'.2
      ⟨normalized, hnormalized_nonnegative, hnormalized_sum,
        hnormalized_bary⟩
  have heraseSubset :
      (↑(s.erase q) : Set (RealCoord d)) ⊆ P.carrier \ {q} := by
    intro x hx
    have hxErase : x ∈ s.erase q := hx
    exact ⟨P.vertexFinset_subset_carrier (Finset.mem_of_mem_erase hxErase),
      fun hxq ↦ (Finset.ne_of_mem_erase hxErase) (Set.mem_singleton_iff.mp hxq)⟩
  have hqHullComplement : q ∈ convexHull ℝ (P.carrier \ {q}) :=
    convexHull_mono heraseSubset hqHullErase
  exact ((P.convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp hq).2
    hqHullComplement)

/-- Equivalently, every vertex different from an extreme represented point
has zero weight. -/
theorem weight_eq_zero_of_mem_vertexSet_of_ne {d : ℕ}
    {P : RationalPolytope d} {q : RealCoord d} (W : P.VertexWeights q)
    (hq : q ∈ P.vertexSet) {v : RealCoord d} (hv : v ∈ P.vertexFinset)
    (hvq : v ≠ q) : W.weight v = 0 := by
  apply le_antisymm
  · exact not_lt.mp (fun hpos ↦ hvq (W.eq_of_pos_of_mem_vertexSet hq hv hpos))
  · exact W.nonnegative v hv

end VertexWeights

end EGZ.RationalPolytope
