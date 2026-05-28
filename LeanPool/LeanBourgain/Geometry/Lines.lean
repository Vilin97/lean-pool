/-
Copyright (c) 2026 Command Master. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Command Master
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Lines in the affine plane over a field

Lines in the affine plane are modelled as two-dimensional subspaces of `α × α × α`
(the projectivisation of `α²`). This file develops the basic incidence theory: a
pair of distinct points lies on a unique line (`point_intersect`), two distinct
lines meet in at most one point (`line_intersect`), and the Cauchy-Schwarz upper
bound on the number of point-line incidences (`CS_UB`). These results form the
combinatorial backbone of the prime-field Szemerédi-Trotter estimate.
-/

namespace LeanPool.LeanBourgain

variable {α : Type*} [Field α]

open Finset Module

/-- A line in the affine plane over `α`, represented as a two-dimensional subspace
of the projective space `α × α × α`. -/
def Line (α : Type*) [Ring α] := {x : Submodule α (α × α × α) // Module.finrank α x = 2}

/-- Lines are sets of projective points via the underlying subspace. -/
instance instSetLike : SetLike (Line α) (α × α × α) where
  coe x := x.val
  coe_injective' x1 x2 h := by
    apply Subtype.ext
    simp_all

theorem set_like_val {x : α × α × α} {l : Line α} : x ∈ l ↔ x ∈ l.val := by aesop

@[simp]
lemma Line_finrank {l : Line α} : Module.finrank α l.val = 2 := by
  cases l
  simp_all

/-- A point `(x₁, x₂)` of the affine plane lies on a line when its projective lift
`(x₁, x₂, 1)` belongs to the underlying subspace. -/
instance mem2 : Membership (α × α) (Line α) where
  mem l x := ⟨x.1, x.2, 1⟩ ∈ l

/-- Membership of an affine point in a line is decidable. -/
noncomputable instance instDecidableMem2 (x : α × α) (y : Line α) : Decidable (x ∈ y) := by
  classical apply inferInstance

/-- Equality of lines is decidable. -/
noncomputable instance instDecidableEqLine : DecidableEq (Line α) := by
  classical apply inferInstance

namespace Line

/-- The image of a line under a linear automorphism of the projective space. -/
def apply (l : Line α) (p : (α × α × α) ≃ₗ[α] (α × α × α)) : Line α :=
  ⟨Submodule.map (p : (α × α × α) →ₗ[α] (α × α × α)) l.val, by
    rw [LinearEquiv.finrank_map_eq]
    simp⟩

end Line

/-- Applying a fixed linear automorphism to lines is injective. -/
theorem apply_injective (l₁ l₂ : Line α) (p : (α × α × α) ≃ₗ[α] (α × α × α))
    (h : l₁.apply p = l₂.apply p) : l₁ = l₂ := by
  have hmap : Submodule.map (p : (α × α × α) →ₗ[α] (α × α × α)) l₁.val =
      Submodule.map (p : (α × α × α) →ₗ[α] (α × α × α)) l₂.val :=
    congrArg Subtype.val h
  apply Subtype.ext
  exact Submodule.map_injective_of_injective (LinearEquiv.injective p) hmap

lemma mem_iff_mem_val (x : α × α) (l : Line α) :
    x ∈ l ↔ (⟨x.1, x.2, 1⟩ : α × α × α) ∈ (l.val : Set _) := Iff.rfl

namespace Submodule

/-- The subspace spanned by the projective lifts of two affine points. -/
def pair (i j : α × α) :=
  Submodule.span α (M := α × α × α) {⟨i.1, i.2, 1⟩, ⟨j.1, j.2, 1⟩}

end Submodule

lemma mem_span1 (i j : α × α) : (⟨i.1, i.2, 1⟩ : α × α × α) ∈ Submodule.pair i j :=
  Submodule.subset_span <| (by simp)

lemma mem_span2 (i j : α × α) : (⟨j.1, j.2, 1⟩ : α × α × α) ∈ Submodule.pair i j :=
  Submodule.subset_span <| (by simp)

namespace Submodule

/-- A basis of the span of two distinct affine points, given by their projective
lifts. -/
noncomputable def pair_basis (i j : α × α) (h : i ≠ j) :
    Basis (Fin 2) α (Submodule.pair i j) := by
  have := Basis.span
    (R := α)
    (M := α × α × α)
    (v := ![⟨i.1, i.2, 1⟩, ⟨j.1, j.2, 1⟩]) (by
      rw [linearIndependent_fin2]
      aesop)
  apply this.map (LinearEquiv.ofEq ..)
  simp [pair]
  congr 1
  aesop

end Submodule

lemma repr_pair_basis_first' (i j : α × α) (h : i ≠ j) :
    (Submodule.pair_basis i j h) 0 = ⟨⟨i.1, i.2, 1⟩, mem_span1 i j⟩ := by
  apply Subtype.ext
  simp [Submodule.pair_basis, Basis.span_apply]

lemma repr_pair_basis_first (i j : α × α) (h : i ≠ j) :
    (Submodule.pair_basis i j h).repr ⟨⟨i.1, i.2, 1⟩, mem_span1 i j⟩ = Finsupp.single 0 1 := by
  rw [← repr_pair_basis_first' i j h]
  rw [Basis.repr_self]

lemma repr_pair_basis_second' (i j : α × α) (h : i ≠ j) :
    (Submodule.pair_basis i j h) 1 = ⟨⟨j.1, j.2, 1⟩, mem_span2 i j⟩ := by
  apply Subtype.ext
  simp [Submodule.pair_basis, Basis.span_apply]

lemma repr_pair_basis_second (i j : α × α) (h : i ≠ j) :
    (Submodule.pair_basis i j h).repr ⟨⟨j.1, j.2, 1⟩, mem_span2 i j⟩ = Finsupp.single 1 1 := by
  rw [← repr_pair_basis_second' i j h]
  rw [Basis.repr_self]

namespace Line

/-- The line through two distinct affine points. -/
def of (i j : α × α) (h : i ≠ j) : Line α := ⟨Submodule.pair i j, by
    rw [finrank_eq_nat_card_basis <| Submodule.pair_basis i j h]
    simp⟩

end Line

namespace Submodule

/-- The line at infinity, spanned by the two directions at infinity. -/
def infinity (α : Type*) [Field α] :=
  Submodule.span α (M := α × α × α) {⟨1, 0, 0⟩, ⟨0, 1, 0⟩}

/-- A basis of the line at infinity. -/
noncomputable def infinity_basis (α : Type*) [Field α] :
    Basis (Fin 2) α (Submodule.infinity α) := by
  have := Basis.span
    (R := α)
    (M := α × α × α)
    (v := ![⟨1, 0, 0⟩, ⟨0, 1, 0⟩]) (by
      rw [linearIndependent_fin2]
      aesop)
  apply this.map (LinearEquiv.ofEq ..)
  simp [infinity]
  congr 1
  aesop

end Submodule

lemma infinity_mem (x : α × α × α) : x ∈ (Submodule.infinity α : Set _) ↔ x.2.2 = 0 := by
  constructor
  · intro v
    rw [Submodule.infinity] at v
    simp only [SetLike.mem_coe, Submodule.mem_span_pair] at v
    have ⟨a, b, s⟩ := v
    rw [← s]
    simp
  · intro v
    rw [Submodule.infinity]
    simp only [SetLike.mem_coe, Submodule.mem_span_pair]
    exists x.1, x.2.1
    simp
    aesop

lemma infinity_mem_first : ((1, 0, 0) : α × α × α) ∈ (Submodule.infinity α : Set _) := by
  rw [infinity_mem]

lemma infinity_first : Submodule.infinity_basis α 0 = ⟨⟨1, 0, 0⟩, infinity_mem_first⟩ := by
  apply Subtype.ext
  simp [Submodule.infinity_basis, Basis.span_apply]

lemma infinity_mem_second : ((0, 1, 0) : α × α × α) ∈ (Submodule.infinity α : Set _) := by
  rw [infinity_mem]

lemma infinity_second : Submodule.infinity_basis α 1 = ⟨⟨0, 1, 0⟩, infinity_mem_second⟩ := by
  apply Subtype.ext
  simp [Submodule.infinity_basis, Basis.span_apply]

namespace Line

/-- The line at infinity, as an element of `Line α`. -/
def infinity (α) [Field α] : Line α := ⟨Submodule.infinity α, by
    rw [finrank_eq_nat_card_basis <| Submodule.infinity_basis α]
    simp⟩

end Line

/-- Normalise a nonzero projective point to its affine representative. -/
def Vnorm (x : α × α × α) := (x.1 / x.2.2, x.2.1 / x.2.2)

lemma norm_mem (l : Line α) (x : α × α × α) (h₂ : x.2.2 ≠ 0) :
    x ∈ (l : Set _) ↔ Vnorm x ∈ l := by
  have key : ((1 / x.2.2) • x : α × α × α) = ⟨(Vnorm x).1, (Vnorm x).2, 1⟩ := by
    simp only [Vnorm]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.smul_fst, smul_eq_mul, one_div, ← div_eq_inv_mul]
    · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul, one_div, ← div_eq_inv_mul]
    · simp only [Prod.smul_snd, smul_eq_mul]
      field_simp
  rw [show Vnorm x ∈ l ↔ ((1 / x.2.2) • x ∈ (l : Set _)) from ?_]
  · rw [SetLike.mem_coe, SetLike.mem_coe]
    exact (Submodule.smul_mem_iff l.val (by simp_all)).symm
  · rw [key, SetLike.mem_coe]
    exact (set_like_val).symm

lemma vnorm_eq_vnorm (x y : α × α × α) (h : Vnorm x = Vnorm y) (h₂ : x.2.2 ≠ 0)
    (h₃ : y.2.2 ≠ 0) : ∃ r : α, r • x = y := by
  exists y.2.2 / x.2.2
  simp only [Vnorm, Prod.mk.injEq] at h
  field_simp at h
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination h.1
  · simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
    field_simp
    linear_combination h.2
  · simp only [Prod.smul_snd, smul_eq_mul]
    field_simp

lemma mem_line1 (i j : α × α) (h : i ≠ j) : i ∈ (Line.of i j h) := by
  have : ({⟨i.1, i.2, 1⟩, ⟨j.1, j.2, 1⟩} : Set (α × α × α)) ⊆ (Line.of i j h).val := by
    simp [Line.of, Submodule.pair]
  aesop

lemma mem_line2 (i j : α × α) (h : i ≠ j) : j ∈ (Line.of i j h) := by
  have : ({⟨i.1, i.2, 1⟩, ⟨j.1, j.2, 1⟩} : Set (α × α × α)) ⊆ (Line.of i j h).val := by
    simp [Line.of, Submodule.pair]
  aesop

theorem line_eq_of (i j : α × α) (oh : i ≠ j) (l₂ : Line α)
    (h : i ∈ l₂ ∧ j ∈ l₂) : l₂ = Line.of i j oh := by
  have : (Line.of i j oh).val ≤ l₂.val := by
    simp [Line.of, Submodule.pair, Submodule.span_le, Set.subset_def]
    constructor <;> aesop
  apply Eq.symm
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · assumption
  · simp

namespace Line

/-- A line is horizontal when it contains the horizontal direction at infinity. -/
def horiz (l : Line α) : Prop := ((1, 0, 0) : α × α × α) ∈ (l : Set _)

theorem of_horiz_iff (x y : α × α) (h : x ≠ y) : (Line.of x y h).horiz ↔ x.2 = y.2 := by
  unfold horiz of
  rw [SetLike.mem_coe]
  change (⟨1, 0, 0⟩ : α × α × α) ∈ Submodule.pair x y ↔ x.2 = y.2
  rw [Submodule.pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, v⟩
    rw [Prod.ext_iff, Prod.ext_iff] at v
    obtain ⟨v1, v2, v3⟩ := v
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one] at v1 v2 v3
    have hab : a = -b := by linear_combination v3
    have hbne : b * (y.1 - x.1) = 1 := by linear_combination v1 - x.1 * v3
    have : b * (y.2 - x.2) = 0 := by linear_combination v2 - x.2 * v3
    rcases mul_eq_zero.mp this with hb | hxy
    · rw [hb] at hbne
      simp at hbne
    · exact (sub_eq_zero.mp hxy).symm
  · intro v
    refine ⟨(x.1 - y.1)⁻¹, -(x.1 - y.1)⁻¹, ?_⟩
    have hne : x.1 - y.1 ≠ 0 := by
      intro v2
      exact h (Prod.ext (sub_eq_zero.mp v2) v)
    rw [Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one]
    · linear_combination inv_mul_cancel₀ hne
    · rw [← v]
      ring
    · ring

theorem horiz_constant (l : Line α) (x y : α × α) (h : x ∈ l) (h₂ : y ∈ l)
    (hor : l.horiz) : x.2 = y.2 := by
  by_cases hxy : x = y
  · simp_all
  · apply (Line.of_horiz_iff x y hxy).mp
    rw [← line_eq_of x y hxy l]
    · assumption
    · constructor <;> assumption

/-- A line is vertical when it contains the vertical direction at infinity. -/
def vert (l : Line α) : Prop := ((0, 1, 0) : α × α × α) ∈ (l : Set _)

theorem of_vert_iff (x y : α × α) (h : x ≠ y) : (Line.of x y h).vert ↔ x.1 = y.1 := by
  unfold vert of
  rw [SetLike.mem_coe]
  change (⟨0, 1, 0⟩ : α × α × α) ∈ Submodule.pair x y ↔ x.1 = y.1
  rw [Submodule.pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, v⟩
    rw [Prod.ext_iff, Prod.ext_iff] at v
    obtain ⟨v1, v2, v3⟩ := v
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one] at v1 v2 v3
    have hbne : b * (y.2 - x.2) = 1 := by linear_combination v2 - x.2 * v3
    have : b * (y.1 - x.1) = 0 := by linear_combination v1 - x.1 * v3
    rcases mul_eq_zero.mp this with hb | hxy
    · rw [hb] at hbne
      simp at hbne
    · exact (sub_eq_zero.mp hxy).symm
  · intro v
    refine ⟨(x.2 - y.2)⁻¹, -(x.2 - y.2)⁻¹, ?_⟩
    have hne : x.2 - y.2 ≠ 0 := by
      intro v2
      exact h (Prod.ext v (sub_eq_zero.mp v2))
    rw [Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_one]
    · rw [← v]
      ring
    · linear_combination inv_mul_cancel₀ hne
    · ring

theorem vert_constant (l : Line α) (x y : α × α) (h : x ∈ l) (h₂ : y ∈ l)
    (hor : l.vert) : x.1 = y.1 := by
  by_cases hxy : x = y
  · simp_all
  · apply (Line.of_vert_iff x y hxy).mp
    rw [← line_eq_of x y hxy l]
    · assumption
    · constructor <;> assumption

/-- The line `{(x, y) : y = a * x + b}`. -/
def of_equation (a b : α) : Line α := Line.of (0, b) (1, a + b) (by simp)

end Line

theorem mem_of_equation_iff (a b : α) (x : α × α) :
    x ∈ Line.of_equation a b ↔ a * x.1 + b = x.2 := by
  unfold Line.of_equation Line.of Submodule.pair
  conv =>
    lhs
    apply propext Submodule.mem_span_pair
  simp only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one, Prod.mk_add_mk, zero_add, Prod.mk.injEq,
    exists_eq_left]
  constructor
  · rintro ⟨_, hy1, hy2⟩
    linear_combination hy1 - b * hy2
  · intro h
    exists 1 - x.1
    ring_nf
    rw [mul_comm] at h
    simp [h]

namespace Line

theorem uncurry_of_equation_injective :
    Function.Injective (Function.uncurry (Line.of_equation (α := α))) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [Function.uncurry] at h
  have t1 := congr((0, a2) ∈ $h)
  rw [mem_of_equation_iff, mem_of_equation_iff] at t1
  simp only [mul_zero, zero_add, eq_iff_iff, true_iff] at t1
  have t2 := congr((1, a1 + a2) ∈ $h)
  rw [mem_of_equation_iff, mem_of_equation_iff] at t2
  simp only [mul_one, eq_iff_iff, true_iff] at t2
  rw [Prod.mk.injEq]
  constructor
  · linear_combination t1 - t2
  · linear_combination -t1

end Line

theorem point_intersect [Fintype α] (i j : α × α) (oh : i ≠ j) :
    (univ.filter (fun (x : Line α) => i ∈ x ∧ j ∈ x)).card = 1 := by
  rw [card_eq_one]
  exists Line.of i j oh
  rw [eq_singleton_iff_unique_mem]
  constructor
  · simp only [mem_filter, mem_univ, true_and]
    constructor
    · apply mem_line1
    · apply mem_line2
  · intro l₂ h
    simp only [mem_filter, mem_univ, true_and] at h
    apply line_eq_of
    exact h

theorem line_intersect [Fintype α] (i j : Line α) (h : i ≠ j) :
    (univ.filter (fun (x : α × α) => x ∈ i ∧ x ∈ j)).card ≤ 1 := by
  by_contra! nh
  rw [Finset.one_lt_card] at nh
  obtain ⟨a, ha, b, hb, neq⟩ := nh
  simp only [mem_filter, mem_univ, true_and] at ha hb
  let S := (univ.filter (fun (x : Line α) => a ∈ x ∧ b ∈ x))
  have hcard : S.card = 1 := point_intersect a b neq
  have m1 : i ∈ S := by simp only [S, mem_filter, mem_univ, true_and]; exact ⟨ha.1, hb.1⟩
  have m2 : j ∈ S := by simp only [S, mem_filter, mem_univ, true_and]; exact ⟨ha.2, hb.2⟩
  have := one_lt_card.mpr ⟨i, m1, j, m2, h⟩
  linarith

/-- The set of point-line incidences between a set of points and a set of lines. -/
noncomputable def Intersections (P : Finset (α × α)) (L : Finset (Line α)) :=
  (P ×ˢ L).filter (fun x => x.1 ∈ x.2)

/-- The points of `P` lying on a fixed line `L`. -/
noncomputable def IntersectionsP (P : Finset (α × α)) (L : Line α) :=
  P.filter (fun x => x ∈ L)

/-- The lines of `L` passing through a fixed point `P`. -/
noncomputable def IntersectionsL (P : α × α) (L : Finset (Line α)) :=
  L.filter (fun x => P ∈ x)

lemma IntP_subset_of_subset {P₁ P₂ : Finset (α × α)} {l : Line α} (h : P₁ ⊆ P₂) :
    IntersectionsP P₁ l ⊆ IntersectionsP P₂ l := by
  apply filter_subset_filter
  assumption

@[simp]
lemma Int_empty {L : Finset (Line α)} :
    Intersections ∅ L = ∅ := by
  simp [Intersections]

@[simp]
lemma Int2_empty {P : Finset (α × α)} :
    Intersections P ∅ = ∅ := by
  simp [Intersections]

lemma IntersectionsP_sum (P : Finset (α × α)) (L : Finset (Line α)) :
    (Intersections P L).card = ∑ y ∈ L, (IntersectionsP P y).card := by
  calc
    (Intersections P L).card = ((P ×ˢ L).filter (fun x => x.1 ∈ x.2)).card := rfl
    _ = ∑ x ∈ (P ×ˢ L).filter (fun x => x.1 ∈ x.2), 1 := by simp
    _ = ∑ x ∈ (P ×ˢ L), if x.1 ∈ x.2 then 1 else 0 := by rw [sum_filter]
    _ = ∑ y ∈ L, ∑ x ∈ P, if x ∈ y then 1 else 0 := by rw [sum_product_right]
    _ = ∑ y ∈ L, (P.filter (fun x => x ∈ y)).card := by simp
    _ = ∑ y ∈ L, (IntersectionsP P y).card := rfl

lemma IntersectionsL_sum (P : Finset (α × α)) (L : Finset (Line α)) :
    (Intersections P L).card = ∑ y ∈ P, (IntersectionsL y L).card := by
  calc
    (Intersections P L).card = ((P ×ˢ L).filter (fun x => x.1 ∈ x.2)).card := rfl
    _ = ∑ x ∈ (P ×ˢ L).filter (fun x => x.1 ∈ x.2), 1 := by simp
    _ = ∑ x ∈ (P ×ˢ L), if x.1 ∈ x.2 then 1 else 0 := by rw [sum_filter]
    _ = ∑ x ∈ P, ∑ y ∈ L, if x ∈ y then 1 else 0 := by rw [sum_product]
    _ = ∑ x ∈ P, (L.filter (fun y => x ∈ y)).card := by simp
    _ = ∑ y ∈ P, (IntersectionsL y L).card := rfl

lemma lin_ST (P : Finset (α × α)) (L : Finset (Line α)) :
    (Intersections P L).card ≤ P.card * L.card := by
  calc
    (Intersections P L).card ≤ (P ×ˢ L).card := Finset.card_filter_le _ _
    _ = P.card * L.card := by simp

lemma CS_UB [Finite α] (P : Finset <| α × α) (L : Finset <| Line α) :
    (Intersections P L).card ^ 2 ≤ L.card * P.card * (L.card + P.card) := by
  have : Fintype α := Fintype.ofFinite α
  calc
    (Intersections P L).card ^ 2 = (∑ x ∈ P, (IntersectionsL x L).card) ^ 2 := by
      rw [IntersectionsL_sum]
    _ ≤ P.card * ∑ x ∈ P, (IntersectionsL x L).card ^ 2 := by
      rw [← Nat.cast_le (α := ℝ)]
      push_cast
      apply sq_sum_le_card_mul_sum_sq
    _ = P.card * ∑ x ∈ P, ∑ y ∈ L, ∑ z ∈ L,
        (if x ∈ y then 1 else 0) * (if x ∈ z then 1 else 0) := by
      congr
      ext x
      rw [← mul_one (a := (IntersectionsL x L).card), ← smul_eq_mul, ← sum_const, IntersectionsL,
        sum_filter, sq, sum_mul_sum]
    _ = P.card * ∑ y ∈ L, ∑ z ∈ L, ∑ x ∈ P,
        (if x ∈ y then 1 else 0) * (if x ∈ z then 1 else 0) := by
      rw [sum_comm]
      congr
      ext
      rw [sum_comm]
    _ ≤ P.card * ∑ y ∈ L, (∑ x ∈ P, (if x ∈ y then 1 else 0) + ∑ z ∈ L, 1) := by
      apply mul_le_mul_of_nonneg_left
      · apply sum_le_sum
        intro i h
        rw [sum_eq_add_sum_diff_singleton_of_mem h]
        apply add_le_add
        · apply le_of_eq
          apply sum_congr
          · rfl
          · aesop
        · rw [sum_eq_add_sum_diff_singleton_of_mem (s := L) h]
          apply le_add_left
          apply sum_le_sum
          intro j h₂
          have neq : i ≠ j := by aesop
          calc ∑ x ∈ P, (if x ∈ i then 1 else 0) * (if x ∈ j then 1 else 0)
            _ = ∑ x ∈ P, if x ∈ i ∧ x ∈ j then 1 else 0 := by
                apply sum_congr
                · rfl
                · aesop
            _ = (P.filter (fun x => x ∈ i ∧ x ∈ j)).card := by simp
            _ ≤ (univ.filter (fun (x : α × α) => x ∈ i ∧ x ∈ j)).card := by
                apply card_le_card
                apply filter_subset_filter
                apply subset_univ
            _ ≤ 1 := line_intersect i j neq
      · simp
    _ = P.card * (∑ y ∈ L, ∑ x ∈ P, if x ∈ y then 1 else 0) + P.card * L.card * L.card := by
      simp [sum_add_distrib]; ring
    _ = P.card * (∑ x ∈ (P ×ˢ L), if x.1 ∈ x.2 then 1 else 0) + P.card * L.card * L.card := by
      rw [sum_product_right]
    _ = P.card * (∑ x ∈ (P ×ˢ L).filter (fun x => x.1 ∈ x.2), 1) + P.card * L.card * L.card := by
      rw [sum_filter]
    _ = P.card * ((P ×ˢ L).filter (fun x => x.1 ∈ x.2)).card + P.card * L.card * L.card := by simp
    _ = P.card * (Intersections P L).card + P.card * L.card * L.card := rfl
    _ ≤ P.card * (P.card * L.card) + P.card * L.card * L.card := by gcongr; apply lin_ST
    _ = L.card * P.card * (L.card + P.card) := by ring

end LeanPool.LeanBourgain
