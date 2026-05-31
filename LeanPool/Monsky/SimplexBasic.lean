/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha and contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Finset







-- Shorthand for defining an element of ℝ²
/-- The plane vector with the two given real coordinates. -/
def v (x y : ℝ) : ℝ² := !₂[x, y]

@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := by simp [v]
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := by simp [v]


-- Definition of an n-dimensional standard simplex.
/-- The closed standard `n`-simplex of nonnegative weights summing to one. -/
def closed_simplex (n : ℕ) : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
/-- The open standard `n`-simplex of positive weights summing to one. -/
def open_simplex (n : ℕ) : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

/-
  The Fin n → ℝ² in the following definitions represents the vertices of a polygon.
  Beware: Whenever the n vertices do not define an n-gon, i.e. a vertex lies within the
  convex hull of the others, the open_hull does not give the topological interior of the closed
  hull.

  Also when f i = P for all i, both the closed_hull and open_hull are {P i}.
-/
/-- The closed convex hull of a finite point family, via the closed simplex. -/
def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
/-- The open convex hull of a finite point family, via the open simplex. -/
def open_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n


/- Corner of the standard simplex.-/
/-- The `i`-th vertex of the standard simplex, as a weight function. -/
def simplex_vertex {n : ℕ} (i : Fin n) : Fin n → ℝ :=
    fun j ↦ if i = j then 1 else 0

lemma simplex_vertex_in_simplex {n : ℕ} {i : Fin n} : simplex_vertex i ∈ closed_simplex n := by
  exact ⟨fun j ↦ by by_cases h : i = j <;> simp [simplex_vertex, h], by simp [simplex_vertex]⟩

lemma closed_simplex_zero_empty : closed_simplex 0 = ∅ := by
  rw [←Set.not_nonempty_iff_eq_empty]
  exact fun ⟨_,⟨_,hx⟩⟩ ↦ by rw [@Fin.sum_univ_zero] at hx; exact zero_ne_one' _ hx

lemma open_simplex_zero_empty : open_simplex 0 = ∅ := by
  rw [←Set.not_nonempty_iff_eq_empty]
  exact fun ⟨_,⟨_,hx⟩⟩ ↦ by rw [@Fin.sum_univ_zero] at hx; exact zero_ne_one' _ hx

@[simp]
lemma simplex_vertex_image {n : ℕ} {i : Fin n} (f : Fin n → ℝ²) :
    ∑ k, (simplex_vertex i k) • f k = f i := by simp [simplex_vertex]

@[simp]
lemma corner_in_closed_hull {n : ℕ} {i : Fin n} {P : Fin n → ℝ²} : P i ∈ closed_hull P := by
  exact ⟨simplex_vertex i, simplex_vertex_in_simplex, by simp⟩

lemma closed_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0) :
    closed_hull (fun (_ : Fin n) ↦ P) = {P} := by
  ext _
  constructor
  · intro ⟨_, hα, hαv⟩
    simp [←hαv, ←sum_smul, hα.2, one_smul, Set.mem_singleton_iff]
  · intro hv; rw [hv]
    exact corner_in_closed_hull (i := ⟨0, Nat.zero_lt_of_ne_zero hn⟩)

lemma closed_hull_constant_rev {n : ℕ} {P : ℝ²} {f : Fin n → ℝ²}
    (hc : closed_hull f = {P}) : ∀ i, f i = P := by
  simp_rw [←Set.mem_singleton_iff, ←hc]
  exact fun _ ↦ corner_in_closed_hull


lemma open_pol_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ²) : Set.Nonempty (open_hull P) := by
  use ∑ i, (1/(n : ℝ)) • P i, fun _ ↦ (1/(n : ℝ))
  refine ⟨⟨fun _ ↦ by simp [hn], ?_⟩, by simp⟩
  simp only [one_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by simp; linarith)


lemma open_sub_closed_simplex {n : ℕ} : open_simplex n ⊆ closed_simplex n :=
  fun _ ⟨hαpos, hαsum⟩ ↦ ⟨fun i ↦ by linarith [hαpos i], hαsum⟩

lemma open_sub_closed {n : ℕ} (P : Fin n → ℝ²) : open_hull P ⊆ closed_hull P :=
  Set.image_mono open_sub_closed_simplex

lemma closed_pol_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ²) : Set.Nonempty (closed_hull P) :=
  Set.Nonempty.mono (open_sub_closed P) (open_pol_nonempty hn P)

lemma open_hull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0) :
    open_hull (fun (_ : Fin n) ↦ P) = {P} :=
  (Set.Nonempty.subset_singleton_iff (open_pol_nonempty (Nat.zero_lt_of_ne_zero hn) _)).mp
      (subset_of_subset_of_eq (open_sub_closed _) (closed_hull_constant hn))

lemma closed_hull_zero_dim (f : Fin 0 → ℝ²) : closed_hull f = ∅ := by
  rw [closed_hull, closed_simplex_zero_empty, Set.image_empty]

lemma open_hull_zero_dim (f : Fin 0 → ℝ²) : open_hull f = ∅ := by
  rw [open_hull, open_simplex_zero_empty, Set.image_empty]




/-- The point obtained as a weighted combination of a point family. -/
noncomputable def linear_combination {n : ℕ} (α : Fin n → ℝ) (f : Fin n → ℝ²)
    : ℝ² := ∑ i, α i • f i

lemma linear_co_closed {n : ℕ} {α : Fin n → ℝ} (f : Fin n → ℝ²) (h : α ∈ closed_simplex n) :
    linear_combination α f ∈ closed_hull f := ⟨α, h, by rfl⟩




/- Implications of the requirements that (∀ i, 0 ≤ α i),  ∑ i, α i = 1. -/

lemma simplex_co_eq_1 {n : ℕ} {α : Fin n → ℝ} {i : Fin n}
    (h₁ : α ∈ closed_simplex n) (h₂ : α i = 1) : ∀ j, j ≠ i → α j = 0 := by
  by_contra hcontra; push Not at hcontra
  have ⟨j, hji, hj0⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1 = α i               := h₂.symm
    _ < α i + α j         := by rw [lt_add_iff_pos_right]; exact lt_of_le_of_ne (h₁.1 j) (hj0.symm)
    _ = ∑(k ∈ {i,j}), α k := (sum_pair hji.symm).symm
    _ ≤ ∑ k, α k          := sum_le_univ_sum_of_nonneg h₁.1
    _ = 1                 := h₁.2

lemma simplex_exists_co_pos {n : ℕ} {α : Fin n → ℝ} (h : α ∈ closed_simplex n)
    : ∃ i, 0 < α i := by
  by_contra hcontra; push Not at hcontra
  have t : 1 ≤ (0: ℝ)  := by
    calc
      1 = ∑ i, α i        := h.2.symm
      _ ≤ ∑ (i: Fin n), 0 := sum_le_sum fun i _ ↦ hcontra i
      _ = 0               := Fintype.sum_eq_zero _ (fun _ ↦ rfl)
  linarith

lemma simplex_co_leq_1 {n : ℕ} {α : Fin n → ℝ}
    (h₁ : α ∈ closed_simplex n) : ∀ i, α i ≤ 1 := by
  by_contra hcontra; push Not at hcontra
  have ⟨i,hi⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1   < α i             := hi
    _   = ∑ k ∈ {i}, α k  := (sum_singleton _ _).symm
    _   ≤ ∑ k, α k        := sum_le_univ_sum_of_nonneg h₁.1
    _   = 1               := h₁.2


lemma simplex_co_leq_1_open {n : ℕ} {α : Fin n → ℝ} (hn : 1 < n)
    (h₁ : α ∈ open_simplex n) : ∀ i, α i < 1 := by
  intro i
  apply lt_of_le_of_ne (simplex_co_leq_1 (open_sub_closed_simplex h₁) i)
  intro hα
  have hj : ∃ j, i ≠ j := by
    by_cases hs : i = ⟨0, by linarith⟩
    · use ⟨1, by linarith⟩
      simp [hs]
    · use ⟨0, by linarith⟩
  have ⟨j, hj⟩ := hj
  linarith [h₁.1 j, simplex_co_eq_1 (open_sub_closed_simplex h₁) hα j hj.symm]

/- Some lemmas specifically about Fin 2 → ℝ. -/

lemma simplex_closed_sub_fin2 {α : Fin 2 → ℝ} (h : α ∈ closed_simplex 2) :
    ∀ i, α i = 1 - α ((fun | 0 => 1 | 1 => 0) i) := by
    intro i;
    rw [←h.2, Fin.sum_univ_two]
    fin_cases i <;> simp

lemma simplex_open_sub_fin2 {α : Fin 2 → ℝ} (h : α ∈ open_simplex 2) :
    ∀ i, α i = 1 - α ((fun | 0 => 1 | 1 => 0) i) :=
  simplex_closed_sub_fin2 (open_sub_closed_simplex h)

/-- Encodes a real `x` as the pair of weights `(x, 1 - x)`. -/
def real_to_fin_2 (x : ℝ) : (Fin 2 → ℝ) := fun | 0 => x | 1 => 1 - x

lemma real_to_fin_2_closed {x : ℝ} (h₁ : 0 ≤ x) (h₂ : x ≤ 1)
    : real_to_fin_2 x ∈ closed_simplex 2 :=
  ⟨fun i ↦ by fin_cases i <;> (simp only [real_to_fin_2, sub_nonneg]; assumption),
    by simp only [real_to_fin_2, Fin.sum_univ_two, add_sub_cancel]⟩

lemma real_to_fin_2_open {x : ℝ} (h₁ : 0 < x) (h₂ : x < 1)
    : real_to_fin_2 x ∈ open_simplex 2 :=
  ⟨fun i ↦ by fin_cases i <;> (simp only [real_to_fin_2, sub_pos]; assumption),
    by simp only [real_to_fin_2, Fin.sum_univ_two, add_sub_cancel]⟩




/- Vertex set of polygon P₁ lies inside the closed hull of polygon P₂ implies
    the closed hull of P₁ lies inside the closed hull of P₂. -/
lemma closed_hull_convex {n₁ n₂ : ℕ} {P₁ : Fin n₁ → ℝ²} {P₂ : Fin n₂ → ℝ²}
  (h : ∀ i, P₁ i ∈ closed_hull P₂) :
  closed_hull P₁ ⊆ closed_hull P₂ := by
  intro p ⟨β, hβ, hβp⟩
  use fun i ↦ ∑ k, (β k) * (Classical.choose (h k) i)
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact fun _ ↦ Fintype.sum_nonneg fun _ ↦
      mul_nonneg (hβ.1 _) ((Classical.choose_spec (h _)).1.1 _)
  · simp_rw [sum_comm (γ := Fin n₂), ←mul_sum, (Classical.choose_spec (h _)).1.2,
      mul_one]
    exact hβ.2
  · simp_rw [sum_smul, mul_smul, sum_comm (γ := Fin n₂), ←smul_sum,
      (Classical.choose_spec (h _)).2]
    exact hβp


lemma closed_hull_open_hull_com {n : ℕ} {P : Fin n → ℝ²} {x y : ℝ²}
  (hx : x ∈ open_hull P) (hy : y ∈ closed_hull P) :
    (1/(2:ℝ)) • x + (1/(2:ℝ)) • y ∈ open_hull P := by
  have ⟨α, hα, hαx⟩ := hx
  have ⟨β, hβ, hβy⟩ := hy
  use fun i ↦ (1/(2 : ℝ)) * α i + (1/(2:ℝ)) * β i
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    linarith [hα.1 i, hβ.1 i]
  · rw [sum_add_distrib, ←mul_sum,  ←mul_sum, hα.2, hβ.2]
    ring
  · simp_rw [add_smul _, sum_add_distrib, mul_smul, ←smul_sum, hαx, hβy]



/-
  We define the boundary of a polygon as the elements in the closed hull but not
  in the open hull.
-/

/-- The boundary of the convex hull of a point family: closed hull minus open hull. -/
def boundary {n : ℕ} (P : Fin n → ℝ²) : Set ℝ² := (closed_hull P) \ (open_hull P)

lemma boundary_sub_closed {n : ℕ} (P : Fin n → ℝ²) : boundary P ⊆ closed_hull P :=
  Set.diff_subset

lemma boundary_not_in_open {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∉ open_hull P := hx.2

lemma boundary_in_closed {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∈ closed_hull P := Set.mem_of_mem_diff hx

lemma boundary_int_open_empty {n : ℕ} {P : Fin n → ℝ²} : boundary P ∩ open_hull P = ∅ :=
  Set.diff_inter_self

lemma boundary_open_disjoint {n : ℕ} {P : Fin n → ℝ²} : Disjoint (boundary P) (open_hull P) :=
  Set.disjoint_iff_inter_eq_empty.mpr boundary_int_open_empty

lemma boundary_union_open_closed {n : ℕ} {P : Fin n → ℝ²} :
    boundary P ∪ open_hull P = closed_hull P := Set.diff_union_of_subset (open_sub_closed P)

lemma open_closed_hull_minus_boundary {n : ℕ} {P : Fin n → ℝ²} :
    closed_hull P \ boundary P = open_hull P := by
  simp [boundary, open_sub_closed]

lemma boundary_constant {n : ℕ} {P : ℝ²} :
    boundary (fun (_ : Fin n) ↦ P) = ∅ := by
  rcases (ne_or_eq n 0) with hn | hz
  · unfold boundary
    rw [open_hull_constant hn, closed_hull_constant hn]
    simp only [sdiff_self, Set.bot_eq_empty]
  · unfold boundary
    unfold closed_hull
    rw [hz]
    rw [closed_simplex_zero_empty]
    simp only [univ_eq_empty, sum_empty, Set.image_empty, Set.empty_diff]




lemma open_hull_constant_rev {n : ℕ} {P : ℝ²} {f : Fin n → ℝ²}
    (ho : open_hull f = {P}) : ∀ i, f i = P :=  by
  rcases eq_or_ne 0 n with hz | hn
  · intro i
    subst hz
    by_contra h
    unfold open_hull at ho
    rw [open_simplex_zero_empty] at ho
    simp only [univ_eq_empty, sum_empty, Set.image_empty] at ho
    symm at ho
    exact Set.singleton_ne_empty P ho
  · by_contra hc; push Not at hc
    have hP : P ∈ open_hull f := by
      rw [ho, Set.mem_singleton_iff]
    have ⟨i, hi⟩ := hc
    have this := closed_hull_open_hull_com hP (corner_in_closed_hull (i := i) (P := f))
    have bla := (one_smul (M := ℝ) P)
    rw [ho, Set.mem_singleton_iff, add_comm, ←eq_sub_iff_add_eq] at this
    nth_rw 1 [←(one_smul (M := ℝ) P), ←sub_smul] at this
    ring_nf at this
    apply hi
    rwa [IsUnit.smul_left_cancel (by norm_num)] at this

end Monsky
end LeanPool
