/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha and contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import LeanPool.Monsky.SimplexBasic
import LeanPool.Monsky.SegmentTriangle
import LeanPool.Monsky.BasicDefinitions
import LeanPool.Monsky.RainbowTriangles
import LeanPool.Monsky.Square

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²


open BigOperators
open Finset

attribute [local instance] Classical.propDecidable



/-- The set of nondegenerate segments with both endpoints in `X`. -/
noncomputable def segment_set (X : Finset ℝ²) : Finset Segment :=
    Finset.image (fun (a,b) ↦ to_segment a b) ((Finset.product X X).filter (fun (a,b) ↦ a ≠ b))

/-- The segments of `segment_set X` whose open hull avoids the set `A`. -/
noncomputable def avoiding_segment_set (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (segment_set X).filter (fun L ↦ Disjoint (closed_hull L) (A))

/-- The avoiding segments of `X` that are basic, i.e. contain no point of `X` in their interior. -/
noncomputable def basic_avoiding_segment_set (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (avoiding_segment_set X A).filter (fun L ↦ ∀ x ∈ X, x ∉ open_hull L)



/-- An inductively defined chain of collinear segments between two points. -/
inductive Chain : ℝ² → ℝ² → Type
    | basic {u v : ℝ²}  : Chain u v
    | join {u v w : ℝ²} (hCollineair : colin u v w) (C : Chain v w) : Chain u w

/-- The finite set of basic segments making up a chain. -/
noncomputable def to_basic_segments {u v : ℝ²} : Chain u v → Finset Segment
    | Chain.basic              => {to_segment u v}
    | @Chain.join _ w _ _ C    => to_basic_segments C ∪ {to_segment u w}

/-- Concatenates two chains sharing an endpoint into a single chain. -/
noncomputable def glue_chains {u v w : ℝ²} (hCollinear : colin u v w)
    : Chain u v → Chain v w → Chain u w
    | Chain.basic, C      => Chain.join hCollinear C
    | Chain.join h C', C  => Chain.join ⟨hCollinear.1, interior_left_trans h.2 hCollinear.2⟩
        (glue_chains (sub_collinear_right hCollinear h.2) C' C)

/-- Reverses the direction of a chain. -/
noncomputable def reverse_chain {u v : ℝ²} : Chain u v → Chain v u
    | Chain.basic           => Chain.basic
    | @Chain.join _ x _ h C => glue_chains (colin_reverse h) (reverse_chain C) (@Chain.basic x u)

/-- The single segment from the start to the end of a chain. -/
noncomputable def chain_to_big_segment {u v : ℝ²} (C : Chain u v) : Segment :=
  match C with
  | _ => to_segment u v

lemma chain_to_big_segment_join {u v w} (h : colin u v w) (C : Chain v w) :
    chain_to_big_segment (Chain.join h C) = to_segment u w := rfl

lemma chain_to_big_segment_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w) : chain_to_big_segment (glue_chains h CL CR) = to_segment u w := rfl

lemma glue_chains_assoc {u v w x : ℝ²} (C₁ : Chain u v) (C₂ : Chain v w) (C₃ : Chain w x)
    (h₁ : colin u v w) (h₂ : colin v w x) :
    glue_chains (colin_trans_right h₁ h₂) (glue_chains h₁ C₁ C₂) C₃ =
    glue_chains (colin_trans_left h₁ h₂) C₁ (glue_chains h₂ C₂ C₃) := by
  induction C₁ with
  | basic         => rfl
  | join h₃ C ih  =>
    simp only [glue_chains, Chain.join.injEq, heq_eq_eq, true_and]
    exact ih C₂ _ _


lemma reverse_chain_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w)
    : reverse_chain (glue_chains h CL CR)
    = glue_chains (colin_reverse h) (reverse_chain CR) (reverse_chain CL) := by
  induction CL with
  | basic         => rfl
  | join h₂ C ih  =>
      simp only [glue_chains, reverse_chain, ih (sub_collinear_right h h₂.2) CR]
      rw [←glue_chains_assoc]

lemma basic_segments_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w)
    : to_basic_segments (glue_chains h CL CR) = to_basic_segments CL ∪ to_basic_segments CR := by
  induction CL with
  | basic       => rw [union_comm]; rfl
  | join h₂ C ih  =>
      simp [to_basic_segments, glue_chains, ih (sub_collinear_right h h₂.2) CR]


lemma basic_segment_in_open_hull {u v : ℝ²} (C : Chain u v) {S : Segment}
    (hS : S ∈ to_basic_segments C) : open_hull S ⊆ open_hull (to_segment u v) := by
  induction C with
  |basic         => simp only [to_basic_segments, mem_singleton] at *; rw [hS]
  |join h₂ C ih  =>
    simp only [to_basic_segments, mem_union, mem_singleton] at *
    rcases hS with hS | hS
    · refine subset_trans (ih hS) ?_
      apply right_open_hull_in_colin; exact h₂
    · rw [hS]
      apply left_open_hull_in_colin; exact h₂



lemma basic_segments_colin_disjoint {u v w : ℝ²} {C : Chain v w} (h : colin u v w) :
    to_segment u v ∉ to_basic_segments C := by
  intro hc
  have this := basic_segment_in_open_hull _ hc
  have other : open_hull (to_segment u v) ∩ open_hull (to_segment v w) = ∅ := by
    apply colin_intersection_open_hulls_empty
    apply h
  have nonempty : ∃ (b : ℝ²), b ∈ open_hull (to_segment u v) := by
    apply open_pol_nonempty
    linarith
  rcases nonempty with ⟨p, q⟩
  have contra' :  p ∈ open_hull (to_segment v w) := by
      tauto_set
  have contra : open_hull (to_segment u v) ∩ open_hull (to_segment v w) ≠ ∅ := by
    rw [← Set.nonempty_iff_ne_empty]
    tauto
  contradiction


lemma basic_segments_colin_disjoint2 {u v w : ℝ²} {C : Chain v w} (h : colin u v w) :
    to_segment v u ∉ to_basic_segments C := by
  intro hc
  have this := basic_segment_in_open_hull _ hc
  rw [← reverse_segment_to_segment, reverse_segment_open_hull] at this
  have other : open_hull (to_segment u v) ∩ open_hull (to_segment v w) = ∅ := by
    apply colin_intersection_open_hulls_empty
    apply h
  have nonempty : ∃ (b : ℝ²), b ∈ open_hull (to_segment u v) := by
    apply open_pol_nonempty
    linarith
  rcases nonempty with ⟨p, q⟩
  have contra' :  p ∈ open_hull (to_segment v w) := by
      tauto_set
  have contra : open_hull (to_segment u v) ∩ open_hull (to_segment v w) ≠ ∅ := by
    rw [← Set.nonempty_iff_ne_empty]
    tauto
  contradiction

lemma basic_segments_colin_disjoint_reverse {u v w : ℝ²} {C : Chain v w} (h : colin u v w) :
    to_segment  u v ∉ to_basic_segments (reverse_chain C ):= by
    intro hc
    have this := basic_segment_in_open_hull _ hc
    have other : open_hull (to_segment u v) ∩ open_hull (to_segment v w) = ∅ := by
      apply colin_intersection_open_hulls_empty
      apply h
    have nonempty : ∃ (b : ℝ²), b ∈ open_hull (to_segment u v) := by
      apply open_pol_nonempty
      linarith
    rcases nonempty with ⟨p, q⟩
    have contra' :  p ∈ open_hull (to_segment w v) := by
        tauto_set
    have contra : open_hull (to_segment u v) ∩ open_hull (to_segment v w) ≠ ∅ := by
      rw [← Set.nonempty_iff_ne_empty]
      have hvw : open_hull (to_segment v w) = open_hull (to_segment w v) := by
        rw [← reverse_segment_to_segment, reverse_segment_open_hull]
      rw [hvw]
      tauto
    contradiction

lemma reverse_chain_basic_segments {u v : ℝ²} (C : Chain u v) :
    to_basic_segments (reverse_chain C) =
    Finset.image (fun S ↦ reverse_segment S) (to_basic_segments C) := by
  induction C with
  |basic         => rfl
  | join _ _ ih   =>
      simp only [reverse_chain, to_basic_segments, basic_segments_glue, ih, Finset.image_union]
      congr 1

lemma reverse_chain_basic_segments_disjoint {u v : ℝ²} (C : Chain u v) (huv : u ≠ v) :
    Disjoint (to_basic_segments C) (to_basic_segments (reverse_chain C)) := by
  induction C with
  | basic =>
      simp only [to_basic_segments, reverse_chain, disjoint_singleton_left, mem_singleton]
      exact fun h ↦ huv (congrFun h 0)
  | @join x y z h₂ C ih =>
      have hyz : y ≠ z := (middle_not_boundary_colin h₂).2
      have hxy : x ≠ y := (middle_not_boundary_colin h₂).1
      simp only [to_basic_segments, union_singleton, reverse_chain, basic_segments_glue,
        disjoint_insert_right, mem_insert, not_or, disjoint_insert_left]
      refine ⟨⟨fun h ↦ hxy (congrFun h 1), basic_segments_colin_disjoint2 h₂⟩,
        basic_segments_colin_disjoint_reverse h₂, ih hyz⟩


lemma segment_set_vertex {X : Finset ℝ²} {S : Segment}
  (hS : S ∈ segment_set X) : ∀ i, S i ∈ X := by
  simp only [segment_set, ne_eq, product_eq_sprod, mem_image,
              mem_filter, mem_product, Prod.exists] at hS
  have ⟨a, b, ⟨⟨⟨ha,hb⟩ ,h₁⟩,h₂⟩⟩ := hS
  rw [←h₂]
  intro i; fin_cases i <;> (simp only [to_segment]; assumption)


lemma avoiding_segment_set_sub {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) : S ∈ segment_set X :=
  mem_of_mem_filter S hS

lemma basic_avoiding_segment_set_sub {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ basic_avoiding_segment_set X A) : S ∈ segment_set X :=
  avoiding_segment_set_sub (A := A) (mem_of_mem_filter S hS)

lemma segment_set_vertex_distinct {X : Finset ℝ²} {S : Segment}
    (hS : S ∈ segment_set X) : S 0 ≠ S 1 := by
  simp only [segment_set, ne_eq, product_eq_sprod, mem_image,
              mem_filter, mem_product, Prod.exists] at hS
  have ⟨_, _, ⟨⟨_,_⟩ ,h₂⟩⟩ := hS
  rw [←h₂]
  simpa [to_segment]

lemma segment_set_boundary {X : Finset ℝ²} {x : ℝ²} {S : Segment} (hS : S ∈ segment_set X)
    (hx : x ∈ boundary S) : x ∈ X := by
  rw [boundary_seg (segment_set_vertex_distinct hS), mem_coe, mem_image] at hx
  have ⟨i, _, hi⟩ := hx
  rw [←hi]
  exact segment_set_vertex hS i

lemma segment_set_reverse {X : Finset ℝ²} {S : Segment} (hS : S ∈ segment_set X) :
    reverse_segment S ∈ segment_set X := by
  simp only [segment_set, ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product,
    Prod.exists] at *
  rcases hS with ⟨a, ⟨  b, h⟩⟩
  rw[← h.2, reverse_segment_to_segment]
  exact ⟨b, a, ⟨ ⟨ h.1.1.2,h.1.1.1 ⟩ , fun a_1 ↦ h.1.2 (id (Eq.symm a_1))⟩, by rfl  ⟩

lemma avoiding_segment_set_reverse {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) : reverse_segment S ∈ avoiding_segment_set X A := by
  simp only[ avoiding_segment_set, mem_filter, reverse_segment_closed_hull ] at *
  exact ⟨ segment_set_reverse hS.1, hS.2⟩

lemma basic_avoiding_segment_set_reverse {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ basic_avoiding_segment_set X A) :
    reverse_segment S ∈ basic_avoiding_segment_set X A := by
  simp only[basic_avoiding_segment_set, mem_filter ,reverse_segment_open_hull] at *
  exact ⟨ avoiding_segment_set_reverse hS.1, hS.2 ⟩

lemma avoiding_segment_set_sub_left {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) {x : ℝ²} (hx : x ∈ X) (hxS : x ∈ open_hull S)
    : to_segment (S 0) x ∈ avoiding_segment_set X A := by
  simp only [avoiding_segment_set, mem_filter, Fin.isValue] at *
  constructor
  · simp only [segment_set, ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product,
    Prod.exists, Fin.isValue] at *
    rcases hS with ⟨⟨ a, ⟨ b, h⟩⟩, _⟩
    exact ⟨a, x, ⟨ ⟨h.1.1.1 , hx⟩ ,
      (middle_not_boundary_colin ⟨h.1.2 , by rw[h.2]; exact hxS ⟩).1⟩,
      by rw[← h.2]; simp only [to_segment]  ⟩
  · refine Set.disjoint_of_subset (closed_hull_convex ?_) (fun ⦃a⦄ a ↦ a) hS.2
    intro i; fin_cases i <;> simp only [to_segment, Fin.isValue, corner_in_closed_hull]
    exact open_sub_closed S hxS

lemma avoiding_segment_set_sub_right {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) {x : ℝ²} (hx : x ∈ X) (hxS : x ∈ open_hull S)
    : to_segment x (S 1) ∈ avoiding_segment_set X A := by
  rw[← reverse_segment_to_segment]
  refine avoiding_segment_set_reverse
    (avoiding_segment_set_sub_left (avoiding_segment_set_reverse hS) hx ?_ )
  rwa[← reverse_segment_open_hull]




-- lemma segment_induction {A : Set ℝ²} {X : Finset ℝ²}
--     {f : Segment → Prop} (hBasic : ∀ {S}, S ∈ basic_avoiding_segment_set X A → f S)
--     (hJoin : ∀ {u v w}, u ∈ X → v ∈ X → w ∈ X → colin u v w → f (to_segment u v) →
--     f (to_segment v w) → f (to_segment u w))
--     : ∀ {S : Segment}, S ∈ avoiding_segment_set X A → f S := by
--   intro S hS
--   generalize Scard : (Finset.filter (fun p ↦ p ∈ open_hull S) X).card = n
--   induction n using Nat.strong_induction_on generalizing S with
--   | h N hN =>
--   by_cases hN₀ : N = 0
--   · apply hBasic
--     simp only [basic_avoiding_segment_set, mem_filter]
--     refine ⟨hS,?_⟩
--     simp [hN₀, filter_eq_empty_iff] at Scard
--     exact Scard
--   · rw [←Scard, ←ne_eq, Finset.card_ne_zero, filter_nonempty_iff] at hN₀
--     have ⟨x, ⟨hx, hxS⟩⟩ := hN₀
--     have hcolin : colin (S 0) x (S 1) :=
--       ⟨segment_set_vertex_distinct (avoiding_segment_set_sub hS), hxS⟩
--     convert hJoin (segment_set_vertex (avoiding_segment_set_sub hS) 0) hx
--         (segment_set_vertex (avoiding_segment_set_sub hS) 1) hcolin ?_ ?_
--     · exact segment_rfl.symm
--     · refine hN (Finset.filter (fun p ↦ p ∈ open_hull (to_segment (S 0) x)) X).card ?_
--         (avoiding_segment_set_sub_left hS hx hxS) rfl
--       sorry
--     · refine hN (Finset.filter (fun p ↦ p ∈ open_hull (to_segment x (S 1))) X).card ?_
--         (avoiding_segment_set_sub_right hS hx hxS) rfl
--       sorry

-- theorem segment_decomposition' {A : Set ℝ²} {X : Finset ℝ²} {S : Segment}
--     (hS : S ∈ avoiding_segment_set X A) :
--     ∃ (C : Chain (S 0) (S 1)),
--     S = chain_to_big_segment C ∧
--     (basic_avoiding_segment_set X A).filter (fun s ↦ closed_hull s ⊆ closed_hull S)
--     = to_basic_segments C ∪ (to_basic_segments (reverse_chain C)) := by
--   revert S
--   apply segment_induction
--   · intro S hS
--     use @Chain.basic (S 0) (S 1)
--     simp only [chain_to_big_segment, Fin.isValue, segment_rfl,
--       to_basic_segments, reverse_chain, true_and]
--     ext L
--     constructor
--     · simp only [mem_filter, Fin.isValue, mem_union, mem_singleton,
--         basic_avoiding_segment_set, avoiding_segment_set, segment_set,
--         ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product, Prod.exists,
--         Fin.isValue, and_imp, forall_exists_index]
--       intro a b  haX hbX hneq habL _ hLx hLS
--       simp only [←habL, ←List.ofFn_inj,List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
--         List.ofFn_zero, List.cons.injEq, and_true, to_segment]
--       by_contra hc; push Not at hc
--       have hf : a ∈ open_hull S ∨ b ∈ open_hull S := by
--         rw [←habL] at hLS
--         rw [@or_iff_not_imp_left]
--         intro ha; by_contra hb
--         have haB : a ∈ boundary S := by
--           rw [boundary, Set.mem_diff]
--           refine ⟨hLS (corner_in_closed_hull (i := ⟨0, by omega⟩)), ha⟩
--         have hbB : b ∈ boundary S := by
--           rw [boundary, Set.mem_diff]
--           refine ⟨hLS (corner_in_closed_hull (i := ⟨1, by omega⟩)), hb⟩
-- simp only [boundary_seg (segment_set_vertex_distinct (basic_avoiding_segment_set_sub hS)),
--             coe_image, coe_univ, Set.image_univ, Set.mem_range] at hbB haB
--         have ⟨i, hai⟩ := haB
--         have ⟨j, hbj⟩ := hbB
--         fin_cases i <;> fin_cases j <;> (
--           simp only [Fin.zero_eta, Fin.isValue] at hai hbj
--           rw [←hai, ←hbj] at hc hneq
--           tauto
--         )
--       simp [basic_avoiding_segment_set] at hS
--       cases' hf with haS hbS
--       · exact hS.2 _ haX haS
--       · exact hS.2 _ hbX hbS
--     · simp only [Fin.isValue, mem_union, mem_singleton, mem_filter]
--       rintro (hLS | hLS) <;> rw [hLS]
--       · simpa
--       · refine ⟨basic_avoiding_segment_set_reverse hS,?_⟩
--         rw [←reverse_segment_closed_hull]
--         rfl

--   · intro u v w huX hvX hwX hc ⟨C₁,⟨hSC₁,hC₁⟩⟩ ⟨C₂,⟨hSC₂,hC₂⟩⟩
--     use glue_chains hc C₁ C₂
--     have haux {A₁ A₂ A₃ A₄ : Finset (Fin 2 → ℝ²)}
--       : (A₁ ∪ A₃) ∪ (A₄ ∪ A₂) = (A₁ ∪ A₂) ∪ (A₃ ∪ A₄) := by
--       simp only [←coe_inj, coe_union]; tauto_set
--     simp only [chain_to_big_segment_glue, segment_rfl, reverse_chain_glue,
--         basic_segments_glue, true_and, haux,
--         ←hC₁, ←hC₂]
--     ext L
--     simp [basic_avoiding_segment_set]
--     constructor
--     · intro ⟨h , hLS⟩
--       cases' colin_sub hc hLS (h.2 _ hvX) with hLleft hLright
--       · left
--         exact ⟨h,hLleft⟩
--       · right
--         exact ⟨h,hLright⟩
--     · rintro (hL | hR)
--       · refine ⟨hL.1, subset_trans hL.2 (closed_hull_convex ?_)⟩
--         intro i; fin_cases i
--         · exact corner_in_closed_hull (i := ⟨0, by omega⟩)
--         · exact open_sub_closed _ hc.2
--       · refine ⟨hR.1, subset_trans hR.2 (closed_hull_convex ?_)⟩
--         intro i; fin_cases i
--         · exact open_sub_closed _ hc.2
--         · exact corner_in_closed_hull (i := ⟨1, by omega⟩)



theorem segment_decomposition {A : Set ℝ²} {X : Finset ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) :
    ∃ (C : Chain (S 0) (S 1)),
    S = chain_to_big_segment C ∧
    (basic_avoiding_segment_set X A).filter (fun s ↦ closed_hull s ⊆ closed_hull S)
    = to_basic_segments C ∪ (to_basic_segments (reverse_chain C)) := by
  generalize Scard : (Finset.filter (fun p ↦ p ∈ open_hull S) X).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h N hm =>
  have hSboundary := boundary_seg (segment_set_vertex_distinct (avoiding_segment_set_sub hS))
  by_cases hN : N = 0
  · use @Chain.basic (S 0) (S 1)
    simp only [chain_to_big_segment, Fin.isValue, segment_rfl,
      to_basic_segments, reverse_chain, true_and]
    simp only [hN, card_eq_zero, filter_eq_empty_iff] at Scard
    ext L
    simp only [mem_filter, Fin.isValue, mem_union, mem_singleton]
    constructor
    · intro ⟨hL, hLS⟩
      have hLi : ∀ i, L i ∈ boundary S := by
        intro i
        simp only [boundary, Set.mem_diff]
        refine ⟨hLS (corner_in_closed_hull),?_⟩
        apply Scard
        exact segment_set_vertex (basic_avoiding_segment_set_sub hL) i
      have hLdif := segment_set_vertex_distinct (basic_avoiding_segment_set_sub hL)
      simp only [hSboundary, coe_image, coe_univ, Set.image_univ, Set.mem_range, Fin.exists_fin_two,
        Fin.isValue, Fin.forall_fin_two] at hLi
      obtain ⟨h0 | h0, h1 | h1⟩ := hLi
      · exact absurd (h0 ▸ h1) hLdif
      · left
        exact List.ofFn_inj.mp (by simp [← h0, ← h1])
      · right
        exact List.ofFn_inj.mp (by simp [to_segment, ← h0, ← h1])
      · exact absurd (h0 ▸ h1) hLdif
    · rintro (hL | hL) <;> rw [hL]
      · refine ⟨?_, fun _ a ↦ a⟩
        simp only [basic_avoiding_segment_set, mem_filter]
        exact ⟨hS,Scard⟩
      · rw [←reverse_segment]
        refine ⟨?_, by rw [reverse_segment_closed_hull]⟩
        apply basic_avoiding_segment_set_reverse
        simp only [basic_avoiding_segment_set, mem_filter]
        exact ⟨hS,Scard⟩
  · have hEl : Finset.Nonempty (filter (fun p ↦ p ∈ open_hull S) X) := by
      rw [← Finset.card_pos, Scard]
      exact Nat.zero_lt_of_ne_zero hN
    have ⟨x, hx⟩ := hEl
    let Sleft := to_segment (S 0) x
    let Sright := to_segment x (S 1)
    have hSlefti : ∀ i, Sleft i ∈ closed_hull S := by
      rw [mem_filter] at hx
      intro i; fin_cases i
      · convert (corner_in_closed_hull (i := 0) (P := S)) using 1
      · convert open_sub_closed _ hx.2
    have hSrighti : ∀ i, Sright i ∈ closed_hull S := by
      rw [mem_filter] at hx
      intro i; fin_cases i
      · convert open_sub_closed _ hx.2
      · convert (corner_in_closed_hull (i := 1) (P := S)) using 1
    have hcolin : colin (S 0) x (S 1) := by
      rw [mem_filter] at hx
      exact ⟨segment_set_vertex_distinct (avoiding_segment_set_sub hS), hx.2⟩
    have Sleftcard : (filter (fun p ↦ p ∈ open_hull Sleft) X).card < N := by
      rw [←Scard]
      refine card_lt_card ⟨?_,?_⟩
      · intro t ht
        simp only [mem_filter] at *
        refine ⟨ht.1, (open_segment_sub hSlefti ?_) ht.2⟩
        convert (middle_not_boundary_colin hcolin).1 using 1
      · rw [@not_subset]
        use x, hx
        intro hcontra
        rw [mem_filter] at hcontra
        refine (boundary_not_in_open (boundary_seg' ?_ 1)) hcontra.2
        convert (middle_not_boundary_colin hcolin).1 using 1
    have Srightcard : (filter (fun p ↦ p ∈ open_hull Sright) X).card < N := by
      rw [←Scard]
      refine card_lt_card ⟨?_,?_⟩
      · intro t ht
        simp only [mem_filter] at *
        refine ⟨ht.1, (open_segment_sub hSrighti ?_) ht.2⟩
        convert (middle_not_boundary_colin hcolin).2 using 1
      · rw [@not_subset]
        use x, hx
        intro hcontra
        rw [mem_filter] at hcontra
        refine (boundary_not_in_open (boundary_seg' ?_ 0)) hcontra.2
        convert (middle_not_boundary_colin hcolin).2 using 1
    rw [mem_filter] at hx
    have ⟨CL,hSCL,hLSegUnion⟩ :=
      hm (filter (fun p ↦ p ∈ open_hull Sleft) X).card Sleftcard
      (avoiding_segment_set_sub_left hS hx.1 hx.2) rfl
    have ⟨CR,hSCR,hRSegUnion⟩ :=
      hm (filter (fun p ↦ p ∈ open_hull Sright) X).card Srightcard
      (avoiding_segment_set_sub_right hS hx.1 hx.2) rfl
    use glue_chains hcolin CL CR
    simp only [chain_to_big_segment_glue, segment_rfl, reverse_chain_glue,
        basic_segments_glue, true_and]
    -- Membership characterisations of the two sub-chains, derived directly from
    -- `hLSegUnion`/`hRSegUnion`. We avoid `rw`-ing the union *term* (whose `Finset`
    -- instance no longer matches after associativity reshuffling) and work purely
    -- at the level of `Finset.mem_union`, which matches up to instance defeq.
    have hLmem : ∀ L, (L ∈ to_basic_segments CL ∨ L ∈ to_basic_segments (reverse_chain CL)) ↔
        (L ∈ basic_avoiding_segment_set X A ∧ closed_hull L ⊆ closed_hull (to_segment (S 0) x)) :=
      fun L ↦ by rw [← Finset.mem_union, ← hLSegUnion]; simp only [Finset.mem_filter]
    have hRmem : ∀ L, (L ∈ to_basic_segments CR ∨ L ∈ to_basic_segments (reverse_chain CR)) ↔
        (L ∈ basic_avoiding_segment_set X A ∧ closed_hull L ⊆ closed_hull (to_segment x (S 1))) :=
      fun L ↦ by rw [← Finset.mem_union, ← hRSegUnion]; simp only [Finset.mem_filter]
    ext L
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h , hLS⟩
      rcases colin_sub hcolin (by convert hLS; exact segment_rfl)
          ((Finset.mem_filter.mp h).2 x hx.1) with hLleft | hLright
      · rcases (hLmem L).mpr ⟨h, hLleft⟩ with hCL | hrevCL
        · exact Or.inl (Or.inl hCL)
        · exact Or.inr (Or.inr hrevCL)
      · rcases (hRmem L).mpr ⟨h, hLright⟩ with hCR | hrevCR
        · exact Or.inl (Or.inr hCR)
        · exact Or.inr (Or.inl hrevCR)
    · rintro ((hCL | hCR) | (hrevCR | hrevCL))
      · exact ⟨((hLmem L).mp (Or.inl hCL)).1,
          subset_trans ((hLmem L).mp (Or.inl hCL)).2 (closed_hull_convex hSlefti)⟩
      · exact ⟨((hRmem L).mp (Or.inl hCR)).1,
          subset_trans ((hRmem L).mp (Or.inl hCR)).2 (closed_hull_convex hSrighti)⟩
      · exact ⟨((hRmem L).mp (Or.inr hrevCR)).1,
          subset_trans ((hRmem L).mp (Or.inr hrevCR)).2 (closed_hull_convex hSrighti)⟩
      · exact ⟨((hLmem L).mp (Or.inr hrevCL)).1,
          subset_trans ((hLmem L).mp (Or.inr hrevCL)).2 (closed_hull_convex hSlefti)⟩


/-- A function on segments that is additive modulo 2 along collinear splits. -/
def two_mod_function (f : Segment → ℕ)
    := ∀ {u v w}, colin u v w →
      (f (to_segment u v) + f (to_segment v w)) % 2 = f (to_segment u w) % 2

/-- A function on segments invariant under reversing the segment. -/
def symm_fun (f : Segment → ℕ) := ∀ S, f (reverse_segment S) = f S

lemma two_mod_function_chains {f : Segment → ℕ} (hf : two_mod_function f) {u v : ℝ²}
    (C : Chain u v) : (∑ S ∈ to_basic_segments C, f S) % 2 = f (to_segment u v) % 2 := by
  induction C with
  | basic         => simp only [to_basic_segments, sum_singleton]
  | join h₂ C ih  =>
      simp only [to_basic_segments]
      rw [Finset.sum_union (by simpa only [disjoint_singleton_right] using
        basic_segments_colin_disjoint h₂)]
      simp only [sum_singleton, Nat.add_mod, ih, dvd_refl, Nat.mod_mod_of_dvd]
      simp only [dvd_refl, Nat.mod_mod_of_dvd, Nat.add_mod_mod, Nat.mod_add_mod, ←hf h₂]
      rw [add_comm]


lemma symm_function_reverse_sum {f : Segment → ℕ} (hf : symm_fun f) {u v : ℝ²}
    (C : Chain u v) :
    (∑ S ∈ to_basic_segments (reverse_chain C), f S) =
    (∑ S ∈ to_basic_segments C, f S) := by
  rw [reverse_chain_basic_segments, Finset.sum_image]
  · congr
    ext L
    exact hf L
  · intro _ _ _ _
    have ⟨hi,_⟩ := reverse_segment_bijective
    exact fun a ↦ hi (hi (hi a))


lemma mod_two_mul {a b : ℕ} (h : a % 2 = b % 2) : (2 * a) % 4 = (2 * b) % 4 := by
  rw [←Int.natCast_inj, Int.natCast_mod, Int.natCast_mod, ←ZMod.intCast_eq_intCast_iff',
      ←sub_eq_zero, ←Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at *
  have ⟨c, hc⟩ := h
  exact ⟨c, by simp only [Nat.cast_mul, ←mul_sub, hc]; ring⟩


lemma sum_two_mod_fun_seg {A : Set ℝ²} {X : Finset ℝ²} {S : Segment}
    (hS : S ∈ avoiding_segment_set X A) {f : Segment → ℕ} (hf₁ : two_mod_function f)
    (hf₂ : symm_fun f) :
    (∑ T ∈ (basic_avoiding_segment_set X A).filter (fun s ↦ closed_hull s ⊆ closed_hull S),
      f T) % 4 =
    (2 * f S) % 4 := by
  have ⟨C, _, hSdecomp⟩ := segment_decomposition hS
  rw [hSdecomp, Finset.sum_union]
  · rw [symm_function_reverse_sum hf₂, ←Nat.two_mul]
    apply mod_two_mul
    convert two_mod_function_chains hf₁ C
  · exact reverse_chain_basic_segments_disjoint _
      (segment_set_vertex_distinct (avoiding_segment_set_sub hS))


variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation ℝ Γ₀)


-- The following function determines whether a segment is purple. We want to sum the value
-- of this function over all segments, so we let it take values in ℕ

/-- Indicator (`0` or `1`) of whether a segment is purple, i.e. red-blue colored. -/
noncomputable def isPurple : Segment → ℕ :=
    fun S ↦ if ( (coloring v (S 0) = Color.Red ∧ coloring v (S 1) = Color.Blue) ∨
      (coloring v (S 0) = Color.Blue ∧ coloring v (S 1) = Color.Red)) then 1 else 0

/-- Indicator (`0` or `1`) of whether a triangle is rainbow. -/
noncomputable def isRainbow : Triangle → ℕ :=
    fun T ↦ if (Function.Surjective (coloring v ∘ T)) then 1 else 0




lemma isPurple_two_mod_function : two_mod_function (isPurple v) := by
  unfold two_mod_function
  intro x y z hColin
  have h := no_Color_lines (to_segment x z) v
  -- In order to use the no color lines, we need that all our points are in the closed hull, to
  -- prove this was slightly frustrating
  have hhelpz : z = (to_segment x z) 1  := by rfl
  have hhelpx : x = (to_segment x z) 0  := by rfl
  have hx : x ∈ closed_hull (to_segment x z) := by
    nth_rewrite 2[hhelpx]; exact corner_in_closed_hull
  have hz : z ∈ closed_hull (to_segment x z) := by
    nth_rewrite 2[hhelpz]; exact corner_in_closed_hull
  have hy : y ∈ closed_hull (to_segment x z) := by
    exact (open_sub_closed (to_segment x z) hColin.2)
  --This finishes the aux lemmas
  rcases h with ⟨ c, hnotc⟩
  have hx1 := hnotc x hx; have hy1 := hnotc y hy; have hz1 := hnotc z hz
  clear hhelpx hhelpz hx hy hz hColin hnotc
  simp only [isPurple, Fin.isValue]
  generalize hcx : coloring v x = cx at hx1
  generalize hcy : coloring v y = cy at hy1
  generalize hcz : coloring v z = cz at hz1
  simp only [to_segment]
  simp_rw [hcx, hcy, hcz]
  -- I am doing an induction over 81 cases.... I hope it is not too slow
  induction c <;> induction cx <;> induction cy <;> induction cz <;> simp only [reduceCtorEq,
    and_false, and_true, or_self, ↓reduceIte, add_zero, Nat.zero_mod] <;> tauto


lemma isPurple_symm_function : symm_fun (isPurple v) := by
  unfold symm_fun
  intro S
  unfold isPurple reverse_segment
  simp only [to_segment]
  congr 1
  rw [eq_iff_iff]
  tauto

-- The segment covered by a chain is purple if and only if an odd number of its basic
-- segments are purple.
/-lemma purple_parity {u v : ℝ²} (C : Chain u v) : ∑ T ∈ to_basic_segments C, isPurple T % 2
    = isPurple (chain_to_big_segment C) := by
  sorry -- can apply two_mod_function_chains
-/

/-- The finite set of all vertices appearing in a triangulation. -/
noncomputable def triangulation_points (Δ : Finset Triangle) : Finset ℝ² :=
  Finset.biUnion Δ (fun T ↦ {T 0, T 1, T 2})


-- This definition might be better so
-- TODO: Change to this
/-- The set of triangulation vertices, viewed as a set of points of the plane. -/
noncomputable def triangulation_points₂ (Δ : Finset Triangle) : Finset ℝ² :=
  Finset.biUnion Δ (fun T ↦ (Finset.image (fun i ↦ T i) Finset.univ))


lemma triangulation_points_mem {Δ : Finset Triangle} {T : Triangle} (hT : T ∈ Δ)
    : ∀ i, T i ∈ triangulation_points Δ := by
  intro i
  simp only [triangulation_points, Fin.isValue, mem_biUnion, mem_insert, mem_singleton]
  use T, hT
  fin_cases i <;> simp


-- The union of the interiors of the triangles of a triangulation
/-- The union of triangle interiors that basic segments of the triangulation must avoid. -/
noncomputable def triangulation_avoiding_set (Δ : Finset Triangle) : Set ℝ² :=
    ⋃ (T ∈ Δ), open_hull T

/-- The basic avoiding segments of a triangulation. -/
noncomputable def triangulation_basic_segments (Δ : Finset Triangle) : Finset Segment :=
  basic_avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)

/-- The basic segments lying on the boundary of the unit square. -/
noncomputable def triangulation_boundary_basic_segments (Δ : Finset Triangle) : Finset Segment :=
  {S ∈ triangulation_basic_segments Δ | open_hull S ⊆ boundary unit_square}

/-- The basic segments lying in the interior of the unit square. -/
noncomputable def triangulation_interior_basic_segments (Δ : Finset Triangle) : Finset Segment :=
  {S ∈ triangulation_basic_segments Δ | open_hull S ⊆ open_hull unit_square}

/-- `is_triangulation Δ` states that `Δ` is a disjoint cover of the unit square by triangles. -/
noncomputable def is_triangulation (Δ : Finset Triangle) : Prop :=
  is_cover (closed_hull unit_square) (↑Δ : Set Triangle)

/-- Every vertex of a triangulation lies in the closed unit square. -/
lemma triangulation_points_subset_unit_square {Δ : Finset Triangle}
    (hCover : is_triangulation Δ) :
    (↑(triangulation_points Δ) : Set ℝ²) ⊆ closed_hull unit_square := by
  unfold triangulation_points
  simp only [Fin.isValue, coe_biUnion, mem_coe, coe_insert, coe_singleton,
    Set.iUnion_subset_iff]
  intro T hT z hz
  have hTsub : closed_hull T ⊆ closed_hull unit_square := by
    rw [hCover]
    intro w hw
    simp_all only [mem_coe, Fin.isValue, Set.mem_iUnion, exists_prop]
    exact ⟨T, hT, hw⟩
  have zT : ∃ i : Fin 3, z = T i := by
    simp_all only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hz with h | h | h <;> exact ⟨_, h⟩
  rcases zT with ⟨i, hi⟩
  exact hTsub (hi ▸ corner_in_closed_hull)

lemma segment_in_interior_aux {Δ : Finset Triangle} (hCover : is_triangulation Δ)
(non_degen : ∀ P ∈ Δ, det P ≠ 0) {L : Segment} (hL : L ∈ triangulation_basic_segments Δ) :
 ∃ T ∈ Δ, closed_hull L ⊆ closed_hull T := by
-- The strategy of this proof is to just verify all the conditions of seg_sub_side
-- in the first block of code we just unravel all the hypothesis and the then
-- every other block is just simply verifiing all hypothesis of seg_sub_side.
  unfold triangulation_basic_segments at hL
  unfold basic_avoiding_segment_set at hL
  simp only [mem_filter, mem_filter] at hL
  rcases hL with ⟨p, q⟩
  unfold avoiding_segment_set at p
  simp only [mem_filter] at p
  rcases p with ⟨a, b⟩
  unfold segment_set at a
  simp only [mem_image, mem_filter, Prod.exists] at a
  rcases a with ⟨c, d, e⟩
  rcases e with ⟨f, g⟩
  rcases f with ⟨m, n⟩
  simp only [product_eq_sprod, mem_product] at m
  have Lnonempty : ∃ (x : ℝ²), x ∈ open_hull L := by
    apply open_seg_nonempty
  rcases Lnonempty with ⟨x, hx⟩
  have convex : closed_hull L ⊆ closed_hull unit_square := by
    apply unit_square_is_convex
    · simp only [Fin.zero_eta, Fin.isValue]
      have L0 : to_segment c d 0 = L 0 := by
          rw [g]
      rw [to_segment] at L0
      rw [L0] at m
      have hL0 : L 0 ∈ triangulation_points Δ := m.1
      exact triangulation_points_subset_unit_square hCover hL0
    · simp only [Fin.mk_one, Fin.isValue]
      have L1 : to_segment c d 1 = L 1 := by
          rw [g]
      rw [to_segment] at L1
      rw [L1] at m
      have hL1 : L 1 ∈ triangulation_points Δ := m.2
      exact triangulation_points_subset_unit_square hCover hL1
  have xinTriangle : ∃ P ∈ Δ, x ∈ closed_hull P := by
    have xclosed : x ∈ closed_hull unit_square := by
      exact convex (open_sub_closed L hx)
    rw [hCover] at xclosed
    simp only [mem_coe, Set.mem_iUnion, exists_prop] at xclosed
    exact xclosed
  rcases xinTriangle with ⟨P, hP⟩
  have Pnondegen : det P ≠ 0 := by
    apply non_degen
    apply hP.1
  have xinBT : x ∈ boundary P := by
    unfold triangulation_avoiding_set at b
    simp only [Set.disjoint_iUnion_right] at b
    specialize b P
    rcases hP with ⟨P', hP''⟩
    apply b at P'
    have xinclosed : x ∈ closed_hull L := by
      exact open_sub_closed L hx
    have xnotinopen : x ∉ open_hull P := by
      by_contra hcontra
      tauto_set
    tauto_set
  have xinTside : ∃ i : Fin 3, x ∈ open_hull (Tside P i) := by
    have xinclosed : ∃ i : Fin 3, x ∈ closed_hull (Tside P i) := by
        rw [boundary_is_union_sides Pnondegen] at xinBT
        rcases xinBT with ⟨i, hi⟩
        simp only [Set.mem_range] at hi
        rcases hi with ⟨hi, hi'⟩
        rcases hi with ⟨j, hj⟩
        use j
        rw [hj]
        exact hi'
    rcases xinclosed with ⟨i, hi⟩
    use i
    by_contra hcontra
    have xboundTside : x ∈ boundary (Tside P i) := by
      tauto_set
    have enddiff : Tside P i 0 ≠ Tside P i 1 := by
      apply nondegen_triangle_imp_nondegen_side
      exact Pnondegen
    have xtriangulationpt: x ∈ triangulation_points Δ := by
      unfold triangulation_points
      simp only [Fin.isValue, mem_biUnion, mem_insert, mem_singleton]
      use P
      constructor
      · exact hP.1
      · rw [boundary_seg_set (enddiff)] at xboundTside
        by_cases iota : i = 0 ∨ i = 1
        · rcases iota with (hiota| hiota')
          · rw [hiota] at xboundTside
            right
            rw [Tside] at xboundTside
            simp only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff] at xboundTside
            apply xboundTside
          · rw [hiota'] at xboundTside
            rw [Tside] at xboundTside
            simp only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff] at xboundTside
            tauto
        · have h3 : i = 2 := by
            fin_cases i
            · simp only [Fin.zero_eta, Fin.isValue]
              tauto
            · simp only [Fin.mk_one, Fin.isValue]
              tauto
            · simp
          rw [h3] at xboundTside
          rw [Tside] at xboundTside
          simp only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff] at xboundTside
          tauto
    apply q at xtriangulationpt
    contradiction
  rcases xinTside with ⟨i, hi⟩
  have dis : open_hull P ∩ closed_hull L = ∅ := by
    by_contra hcontra
    have nonemp' : Set.Nonempty (open_hull P ∩ closed_hull L) := by
      exact Set.nonempty_iff_ne_empty.mpr hcontra
    have nonempt : ∃ z,  z ∈ open_hull P ∧ z ∈ closed_hull L := by
      exact nonemp'
    rcases nonempt with ⟨z, hz⟩
    unfold triangulation_avoiding_set  at b
    simp only [Set.disjoint_iUnion_right] at b
    specialize b P
    tauto_set
  have this : ∀ i : Fin 3, P i ∉ open_hull L := by
    by_contra hcontra
    simp only [not_forall, Decidable.not_not] at hcontra
    rcases hcontra with ⟨i, hi⟩
    have hP' : P i ∈ triangulation_points Δ := by
      unfold triangulation_points
      simp only [Fin.isValue, mem_biUnion, mem_insert, mem_singleton]
      use P
      constructor
      · exact hP.1
      by_cases iota : i = 0 ∨ i = 1
      · rcases iota with (hiota| hiota')
        · rw [hiota] at hi
          left
          rw [hiota]
        · right
          constructor
          · rw [hiota']
      · simp only [not_or] at iota
        have h3 : i = 2 := by
          fin_cases i
          · simp only [Fin.zero_eta, Fin.isValue]
            tauto
          · simp only [Fin.mk_one, Fin.isValue]
            tauto
          · simp
        right
        right
        rw [h3]
    apply q at hP'
    contradiction
  have fin : closed_hull L ⊆ closed_hull (Tside P i) := by
    exact seg_sub_side (non_degen P hP.1) hx hi dis this
  rcases hP with ⟨T, hT, hT'⟩
  use P
  constructor
  · exact T
  · have htside : closed_hull (Tside P i) ⊆ closed_hull P := by
      apply closed_side_sub'
    tauto_set

lemma segment_in_interior_or_boundary {Δ : Finset Triangle} (hCover : is_triangulation Δ)
(non_degen : ∀ P ∈ Δ, det P ≠ 0) {L : Segment} (hL : L ∈ triangulation_basic_segments Δ) :
  open_hull L ⊆ boundary unit_square ∨ open_hull L ⊆ open_hull unit_square := by
  have hclosed : closed_hull unit_square = boundary unit_square ∪ open_hull unit_square := by
    rw [← boundary_union_open_closed]
  have hT : ∃ T ∈ Δ, closed_hull L ⊆ closed_hull T := by
    apply segment_in_interior_aux hCover non_degen hL
  rcases hT with ⟨t, ht⟩
  have hLunitS : closed_hull L ⊆ closed_hull unit_square := by
    apply is_cover_sub at hCover
    simp only [mem_coe] at hCover
    specialize hCover t ht.1
    exact subset_trans ht.2 hCover
  by_cases h : open_hull L ⊆ boundary unit_square
  · left
    exact h
  have hLclosed : open_hull L ⊆ closed_hull unit_square := by
    exact subset_trans (open_sub_closed L) hLunitS
  right
  · have this : ∀ x, x ∈ open_hull L → x ∉ boundary unit_square  := by
      by_contra hcontra
      have hcontra' : ∃ x, x ∈ open_hull L ∩ boundary unit_square := by
        simp_all only [not_forall, Decidable.not_not, Set.mem_inter_iff]
        simp only [exists_prop] at hcontra
        exact hcontra
      have that : closed_hull L ⊆ boundary unit_square := by
        obtain ⟨x, hx⟩ := hcontra'
        apply line_in_boundary hLunitS hx
      have that' : open_hull L ⊆ boundary unit_square := by
        have hopen : open_hull L ⊆ closed_hull L := by
          apply open_sub_closed
        apply _root_.trans hopen that
      contradiction
    tauto_set


lemma triangulation_boundary_union (Δ : Finset Triangle) (hCover : is_triangulation Δ)
(non_degen : ∀ P ∈ Δ, det P ≠ 0) : triangulation_basic_segments Δ =
    triangulation_boundary_basic_segments Δ ∪ triangulation_interior_basic_segments Δ := by
  unfold triangulation_boundary_basic_segments triangulation_interior_basic_segments
  have hfilter : triangulation_basic_segments Δ =
      filter (fun S ↦ open_hull S ⊆ closed_hull unit_square) (triangulation_basic_segments Δ) := by
    ext L
    rw [mem_filter, iff_self_and]
    intro hL
    have hT : ∃ T ∈ Δ, closed_hull L ⊆ closed_hull T := by
     rcases segment_in_interior_aux hCover non_degen hL with ⟨T, hT⟩
     exact ⟨T, hT⟩
    obtain ⟨T, hT⟩ := hT
    apply is_cover_sub at hCover
    calc open_hull L ⊆ closed_hull L := open_sub_closed L
        _ ⊆ closed_hull T := hT.right
        _ ⊆ closed_hull unit_square := hCover T hT.left
  rw [hfilter, ← boundary_union_open_closed, ← filter_or]
  ext L
  repeat rw [mem_filter]
  simp only [iff_self_and, and_imp]
  intro hL hinc
  apply segment_in_interior_or_boundary hCover non_degen hL


lemma triangulation_boundary_intersection (Δ : Finset Triangle) :
    triangulation_boundary_basic_segments Δ ∩ triangulation_interior_basic_segments Δ = ∅ := by
  unfold triangulation_boundary_basic_segments triangulation_interior_basic_segments
  ext S
  simp only [mem_inter, mem_filter, notMem_empty, iff_false, not_and, and_imp]
  intro hS hOpen hS2
  by_contra h
  have h_elt : ∃ x, x ∈ open_hull S := by
    apply open_pol_nonempty
    linarith
  have h_open_nonempty : open_hull S ≠ ∅ := by
    obtain ⟨x, h_1⟩ := h_elt
    intro h
    simp_all only [Set.empty_subset, Set.mem_empty_iff_false]
  have h_open_empty : open_hull S ⊆ ∅ := by
    rw [← boundary_int_open_empty]
    tauto_set
  simp_all only [ne_eq, Set.subset_empty_iff]


/-- All basic segments of a triangulation, both boundary and interior. -/
noncomputable def triangulation_all_segments (Δ : Finset Triangle) : Finset Segment :=
  avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)

/-- The total number of purple segments in a triangulation. -/
noncomputable def purple_sum (Δ : Finset Triangle) : ℕ :=
  ∑ (S ∈ triangulation_boundary_basic_segments Δ), isPurple v S

/-- The total number of rainbow triangles in a triangulation. -/
noncomputable def rainbow_sum (Δ : Finset Triangle) : ℕ :=
  ∑ (T ∈ Δ), isRainbow v  T

/-- The finite set of rainbow triangles of a triangulation. -/
noncomputable def rainbow_triangles (Δ : Finset Triangle) : Finset Triangle :=
  {T ∈ Δ | isRainbow v T = 1}

-- Given a collection of segments X and a segment S, give all elements of X with open_hull contained
-- in open_hull S.

/-- The basic segments of a segment family contained in a given side. -/
noncomputable def basic_segment_segments (X : Finset Segment) (S : Segment) :=
  filter (fun L ↦ open_hull L ⊆ open_hull S) X

lemma segment_sum_splitting (A : Finset Segment) (AVOID : Set ℝ²) (X : Finset ℝ²)
    (hA : A ⊆ avoiding_segment_set X AVOID)
    (hDisj : ∀ S T, S ∈ A → T ∈ A → S ≠ T → open_hull S ∩ open_hull T = ∅)
    (f : Segment → ℕ) (hfTwoMod : two_mod_function f) (hSymm : symm_fun f) :
    (∑ S ∈ filter (fun S ↦ closed_hull S ⊆ (⋃ T ∈ A, closed_hull T))
      (basic_avoiding_segment_set X AVOID), f S) % 4
    = (2 * ∑ T ∈ A, f T) % 4 := by
  have h_disj : (↑A : Set Segment).PairwiseDisjoint
    (fun T ↦ (filter (fun S ↦ closed_hull S ⊆ closed_hull T) (basic_avoiding_segment_set X AVOID)))
      := by
    intro S hS T hT hST Y hY h
    have hDisj2 := hDisj S T hS hT hST
    simp_all only [mem_coe, ne_eq, le_eq_subset, bot_eq_empty, subset_empty]
    have h_nontriv : ∀ L ∈ Y, L 0 ≠ L 1 := by
      intro L hL
      apply @segment_set_vertex_distinct X L
      have hY_segment_set : Y ⊆ segment_set X := by
        calc Y ⊆ filter (fun S_1 ↦ closed_hull S_1 ⊆ closed_hull S)
              (basic_avoiding_segment_set X AVOID) := hY
             _ ⊆ basic_avoiding_segment_set X AVOID := by exact filter_subset _ _
             _ ⊆ avoiding_segment_set X AVOID := by exact filter_subset _ _
             _ ⊆ segment_set X := by exact filter_subset _ _
      exact hY_segment_set hL
    have hLS : ∀ L ∈ Y, open_hull L ⊆ open_hull S := by
      intro L hL
      apply open_segment_sub'
      · have h2 := hY hL
        rw [mem_filter] at h2
        exact h2.right
      · exact h_nontriv L hL
    have hLT : ∀ L ∈ Y, open_hull L ⊆ open_hull T := by
      intro L hL
      apply open_segment_sub'
      · have h2 := h hL
        rw [mem_filter] at h2
        exact h2.right
      · exact h_nontriv L hL
    have hST2 := hDisj S T hS hT
    ext L
    constructor
    · intro hL
      have hNonEmpty : open_hull L ≠ ∅ := by
        simp_all only [ne_eq]
        obtain ⟨w, h_1⟩ := open_pol_nonempty (by linarith) L
        intro a
        simp_all only [Set.mem_empty_iff_false]
      have hEmpty : open_hull L ⊆ ∅ := by
        calc open_hull L ⊆ open_hull S ∩ open_hull T := by
                exact Set.subset_inter_iff.mpr ⟨(hLS L hL), (hLT L hL)⟩
          _ = ∅ := by exact hDisj S T hS hT hST
      simp_all only [ne_eq, Set.subset_empty_iff]
    · tauto
  have h_eq : filter (fun S ↦ closed_hull S ⊆ (⋃ T ∈ A, closed_hull T))
      (basic_avoiding_segment_set X AVOID) =
      Finset.disjiUnion A
        (fun T ↦ (filter (fun S ↦ closed_hull S ⊆ closed_hull T)
          (basic_avoiding_segment_set X AVOID)))
        h_disj
      := by
    ext L
    rw [mem_filter, Finset.mem_disjiUnion]
    constructor
    · intro hL
      simp_all only [mem_filter, true_and]
      apply closed_segment_sub_union_segment
          (segment_set_vertex_distinct (basic_avoiding_segment_set_sub hL.1)) hL.2
      intro S hSA
      rw [Set.disjoint_right]
      intro y hyb hopen
      have hyX := segment_set_boundary (X := X) ?_ hyb
      · have hLAvoid := hL.1
        simp only [basic_avoiding_segment_set, mem_filter] at hLAvoid
        exact hLAvoid.2 y hyX hopen
      · refine avoiding_segment_set_sub (A := AVOID) (hA ?_)
        simp_all only [ne_eq]
    · intro hL
      obtain ⟨S, hS⟩ := hL
      constructor
      · simp_all only [mem_filter]
      · rw [mem_filter] at hS
        have h : closed_hull S ⊆ ⋃ T ∈ A, closed_hull T := by
          refine Set.subset_biUnion_of_mem ?_
          exact hS.1
        tauto_set
  rw [h_eq]
  rw [Finset.sum_disjiUnion A
    (fun T ↦ (filter (fun S ↦ closed_hull S ⊆ closed_hull T) (basic_avoiding_segment_set X AVOID)))
    h_disj]
  rw [← ZMod.natCast_eq_natCast_iff']
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, mul_sum]
  refine sum_congr rfl ?_
  intro T hT
  have bla := sum_two_mod_fun_seg (hA hT) hfTwoMod hSymm
  rw [← ZMod.natCast_eq_natCast_iff'] at bla
  convert bla <;> simp


-- Shorthand for defining an element of ℝ²
/-- Auxiliary index function used in the square boundary decomposition. -/
noncomputable def p (x y : ℝ) : ℝ² := !₂[x, y]

-- def bottom : Segment := fun | 0 => p 0 0 | 1 => p 1 0
-- def top : Segment := fun | 0 => p 0 1 | 1 => p 1 1
-- def left : Segment := fun | 0 => p 0 0 | 1 => p 0 1
-- def right : Segment := fun | 0 => p 1 0 | 1 => p 1 1

/-- The basic boundary segments of the unit square lying on side `i`. -/
noncomputable def square_boundary_basic (Δ : Finset Triangle) : Fin 4 → Finset Segment :=
  fun i ↦ filter (fun S ↦ open_hull S ⊆ open_hull (square_boundary_big i))
    (triangulation_boundary_basic_segments Δ)

lemma unit_square_boundary_decomposition (Δ : Finset Triangle) (hCovering : is_triangulation Δ) :
    triangulation_boundary_basic_segments Δ =
    @Finset.biUnion (Fin 4) Segment _ ⊤ (square_boundary_basic Δ)
    := by
  ext S
  constructor
  · intro hS
    simp only [triangulation_boundary_basic_segments, mem_filter] at hS
    have ⟨i, hi⟩ := open_hull_segment_in_boundary (S := S) hS.2 ?_
    · rw [mem_biUnion]
      use i, by simp only [top_eq_univ, mem_univ]
      simp only [square_boundary_basic, mem_filter, triangulation_boundary_basic_segments]
      refine ⟨hS,?_⟩
      apply open_segment_sub' hi
      simp only [triangulation_basic_segments, basic_avoiding_segment_set, avoiding_segment_set,
        mem_filter] at hS
      exact segment_set_vertex_distinct hS.1.1.1
    · apply closed_hull_convex
      intro i
      simp only [triangulation_basic_segments, basic_avoiding_segment_set, avoiding_segment_set,
        mem_filter, segment_set] at hS
      have this := hS.1.1.1
      simp only [ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product, Prod.exists] at this
      have ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, hS⟩ := this
      simp only [is_triangulation, is_cover, SetLike.mem_coe] at hCovering
      have hSub : (↑(triangulation_points Δ) : Set ℝ²) ⊆ (closed_hull unit_square) := by
        rw [hCovering]
        intro x hx
        simp only [triangulation_points, Fin.isValue, coe_biUnion, mem_coe, coe_insert,
          coe_singleton, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff,
          exists_prop] at hx
        have ⟨T,hT, hp⟩ := hx
        rw [Set.mem_iUnion₂]
        use T, hT
        rcases hp with hp | hp
        · rw [hp]
          exact corner_in_closed_hull
        · obtain hp | hp := hp <;> (rw [hp]; exact corner_in_closed_hull)
      rw [←hS]
      fin_cases i <;> (simp only [to_segment])
      · exact hSub ha
      · exact hSub hb
  · intro hS
    simp only [top_eq_univ, mem_biUnion, mem_univ, square_boundary_basic, mem_filter, true_and,
      exists_and_left] at hS
    have ⟨h, ⟨i, hi⟩⟩ := hS
    simp only [triangulation_boundary_basic_segments, mem_filter]
    refine ⟨?_,?_⟩
    · simp only [triangulation_boundary_basic_segments, mem_filter] at h
      exact h.1
    · trans open_hull (square_boundary_big i)
      · exact hi
      · trans closed_hull (square_boundary_big i)
        · exact open_sub_closed _
        · exact square_boundary_segments_in_boundary i




lemma unit_square_cover_segment_set
    {S : Finset Triangle}
    (hCover : is_cover (closed_hull unit_square) (↑S : Set Triangle)) :
    ∀ {i}, square_boundary_big i ∈ segment_set (triangulation_points S) := by
  intro i
  rw [segment_set]
  simp only [ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product, Prod.exists]
  use square_boundary_big i 0, square_boundary_big i 1
  simp only [Fin.isValue, segment_rfl, and_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · have ⟨k,hk⟩ := square_boundary_big_corners i 0
    rw [hk]
    have ⟨T,hT,⟨j,Tj⟩ ⟩  := cover_imples_corner_in_triangle hCover k
    rw [Tj]
    exact triangulation_points_mem hT _
  · have ⟨k,hk⟩ := square_boundary_big_corners i 1
    rw [hk]
    have ⟨T,hT,⟨j,Tj⟩ ⟩  := cover_imples_corner_in_triangle hCover k
    rw [Tj]
    exact triangulation_points_mem hT _
  · exact square_boundary_sides_nonDegen i

lemma unit_square_boundary_intersections (i j : Fin 4) (h_neq : i ≠ j) :
    open_hull (square_boundary_big i) ∩ open_hull (square_boundary_big j) = ∅ := by
  ext x
  have hh2help : 1 < 2 := by norm_num
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1
  unfold square_boundary_big at *
  rintro  ⟨ aj,h2j , h3j⟩
  rcases h1 with ⟨ ai,h2i , h3i⟩
  rcases h2j with ⟨h4j, h5j⟩
  rcases h2i with ⟨h4i, h5i⟩
  simp only at h3j h3i
  have h4i1:= h4i 1; have h4i2 := h4i 2
  have h3j0 := congrArg (· 0) h3j; have h3j1 := congrArg (· 1) h3j
  have h3i0 := congrArg (· 0) h3i; have h3i1 := congrArg (· 1) h3i
  clear h4i h3i h3j hh2help
  fin_cases i <;> fin_cases j <;> simp at * <;> linarith


lemma purple_computation0 (i : Fin 4) : i ≠ 0 → isPurple v (square_boundary_big i) = 0 := by
  have hR : coloring v !₂[0, 0] = Color.Red := red00 v
  have hB1 : coloring v !₂[1, 0] = Color.Blue := blue10 v
  have hB2 : coloring v !₂[1, 1] = Color.Blue := blue11 v
  have hG : coloring v !₂[0, 1] = Color.Green := green01 v
  unfold isPurple square_boundary_big
  intro hi
  fin_cases i
  · tauto
  · simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_and]
    simp_all [LeanPool.Monsky.v]
  · simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_and]
    simp_all [LeanPool.Monsky.v]
  · simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_and]
    simp_all [LeanPool.Monsky.v]

lemma purple_computation1 : isPurple v (square_boundary_big 0) = 1 := by
  unfold isPurple square_boundary_big
  simp only [ite_eq_left_iff, not_or, not_and, zero_ne_one, imp_false, Classical.not_imp,
    Decidable.not_not]
  have hR : coloring v (p 0 0) = Color.Red := by
    rw [← red00 v]
    rfl
  have hB : coloring v (p 1 0) = Color.Blue := by
    rw [← blue10 v]
    rfl
  tauto

lemma open_triangle_in_open_square {Δ : Finset Triangle} {T : Triangle} (hT : T ∈ Δ)
    (non_degen : det T ≠ 0) (hCovering : is_triangulation Δ) :
    open_hull T ⊆ open_hull unit_square := by
  by_contra h
  have h_inc : open_hull T ⊆ closed_hull unit_square := by
      unfold is_triangulation at hCovering
      exact subset_trans (open_sub_closed T) (@is_cover_sub _ Δ _ (id hCovering) T hT)
  have hp : ∃ p : ℝ², p ∈ open_hull T ∧ p ∈ boundary unit_square := by
    obtain ⟨p, hp⟩ := Set.not_subset.mp h
    use p
    refine ⟨hp.left, ?_⟩
    unfold boundary
    rw [Set.mem_diff]
    exact ⟨by tauto, hp.right⟩
  obtain ⟨p, hp⟩ := hp
  obtain ⟨σ, hσ⟩ := (boundary_leave_dir hp.2)
  obtain ⟨ε, hε⟩ := (@triangle_open_hull_open _ non_degen _ (σ • (!₂[1, 1] : ℝ²)) hp.1)
  have h1 : p + ε • σ • (!₂[1, 1] : ℝ²) ∉ closed_hull unit_square := by
    have hrw : p + ε • σ • (!₂[1, 1] : ℝ²) = p + (σ * ε) • (!₂[1, 1] : ℝ²) := by
      module
    rw [hrw]
    exact (hσ.right ε hε.left)
  tauto


theorem segment_sum_odd (Δ : Finset Triangle) (hCovering : is_triangulation Δ)
    (non_degen : ∀ P ∈ Δ, det P ≠ 0) :
    purple_sum v Δ % 4 = 2 := by
  -- Strategy: show that triangulation_boundary_basic_segments Δ is the disjoint union over the
  -- segments contained in the four sides of the squares. Then for each side, use that the purple
  -- sum mod 4 is just 2 times the value of IsPurple of the whole segment.
  unfold purple_sum
  have h : ∑ S ∈ triangulation_boundary_basic_segments Δ, isPurple v S =
      ∑ S ∈ filter (fun S ↦ closed_hull S ⊆ (⋃ T ∈ square_boundary_big_set, closed_hull T))
        (basic_avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)),
        isPurple v S := by
    rw [sum_congr]
    · rw [unit_square_boundary_decomposition Δ hCovering]
      unfold square_boundary_basic square_boundary_big_set triangulation_boundary_basic_segments
      unfold triangulation_basic_segments
      simp_all only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and, Set.iUnion_exists]
      ext S
      constructor
      · intro hS
        simp_all only [mem_biUnion, mem_univ, mem_filter, true_and, exists_and_left]
        obtain ⟨j, hj⟩ := hS.right
        have h_closed : closed_hull S ⊆ closed_hull (square_boundary_big j) := by
          exact open_sub_closed_sub _ _ hj
        suffices h2 : closed_hull (square_boundary_big j) ⊆
          ⋃ T, ⋃ i, ⋃ (_ : T = square_boundary_big i), closed_hull (square_boundary_big i)
        · tauto_set
        · intro x hx
          simp only [Set.mem_iUnion, exists_prop]
          use square_boundary_big j
          use j
      · intro hS
        simp_all only [mem_filter, mem_biUnion, mem_univ, true_and, exists_and_left]
        have hClosedSinBoundary : closed_hull S ⊆ boundary unit_square := by
          have hBoundary : ∀ i : Fin 4,
              closed_hull (square_boundary_big i) ⊆ boundary unit_square := by
              exact square_boundary_segments_in_boundary
          have hUnion : ⋃ T, ⋃ i, ⋃ (_ : T = square_boundary_big i),
              closed_hull (square_boundary_big i)
              ⊆ boundary unit_square := by
            simp only [Set.iUnion_subset_iff]
            intro T i hT
            exact hBoundary i
          calc closed_hull S ⊆ ⋃ T, ⋃ i, ⋃ (_ : T = square_boundary_big i),
                closed_hull (square_boundary_big i) := by exact hS.2
                           _ ⊆ boundary unit_square := by exact hUnion
        have hopenSinBoundary : open_hull S ⊆ boundary unit_square := by
          have hInc : open_hull S ⊆ closed_hull S := open_sub_closed S
          suffices h : closed_hull S ⊆ boundary unit_square
          · tauto_set
          · exact hClosedSinBoundary
        refine ⟨hopenSinBoundary, ?_⟩
        apply unit_square_is_convex_open
        · exact hClosedSinBoundary
        · unfold basic_avoiding_segment_set avoiding_segment_set segment_set at hS
          simp_all only [ne_eq, product_eq_sprod, mem_filter, mem_image, mem_product, Prod.exists,
            Fin.isValue]
          obtain ⟨w, h⟩ := hS.1.1.1
          obtain ⟨w_1, h⟩ := h
          obtain ⟨left, right_3⟩ := h
          obtain ⟨left, right_4⟩ := left
          obtain ⟨left, right_5⟩ := left
          subst right_3
          exact right_4
    · intro _ _
      rfl
  rw [h]
  have h1 : square_boundary_big_set ⊆
      avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ) := by
    unfold avoiding_segment_set
    have h_triangle_avoiding_set : (triangulation_avoiding_set Δ) ⊆ open_hull unit_square := by
      unfold triangulation_avoiding_set
      simp only [Set.iUnion_subset_iff]
      intro T hT
      exact (open_triangle_in_open_square hT (non_degen T hT) hCovering)
    have h_square_boundary : ∀ L ∈ square_boundary_big_set,
        closed_hull L ⊆ boundary unit_square := by
      intro L hL
      unfold square_boundary_big_set at hL
      simp only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and] at hL
      obtain ⟨i, hi⟩ := hL
      rw [hi]
      exact square_boundary_segments_in_boundary i
    intro S hS
    rw [mem_filter]
    constructor
    · -- I think this needs that the triangulation points of a covering must include
      -- the corners of the square.
      rw [square_boundary_big_set, mem_biUnion] at hS
      have ⟨_, _, hST⟩ := hS
      rw [mem_singleton] at hST
      rw [hST]
      exact unit_square_cover_segment_set hCovering
    · suffices h_disj : Disjoint (boundary unit_square) (open_hull unit_square)
      · tauto_set
      · unfold boundary
        tauto_set
  have h2 : ∀ S L, S ∈ (square_boundary_big_set) → L ∈ (square_boundary_big_set) → S ≠ L →
      open_hull S ∩ open_hull L = ∅ := by
    unfold square_boundary_big_set
    intro S L hS hL hSL
    simp_all only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and]
    obtain ⟨i, hi⟩ := hS
    obtain ⟨j, hj⟩ := hL
    rw [hi, hj]
    have hij : i ≠ j := by
      by_contra h_contra
      rw [hi, hj, h_contra] at hSL
      tauto
    exact unit_square_boundary_intersections i j hij
  rw [segment_sum_splitting square_boundary_big_set (triangulation_avoiding_set Δ)
    (triangulation_points Δ) h1 h2 (isPurple v) (isPurple_two_mod_function v)
    (isPurple_symm_function v)]
  unfold square_boundary_big_set
  have hTop : (⊤ : Finset (Fin 4)) = {0, 1, 2, 3} := by rfl
  have hDisjSum : (⊤ : Finset (Fin 4)).biUnion (fun i ↦ {square_boundary_big i}) =
      Finset.disjiUnion (⊤ : Finset (Fin 4)) (fun i ↦ {square_boundary_big i}) ?_ := by
    refine Eq.symm (disjiUnion_eq_biUnion ⊤ (fun i ↦ {square_boundary_big i}) ?_)
    intro i _ j _ hij
    simp only [disjoint_singleton_right, mem_singleton]
    intro heq
    exact hij.symm (square_boundary_big_injective heq)
  · intro i _ j _ hij
    simp only [disjoint_singleton_right, mem_singleton]
    intro heq
    exact hij.symm (square_boundary_big_injective heq)
  rw [hDisjSum, sum_disjiUnion]
  simp only [top_eq_univ, sum_singleton]
  simp_all only [ne_eq, top_eq_univ, Fin.isValue, biUnion_insert, singleton_biUnion,
    disjiUnion_eq_biUnion, mem_insert, zero_ne_one, Fin.reduceEq, mem_singleton, or_self,
    not_false_eq_true, sum_insert, sum_singleton]
  rw [purple_computation1]
  repeat rw [purple_computation0]
  · ring
  all_goals decide


theorem segment_sum_rainbow_triangle (Δ : Finset Triangle) :
    rainbow_sum v Δ = (rainbow_triangles v Δ).card := by
  unfold rainbow_sum rainbow_triangles isRainbow
  simp only [sum_boole, Nat.cast_id, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]


/-- The basic segments of a triangulation lying on the boundary of triangle `T`. -/
noncomputable def triangle_basic_boundary (Δ : Finset Triangle) (T : Triangle) :=
    {S ∈ triangulation_basic_segments Δ | closed_hull S ⊆ boundary T}

lemma triangle_edges_disjoint (T : Triangle) (i j : Fin 3) (h : i ≠ j) (hdet : det T ≠ 0) :
    Disjoint (open_hull (Tside T i))  (open_hull (Tside T j)) := by
  by_contra h1
  rw [@Set.not_disjoint_iff] at h1
  rcases h1 with ⟨x ,hi,hj ⟩
  have hx  := closed_side_sub (open_sub_closed _ hi)
  rw[←  mem_open_side hdet hx i] at hi
  rw[←  mem_open_side hdet hx j] at hj
  exact Ne.symm (ne_of_lt (hj.2 i h)) hi.1

lemma triangle_boundary_decomposition {Δ : Finset Triangle} {T : Triangle} (hdet : det T ≠ 0)
    (h : T ∈ Δ) :
    triangle_basic_boundary Δ T =
    @Finset.biUnion (Fin 3) Segment _ ⊤
      (fun i ↦ (basic_segment_segments (triangle_basic_boundary Δ T) (Tside T i)))
    := by
    ext S
    constructor
    · intro hS
      unfold triangle_basic_boundary at hS
      rw [mem_filter] at hS
      rcases hS with ⟨α, hα ⟩
      rw [boundary_is_union_sides hdet] at hα
      have TsideS : ∃ i : Fin 3, closed_hull S ⊆ closed_hull (Tside T i) := by
        unfold triangulation_basic_segments at α
        unfold basic_avoiding_segment_set at α
        rw [mem_filter] at α
        unfold avoiding_segment_set at α
        rw [mem_filter] at α
        rcases α with ⟨δ, hδ⟩
        rcases δ with ⟨η, hη⟩
        unfold triangulation_avoiding_set at hη
        have xopoenhullS : ∃ x, x ∈ open_hull S := by
          apply open_pol_nonempty
          linarith
        rcases xopoenhullS with ⟨x, hx⟩
        have xclosedhullS : x ∈ closed_hull S := by
          exact open_sub_closed S hx
        have xinboundaryT : x ∈ boundary T := by
          rw [boundary_is_union_sides hdet]
          apply hα at xclosedhullS
          exact xclosedhullS
        have xinTsideopen: ∃ i : Fin 3, x ∈ open_hull (Tside T i) := by
          apply el_in_boundary_imp_side
          · apply hdet
          · apply xinboundaryT
          · by_contra hcontra
            simp only [ne_eq, not_forall, Decidable.not_not] at hcontra
            rcases hcontra with ⟨i, hi⟩
            have hcontra' : x ∈ triangulation_points Δ := by
              unfold triangulation_points
              rw [hi]
              simp only [Fin.isValue, mem_biUnion, mem_insert, mem_singleton]
              use T
              constructor
              · exact h
              · by_cases hfin : i = 0 ∨ i = 1
                · rcases hfin with (hfin | hfin)
                  · left
                    rw [hfin]
                  · right
                    left
                    rw [hfin]
                · have i2: i = 2 := by
                    fin_cases i
                    · simp at hfin
                    · simp at hfin
                    · simp at hfin
                      simp
                  right
                  right
                  rw [i2]
            apply hδ at hcontra'
            contradiction
        rcases xinTsideopen with ⟨i, hi⟩
        use i
        apply seg_sub_side
        · apply hdet
        · apply hx
        · apply hi
        · by_contra hcontra
          have nonemp' : Set.Nonempty (open_hull T ∩ closed_hull S) := by
            exact Set.nonempty_iff_ne_empty.mpr hcontra
          have nonempt : ∃ z,  z ∈ open_hull T ∧ z ∈ closed_hull S := by
            exact nonemp'
          rcases nonempt with ⟨z, hz⟩
          simp only [Set.disjoint_iUnion_right] at hη
          specialize hη T
          tauto_set
        · by_contra hcontra
          simp only [not_forall, Decidable.not_not] at hcontra
          rcases hcontra with ⟨j, hj⟩
          have tj : T j ∈ triangulation_points Δ := by
            unfold triangulation_points
            simp only [Fin.isValue, mem_biUnion, mem_insert, mem_singleton]
            use T
            constructor
            · exact h
            · by_cases hfin : j = 0 ∨ j = 1
              · rcases hfin with (hfin | hfin)
                · left
                  rw [hfin]
                · right
                  left
                  rw [hfin]
              · have j2: j = 2 := by
                  fin_cases j
                  · simp at hfin
                  · simp at hfin
                  · simp at hfin
                    simp
                right
                right
                rw [j2]
          apply hδ at tj
          contradiction
      rcases TsideS with ⟨i, hi ⟩
      simp_all only [ne_eq, top_eq_univ, mem_biUnion, mem_univ, true_and]
      use i
      unfold basic_segment_segments
      rw [mem_filter]
      constructor
      · unfold triangle_basic_boundary
        rw [mem_filter]
        constructor
        · apply α
        · have this : closed_hull (Tside T i)  ⊆ boundary T := by
            apply side_in_boundary hdet
          tauto_set
      · apply open_segment_sub'
        · apply hi
        · unfold triangulation_basic_segments at α
          unfold basic_avoiding_segment_set at α
          rw [mem_filter] at α
          unfold avoiding_segment_set at α
          rw [mem_filter] at α
          rcases α with ⟨β, hβ⟩
          rcases β with ⟨γ, hγ ⟩
          apply segment_set_vertex_distinct
          apply γ
    · intro hS
      simp_all only [ne_eq, top_eq_univ, mem_biUnion, mem_univ, true_and]
      rcases hS with ⟨a, ha⟩
      unfold basic_segment_segments at ha
      rw [mem_filter] at ha
      apply ha.1


/-- The three sides of a triangle `T`, as a set of segments. -/
noncomputable def triangle_boundary (T : Triangle) := Finset.biUnion ⊤ (fun i ↦ {Tside T i})

lemma color_trichotomy (c : Color) : c = Color.Red ∨ c = Color.Blue ∨ c = Color.Green := by
  induction c <;> simp

lemma different_points (T : Triangle) (h_det : det T ≠ 0) (i j : Fin 3) (hneq : i ≠ j) :
    T i ≠ T j := by
  by_contra hcontra
  have hk : ∃ k : Fin 3, i ≠ k  ∧  j ≠ k := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, ne_eq]
      by_cases hj : j = 1
      · subst hj
        use 2
        simp only [Fin.isValue, Fin.reduceEq, not_false_eq_true, and_self]
      · use 1
        simp only [Fin.isValue, zero_ne_one, not_false_eq_true, true_and]
        use hj
    · simp only [Fin.mk_one, Fin.isValue, ne_eq]
      by_cases hj : j = 0
      · subst hj
        use 2
        simp only [Fin.isValue, Fin.reduceEq, not_false_eq_true, and_self]
      · use 0
        simp only [Fin.isValue, one_ne_zero, not_false_eq_true, true_and]
        use hj
    · simp only [Fin.reduceFinMk, ne_eq, Fin.isValue]
      by_cases hj : j = 0
      · subst hj
        use 1
        simp only [Fin.isValue, Fin.reduceEq, not_false_eq_true, and_self]
      · use 0
        simp only [Fin.isValue, Fin.reduceEq, not_false_eq_true, true_and]
        use hj
  rcases hk with ⟨k, hik, hjk⟩
  have hT : ∃ b, σ b = (fun | 0 =>  i | 1 =>  j | 2 => k) := by
    exact fun_in_bijections hneq hik hjk
  rcases hT with ⟨b, hb⟩
  have det0 : det T = 0 := by
    rw [det_perm b]
    have T' : T ∘ σ b = fun | 0 => T i | 1 => T j | 2 => T k := by
      simp_all only [ne_eq]
      ext x i_1 : 2
      simp_all only [Function.comp_apply]
      split
      next x => simp_all only
      next x => simp_all only
      next x => simp_all only
    have det0' : det (fun | 0 => T i | 1 => T j | 2 => T k) = 0 := by
      rw [hcontra]
      exact det_triv_triangle (T j) (T k)
    rw [T', det0']
    linarith
  contradiction


-- A fully computable version of `isPurple`, taking the two endpoint colours.
-- We use `Bool` operators so that `decide` reduces even though the ambient
-- `Classical.propDecidable` instance is active in this file.
/-- The number (`0`, `1` or `2`) of purple edges among the edges with two given colors. -/
def purpleB (a b : Color) : ℕ :=
  if ((a == Color.Red && b == Color.Blue) || (a == Color.Blue && b == Color.Red)) then 1 else 0

-- A fully computable version of `isRainbow`, taking the three vertex colours:
-- a triangle is rainbow exactly when its three vertices carry distinct colours.
/-- Indicator of whether the three given colors form a rainbow triangle. -/
def rainbowB (a b c : Color) : ℕ :=
  if (a == b || b == c || a == c) then 0 else 1

-- Surjectivity of a `Fin 3 → Color` map is decided by pairwise distinctness.
-- This isolates a small finite check from the main proof.
lemma surj_iff_distinct (c0 c1 c2 : Color) :
    Function.Surjective (![c0, c1, c2]) ↔ (c0 ≠ c1 ∧ c1 ≠ c2 ∧ c0 ≠ c2) := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_⟩ <;>
    · rintro he
      have : ¬ Function.Surjective (![c0, c1, c2]) := by revert he; revert c0 c1 c2; decide
      exact this hs
  · rintro ⟨h01, h12, h02⟩; revert h01 h12 h02; revert c0 c1 c2; decide

-- `isPurple` expressed through the endpoint colours.
lemma isPurple_eq_colors (S : Segment) :
    isPurple v S = purpleB (coloring v (S 0)) (coloring v (S 1)) := by
  unfold isPurple purpleB
  rcases (coloring v (S 0)) <;> rcases (coloring v (S 1)) <;> decide +revert

-- `isRainbow` expressed through the three vertex colours.
lemma isRainbow_eq_colors (T : Triangle) :
    isRainbow v T = rainbowB (coloring v (T 0)) (coloring v (T 1)) (coloring v (T 2)) := by
  unfold isRainbow
  have hcomp : (coloring v ∘ T) = ![coloring v (T 0), coloring v (T 1), coloring v (T 2)] := by
    funext i; fin_cases i <;> rfl
  rw [hcomp]
  by_cases hs : Function.Surjective (![coloring v (T 0), coloring v (T 1), coloring v (T 2)])
  · rw [if_pos hs]
    obtain ⟨h01, h12, h02⟩ := (surj_iff_distinct _ _ _).mp hs
    unfold rainbowB; revert h01 h12 h02
    generalize coloring v (T 0) = a; generalize coloring v (T 1) = b
    generalize coloring v (T 2) = c
    revert a b c; decide
  · rw [if_neg hs, surj_iff_distinct] at *
    unfold rainbowB; revert hs
    generalize coloring v (T 0) = a; generalize coloring v (T 1) = b
    generalize coloring v (T 2) = c
    revert a b c; decide

-- The core counting identity, stated purely on the three vertex colours. It is a
-- finite check over the 27 colourings, cheap under the default heartbeat budget.
lemma rainbow_purple_color_identity (c0 c1 c2 : Color) :
    2 * rainbowB c0 c1 c2 % 4 = 2 * (purpleB c1 c2 + purpleB c2 c0 + purpleB c0 c1) % 4 := by
  decide +revert

lemma rainbow_triangle_purple_sum {Δ : Finset Triangle}
    (non_degen : ∀ P ∈ Δ, det P ≠ 0)
    (hDisjointCover : is_disjoint_cover (closed_hull unit_square) (↑Δ : Set Triangle))
    : ∀ T ∈ Δ,
    2 * isRainbow v T % 4 = (∑ (S ∈ triangle_basic_boundary Δ T), isPurple v S) % 4 := by
  intro T hT
  have h : triangle_basic_boundary Δ T =
      filter (fun S ↦ closed_hull S ⊆ (⋃ L ∈ triangle_boundary T, closed_hull L))
        (basic_avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ)) := by
    rw [triangle_boundary_decomposition (non_degen T hT) hT]
    unfold triangle_boundary
    ext S
    constructor
    · intro h
      rw [mem_filter]
      rw [mem_biUnion] at h
      obtain ⟨i, hi⟩ := h
      constructor
      · unfold basic_segment_segments at hi
        unfold triangle_basic_boundary at hi
        unfold triangulation_basic_segments at hi
        simp_all only [ne_eq, top_eq_univ, mem_univ, mem_filter, true_and]
      · simp_all only [ne_eq, top_eq_univ, mem_univ, true_and, mem_biUnion, mem_singleton,
          Set.iUnion_exists]
        unfold basic_segment_segments at hi
        rw [mem_filter] at hi
        have h1 : closed_hull S ⊆ closed_hull (Tside T i) :=
          (open_sub_closed_sub S (Tside T i) hi.right)
        have h2 : closed_hull (Tside T i) ⊆
            ⋃ L, ⋃ i, ⋃ (_ : L = Tside T i), closed_hull (Tside T i) := by
          apply (Set.subset_iUnion_of_subset (Tside T i))
          apply (Set.subset_iUnion_of_subset i)
          simp only [Set.iUnion_true, subset_refl]
        calc closed_hull S ⊆ closed_hull (Tside T i) := by exact h1
                         _ ⊆ ⋃ L, ⋃ i, ⋃ (_ : L = Tside T i), closed_hull (Tside T i) := by exact h2
    · simp only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and, Set.iUnion_exists,
      mem_filter, and_imp]
      intro hS1 hS2
      unfold basic_segment_segments
      simp only [mem_filter, exists_and_left]
      have hBoundaryIncl : closed_hull S ⊆ boundary T := by
        have hInc : ⋃ L, ⋃ i, ⋃ (_ : L = Tside T i), closed_hull L ⊆ boundary T := by
          simp only [Set.iUnion_subset_iff, forall_eq_apply_imp_iff]
          intro i
          exact (side_in_boundary (non_degen T hT) i)
        tauto_set
      constructor
      · unfold triangle_basic_boundary triangulation_basic_segments
        rw [mem_filter]
        refine ⟨hS1, ?_⟩
        exact hBoundaryIncl
      · obtain ⟨i, hi⟩ := segment_in_boundary_imp_in_side (non_degen T hT) hBoundaryIncl
        use i
        apply open_segment_sub' hi
        unfold basic_avoiding_segment_set avoiding_segment_set segment_set at hS1
        simp_all only [ne_eq, product_eq_sprod, mem_filter, mem_image, mem_product, Prod.exists,
          Fin.isValue]
        obtain ⟨left, right⟩ := hS1
        obtain ⟨left, right_1⟩ := left
        obtain ⟨w, h⟩ := left
        obtain ⟨w_1, h⟩ := h
        obtain ⟨left, right_2⟩ := h
        obtain ⟨left, right_3⟩ := left
        obtain ⟨left, right_4⟩ := left
        subst right_2
        exact right_3
  have h1 : (triangle_boundary T) ⊆
      avoiding_segment_set (triangulation_points Δ) (triangulation_avoiding_set Δ) := by
    unfold triangle_boundary avoiding_segment_set
    simp only [top_eq_univ, biUnion_subset_iff_forall_subset, mem_univ, singleton_subset_iff,
      mem_filter, forall_const]
    intro i
    constructor
    · unfold segment_set
      simp only [product_eq_sprod, mem_image, mem_filter, mem_product, Prod.exists]
      use (Tside T i) 0, (Tside T i 1)
      simp only [Fin.isValue, segment_rfl, and_true]
      unfold triangulation_points
      constructor
      · simp only [Fin.isValue, mem_biUnion, mem_insert, mem_singleton]
        constructor
        · use T
          refine ⟨hT, ?_⟩
          unfold Tside
          fin_cases i
          all_goals try (simp only [Fin.isValue, true_or, or_true])
        · use T
          refine ⟨hT, ?_⟩
          unfold Tside
          fin_cases i
          all_goals try (simp only [Fin.isValue, true_or, or_true])
      · exact (nondegen_triangle_imp_nondegen_side i (non_degen T hT))
    · unfold triangulation_avoiding_set
      simp only [Set.disjoint_iUnion_right]
      intro T' hT'
      by_cases hTT' : T = T'
      · rw [hTT']
        exact Set.disjoint_of_subset (side_in_boundary (non_degen T' hT') _) (fun _ a ↦ a)
          boundary_open_disjoint
      · have this := disjoint_opens_implies_disjoint_open_closed (T₁ := T) (T₂ := T') ?_
          (non_degen T' hT')
        · exact Set.disjoint_of_subset closed_side_sub' (fun ⦃a⦄ a ↦ a) this
        · exact hDisjointCover.2 _ hT _ hT' hTT'
  have h2 : ∀ S L, S ∈ (triangle_boundary T) → L ∈ (triangle_boundary T) → S ≠ L →
      open_hull S ∩ open_hull L = ∅ := by
    intro S L hS hL hSL
    unfold triangle_boundary at hS hL
    simp only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and] at hS hL
    obtain ⟨i, hi⟩ := hS
    obtain ⟨j, hj⟩ := hL
    have hij : i ≠ j := by
      by_contra hij
      apply hSL
      rw [hi, hj, hij]
    rw [← Set.disjoint_iff_inter_eq_empty, hi, hj]
    exact (triangle_edges_disjoint T i j hij (non_degen T hT))
  rw [h]
  rw [segment_sum_splitting (triangle_boundary T) (triangulation_avoiding_set Δ)
    (triangulation_points Δ) h1 h2 (isPurple v) (isPurple_two_mod_function v)
    (isPurple_symm_function v)]
  unfold triangle_boundary
  simp only [top_eq_univ]
  rw [Finset.sum_biUnion _, Fin.sum_univ_three]
  · -- Reduce each side's purple count to a colour computation and apply the pure
    -- 27-case identity, keeping every step within the default heartbeat budget.
    simp only [Finset.sum_singleton]
    rw [isRainbow_eq_colors v T,
        isPurple_eq_colors v (Tside T 0), isPurple_eq_colors v (Tside T 1),
        isPurple_eq_colors v (Tside T 2)]
    exact rainbow_purple_color_identity _ _ _
  · intro i _ j _ hij
    have h_diff_points01 : T 0 ≠ T 1 := different_points T (non_degen T hT) 0 1 (by decide)
    have h_diff_points02 : T 0 ≠ T 2 := different_points T (non_degen T hT) 0 2 (by decide)
    have h_diff_points12 : T 1 ≠ T 2 := different_points T (non_degen T hT) 1 2 (by decide)
    simp only [disjoint_singleton_left, mem_singleton, ne_eq]
    -- Annoying
    suffices hs : ¬ Tside T j 0 = Tside T i 0
    · by_contra h_contra
      exact hs (congrFun h_contra.symm 0)
    · unfold Tside
      fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, not_true_eq_false]
      all_goals try (
        simp_all only [ne_eq, coe_univ, Fin.zero_eta, Set.mem_univ, not_true_eq_false]
      )
      all_goals try (rw [not_false_eq_true]; trivial)
      all_goals (intro h_contra; apply (Eq.symm) at h_contra)
      · exact h_diff_points12 h_contra
      · exact h_diff_points01 h_contra
      · exact h_diff_points02 h_contra



lemma boundary_filter_union (Δ : Finset Triangle) (T : Triangle) : T ∈ Δ →
    filter (fun S ↦ closed_hull S ⊆ boundary T) (triangulation_boundary_basic_segments Δ ∪
        triangulation_interior_basic_segments Δ) =
    filter (fun S ↦ closed_hull S ⊆ boundary T) (triangulation_boundary_basic_segments Δ) ∪
        filter (fun S ↦ closed_hull S ⊆ boundary T) (triangulation_interior_basic_segments Δ) := by
  intro a
  ext a_1 : 1
  simp_all only [mem_filter, mem_union]
  apply Iff.intro
  · intro a_2
    simp_all only [and_true]
  · intro a_2
    cases a_2 with
    | inl h => simp_all only [true_or, and_self]
    | inr h_1 => simp_all only [or_true, and_self]


lemma boundary_filter_intersection (Δ : Finset Triangle) (T : Δ) :
    filter (fun S ↦ closed_hull S ⊆ boundary T.val) (triangulation_boundary_basic_segments Δ) ∩
        filter (fun S ↦ closed_hull S ⊆ boundary T.val)
          (triangulation_interior_basic_segments Δ) = ∅ := by
  ext x
  constructor
  · intro h
    simp only [mem_inter, mem_filter] at h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨h1, h1'⟩
    rcases h2 with ⟨h2, h2'⟩
    have int : triangulation_boundary_basic_segments Δ ∩
        triangulation_interior_basic_segments Δ = ∅ := by
      exact triangulation_boundary_intersection Δ
    rw [← int]
    simp only [mem_inter]
    constructor
    · exact h1
    · exact h2
  tauto


/-lemma reverse_open_hull_basic (Δ : Finset Triangle) (S : Segment) :
    S ∈ triangulation_basic_segments Δ ↔ reverse_segment S ∈ triangulation_basic_segments Δ := by
  sorry

lemma interior_iff_reverse_interior (Δ : Finset Triangle) (S : Segment) :
    S ∈ triangulation_interior_basic_segments Δ ↔
      reverse_segment S ∈ triangulation_interior_basic_segments Δ := by
  unfold triangulation_interior_basic_segments
  repeat rw [mem_filter]
  constructor <;> intro a <;> obtain ⟨left, right⟩ := a
  · rw [← reverse_open_hull_basic, reverse_segment_open_hull]
    exact ⟨left, right⟩
  · rw [reverse_open_hull_basic, ← reverse_segment_open_hull]
    exact ⟨left, right⟩-/

/-- The open hulls of the interior basic segments of a triangulation. -/
def triangulation_interior_basic_segments_hulls (Δ : Finset Triangle) :=
  {open_hull S | S ∈ triangulation_interior_basic_segments Δ}


lemma basic_seg_non_degenerate {Δ : Finset Triangle} {S : Segment}
    (h : S ∈ triangulation_basic_segments Δ) : S 0 ≠ S 1 :=
  segment_set_vertex_distinct (basic_avoiding_segment_set_sub h)


theorem interior_purple_sum (Δ : Finset Triangle) :
    (∑ (S ∈ triangulation_interior_basic_segments Δ), isPurple v S) % 2 = 0 % 2 := by
  rw [←Int.natCast_inj, Int.natCast_mod, Int.natCast_mod, ←ZMod.intCast_eq_intCast_iff']
  simp only [Nat.cast_sum, Int.cast_sum, Int.cast_natCast, CharP.cast_eq_zero, Int.cast_zero]
  apply (Finset.sum_involution (fun x ↦ (fun y ↦ reverse_segment x)))
  · intro a ha
    rw [isPurple_symm_function, ← two_mul, mul_eq_zero]
    left
    rfl
  · intro a ha h1
    by_contra h
    have h_eq : a 0 = a 1 := by
      unfold reverse_segment at h
      conv => left; rw [← h]
      unfold to_segment
      rfl
    unfold triangulation_interior_basic_segments at ha
    rw [mem_filter] at ha
    apply basic_seg_non_degenerate ha.1
    exact h_eq
  · intro a ha
    unfold triangulation_interior_basic_segments at *
    rw [mem_filter] at *
    constructor
    · unfold triangulation_basic_segments at *
      exact basic_avoiding_segment_set_reverse ha.1
    · rw [reverse_segment_open_hull]
      exact ha.right
  · intro a ha
    exact reverse_segment_involution


/-- Indicator of whether a segment lies on the boundary of the unit square. -/
noncomputable def boundary_indicator (T : Triangle) (S : Segment) :=
    if (closed_hull S ⊆ boundary T) then 1 else 0

lemma triangle_basic_boundary_indicator_rw {Δ : Finset Triangle} (T : Triangle) {f : Segment → ℕ} :
    ∑ S ∈ triangle_basic_boundary Δ T, f S =
    ∑ S ∈ triangulation_basic_segments Δ, (f S) * boundary_indicator T S := by
  unfold triangle_basic_boundary
  rw [sum_filter]
  congr
  simp [boundary_indicator]

lemma open_triangle_segment (Δ : Finset Triangle) (S : Segment)
    (hS : S ∈ triangulation_basic_segments Δ) :
    ∀ T ∈ Δ, open_hull T ∩ closed_hull S = ∅ := by
  unfold triangulation_basic_segments triangulation_avoiding_set basic_avoiding_segment_set
    avoiding_segment_set at hS
  intro T hT
  simp only [Set.disjoint_iUnion_right, mem_filter] at hS
  rw [← Set.disjoint_iff_inter_eq_empty]
  apply Disjoint.symm
  exact hS.1.2 T hT

lemma split_segment_sum (Δ : Finset Triangle)
  (hDisjointCover : is_disjoint_cover (closed_hull unit_square) (↑Δ : Set Triangle))
 (f : Segment → ℕ) (non_degen : ∀ P ∈ Δ, det P ≠ 0)
    : ∑ T ∈ Δ, ∑ (S ∈ triangle_basic_boundary Δ T), f S =
    ∑ (S ∈ triangulation_boundary_basic_segments Δ), f S +
    2 * ∑ (S ∈ triangulation_interior_basic_segments Δ), f S := by
  simp_rw [triangle_basic_boundary_indicator_rw]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  rw [triangulation_boundary_union _ hDisjointCover.1 non_degen, Finset.sum_union ?_]
  · congr 1
    · rw [sum_congr rfl]
      intro S hS
      nth_rewrite 2 [←mul_one (f S)]
      congr
      simp_rw [boundary_indicator, ←Finset.card_filter]
      refine segment_triangle_pairing_boundary Δ hDisjointCover non_degen S ?_ ?_ ?_ ?_
      · apply segment_set_vertex_distinct (X := triangulation_points Δ)
        refine basic_avoiding_segment_set_sub (A := (triangulation_avoiding_set Δ)) ?_
        exact mem_of_mem_filter S hS
      · have h2 : S ∈ triangulation_basic_segments Δ := by
          unfold triangulation_boundary_basic_segments at hS
          exact Finset.filter_subset (fun S ↦ open_hull S ⊆ boundary unit_square)
            (triangulation_basic_segments Δ) hS
        exact open_triangle_segment Δ S h2
      · simp only [triangulation_boundary_basic_segments, mem_filter] at hS
        exact hS.2
      · intro T hT
        simp only [triangulation_boundary_basic_segments, mem_filter,
          triangulation_basic_segments, basic_avoiding_segment_set] at hS
        intro _
        refine hS.1.2 ?_ ?_
        exact triangulation_points_mem hT _
    · rw [mul_sum, sum_congr rfl]
      intro S hS
      rw [mul_comm]
      congr
      simp_rw [boundary_indicator, ←Finset.card_filter]
      refine segment_triangle_pairing_int Δ hDisjointCover non_degen S ?_ ?_ ?_
      · have h2 : S ∈ triangulation_basic_segments Δ := by
          unfold triangulation_interior_basic_segments at hS
          exact Finset.filter_subset (fun S ↦ open_hull S ⊆ open_hull unit_square)
            (triangulation_basic_segments Δ) hS
        exact open_triangle_segment Δ S h2
      · simp only [triangulation_interior_basic_segments, mem_filter] at hS
        exact hS.2
      · intro T hT
        simp only [triangulation_interior_basic_segments, mem_filter,
          triangulation_basic_segments, basic_avoiding_segment_set] at hS
        intro _
        refine hS.1.2 ?_ ?_
        exact triangulation_points_mem hT _
  · rw [Finset.disjoint_iff_inter_eq_empty]
    exact triangulation_boundary_intersection Δ

theorem rainbow_sum_is_purple_sum (Δ : Finset Triangle)
    (hDisjointCover : is_disjoint_cover (closed_hull unit_square) (↑Δ : Set Triangle))
    (non_degen : ∀ P ∈ Δ, det P ≠ 0) :
    2 * rainbow_sum v Δ % 4 = purple_sum v Δ % 4 := by
  /-
    Split the rainbow_sum to a sum over all basic segments. One can then sum over all segments first
    or over all triangles first.
  -/
  unfold rainbow_sum purple_sum
  rw [mul_sum, sum_nat_mod]
  rw [sum_congr rfl (rainbow_triangle_purple_sum v non_degen hDisjointCover) , ←sum_nat_mod]
  rw [split_segment_sum Δ hDisjointCover (isPurple v) non_degen]
  have h : (2 * ∑ (S ∈ triangulation_interior_basic_segments Δ), isPurple v S) % 4 = 0 := by
    exact mod_two_mul (interior_purple_sum v Δ)
  rw [Nat.add_mod, h, add_zero, Nat.mod_mod]

theorem monsky_rainbow (Δ : Finset Triangle)
    (hDisjointCover : is_disjoint_cover (closed_hull unit_square) (↑Δ : Set Triangle))
    (non_degen : ∀ P ∈ Δ, det P ≠ 0)
    : ∃ T ∈ Δ, rainbow_triangle v T := by
  have this := rainbow_sum_is_purple_sum v _ hDisjointCover non_degen
  rw [segment_sum_odd v _ hDisjointCover.1 non_degen] at this
  have hf : rainbow_sum v Δ ≠ 0 := by
    intro hc
    rw [hc] at this
    simp only [mul_zero, Nat.zero_mod, OfNat.zero_ne_ofNat] at this
  simp_rw [rainbow_sum, isRainbow, ←Finset.card_filter, card_ne_zero] at hf
  have ⟨T, hT⟩ := hf
  simp only [mem_filter] at hT
  refine ⟨T, hT.1, hT.2⟩

end Monsky
end LeanPool
