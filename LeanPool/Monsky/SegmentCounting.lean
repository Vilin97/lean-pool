/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Abel
import LeanPool.Monsky.SimplexBasic
import LeanPool.Monsky.SegmentTriangle
import LeanPool.Monsky.BasicDefinitions
import LeanPool.Monsky.RainbowTriangles
import LeanPool.Monsky.Square

/-!
# LeanPool.Monsky.SegmentCounting

Imported Lean Pool material for `LeanPool.Monsky.SegmentCounting`.
-/

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²


open BigOperators
open Finset

attribute [local instance] Classical.propDecidable



/-- The set of nondegenerate segments with both endpoints in `X`. -/
noncomputable def segmentSet (X : Finset ℝ²) : Finset Segment :=
    Finset.image (fun (a,b) ↦ toSegment a b) ((Finset.product X X).filter (fun (a,b) ↦ a ≠ b))

/-- The segments of `segmentSet X` whose open hull avoids the set `A`. -/
noncomputable def avoidingSegmentSet (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (segmentSet X).filter (fun L ↦ Disjoint (closedHull L) (A))

/-- The avoiding segments of `X` that are basic, i.e. contain no point of `X` in their interior. -/
noncomputable def basicAvoidingSegmentSet (X : Finset ℝ²) (A : Set ℝ²) : Finset Segment :=
    (avoidingSegmentSet X A).filter (fun L ↦ ∀ x ∈ X, x ∉ openHull L)



/-- An inductively defined chain of collinear segments between two points. -/
inductive Chain : ℝ² → ℝ² → Type
    | basic {u v : ℝ²}  : Chain u v
    | join {u v w : ℝ²} (hCollineair : colin u v w) (C : Chain v w) : Chain u w

/-- The finite set of basic segments making up a chain. -/
noncomputable def toBasicSegments {u v : ℝ²} : Chain u v → Finset Segment
    | Chain.basic              => {toSegment u v}
    | @Chain.join _ w _ _ C    => toBasicSegments C ∪ {toSegment u w}

/-- Concatenates two chains sharing an endpoint into a single chain. -/
noncomputable def glueChains {u v w : ℝ²} (hCollinear : colin u v w)
    : Chain u v → Chain v w → Chain u w
    | Chain.basic, C      => Chain.join hCollinear C
    | Chain.join h C', C  => Chain.join ⟨hCollinear.1, interior_left_trans h.2 hCollinear.2⟩
        (glueChains (sub_collinear_right hCollinear h.2) C' C)

/-- Reverses the direction of a chain. -/
noncomputable def reverseChain {u v : ℝ²} : Chain u v → Chain v u
    | Chain.basic           => Chain.basic
    | @Chain.join _ x _ h C => glueChains (colin_reverse h) (reverseChain C) (@Chain.basic x u)

/-- The single segment from the start to the end of a chain. -/
noncomputable def chainToBigSegment {u v : ℝ²} (C : Chain u v) : Segment :=
  match C with
  | _ => toSegment u v

lemma chainToBigSegment_join {u v w} (h : colin u v w) (C : Chain v w) :
    chainToBigSegment (Chain.join h C) = toSegment u w := rfl

lemma chainToBigSegment_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w) : chainToBigSegment (glueChains h CL CR) = toSegment u w := rfl

lemma glueChains_assoc {u v w x : ℝ²} (C₁ : Chain u v) (C₂ : Chain v w) (C₃ : Chain w x)
    (h₁ : colin u v w) (h₂ : colin v w x) :
    glueChains (colin_trans_right h₁ h₂) (glueChains h₁ C₁ C₂) C₃ =
    glueChains (colin_trans_left h₁ h₂) C₁ (glueChains h₂ C₂ C₃) := by
  induction C₁ with
  | basic         => rfl
  | join h₃ C ih  =>
    simpa only [glueChains, Chain.join.injEq, heq_eq_eq, true_and] using ih C₂ _ _


lemma reverseChain_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w)
    : reverseChain (glueChains h CL CR)
    = glueChains (colin_reverse h) (reverseChain CR) (reverseChain CL) := by
  induction CL with
  | basic         => rfl
  | join h₂ C ih  =>
      simp only [glueChains, reverseChain, ih (sub_collinear_right h h₂.2) CR]
      rw [←glueChains_assoc]

lemma basic_segments_glue {u v w : ℝ²} (h : colin u v w) (CL : Chain u v)
    (CR : Chain v w)
    : toBasicSegments (glueChains h CL CR) = toBasicSegments CL ∪ toBasicSegments CR := by
  induction CL with
  | basic       => rw [union_comm]; rfl
  | join h₂ C ih  =>
      simp [toBasicSegments, glueChains, ih (sub_collinear_right h h₂.2) CR]


lemma basic_segment_in_openHull {u v : ℝ²} (C : Chain u v) {S : Segment}
    (hS : S ∈ toBasicSegments C) : openHull S ⊆ openHull (toSegment u v) := by
  induction C with
  |basic         => simp only [toBasicSegments, mem_singleton] at *; rw [hS]
  |join h₂ C ih  =>
    simp only [toBasicSegments, mem_union, mem_singleton] at *
    rcases hS with hS | hS
    · refine subset_trans (ih hS) ?_
      apply right_openHull_in_colin; exact h₂
    · rw [hS]
      apply left_openHull_in_colin; exact h₂



/-- Helper: a segment whose open hull lands in `openHull (toSegment u v)` cannot also land in
`openHull (toSegment v w)` when `u, v, w` are collinear. -/
private lemma basic_segments_colin_disjoint_aux {u v w : ℝ²} {S : Segment} (h : colin u v w)
    (hL : openHull S ⊆ openHull (toSegment u v))
    (hR : openHull S ⊆ openHull (toSegment v w)) : False := by
  have other : openHull (toSegment u v) ∩ openHull (toSegment v w) = ∅ :=
    colin_intersection_openHulls_empty (h := h)
  have ⟨p, q⟩ : ∃ (b : ℝ²), b ∈ openHull S := open_pol_nonempty (by linarith) S
  rw [Set.eq_empty_iff_forall_notMem] at other
  exact other p ⟨hL q, hR q⟩

lemma basic_segments_colin_disjoint {u v w : ℝ²} {C : Chain v w} (h : colin u v w) :
    toSegment u v ∉ toBasicSegments C := fun hc ↦
  basic_segments_colin_disjoint_aux h (fun _ a ↦ a) (basic_segment_in_openHull _ hc)

lemma basic_segments_colin_disjoint2 {u v w : ℝ²} {C : Chain v w} (h : colin u v w) :
    toSegment v u ∉ toBasicSegments C := by
  intro hc
  have this := basic_segment_in_openHull _ hc
  refine basic_segments_colin_disjoint_aux h ?_ this
  rw [← reverseSegment_toSegment, reverseSegment_openHull]

lemma basic_segments_colin_disjoint_reverse {u v w : ℝ²} {C : Chain v w} (h : colin u v w) :
    toSegment  u v ∉ toBasicSegments (reverseChain C ):= by
  intro hc
  have this := basic_segment_in_openHull _ hc
  refine basic_segments_colin_disjoint_aux h (fun _ a ↦ a) ?_
  rwa [← reverseSegment_toSegment (u := v) (v := w), reverseSegment_openHull] at this

lemma reverseChain_basic_segments {u v : ℝ²} (C : Chain u v) :
    toBasicSegments (reverseChain C) =
    Finset.image (fun S ↦ reverseSegment S) (toBasicSegments C) := by
  induction C with
  |basic         => rfl
  | join _ _ ih   =>
      simp only [reverseChain, toBasicSegments, basic_segments_glue, ih, Finset.image_union]
      congr 1

lemma reverseChain_basic_segments_disjoint {u v : ℝ²} (C : Chain u v) (huv : u ≠ v) :
    Disjoint (toBasicSegments C) (toBasicSegments (reverseChain C)) := by
  induction C with
  | basic =>
      simpa only [toBasicSegments, reverseChain, disjoint_singleton_left, mem_singleton]
        using fun h ↦ huv (congrFun h 0)
  | @join x y z h₂ C ih =>
      have hyz : y ≠ z := (middle_not_boundary_colin h₂).2
      have hxy : x ≠ y := (middle_not_boundary_colin h₂).1
      simp only [toBasicSegments, union_singleton, reverseChain, basic_segments_glue,
        disjoint_insert_right, mem_insert, not_or, disjoint_insert_left]
      refine ⟨⟨fun h ↦ hxy (congrFun h 1), basic_segments_colin_disjoint2 h₂⟩,
        basic_segments_colin_disjoint_reverse h₂, ih hyz⟩


lemma segmentSet_vertex {X : Finset ℝ²} {S : Segment}
  (hS : S ∈ segmentSet X) : ∀ i, S i ∈ X := by
  simp only [segmentSet, ne_eq, product_eq_sprod, mem_image,
              mem_filter, mem_product, Prod.exists] at hS
  have ⟨a, b, ⟨⟨⟨ha,hb⟩ ,h₁⟩,h₂⟩⟩ := hS
  rw [←h₂]
  intro i; fin_cases i <;> (simp only [toSegment]; assumption)


lemma avoidingSegmentSet_sub {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoidingSegmentSet X A) : S ∈ segmentSet X :=
  mem_of_mem_filter S hS

lemma basicAvoidingSegmentSet_sub {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ basicAvoidingSegmentSet X A) : S ∈ segmentSet X :=
  avoidingSegmentSet_sub (A := A) (mem_of_mem_filter S hS)

lemma segmentSet_vertex_distinct {X : Finset ℝ²} {S : Segment}
    (hS : S ∈ segmentSet X) : S 0 ≠ S 1 := by
  simp only [segmentSet, ne_eq, product_eq_sprod, mem_image,
              mem_filter, mem_product, Prod.exists] at hS
  have ⟨_, _, ⟨⟨_,_⟩ ,h₂⟩⟩ := hS
  rw [←h₂]
  simpa [toSegment]

lemma segmentSet_boundary {X : Finset ℝ²} {x : ℝ²} {S : Segment} (hS : S ∈ segmentSet X)
    (hx : x ∈ boundary S) : x ∈ X := by
  rw [boundary_seg (segmentSet_vertex_distinct hS), mem_coe, mem_image] at hx
  have ⟨i, _, hi⟩ := hx
  rw [←hi]
  exact segmentSet_vertex hS i

lemma segmentSet_reverse {X : Finset ℝ²} {S : Segment} (hS : S ∈ segmentSet X) :
    reverseSegment S ∈ segmentSet X := by
  simp only [segmentSet, ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product,
    Prod.exists] at *
  rcases hS with ⟨a, ⟨  b, h⟩⟩
  rw[← h.2, reverseSegment_toSegment]
  exact ⟨b, a, ⟨ ⟨ h.1.1.2,h.1.1.1 ⟩ , fun a_1 ↦ h.1.2 (id (Eq.symm a_1))⟩, by rfl  ⟩

lemma avoidingSegmentSet_reverse {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoidingSegmentSet X A) : reverseSegment S ∈ avoidingSegmentSet X A := by
  simp only[ avoidingSegmentSet, mem_filter, reverseSegment_closedHull ] at *
  exact ⟨ segmentSet_reverse hS.1, hS.2⟩

lemma basicAvoidingSegmentSet_reverse {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ basicAvoidingSegmentSet X A) :
    reverseSegment S ∈ basicAvoidingSegmentSet X A := by
  simp only[basicAvoidingSegmentSet, mem_filter ,reverseSegment_openHull] at *
  exact ⟨ avoidingSegmentSet_reverse hS.1, hS.2 ⟩

lemma avoidingSegmentSet_sub_left {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoidingSegmentSet X A) {x : ℝ²} (hx : x ∈ X) (hxS : x ∈ openHull S)
    : toSegment (S 0) x ∈ avoidingSegmentSet X A := by
  simp only [avoidingSegmentSet, mem_filter, Fin.isValue] at *
  constructor
  · simp only [segmentSet, ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product,
    Prod.exists, Fin.isValue] at *
    rcases hS with ⟨⟨ a, ⟨ b, h⟩⟩, _⟩
    exact ⟨a, x, ⟨ ⟨h.1.1.1 , hx⟩ ,
      (middle_not_boundary_colin ⟨h.1.2 , by rw[h.2]; exact hxS ⟩).1⟩,
      by rw[← h.2]; simp only [toSegment]  ⟩
  · refine Set.disjoint_of_subset (closedHull_convex ?_) (fun ⦃a⦄ a ↦ a) hS.2
    intro i; fin_cases i <;> simp only [toSegment, Fin.isValue, corner_in_closedHull]
    exact open_sub_closed S hxS

lemma avoidingSegmentSet_sub_right {X : Finset ℝ²} {A : Set ℝ²} {S : Segment}
    (hS : S ∈ avoidingSegmentSet X A) {x : ℝ²} (hx : x ∈ X) (hxS : x ∈ openHull S)
    : toSegment x (S 1) ∈ avoidingSegmentSet X A := by
  rw[← reverseSegment_toSegment]
  refine avoidingSegmentSet_reverse
    (avoidingSegmentSet_sub_left (avoidingSegmentSet_reverse hS) hx ?_ )
  rwa[← reverseSegment_openHull]


theorem segment_decomposition {A : Set ℝ²} {X : Finset ℝ²} {S : Segment}
    (hS : S ∈ avoidingSegmentSet X A) :
    ∃ (C : Chain (S 0) (S 1)),
    S = chainToBigSegment C ∧
    (basicAvoidingSegmentSet X A).filter (fun s ↦ closedHull s ⊆ closedHull S)
    = toBasicSegments C ∪ (toBasicSegments (reverseChain C)) := by
  generalize Scard : (Finset.filter (fun p ↦ p ∈ openHull S) X).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h N hm =>
  have hSboundary := boundary_seg (segmentSet_vertex_distinct (avoidingSegmentSet_sub hS))
  by_cases hN : N = 0
  · use @Chain.basic (S 0) (S 1)
    simp only [chainToBigSegment, Fin.isValue, segment_rfl,
      toBasicSegments, reverseChain, true_and]
    simp only [hN, card_eq_zero, filter_eq_empty_iff] at Scard
    ext L
    simp only [mem_filter, Fin.isValue, mem_union, mem_singleton]
    constructor
    · intro ⟨hL, hLS⟩
      have hLi : ∀ i, L i ∈ boundary S := by
        intro i
        simp only [boundary, Set.mem_sdiff]
        refine ⟨hLS (corner_in_closedHull),?_⟩
        apply Scard
        exact segmentSet_vertex (basicAvoidingSegmentSet_sub hL) i
      have hLdif := segmentSet_vertex_distinct (basicAvoidingSegmentSet_sub hL)
      simp only [hSboundary, coe_image, coe_univ, Set.image_univ, Set.mem_range, Fin.exists_fin_two,
        Fin.isValue, Fin.forall_fin_two] at hLi
      obtain ⟨h0 | h0, h1 | h1⟩ := hLi
      · exact absurd (h0 ▸ h1) hLdif
      · left
        exact List.ofFn_inj.mp (by simp [← h0, ← h1])
      · right
        exact List.ofFn_inj.mp (by simp [toSegment, ← h0, ← h1])
      · exact absurd (h0 ▸ h1) hLdif
    · rintro (hL | hL) <;> rw [hL]
      · refine ⟨?_, fun _ a ↦ a⟩
        simpa only [basicAvoidingSegmentSet, mem_filter] using ⟨hS,Scard⟩
      · rw [←reverseSegment]
        refine ⟨?_, by rw [reverseSegment_closedHull]⟩
        apply basicAvoidingSegmentSet_reverse
        simpa only [basicAvoidingSegmentSet, mem_filter] using ⟨hS,Scard⟩
  · have hEl : Finset.Nonempty (filter (fun p ↦ p ∈ openHull S) X) := by
      rw [← Finset.card_pos, Scard]
      exact Nat.zero_lt_of_ne_zero hN
    have ⟨x, hx⟩ := hEl
    let Sleft := toSegment (S 0) x
    let Sright := toSegment x (S 1)
    have hSlefti : ∀ i, Sleft i ∈ closedHull S := by
      rw [mem_filter] at hx
      intro i; fin_cases i
      · change Sleft 0 ∈ closedHull S
        exact corner_in_closedHull (i := 0) (P := S)
      · change Sleft 1 ∈ closedHull S
        exact open_sub_closed _ hx.2
    have hSrighti : ∀ i, Sright i ∈ closedHull S := by
      rw [mem_filter] at hx
      intro i; fin_cases i
      · change Sright 0 ∈ closedHull S
        exact open_sub_closed _ hx.2
      · change Sright 1 ∈ closedHull S
        exact corner_in_closedHull (i := 1) (P := S)
    have hcolin : colin (S 0) x (S 1) := by
      rw [mem_filter] at hx
      exact ⟨segmentSet_vertex_distinct (avoidingSegmentSet_sub hS), hx.2⟩
    have Sleftcard : (filter (fun p ↦ p ∈ openHull Sleft) X).card < N := by
      rw [←Scard]
      refine card_lt_card ⟨?_,?_⟩
      · intro t ht
        simp only [mem_filter] at *
        refine ⟨ht.1, (open_segment_sub hSlefti ?_) ht.2⟩
        convert (middle_not_boundary_colin hcolin).1 using 1 <;> rfl
      · rw [@not_subset]
        use x, hx
        intro hcontra
        rw [mem_filter] at hcontra
        refine (boundary_not_in_open (boundary_seg' ?_ 1)) hcontra.2
        convert (middle_not_boundary_colin hcolin).1 using 1 <;> rfl
    have Srightcard : (filter (fun p ↦ p ∈ openHull Sright) X).card < N := by
      rw [←Scard]
      refine card_lt_card ⟨?_,?_⟩
      · intro t ht
        simp only [mem_filter] at *
        refine ⟨ht.1, (open_segment_sub hSrighti ?_) ht.2⟩
        convert (middle_not_boundary_colin hcolin).2 using 1 <;> rfl
      · rw [@not_subset]
        use x, hx
        intro hcontra
        rw [mem_filter] at hcontra
        refine (boundary_not_in_open (boundary_seg' ?_ 0)) hcontra.2
        convert (middle_not_boundary_colin hcolin).2 using 1 <;> rfl
    rw [mem_filter] at hx
    have ⟨CL,hSCL,hLSegUnion⟩ :=
      hm (filter (fun p ↦ p ∈ openHull Sleft) X).card Sleftcard
      (avoidingSegmentSet_sub_left hS hx.1 hx.2) rfl
    have ⟨CR,hSCR,hRSegUnion⟩ :=
      hm (filter (fun p ↦ p ∈ openHull Sright) X).card Srightcard
      (avoidingSegmentSet_sub_right hS hx.1 hx.2) rfl
    use glueChains hcolin CL CR
    simp only [chainToBigSegment_glue, segment_rfl, reverseChain_glue,
        basic_segments_glue, true_and]
    -- Membership characterisations of the two sub-chains, derived directly from
    -- `hLSegUnion`/`hRSegUnion`. We avoid `rw`-ing the union *term* (whose `Finset`
    -- instance no longer matches after associativity reshuffling) and work purely
    -- at the level of `Finset.mem_union`, which matches up to instance defeq.
    have hLmem : ∀ L, (L ∈ toBasicSegments CL ∨ L ∈ toBasicSegments (reverseChain CL)) ↔
        (L ∈ basicAvoidingSegmentSet X A ∧ closedHull L ⊆ closedHull (toSegment (S 0) x)) :=
      fun L ↦ by rw [← Finset.mem_union, ← hLSegUnion]; simp only [Finset.mem_filter]
    have hRmem : ∀ L, (L ∈ toBasicSegments CR ∨ L ∈ toBasicSegments (reverseChain CR)) ↔
        (L ∈ basicAvoidingSegmentSet X A ∧ closedHull L ⊆ closedHull (toSegment x (S 1))) :=
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
          subset_trans ((hLmem L).mp (Or.inl hCL)).2 (closedHull_convex hSlefti)⟩
      · exact ⟨((hRmem L).mp (Or.inl hCR)).1,
          subset_trans ((hRmem L).mp (Or.inl hCR)).2 (closedHull_convex hSrighti)⟩
      · exact ⟨((hRmem L).mp (Or.inr hrevCR)).1,
          subset_trans ((hRmem L).mp (Or.inr hrevCR)).2 (closedHull_convex hSrighti)⟩
      · exact ⟨((hLmem L).mp (Or.inr hrevCL)).1,
          subset_trans ((hLmem L).mp (Or.inr hrevCL)).2 (closedHull_convex hSlefti)⟩


/-- A function on segments that is additive modulo 2 along collinear splits. -/
def twoModFunction (f : Segment → ℕ)
    := ∀ {u v w}, colin u v w →
      (f (toSegment u v) + f (toSegment v w)) % 2 = f (toSegment u w) % 2

/-- A function on segments invariant under reversing the segment. -/
def symmFun (f : Segment → ℕ) := ∀ S, f (reverseSegment S) = f S

lemma twoModFunction_chains {f : Segment → ℕ} (hf : twoModFunction f) {u v : ℝ²}
    (C : Chain u v) : (∑ S ∈ toBasicSegments C, f S) % 2 = f (toSegment u v) % 2 := by
  induction C with
  | basic         => simp only [toBasicSegments, sum_singleton]
  | join h₂ C ih  =>
      simp only [toBasicSegments]
      rw [Finset.sum_union (by simpa only [disjoint_singleton_right] using
        basic_segments_colin_disjoint h₂)]
      simp only [sum_singleton, Nat.add_mod, ih, dvd_refl, Nat.mod_mod_of_dvd]
      simp only [dvd_refl, Nat.mod_mod_of_dvd, Nat.add_mod_mod, Nat.mod_add_mod, ←hf h₂]
      rw [add_comm]


lemma symmFunction_reverse_sum {f : Segment → ℕ} (hf : symmFun f) {u v : ℝ²}
    (C : Chain u v) :
    (∑ S ∈ toBasicSegments (reverseChain C), f S) =
    (∑ S ∈ toBasicSegments C, f S) := by
  rw [reverseChain_basic_segments, Finset.sum_image]
  · congr
    ext L
    exact hf L
  · intro _ _ _ _
    have ⟨hi,_⟩ := reverseSegment_bijective
    exact fun a ↦ hi (hi (hi a))


lemma mod_two_mul {a b : ℕ} (h : a % 2 = b % 2) : (2 * a) % 4 = (2 * b) % 4 := by
  rw [←Int.natCast_inj, Int.natCast_mod, Int.natCast_mod, ←ZMod.intCast_eq_intCast_iff',
      ←sub_eq_zero, ←Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at *
  have ⟨c, hc⟩ := h
  exact ⟨c, by simp only [Nat.cast_mul, ←mul_sub, hc]; ring⟩


lemma sum_two_mod_fun_seg {A : Set ℝ²} {X : Finset ℝ²} {S : Segment}
    (hS : S ∈ avoidingSegmentSet X A) {f : Segment → ℕ} (hf₁ : twoModFunction f)
    (hf₂ : symmFun f) :
    (∑ T ∈ (basicAvoidingSegmentSet X A).filter (fun s ↦ closedHull s ⊆ closedHull S),
      f T) % 4 =
    (2 * f S) % 4 := by
  have ⟨C, _, hSdecomp⟩ := segment_decomposition hS
  rw [hSdecomp, Finset.sum_union]
  · rw [symmFunction_reverse_sum hf₂, ←Nat.two_mul]
    apply mod_two_mul
    convert twoModFunction_chains hf₁ C
    funext i; fin_cases i <;> rfl
  · exact reverseChain_basic_segments_disjoint _
      (segmentSet_vertex_distinct (avoidingSegmentSet_sub hS))


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




lemma isPurple_twoModFunction : twoModFunction (isPurple v) := by
  unfold twoModFunction
  intro x y z hColin
  have h := no_Color_lines (toSegment x z) v
  -- In order to use the no color lines, we need that all our points are in the closed hull, to
  -- prove this was slightly frustrating
  have hhelpz : z = (toSegment x z) 1  := by rfl
  have hhelpx : x = (toSegment x z) 0  := by rfl
  have hx : x ∈ closedHull (toSegment x z) := by
    nth_rewrite 2[hhelpx]; exact corner_in_closedHull
  have hz : z ∈ closedHull (toSegment x z) := by
    nth_rewrite 2[hhelpz]; exact corner_in_closedHull
  have hy : y ∈ closedHull (toSegment x z) := by
    exact (open_sub_closed (toSegment x z) hColin.2)
  --This finishes the aux lemmas
  rcases h with ⟨ c, hnotc⟩
  have hx1 := hnotc x hx; have hy1 := hnotc y hy; have hz1 := hnotc z hz
  clear hhelpx hhelpz hx hy hz hColin hnotc
  simp only [isPurple, Fin.isValue]
  generalize hcx : coloring v x = cx at hx1
  generalize hcy : coloring v y = cy at hy1
  generalize hcz : coloring v z = cz at hz1
  simp only [toSegment]
  simp_rw [hcx, hcy, hcz]
  -- I am doing an induction over 81 cases.... I hope it is not too slow
  induction c <;> induction cx <;> induction cy <;> induction cz <;> simp only [reduceCtorEq,
    and_false, and_true, or_self, ↓reduceIte, add_zero, Nat.zero_mod] <;> tauto


lemma isPurple_symmFunction : symmFun (isPurple v) := by
  unfold symmFun
  intro S
  unfold isPurple reverseSegment
  simp only [toSegment]
  congr 1
  rw [eq_iff_iff]
  tauto

-- The segment covered by a chain is purple if and only if an odd number of its basic
-- segments are purple.
/-lemma purple_parity {u v : ℝ²} (C : Chain u v) : ∑ T ∈ toBasicSegments C, isPurple T % 2
    = isPurple (chainToBigSegment C) := by
  sorry -- can apply twoModFunction_chains
-/

/-- The finite set of all vertices appearing in a triangulation. -/
noncomputable def triangulationPoints (Δ : Finset Triangle) : Finset ℝ² :=
  Finset.biUnion Δ (fun T ↦ {T 0, T 1, T 2})


-- This definition might be better so
-- TODO: Change to this
/-- The set of triangulation vertices, viewed as a set of points of the plane. -/
noncomputable def triangulationPoints₂ (Δ : Finset Triangle) : Finset ℝ² :=
  Finset.biUnion Δ (fun T ↦ (Finset.image (fun i ↦ T i) Finset.univ))


lemma triangulationPoints_mem {Δ : Finset Triangle} {T : Triangle} (hT : T ∈ Δ)
    : ∀ i, T i ∈ triangulationPoints Δ := by
  intro i
  simp only [triangulationPoints, Fin.isValue, mem_biUnion, mem_insert, mem_singleton]
  use T, hT
  fin_cases i <;> simp


-- The union of the interiors of the triangles of a triangulation
/-- The union of triangle interiors that basic segments of the triangulation must avoid. -/
noncomputable def triangulationAvoidingSet (Δ : Finset Triangle) : Set ℝ² :=
    ⋃ (T ∈ Δ), openHull T

/-- The basic avoiding segments of a triangulation. -/
noncomputable def triangulationBasicSegments (Δ : Finset Triangle) : Finset Segment :=
  basicAvoidingSegmentSet (triangulationPoints Δ) (triangulationAvoidingSet Δ)

/-- The basic segments lying on the boundary of the unit square. -/
noncomputable def triangulationBoundaryBasicSegments (Δ : Finset Triangle) : Finset Segment :=
  {S ∈ triangulationBasicSegments Δ | openHull S ⊆ boundary unitSquare}

/-- The basic segments lying in the interior of the unit square. -/
noncomputable def triangulationInteriorBasicSegments (Δ : Finset Triangle) : Finset Segment :=
  {S ∈ triangulationBasicSegments Δ | openHull S ⊆ openHull unitSquare}

/-- `isTriangulation Δ` states that `Δ` is a disjoint cover of the unit square by triangles. -/
noncomputable def isTriangulation (Δ : Finset Triangle) : Prop :=
  isCover (closedHull unitSquare) (↑Δ : Set Triangle)

/-- Every vertex of a triangulation lies in the closed unit square. -/
lemma triangulationPoints_subset_unitSquare {Δ : Finset Triangle}
    (hCover : isTriangulation Δ) :
    (↑(triangulationPoints Δ) : Set ℝ²) ⊆ closedHull unitSquare := by
  unfold triangulationPoints
  simp only [Fin.isValue, coe_biUnion, mem_coe, coe_insert, coe_singleton,
    Set.iUnion_subset_iff]
  intro T hT z hz
  have hTsub : closedHull T ⊆ closedHull unitSquare := by
    rw [hCover]
    intro w hw
    simp_all only [mem_coe, Fin.isValue, Set.mem_iUnion, exists_prop]
    exact ⟨T, hT, hw⟩
  have zT : ∃ i : Fin 3, z = T i := by
    simp_all only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hz with h | h | h <;> exact ⟨_, h⟩
  rcases zT with ⟨i, hi⟩
  exact hTsub (hi ▸ corner_in_closedHull)

lemma segment_in_interior_aux {Δ : Finset Triangle} (hCover : isTriangulation Δ)
(non_degen : ∀ P ∈ Δ, det P ≠ 0) {L : Segment} (hL : L ∈ triangulationBasicSegments Δ) :
 ∃ T ∈ Δ, closedHull L ⊆ closedHull T := by
-- The strategy of this proof is to just verify all the conditions of seg_sub_side
-- in the first block of code we just unravel all the hypothesis and the then
-- every other block is just simply verifiing all hypothesis of seg_sub_side.
  unfold triangulationBasicSegments at hL
  unfold basicAvoidingSegmentSet at hL
  simp only [mem_filter, mem_filter] at hL
  rcases hL with ⟨p, q⟩
  unfold avoidingSegmentSet at p
  simp only [mem_filter] at p
  rcases p with ⟨a, b⟩
  unfold segmentSet at a
  simp only [mem_image, mem_filter, Prod.exists] at a
  rcases a with ⟨c, d, e⟩
  rcases e with ⟨f, g⟩
  rcases f with ⟨m, n⟩
  simp only [product_eq_sprod, mem_product] at m
  have Lnonempty : ∃ (x : ℝ²), x ∈ openHull L := by
    apply open_seg_nonempty
  rcases Lnonempty with ⟨x, hx⟩
  have convex : closedHull L ⊆ closedHull unitSquare := by
    apply unitSquare_is_convex
    · simp only [Fin.zero_eta, Fin.isValue]
      have L0 : toSegment c d 0 = L 0 := by
          rw [g]
      rw [toSegment] at L0
      rw [L0] at m
      have hL0 : L 0 ∈ triangulationPoints Δ := m.1
      exact triangulationPoints_subset_unitSquare hCover hL0
    · simp only [Fin.mk_one, Fin.isValue]
      have L1 : toSegment c d 1 = L 1 := by
          rw [g]
      rw [toSegment] at L1
      rw [L1] at m
      have hL1 : L 1 ∈ triangulationPoints Δ := m.2
      exact triangulationPoints_subset_unitSquare hCover hL1
  have xinTriangle : ∃ P ∈ Δ, x ∈ closedHull P := by
    have xclosed : x ∈ closedHull unitSquare := by
      exact convex (open_sub_closed L hx)
    rw [hCover] at xclosed
    simp only [mem_coe, Set.mem_iUnion, exists_prop] at xclosed
    exact xclosed
  rcases xinTriangle with ⟨P, hP⟩
  have Pnondegen : det P ≠ 0 := by
    apply non_degen
    apply hP.1
  have xinBT : x ∈ boundary P := by
    unfold triangulationAvoidingSet at b
    simp only [Set.disjoint_iUnion_right] at b
    specialize b P
    rcases hP with ⟨P', hP''⟩
    apply b at P'
    have xinclosed : x ∈ closedHull L := by
      exact open_sub_closed L hx
    have xnotinopen : x ∉ openHull P := by
      by_contra hcontra
      tauto_set
    tauto_set
  have xinTside : ∃ i : Fin 3, x ∈ openHull (Tside P i) := by
    have xinclosed : ∃ i : Fin 3, x ∈ closedHull (Tside P i) := by
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
    have xtriangulationpt: x ∈ triangulationPoints Δ := by
      unfold triangulationPoints
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
  have dis : openHull P ∩ closedHull L = ∅ := by
    by_contra hcontra
    have nonemp' : Set.Nonempty (openHull P ∩ closedHull L) := by
      exact Set.nonempty_iff_ne_empty.mpr hcontra
    have nonempt : ∃ z,  z ∈ openHull P ∧ z ∈ closedHull L := by
      exact nonemp'
    rcases nonempt with ⟨z, hz⟩
    unfold triangulationAvoidingSet  at b
    simp only [Set.disjoint_iUnion_right] at b
    specialize b P
    tauto_set
  have this : ∀ i : Fin 3, P i ∉ openHull L := by
    by_contra hcontra
    simp only [not_forall, Decidable.not_not] at hcontra
    rcases hcontra with ⟨i, hi⟩
    have hP' : P i ∈ triangulationPoints Δ := by
      unfold triangulationPoints
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
  have fin : closedHull L ⊆ closedHull (Tside P i) := by
    exact seg_sub_side (non_degen P hP.1) hx hi dis this
  rcases hP with ⟨T, hT, hT'⟩
  use P
  constructor
  · exact T
  · have htside : closedHull (Tside P i) ⊆ closedHull P := by
      apply closed_side_sub'
    tauto_set

lemma segment_in_interior_or_boundary {Δ : Finset Triangle} (hCover : isTriangulation Δ)
(non_degen : ∀ P ∈ Δ, det P ≠ 0) {L : Segment} (hL : L ∈ triangulationBasicSegments Δ) :
  openHull L ⊆ boundary unitSquare ∨ openHull L ⊆ openHull unitSquare := by
  have hclosed : closedHull unitSquare = boundary unitSquare ∪ openHull unitSquare := by
    rw [← boundary_union_open_closed]
  have hT : ∃ T ∈ Δ, closedHull L ⊆ closedHull T := by
    apply segment_in_interior_aux hCover non_degen hL
  rcases hT with ⟨t, ht⟩
  have hLunitS : closedHull L ⊆ closedHull unitSquare := by
    apply isCover_sub at hCover
    simp only [mem_coe] at hCover
    specialize hCover t ht.1
    exact subset_trans ht.2 hCover
  by_cases h : openHull L ⊆ boundary unitSquare
  · left
    exact h
  have hLclosed : openHull L ⊆ closedHull unitSquare := by
    exact subset_trans (open_sub_closed L) hLunitS
  right
  · have this : ∀ x, x ∈ openHull L → x ∉ boundary unitSquare  := by
      by_contra hcontra
      have hcontra' : ∃ x, x ∈ openHull L ∩ boundary unitSquare := by
        simp_all only [not_forall, Decidable.not_not, Set.mem_inter_iff]
        simp only [exists_prop] at hcontra
        exact hcontra
      have that : closedHull L ⊆ boundary unitSquare := by
        obtain ⟨x, hx⟩ := hcontra'
        apply line_in_boundary hLunitS hx
      have that' : openHull L ⊆ boundary unitSquare := by
        have hopen : openHull L ⊆ closedHull L := by
          apply open_sub_closed
        apply _root_.trans hopen that
      contradiction
    tauto_set


lemma triangulation_boundary_union (Δ : Finset Triangle) (hCover : isTriangulation Δ)
(non_degen : ∀ P ∈ Δ, det P ≠ 0) : triangulationBasicSegments Δ =
    triangulationBoundaryBasicSegments Δ ∪ triangulationInteriorBasicSegments Δ := by
  unfold triangulationBoundaryBasicSegments triangulationInteriorBasicSegments
  have hfilter : triangulationBasicSegments Δ =
      filter (fun S ↦ openHull S ⊆ closedHull unitSquare) (triangulationBasicSegments Δ) := by
    ext L
    rw [mem_filter, iff_self_and]
    intro hL
    have hT : ∃ T ∈ Δ, closedHull L ⊆ closedHull T := by
     rcases segment_in_interior_aux hCover non_degen hL with ⟨T, hT⟩
     exact ⟨T, hT⟩
    obtain ⟨T, hT⟩ := hT
    apply isCover_sub at hCover
    calc openHull L ⊆ closedHull L := open_sub_closed L
        _ ⊆ closedHull T := hT.right
        _ ⊆ closedHull unitSquare := hCover T hT.left
  rw [hfilter, ← boundary_union_open_closed, ← filter_or]
  ext L
  repeat rw [mem_filter]
  simp only [iff_self_and, and_imp]
  intro hL hinc
  apply segment_in_interior_or_boundary hCover non_degen hL


lemma triangulation_boundary_intersection (Δ : Finset Triangle) :
    triangulationBoundaryBasicSegments Δ ∩ triangulationInteriorBasicSegments Δ = ∅ := by
  unfold triangulationBoundaryBasicSegments triangulationInteriorBasicSegments
  ext S
  simp only [mem_inter, mem_filter, notMem_empty, iff_false, not_and, and_imp]
  intro hS hOpen hS2
  by_contra h
  have h_elt : ∃ x, x ∈ openHull S := by
    apply open_pol_nonempty
    linarith
  have h_open_nonempty : openHull S ≠ ∅ := by
    obtain ⟨x, h_1⟩ := h_elt
    intro h
    simp_all only [Set.empty_subset, Set.mem_empty_iff_false]
  have h_open_empty : openHull S ⊆ ∅ := by
    rw [← boundary_int_open_empty]
    tauto_set
  simp_all only [ne_eq, Set.subset_empty_iff]


/-- All basic segments of a triangulation, both boundary and interior. -/
noncomputable def triangulationAllSegments (Δ : Finset Triangle) : Finset Segment :=
  avoidingSegmentSet (triangulationPoints Δ) (triangulationAvoidingSet Δ)

/-- The total number of purple segments in a triangulation. -/
noncomputable def purpleSum (Δ : Finset Triangle) : ℕ :=
  ∑ (S ∈ triangulationBoundaryBasicSegments Δ), isPurple v S

/-- The total number of rainbow triangles in a triangulation. -/
noncomputable def rainbowSum (Δ : Finset Triangle) : ℕ :=
  ∑ (T ∈ Δ), isRainbow v  T

/-- The finite set of rainbow triangles of a triangulation. -/
noncomputable def rainbowTriangles (Δ : Finset Triangle) : Finset Triangle :=
  {T ∈ Δ | isRainbow v T = 1}

-- Given a collection of segments X and a segment S, give all elements of X with openHull contained
-- in openHull S.

/-- The basic segments of a segment family contained in a given side. -/
noncomputable def basicSegmentSegments (X : Finset Segment) (S : Segment) :=
  filter (fun L ↦ openHull L ⊆ openHull S) X

lemma segment_sum_splitting (A : Finset Segment) (AVOID : Set ℝ²) (X : Finset ℝ²)
    (hA : A ⊆ avoidingSegmentSet X AVOID)
    (hDisj : ∀ S T, S ∈ A → T ∈ A → S ≠ T → openHull S ∩ openHull T = ∅)
    (f : Segment → ℕ) (hfTwoMod : twoModFunction f) (hSymm : symmFun f) :
    (∑ S ∈ filter (fun S ↦ closedHull S ⊆ (⋃ T ∈ A, closedHull T))
      (basicAvoidingSegmentSet X AVOID), f S) % 4
    = (2 * ∑ T ∈ A, f T) % 4 := by
  have h_disj : (↑A : Set Segment).PairwiseDisjoint
    (fun T ↦ (filter (fun S ↦ closedHull S ⊆ closedHull T) (basicAvoidingSegmentSet X AVOID)))
      := by
    intro S hS T hT hST Y hY h
    have hDisj2 := hDisj S T hS hT hST
    simp_all only [mem_coe, ne_eq, le_eq_subset, bot_eq_empty, subset_empty]
    have h_nontriv : ∀ L ∈ Y, L 0 ≠ L 1 := by
      intro L hL
      apply @segmentSet_vertex_distinct X L
      have hY_segmentSet : Y ⊆ segmentSet X := by
        calc Y ⊆ filter (fun S_1 ↦ closedHull S_1 ⊆ closedHull S)
              (basicAvoidingSegmentSet X AVOID) := hY
             _ ⊆ basicAvoidingSegmentSet X AVOID := by exact filter_subset _ _
             _ ⊆ avoidingSegmentSet X AVOID := by exact filter_subset _ _
             _ ⊆ segmentSet X := by exact filter_subset _ _
      exact hY_segmentSet hL
    have hLS : ∀ L ∈ Y, openHull L ⊆ openHull S := by
      intro L hL
      apply open_segment_sub'
      · have h2 := hY hL
        rw [mem_filter] at h2
        exact h2.right
      · exact h_nontriv L hL
    have hLT : ∀ L ∈ Y, openHull L ⊆ openHull T := by
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
      have hNonEmpty : openHull L ≠ ∅ := by
        simp_all only [ne_eq]
        obtain ⟨w, h_1⟩ := open_pol_nonempty (by linarith) L
        intro a
        simp_all only [Set.mem_empty_iff_false]
      have hEmpty : openHull L ⊆ ∅ := by
        calc openHull L ⊆ openHull S ∩ openHull T := by
                exact Set.subset_inter_iff.mpr ⟨(hLS L hL), (hLT L hL)⟩
          _ = ∅ := by exact hDisj S T hS hT hST
      simp_all only [ne_eq, Set.subset_empty_iff]
    · tauto
  have h_eq : filter (fun S ↦ closedHull S ⊆ (⋃ T ∈ A, closedHull T))
      (basicAvoidingSegmentSet X AVOID) =
      Finset.disjiUnion A
        (fun T ↦ (filter (fun S ↦ closedHull S ⊆ closedHull T)
          (basicAvoidingSegmentSet X AVOID)))
        h_disj
      := by
    ext L
    rw [mem_filter, Finset.mem_disjiUnion]
    constructor
    · intro hL
      simp_all only [mem_filter, true_and]
      apply closed_segment_sub_union_segment
          (segmentSet_vertex_distinct (basicAvoidingSegmentSet_sub hL.1)) hL.2
      intro S hSA
      rw [Set.disjoint_right]
      intro y hyb hopen
      have hyX := segmentSet_boundary (X := X) ?_ hyb
      · have hLAvoid := hL.1
        simp only [basicAvoidingSegmentSet, mem_filter] at hLAvoid
        exact hLAvoid.2 y hyX hopen
      · refine avoidingSegmentSet_sub (A := AVOID) (hA ?_)
        simp_all only [ne_eq]
    · intro hL
      obtain ⟨S, hS⟩ := hL
      constructor
      · simp_all only [mem_filter]
      · rw [mem_filter] at hS
        have h : closedHull S ⊆ ⋃ T ∈ A, closedHull T := by
          refine Set.subset_biUnion_of_mem ?_
          exact hS.1
        tauto_set
  rw [h_eq]
  rw [Finset.sum_disjiUnion A
    (fun T ↦ (filter (fun S ↦ closedHull S ⊆ closedHull T) (basicAvoidingSegmentSet X AVOID)))
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
noncomputable def squareBoundaryBasic (Δ : Finset Triangle) : Fin 4 → Finset Segment :=
  fun i ↦ filter (fun S ↦ openHull S ⊆ openHull (squareBoundaryBig i))
    (triangulationBoundaryBasicSegments Δ)

lemma unitSquare_boundary_decomposition (Δ : Finset Triangle) (hCovering : isTriangulation Δ) :
    triangulationBoundaryBasicSegments Δ =
    @Finset.biUnion (Fin 4) Segment _ ⊤ (squareBoundaryBasic Δ)
    := by
  ext S
  constructor
  · intro hS
    simp only [triangulationBoundaryBasicSegments, mem_filter] at hS
    have ⟨i, hi⟩ := openHull_segment_in_boundary (S := S) hS.2 ?_
    · rw [mem_biUnion]
      use i, by simp only [top_eq_univ, mem_univ]
      simp only [squareBoundaryBasic, mem_filter, triangulationBoundaryBasicSegments]
      refine ⟨hS,?_⟩
      apply open_segment_sub' hi
      simp only [triangulationBasicSegments, basicAvoidingSegmentSet, avoidingSegmentSet,
        mem_filter] at hS
      exact segmentSet_vertex_distinct hS.1.1.1
    · apply closedHull_convex
      intro i
      simp only [triangulationBasicSegments, basicAvoidingSegmentSet, avoidingSegmentSet,
        mem_filter, segmentSet] at hS
      have this := hS.1.1.1
      simp only [ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product, Prod.exists] at this
      have ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, hS⟩ := this
      simp only [isTriangulation, isCover, SetLike.mem_coe] at hCovering
      have hSub : (↑(triangulationPoints Δ) : Set ℝ²) ⊆ (closedHull unitSquare) := by
        rw [hCovering]
        intro x hx
        simp only [triangulationPoints, Fin.isValue, coe_biUnion, mem_coe, coe_insert,
          coe_singleton, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff,
          exists_prop] at hx
        have ⟨T,hT, hp⟩ := hx
        rw [Set.mem_iUnion₂]
        use T, hT
        rcases hp with hp | hp
        · rw [hp]
          exact corner_in_closedHull
        · obtain hp | hp := hp <;> (rw [hp]; exact corner_in_closedHull)
      rw [←hS]
      fin_cases i <;> (simp only [toSegment])
      · exact hSub ha
      · exact hSub hb
  · intro hS
    simp only [top_eq_univ, mem_biUnion, mem_univ, squareBoundaryBasic, mem_filter, true_and,
      exists_and_left] at hS
    have ⟨h, ⟨i, hi⟩⟩ := hS
    simp only [triangulationBoundaryBasicSegments, mem_filter]
    refine ⟨?_,?_⟩
    · simp only [triangulationBoundaryBasicSegments, mem_filter] at h
      exact h.1
    · trans openHull (squareBoundaryBig i)
      · exact hi
      · trans closedHull (squareBoundaryBig i)
        · exact open_sub_closed _
        · exact square_boundary_segments_in_boundary i




lemma unitSquare_cover_segmentSet
    {S : Finset Triangle}
    (hCover : isCover (closedHull unitSquare) (↑S : Set Triangle)) :
    ∀ {i}, squareBoundaryBig i ∈ segmentSet (triangulationPoints S) := by
  intro i
  rw [segmentSet]
  simp only [ne_eq, product_eq_sprod, mem_image, mem_filter, mem_product, Prod.exists]
  use squareBoundaryBig i 0, squareBoundaryBig i 1
  simp only [Fin.isValue, segment_rfl, and_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · have ⟨k,hk⟩ := squareBoundaryBig_corners i 0
    rw [hk]
    have ⟨T,hT,⟨j,Tj⟩ ⟩  := cover_imples_corner_in_triangle hCover k
    rw [Tj]
    exact triangulationPoints_mem hT _
  · have ⟨k,hk⟩ := squareBoundaryBig_corners i 1
    rw [hk]
    have ⟨T,hT,⟨j,Tj⟩ ⟩  := cover_imples_corner_in_triangle hCover k
    rw [Tj]
    exact triangulationPoints_mem hT _
  · exact square_boundary_sides_nonDegen i

lemma unitSquare_boundary_intersections (i j : Fin 4) (h_neq : i ≠ j) :
    openHull (squareBoundaryBig i) ∩ openHull (squareBoundaryBig j) = ∅ := by
  ext x
  have hh2help : 1 < 2 := by norm_num
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1
  unfold squareBoundaryBig at *
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


lemma purple_computation0 (i : Fin 4) : i ≠ 0 → isPurple v (squareBoundaryBig i) = 0 := by
  have hR : coloring v !₂[0, 0] = Color.Red := red00 v
  have hB1 : coloring v !₂[1, 0] = Color.Blue := blue10 v
  have hB2 : coloring v !₂[1, 1] = Color.Blue := blue11 v
  have hG : coloring v !₂[0, 1] = Color.Green := green01 v
  unfold isPurple squareBoundaryBig
  intro hi
  fin_cases i
  · tauto
  · simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_and]
    simp_all [LeanPool.Monsky.v]
  · simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_and]
    simp_all [LeanPool.Monsky.v]
  · simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_and]
    simp_all [LeanPool.Monsky.v]

lemma purple_computation1 : isPurple v (squareBoundaryBig 0) = 1 := by
  unfold isPurple squareBoundaryBig
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
    (non_degen : det T ≠ 0) (hCovering : isTriangulation Δ) :
    openHull T ⊆ openHull unitSquare := by
  by_contra h
  have h_inc : openHull T ⊆ closedHull unitSquare := by
      unfold isTriangulation at hCovering
      exact subset_trans (open_sub_closed T) (@isCover_sub _ Δ _ (id hCovering) T hT)
  have hp : ∃ p : ℝ², p ∈ openHull T ∧ p ∈ boundary unitSquare := by
    obtain ⟨p, hp⟩ := Set.not_subset.mp h
    use p
    refine ⟨hp.left, ?_⟩
    unfold boundary
    rw [Set.mem_sdiff]
    exact ⟨by tauto, hp.right⟩
  obtain ⟨p, hp⟩ := hp
  obtain ⟨σ, hσ⟩ := (boundary_leave_dir hp.2)
  obtain ⟨ε, hε⟩ := (@triangle_openHull_open _ non_degen _ (σ • (!₂[1, 1] : ℝ²)) hp.1)
  have h1 : p + ε • σ • (!₂[1, 1] : ℝ²) ∉ closedHull unitSquare := by
    have hrw : p + ε • σ • (!₂[1, 1] : ℝ²) = p + (σ * ε) • (!₂[1, 1] : ℝ²) := by
      module
    rw [hrw]
    exact (hσ.right ε hε.left)
  tauto


theorem segment_sum_odd (Δ : Finset Triangle) (hCovering : isTriangulation Δ)
    (non_degen : ∀ P ∈ Δ, det P ≠ 0) :
    purpleSum v Δ % 4 = 2 := by
  -- Strategy: show that triangulationBoundaryBasicSegments Δ is the disjoint union over the
  -- segments contained in the four sides of the squares. Then for each side, use that the purple
  -- sum mod 4 is just 2 times the value of IsPurple of the whole segment.
  unfold purpleSum
  have h : ∑ S ∈ triangulationBoundaryBasicSegments Δ, isPurple v S =
      ∑ S ∈ filter (fun S ↦ closedHull S ⊆ (⋃ T ∈ squareBoundaryBigSet, closedHull T))
        (basicAvoidingSegmentSet (triangulationPoints Δ) (triangulationAvoidingSet Δ)),
        isPurple v S := by
    rw [sum_congr]
    · rw [unitSquare_boundary_decomposition Δ hCovering]
      unfold squareBoundaryBasic squareBoundaryBigSet triangulationBoundaryBasicSegments
      unfold triangulationBasicSegments
      simp_all only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and, Set.iUnion_exists]
      ext S
      constructor
      · intro hS
        simp_all only [mem_biUnion, mem_univ, mem_filter, true_and, exists_and_left]
        obtain ⟨j, hj⟩ := hS.right
        have h_closed : closedHull S ⊆ closedHull (squareBoundaryBig j) := by
          exact open_sub_closed_sub _ _ hj
        suffices h2 : closedHull (squareBoundaryBig j) ⊆
          ⋃ T, ⋃ i, ⋃ (_ : T = squareBoundaryBig i), closedHull (squareBoundaryBig i) by
          tauto_set
        intro x hx
        simp only [Set.mem_iUnion, exists_prop]
        use squareBoundaryBig j
        use j
      · intro hS
        simp_all only [mem_filter, mem_biUnion, mem_univ, true_and, exists_and_left]
        have hClosedSinBoundary : closedHull S ⊆ boundary unitSquare := by
          have hBoundary : ∀ i : Fin 4,
              closedHull (squareBoundaryBig i) ⊆ boundary unitSquare := by
              exact square_boundary_segments_in_boundary
          have hUnion : ⋃ T, ⋃ i, ⋃ (_ : T = squareBoundaryBig i),
              closedHull (squareBoundaryBig i)
              ⊆ boundary unitSquare := by
            simp only [Set.iUnion_subset_iff]
            intro T i hT
            exact hBoundary i
          calc closedHull S ⊆ ⋃ T, ⋃ i, ⋃ (_ : T = squareBoundaryBig i),
                closedHull (squareBoundaryBig i) := by exact hS.2
                           _ ⊆ boundary unitSquare := by exact hUnion
        have hopenSinBoundary : openHull S ⊆ boundary unitSquare := by
          have hInc : openHull S ⊆ closedHull S := open_sub_closed S
          suffices h : closedHull S ⊆ boundary unitSquare by
            tauto_set
          exact hClosedSinBoundary
        refine ⟨hopenSinBoundary, ?_⟩
        apply unitSquare_is_convex_open
        · exact hClosedSinBoundary
        · unfold basicAvoidingSegmentSet avoidingSegmentSet segmentSet at hS
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
  have h1 : squareBoundaryBigSet ⊆
      avoidingSegmentSet (triangulationPoints Δ) (triangulationAvoidingSet Δ) := by
    unfold avoidingSegmentSet
    have h_triangle_avoiding_set : (triangulationAvoidingSet Δ) ⊆ openHull unitSquare := by
      unfold triangulationAvoidingSet
      simp only [Set.iUnion_subset_iff]
      intro T hT
      exact (open_triangle_in_open_square hT (non_degen T hT) hCovering)
    have h_square_boundary : ∀ L ∈ squareBoundaryBigSet,
        closedHull L ⊆ boundary unitSquare := by
      intro L hL
      unfold squareBoundaryBigSet at hL
      simp only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and] at hL
      obtain ⟨i, hi⟩ := hL
      rw [hi]
      exact square_boundary_segments_in_boundary i
    intro S hS
    rw [mem_filter]
    constructor
    · -- I think this needs that the triangulation points of a covering must include
      -- the corners of the square.
      rw [squareBoundaryBigSet, mem_biUnion] at hS
      have ⟨_, _, hST⟩ := hS
      rw [mem_singleton] at hST
      rw [hST]
      exact unitSquare_cover_segmentSet hCovering
    · suffices h_disj : Disjoint (boundary unitSquare) (openHull unitSquare) by
        tauto_set
      unfold boundary
      tauto_set
  have h2 : ∀ S L, S ∈ (squareBoundaryBigSet) → L ∈ (squareBoundaryBigSet) → S ≠ L →
      openHull S ∩ openHull L = ∅ := by
    unfold squareBoundaryBigSet
    intro S L hS hL hSL
    simp_all only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and]
    obtain ⟨i, hi⟩ := hS
    obtain ⟨j, hj⟩ := hL
    rw [hi, hj]
    have hij : i ≠ j := by
      by_contra h_contra
      rw [hi, hj, h_contra] at hSL
      tauto
    exact unitSquare_boundary_intersections i j hij
  rw [segment_sum_splitting squareBoundaryBigSet (triangulationAvoidingSet Δ)
    (triangulationPoints Δ) h1 h2 (isPurple v) (isPurple_twoModFunction v)
    (isPurple_symmFunction v)]
  unfold squareBoundaryBigSet
  have hTop : (⊤ : Finset (Fin 4)) = {0, 1, 2, 3} := by rfl
  have hDisjSum : (⊤ : Finset (Fin 4)).biUnion (fun i ↦ {squareBoundaryBig i}) =
      Finset.disjiUnion (⊤ : Finset (Fin 4)) (fun i ↦ {squareBoundaryBig i}) ?_ := by
    refine Eq.symm (disjiUnion_eq_biUnion ⊤ (fun i ↦ {squareBoundaryBig i}) ?_)
    intro i _ j _ hij
    simp only [disjoint_singleton_right, mem_singleton]
    intro heq
    exact hij.symm (squareBoundaryBig_injective heq)
  · intro i _ j _ hij
    simp only [disjoint_singleton_right, mem_singleton]
    intro heq
    exact hij.symm (squareBoundaryBig_injective heq)
  rw [hDisjSum, sum_disjiUnion]
  simp only [top_eq_univ, sum_singleton]
  simp_all only [ne_eq, top_eq_univ, Fin.isValue, biUnion_insert, singleton_biUnion,
    disjiUnion_eq_biUnion, mem_insert, zero_ne_one, Fin.reduceEq, mem_singleton, or_self,
    not_false_eq_true, sum_insert, sum_singleton]
  rw [purple_computation1]
  repeat rw [purple_computation0]
  · ring
  all_goals decide


theorem segment_sum_rainbowTriangle (Δ : Finset Triangle) :
    rainbowSum v Δ = (rainbowTriangles v Δ).card := by
  unfold rainbowSum rainbowTriangles isRainbow
  simp only [sum_boole, Nat.cast_id, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]


/-- The basic segments of a triangulation lying on the boundary of triangle `T`. -/
noncomputable def triangleBasicBoundary (Δ : Finset Triangle) (T : Triangle) :=
    {S ∈ triangulationBasicSegments Δ | closedHull S ⊆ boundary T}

lemma triangle_edges_disjoint (T : Triangle) (i j : Fin 3) (h : i ≠ j) (hdet : det T ≠ 0) :
    Disjoint (openHull (Tside T i))  (openHull (Tside T j)) := by
  by_contra h1
  rw [@Set.not_disjoint_iff] at h1
  rcases h1 with ⟨x ,hi,hj ⟩
  have hx  := closed_side_sub (open_sub_closed _ hi)
  rw[←  mem_open_side hdet hx i] at hi
  rw[←  mem_open_side hdet hx j] at hj
  exact Ne.symm (ne_of_lt (hj.2 i h)) hi.1

lemma triangleBoundary_decomposition {Δ : Finset Triangle} {T : Triangle} (hdet : det T ≠ 0)
    (h : T ∈ Δ) :
    triangleBasicBoundary Δ T =
    @Finset.biUnion (Fin 3) Segment _ ⊤
      (fun i ↦ (basicSegmentSegments (triangleBasicBoundary Δ T) (Tside T i)))
    := by
    ext S
    constructor
    · intro hS
      unfold triangleBasicBoundary at hS
      rw [mem_filter] at hS
      rcases hS with ⟨α, hα ⟩
      rw [boundary_is_union_sides hdet] at hα
      have TsideS : ∃ i : Fin 3, closedHull S ⊆ closedHull (Tside T i) := by
        unfold triangulationBasicSegments at α
        unfold basicAvoidingSegmentSet at α
        rw [mem_filter] at α
        unfold avoidingSegmentSet at α
        rw [mem_filter] at α
        rcases α with ⟨δ, hδ⟩
        rcases δ with ⟨η, hη⟩
        unfold triangulationAvoidingSet at hη
        have xopoenhullS : ∃ x, x ∈ openHull S := by
          apply open_pol_nonempty
          linarith
        rcases xopoenhullS with ⟨x, hx⟩
        have xclosedhullS : x ∈ closedHull S := by
          exact open_sub_closed S hx
        have xinboundaryT : x ∈ boundary T := by
          rw [boundary_is_union_sides hdet]
          apply hα at xclosedhullS
          exact xclosedhullS
        have xinTsideopen: ∃ i : Fin 3, x ∈ openHull (Tside T i) := by
          apply el_in_boundary_imp_side
          · apply hdet
          · apply xinboundaryT
          · by_contra hcontra
            simp only [ne_eq, not_forall, Decidable.not_not] at hcontra
            rcases hcontra with ⟨i, hi⟩
            have hcontra' : x ∈ triangulationPoints Δ := by
              unfold triangulationPoints
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
          have nonemp' : Set.Nonempty (openHull T ∩ closedHull S) := by
            exact Set.nonempty_iff_ne_empty.mpr hcontra
          have nonempt : ∃ z,  z ∈ openHull T ∧ z ∈ closedHull S := by
            exact nonemp'
          rcases nonempt with ⟨z, hz⟩
          simp only [Set.disjoint_iUnion_right] at hη
          specialize hη T
          tauto_set
        · by_contra hcontra
          simp only [not_forall, Decidable.not_not] at hcontra
          rcases hcontra with ⟨j, hj⟩
          have tj : T j ∈ triangulationPoints Δ := by
            unfold triangulationPoints
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
      unfold basicSegmentSegments
      rw [mem_filter]
      constructor
      · unfold triangleBasicBoundary
        rw [mem_filter]
        constructor
        · apply α
        · have this : closedHull (Tside T i)  ⊆ boundary T := by
            apply side_in_boundary hdet
          tauto_set
      · apply open_segment_sub'
        · apply hi
        · unfold triangulationBasicSegments at α
          unfold basicAvoidingSegmentSet at α
          rw [mem_filter] at α
          unfold avoidingSegmentSet at α
          rw [mem_filter] at α
          rcases α with ⟨β, hβ⟩
          rcases β with ⟨γ, hγ ⟩
          apply segmentSet_vertex_distinct
          apply γ
    · intro hS
      simp_all only [ne_eq, top_eq_univ, mem_biUnion, mem_univ, true_and]
      rcases hS with ⟨a, ha⟩
      unfold basicSegmentSegments at ha
      rw [mem_filter] at ha
      apply ha.1


/-- The three sides of a triangle `T`, as a set of segments. -/
noncomputable def triangleBoundary (T : Triangle) := Finset.biUnion ⊤ (fun i ↦ {Tside T i})

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

lemma rainbowTriangle_purpleSum {Δ : Finset Triangle}
    (non_degen : ∀ P ∈ Δ, det P ≠ 0)
    (hDisjointCover : isDisjointCover (closedHull unitSquare) (↑Δ : Set Triangle))
    : ∀ T ∈ Δ,
    2 * isRainbow v T % 4 = (∑ (S ∈ triangleBasicBoundary Δ T), isPurple v S) % 4 := by
  intro T hT
  have h : triangleBasicBoundary Δ T =
      filter (fun S ↦ closedHull S ⊆ (⋃ L ∈ triangleBoundary T, closedHull L))
        (basicAvoidingSegmentSet (triangulationPoints Δ) (triangulationAvoidingSet Δ)) := by
    rw [triangleBoundary_decomposition (non_degen T hT) hT]
    unfold triangleBoundary
    ext S
    constructor
    · intro h
      rw [mem_filter]
      rw [mem_biUnion] at h
      obtain ⟨i, hi⟩ := h
      constructor
      · unfold basicSegmentSegments at hi
        unfold triangleBasicBoundary at hi
        unfold triangulationBasicSegments at hi
        simp_all only [ne_eq, top_eq_univ, mem_univ, mem_filter, true_and]
      · simp_all only [ne_eq, top_eq_univ, mem_univ, true_and, mem_biUnion, mem_singleton,
          Set.iUnion_exists]
        unfold basicSegmentSegments at hi
        rw [mem_filter] at hi
        have h1 : closedHull S ⊆ closedHull (Tside T i) :=
          (open_sub_closed_sub S (Tside T i) hi.right)
        have h2 : closedHull (Tside T i) ⊆
            ⋃ L, ⋃ i, ⋃ (_ : L = Tside T i), closedHull (Tside T i) := by
          apply (Set.subset_iUnion_of_subset (Tside T i))
          apply (Set.subset_iUnion_of_subset i)
          simp only [Set.iUnion_true, subset_refl]
        calc closedHull S ⊆ closedHull (Tside T i) := by exact h1
                         _ ⊆ ⋃ L, ⋃ i, ⋃ (_ : L = Tside T i), closedHull (Tside T i) := by exact h2
    · simp only [top_eq_univ, mem_biUnion, mem_univ, mem_singleton, true_and, Set.iUnion_exists,
      mem_filter, and_imp]
      intro hS1 hS2
      unfold basicSegmentSegments
      simp only [mem_filter, exists_and_left]
      have hBoundaryIncl : closedHull S ⊆ boundary T := by
        have hInc : ⋃ L, ⋃ i, ⋃ (_ : L = Tside T i), closedHull L ⊆ boundary T := by
          simp only [Set.iUnion_subset_iff, forall_eq_apply_imp_iff]
          intro i
          exact (side_in_boundary (non_degen T hT) i)
        tauto_set
      constructor
      · unfold triangleBasicBoundary triangulationBasicSegments
        rw [mem_filter]
        refine ⟨hS1, ?_⟩
        exact hBoundaryIncl
      · obtain ⟨i, hi⟩ := segment_in_boundary_imp_in_side (non_degen T hT) hBoundaryIncl
        use i
        apply open_segment_sub' hi
        unfold basicAvoidingSegmentSet avoidingSegmentSet segmentSet at hS1
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
  have h1 : (triangleBoundary T) ⊆
      avoidingSegmentSet (triangulationPoints Δ) (triangulationAvoidingSet Δ) := by
    unfold triangleBoundary avoidingSegmentSet
    simp only [top_eq_univ, biUnion_subset_iff_forall_subset, mem_univ, singleton_subset_iff,
      mem_filter, forall_const]
    intro i
    constructor
    · unfold segmentSet
      simp only [product_eq_sprod, mem_image, mem_filter, mem_product, Prod.exists]
      use (Tside T i) 0, (Tside T i 1)
      simp only [Fin.isValue, segment_rfl, and_true]
      unfold triangulationPoints
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
    · unfold triangulationAvoidingSet
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
  have h2 : ∀ S L, S ∈ (triangleBoundary T) → L ∈ (triangleBoundary T) → S ≠ L →
      openHull S ∩ openHull L = ∅ := by
    intro S L hS hL hSL
    unfold triangleBoundary at hS hL
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
  rw [segment_sum_splitting (triangleBoundary T) (triangulationAvoidingSet Δ)
    (triangulationPoints Δ) h1 h2 (isPurple v) (isPurple_twoModFunction v)
    (isPurple_symmFunction v)]
  unfold triangleBoundary
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
    suffices hs : ¬ Tside T j 0 = Tside T i 0 by
      by_contra h_contra
      exact hs (congrFun h_contra.symm 0)
    unfold Tside
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
    filter (fun S ↦ closedHull S ⊆ boundary T) (triangulationBoundaryBasicSegments Δ ∪
        triangulationInteriorBasicSegments Δ) =
    filter (fun S ↦ closedHull S ⊆ boundary T) (triangulationBoundaryBasicSegments Δ) ∪
        filter (fun S ↦ closedHull S ⊆ boundary T) (triangulationInteriorBasicSegments Δ) := by
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
    filter (fun S ↦ closedHull S ⊆ boundary T.val) (triangulationBoundaryBasicSegments Δ) ∩
        filter (fun S ↦ closedHull S ⊆ boundary T.val)
          (triangulationInteriorBasicSegments Δ) = ∅ := by
  ext x
  constructor
  · intro h
    simp only [mem_inter, mem_filter] at h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨h1, h1'⟩
    rcases h2 with ⟨h2, h2'⟩
    have int : triangulationBoundaryBasicSegments Δ ∩
        triangulationInteriorBasicSegments Δ = ∅ := by
      exact triangulation_boundary_intersection Δ
    rw [← int]
    simp only [mem_inter]
    constructor
    · exact h1
    · exact h2
  tauto


/-lemma reverse_openHull_basic (Δ : Finset Triangle) (S : Segment) :
    S ∈ triangulationBasicSegments Δ ↔ reverseSegment S ∈ triangulationBasicSegments Δ := by
  sorry

lemma interior_iff_reverse_interior (Δ : Finset Triangle) (S : Segment) :
    S ∈ triangulationInteriorBasicSegments Δ ↔
      reverseSegment S ∈ triangulationInteriorBasicSegments Δ := by
  unfold triangulationInteriorBasicSegments
  repeat rw [mem_filter]
  constructor <;> intro a <;> obtain ⟨left, right⟩ := a
  · rw [← reverse_openHull_basic, reverseSegment_openHull]
    exact ⟨left, right⟩
  · rw [reverse_openHull_basic, ← reverseSegment_openHull]
    exact ⟨left, right⟩-/

/-- The open hulls of the interior basic segments of a triangulation. -/
def triangulationInteriorBasicSegmentsHulls (Δ : Finset Triangle) :=
  {openHull S | S ∈ triangulationInteriorBasicSegments Δ}


lemma basic_seg_non_degenerate {Δ : Finset Triangle} {S : Segment}
    (h : S ∈ triangulationBasicSegments Δ) : S 0 ≠ S 1 :=
  segmentSet_vertex_distinct (basicAvoidingSegmentSet_sub h)


theorem interior_purpleSum (Δ : Finset Triangle) :
    (∑ (S ∈ triangulationInteriorBasicSegments Δ), isPurple v S) % 2 = 0 % 2 := by
  rw [←Int.natCast_inj, Int.natCast_mod, Int.natCast_mod, ←ZMod.intCast_eq_intCast_iff']
  simp only [Nat.cast_sum, Int.cast_sum, Int.cast_natCast, CharP.cast_eq_zero, Int.cast_zero]
  apply (Finset.sum_involution (fun x ↦ (fun y ↦ reverseSegment x)))
  · intro a ha
    rw [isPurple_symmFunction]
    exact CharTwo.add_self_eq_zero (↑(isPurple v a) : ZMod 2)
  · intro a ha h1
    by_contra h
    have h_eq : a 0 = a 1 := by
      unfold reverseSegment at h
      conv => left; rw [← h]
      unfold toSegment
      rfl
    unfold triangulationInteriorBasicSegments at ha
    rw [mem_filter] at ha
    apply basic_seg_non_degenerate ha.1
    exact h_eq
  · intro a ha
    unfold triangulationInteriorBasicSegments at *
    rw [mem_filter] at *
    constructor
    · unfold triangulationBasicSegments at *
      exact basicAvoidingSegmentSet_reverse ha.1
    · rw [reverseSegment_openHull]
      exact ha.right
  · intro a ha
    exact reverseSegment_involution


/-- Indicator of whether a segment lies on the boundary of the unit square. -/
noncomputable def boundaryIndicator (T : Triangle) (S : Segment) :=
    if (closedHull S ⊆ boundary T) then 1 else 0

lemma triangleBasicBoundary_indicator_rw {Δ : Finset Triangle} (T : Triangle) {f : Segment → ℕ} :
    ∑ S ∈ triangleBasicBoundary Δ T, f S =
    ∑ S ∈ triangulationBasicSegments Δ, (f S) * boundaryIndicator T S := by
  unfold triangleBasicBoundary
  rw [sum_filter]
  congr
  simp [boundaryIndicator]

lemma open_triangle_segment (Δ : Finset Triangle) (S : Segment)
    (hS : S ∈ triangulationBasicSegments Δ) :
    ∀ T ∈ Δ, openHull T ∩ closedHull S = ∅ := by
  unfold triangulationBasicSegments triangulationAvoidingSet basicAvoidingSegmentSet
    avoidingSegmentSet at hS
  intro T hT
  simp only [Set.disjoint_iUnion_right, mem_filter] at hS
  rw [← Set.disjoint_iff_inter_eq_empty]
  apply Disjoint.symm
  exact hS.1.2 T hT

lemma split_segment_sum (Δ : Finset Triangle)
  (hDisjointCover : isDisjointCover (closedHull unitSquare) (↑Δ : Set Triangle))
 (f : Segment → ℕ) (non_degen : ∀ P ∈ Δ, det P ≠ 0)
    : ∑ T ∈ Δ, ∑ (S ∈ triangleBasicBoundary Δ T), f S =
    ∑ (S ∈ triangulationBoundaryBasicSegments Δ), f S +
    2 * ∑ (S ∈ triangulationInteriorBasicSegments Δ), f S := by
  simp_rw [triangleBasicBoundary_indicator_rw]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  rw [triangulation_boundary_union _ hDisjointCover.1 non_degen, Finset.sum_union ?_]
  · congr 1
    · rw [sum_congr rfl]
      intro S hS
      nth_rewrite 2 [←mul_one (f S)]
      congr
      simp_rw [boundaryIndicator, ←Finset.card_filter]
      refine segment_triangle_pairing_boundary Δ hDisjointCover non_degen S ?_ ?_ ?_ ?_
      · apply segmentSet_vertex_distinct (X := triangulationPoints Δ)
        refine basicAvoidingSegmentSet_sub (A := (triangulationAvoidingSet Δ)) ?_
        exact mem_of_mem_filter S hS
      · have h2 : S ∈ triangulationBasicSegments Δ := by
          unfold triangulationBoundaryBasicSegments at hS
          exact Finset.filter_subset (fun S ↦ openHull S ⊆ boundary unitSquare)
            (triangulationBasicSegments Δ) hS
        exact open_triangle_segment Δ S h2
      · simp only [triangulationBoundaryBasicSegments, mem_filter] at hS
        exact hS.2
      · intro T hT
        simp only [triangulationBoundaryBasicSegments, mem_filter,
          triangulationBasicSegments, basicAvoidingSegmentSet] at hS
        intro _
        refine hS.1.2 ?_ ?_
        exact triangulationPoints_mem hT _
    · rw [mul_sum, sum_congr rfl]
      intro S hS
      rw [mul_comm]
      congr
      simp_rw [boundaryIndicator, ←Finset.card_filter]
      refine segment_triangle_pairing_int Δ hDisjointCover non_degen S ?_ ?_ ?_
      · have h2 : S ∈ triangulationBasicSegments Δ := by
          unfold triangulationInteriorBasicSegments at hS
          exact Finset.filter_subset (fun S ↦ openHull S ⊆ openHull unitSquare)
            (triangulationBasicSegments Δ) hS
        exact open_triangle_segment Δ S h2
      · simp only [triangulationInteriorBasicSegments, mem_filter] at hS
        exact hS.2
      · intro T hT
        simp only [triangulationInteriorBasicSegments, mem_filter,
          triangulationBasicSegments, basicAvoidingSegmentSet] at hS
        intro _
        refine hS.1.2 ?_ ?_
        exact triangulationPoints_mem hT _
  · rw [Finset.disjoint_iff_inter_eq_empty]
    exact triangulation_boundary_intersection Δ

theorem rainbowSum_is_purpleSum (Δ : Finset Triangle)
    (hDisjointCover : isDisjointCover (closedHull unitSquare) (↑Δ : Set Triangle))
    (non_degen : ∀ P ∈ Δ, det P ≠ 0) :
    2 * rainbowSum v Δ % 4 = purpleSum v Δ % 4 := by
  /-
    Split the rainbowSum to a sum over all basic segments. One can then sum over all segments first
    or over all triangles first.
  -/
  unfold rainbowSum purpleSum
  rw [mul_sum, sum_nat_mod]
  rw [sum_congr rfl (rainbowTriangle_purpleSum v non_degen hDisjointCover) , ←sum_nat_mod]
  rw [split_segment_sum Δ hDisjointCover (isPurple v) non_degen]
  have h : (2 * ∑ (S ∈ triangulationInteriorBasicSegments Δ), isPurple v S) % 4 = 0 := by
    exact mod_two_mul (interior_purpleSum v Δ)
  rw [Nat.add_mod, h, add_zero, Nat.mod_mod]

theorem monsky_rainbow (Δ : Finset Triangle)
    (hDisjointCover : isDisjointCover (closedHull unitSquare) (↑Δ : Set Triangle))
    (non_degen : ∀ P ∈ Δ, det P ≠ 0)
    : ∃ T ∈ Δ, rainbowTriangle v T := by
  have this := rainbowSum_is_purpleSum v _ hDisjointCover non_degen
  rw [segment_sum_odd v _ hDisjointCover.1 non_degen] at this
  have hf : rainbowSum v Δ ≠ 0 := by
    intro hc
    rw [hc] at this
    simp only [mul_zero, Nat.zero_mod, OfNat.zero_ne_ofNat] at this
  simp_rw [rainbowSum, isRainbow, ←Finset.card_filter, card_ne_zero] at hf
  have ⟨T, hT⟩ := hf
  simp only [mem_filter] at hT
  refine ⟨T, hT.1, hT.2⟩

end Monsky
end LeanPool
