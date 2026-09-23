/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Subdivide
public import LeanPool.Schoenflies.SegmentOrder
public import LeanPool.Schoenflies.SegmentMeet
public import LeanPool.Schoenflies.Polygonal
public import LeanPool.Schoenflies.Graph.Drawing

/-!
# The polygonal overlay

Finitely many segments become a plane graph once they are subdivided at their meets and each
duplicated subsegment is named once (`lem:polygonal-overlay`).

## Blueprint

* `polygonal_overlay` — Lemma 3.7 (polygonal overlay).
-/

@[expose] public section

open Metric Set

namespace Schoenflies

/-! ### Two more properties of `subdivide`

Both belong in `Schoenflies/Subdivide.lean` beside the other four; they are here because that
module is on `main`.

`subdivide_subset` is `subdivide_interior_subset` with the **closed** inclusion carried
alongside the open one, in one existential: separation reads a piece's ends off its source
segment and its interior off the source's interior, and it needs both at the same source.

`subdivide_ends` is the endpoint criterion — an end of a piece that is not a cut point was an
end all along. Without it the case of two pieces from different sources does not close: two
different subpieces can both sit inside one long overlap. -/

/-- Cutting one piece keeps each half inside the whole, closed and open at once. -/
theorem splitAt_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact ⟨(convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hp,
        openSegment_left_subset h⟩
    · rcases List.mem_singleton.1 hQ with rfl
      exact ⟨(convex_segment P.1 P.2).segment_subset hp (right_mem_segment ℝ _ _),
        openSegment_right_subset h⟩
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact ⟨subset_rfl, subset_rfl⟩

theorem splitAllAt_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_subset p P Q hQP⟩

/-- Every piece of a subdivision lies inside a piece it came from, both as a segment and as an
interior — and at the **same** source. -/
theorem subdivide_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR, hQR'⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP, hRP'⟩ := splitAllAt_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP, hQR'.trans hRP'⟩

/-- Cutting one piece introduces only the cut point as a new end. -/
theorem splitAt_ends (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, ∀ z, (z = Q.1 ∨ z = Q.2) → z = p ∨ (z = P.1 ∨ z = P.2) := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ z hz
    rcases List.mem_cons.1 hQ with rfl | hQ
    · rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · rcases List.mem_singleton.1 hQ with rfl
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
  · intro Q hQ z hz
    rcases List.mem_singleton.1 hQ with rfl
    exact Or.inr hz

theorem splitAllAt_ends (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z = p ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  intro Q hQ z hz
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  rcases splitAt_ends p P Q hQP z hz with h | h
  · exact Or.inl h
  · exact Or.inr ⟨P, hP, h⟩

/-- **The endpoint criterion.** An end of a piece of the subdivision is either a cut point or
was an end of a source piece all along. -/
theorem subdivide_ends (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z ∈ points ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ z hz => Or.inr ⟨Q, hQ, hz⟩
  | cons p ps ih =>
    intro Q hQ z hz
    rcases ih (pieces := splitAllAt p pieces) Q hQ z hz with h | ⟨R, hR, hzR⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases splitAllAt_ends p pieces R hR z hzR with rfl | ⟨P, hP, hzP⟩
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr ⟨P, hP, hzP⟩

/-! ### What the cut points have to cover

Two conditions, and between them they are the blueprint's "subdivide at all old endpoints,
isolated intersections, and endpoints of overlapping intervals". The second asks for **some**
pair of ends of each meet rather than every pair, because that is what a construction can
supply: a meet is `segment ℝ u v` and `segment ℝ v u` alike, and that a nondegenerate
segment's ends are determined by its point set is a theorem this development does not have and
does not need. -/

/-- Where two pieces meet. -/
def meetOf (P Q : Piece) : Set Plane := P.seg ∩ Q.seg

theorem meetOf_comm (P Q : Piece) : meetOf P Q = meetOf Q P := inter_comm _ _

/-- Every end of every source piece is a cut point. -/
def EndsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points

/-- For every pair of distinct source pieces that meet, some pair of ends of the meet is
cut. -/
def MeetsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ Q ∈ pieces, P ≠ Q → (meetOf P Q).Nonempty →
    ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points

/-- With the source ends cut too, the endpoint criterion says outright that every end of every
piece of the subdivision is a cut point. -/
theorem subdivide_ends_are_cuts {pieces : List Piece} {points : List Plane}
    (h : EndsAreCut pieces points) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) → z ∈ points := by
  intro Q hQ z hz
  rcases subdivide_ends pieces points Q hQ z hz with h' | ⟨P, hP, hzP⟩
  · exact h'
  · exact h P hP z hzP

/-! ### Producing the cut points

Nothing computes them. The overlay is stated existentially, so the list is built by the
induction that proves it exists, and `segment_inter_segment` hands over the ends of a meet the
moment the meet is known to be nonempty. That is what keeps the choice operator out: the
witnesses of `segment_inter_segment` are not unique, so there is nothing to name. -/

/-- One piece against a list: a point list holding both ends of every meet. -/
theorem exists_meet_points (P : Piece) (others : List Piece) :
    ∃ points : List Plane, ∀ Q ∈ others, (meetOf P Q).Nonempty →
      ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points := by
  induction others with
  | nil => exact ⟨[], by simp⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, htail⟩ := ih
    by_cases hR : (meetOf P R).Nonempty
    · obtain ⟨u, v, huv⟩ := segment_inter_segment P.1 P.2 R.1 R.2 hR
      refine ⟨u :: v :: tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨u, v, huv, by simp, by simp⟩
      · obtain ⟨s, t, hst, hs, ht⟩ := htail Q hQ hne
        exact ⟨s, t, hst, by simp [hs], by simp [ht]⟩
    · refine ⟨tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact absurd hne hR
      · exact htail Q hQ hne

/-- The whole list: the ends of each piece, and both ends of each meet. No sort and no choice
operator — the point list is existential throughout. -/
theorem exists_cut_points (pieces : List Piece) :
    ∃ points : List Plane, EndsAreCut pieces points ∧ MeetsAreCut pieces points := by
  induction pieces with
  | nil => exact ⟨[], by simp [EndsAreCut], by simp [MeetsAreCut]⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, hEnds, hMeets⟩ := ih
    obtain ⟨meetPoints, hHead⟩ := exists_meet_points R rs
    refine ⟨R.1 :: R.2 :: (meetPoints ++ tailPoints), fun P hP z hz => ?_,
      fun P hP Q hQ hPQ hne => ?_⟩
    · -- The head's two ends open the list; the tail's ends are already in `tailPoints`.
      rcases List.mem_cons.1 hP with rfl | hPt
      · rcases hz with rfl | rfl <;> simp
      · have := hEnds P hPt z hz
        simp [this]
    · -- A pair involving the head is covered by `meetPoints`, in whichever order it is asked
      -- for; a pair inside the tail was covered already.
      rcases List.mem_cons.1 hP with hPh | hPt
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · exact absurd (hPh.trans hQh.symm) hPQ
        · subst hPh
          obtain ⟨u, v, huv, hu, hv⟩ := hHead Q hQt hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · subst hQh
          have hne' : (meetOf Q P).Nonempty := by rwa [meetOf_comm]
          obtain ⟨u, v, huv, hu, hv⟩ := hHead P hPt hne'
          exact ⟨u, v, by rw [meetOf_comm]; exact huv, by simp [hu], by simp [hv]⟩
        · obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hPt Q hQt hPQ hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩

/-! ### Separation

Cut at every end of every source piece and at both ends of every meet, and two pieces of the
subdivision that share an interior point are the **same** segment — equal, not disjoint.
Overlapping collinear pieces cannot be pulled apart by cutting; after enough cuts they
coincide, which is what the blueprint's deduplication clause is for. -/

/-- Collinearity: two pieces of the subdivision that share an interior point lie inside one
nondegenerate segment. If they came from the same source piece, that piece; if from different
ones, the sources' overlap — nondegenerate because the shared point is interior to it, the
overlap's ends being cut points and so interior to nothing. -/
theorem subdivide_common_segment {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    ∃ A : Piece, A.Nondeg ∧ P.seg ⊆ A.seg ∧ Q.seg ⊆ A.seg := by
  obtain ⟨p, hp, hPseg, hPint⟩ := subdivide_subset pieces points P hP
  obtain ⟨q, hq, hQseg, hQint⟩ := subdivide_subset pieces points Q hQ
  by_cases hpq : p = q
  · subst hpq
    exact ⟨p, hnd p hp, hPseg, hQseg⟩
  -- The sources meet at `x`, so their meet is a segment with both ends cut.
  have hxp : x ∈ p.seg := openSegment_subset_segment ℝ _ _ (hPint hxP)
  have hxq : x ∈ q.seg := openSegment_subset_segment ℝ _ _ (hQint hxQ)
  obtain ⟨u, v, huv, hu, hv⟩ := hMeets p hp q hq hpq ⟨x, hxp, hxq⟩
  have hux : u ∉ P.interior := subdivide_avoids points hnd u hu P hP
  have hvx : v ∉ P.interior := subdivide_avoids points hnd v hv P hP
  have huy : u ∉ Q.interior := subdivide_avoids points hnd u hu Q hQ
  have hvy : v ∉ Q.interior := subdivide_avoids points hnd v hv Q hQ
  -- `x` is interior to the meet: it lies on it, and it is neither of its ends.
  have hxuv : x ∈ segment ℝ u v := huv ▸ ⟨hxp, hxq⟩
  have hxu : u ≠ x := fun h => hux (h ▸ hxP)
  have hxv : v ≠ x := fun h => hvx (h ▸ hxP)
  have hxopen : x ∈ openSegment ℝ u v := mem_openSegment_of_ne_left_right hxu hxv hxuv
  have huvne : u ≠ v := by
    rintro rfl
    rw [openSegment_same, mem_singleton_iff] at hxopen
    exact hxu hxopen.symm
  -- Both ends of the meet lie on both sources, so each one-dimensional citation has its
  -- ambient segment.
  have hsubp : segment ℝ u v ⊆ p.seg := huv ▸ inter_subset_left
  have hsubq : segment ℝ u v ⊆ q.seg := huv ▸ inter_subset_right
  refine ⟨(u, v), huvne, ?_, ?_⟩
  · exact segment_inside_of_ends_outside (hnd p hp)
      (hPseg (left_mem_segment ℝ _ _)) (hPseg (right_mem_segment ℝ _ _))
      (hsubp (left_mem_segment ℝ _ _)) (hsubp (right_mem_segment ℝ _ _))
      hxP hxopen hux hvx
  · exact segment_inside_of_ends_outside (hnd q hq)
      (hQseg (left_mem_segment ℝ _ _)) (hQseg (right_mem_segment ℝ _ _))
      (hsubq (left_mem_segment ℝ _ _)) (hsubq (right_mem_segment ℝ _ _))
      hxQ hxopen huy hvy

/-- **Separation.** Two pieces of the subdivision that share an interior point are the same
segment, in one order or the other. -/
theorem subdivide_separated {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    P = Q ∨ P = (Q.2, Q.1) := by
  -- Every end of every piece is a cut point, hence interior to nothing.
  have cut : ∀ R ∈ subdivide pieces points, ∀ z, (z = R.1 ∨ z = R.2) → z ∈ points :=
    subdivide_ends_are_cuts hEnds
  have h₁ : Q.1 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inl rfl)) P hP
  have h₂ : Q.2 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inr rfl)) P hP
  have h₃ : P.1 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inl rfl)) Q hQ
  have h₄ : P.2 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inr rfl)) Q hQ
  obtain ⟨A, hA, hPA, hQA⟩ := subdivide_common_segment hnd hMeets hP hQ hxP hxQ
  rcases same_ends_of_meeting_interiors hA
      (hPA (left_mem_segment ℝ _ _)) (hPA (right_mem_segment ℝ _ _))
      (hQA (left_mem_segment ℝ _ _)) (hQA (right_mem_segment ℝ _ _))
      hxP hxQ h₁ h₂ h₃ h₄ with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact Or.inl (Prod.ext e₁ e₂)
  · exact Or.inr (Prod.ext e₁ e₂)

end Schoenflies
