/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.SegmentCut
public import LeanPool.Schoenflies.SegmentOrder

/-!
# Subdividing a list of segments

A polygonal edge **is** its pair of endpoints: a straight segment is determined by its ends,
so naming one by anything else names a distinction that does not exist. `Piece := Plane ×
Plane`, and the blueprint's "represent every duplicate geometric subsegment only once"
becomes deduplication of a list of *names*, with no geometry in it.

**The subdivision recurses on the POINT list, not on the segment.** `subdivide pieces points`
cuts every current piece at the head point and recurses with the rest. Read literally the
blueprint wants the cut points as data, which would need a choice operator (the meets are
existential) and then a sort (to order them along each segment). Neither is required: order
does not matter, because cutting at a point that has already become an endpoint is a no-op.

Three facts about one cut, each lifted across the piece list and then across the point list:

* `subdivide_cover` — cutting loses nothing, so a subdivision occupies what it came from;
* `subdivide_ne` — no piece degenerates, so the drawing condition's invariant survives;
* `subdivide_interior_subset` — every piece's interior lies inside the interior of a piece
  it came from. This is what makes a cut **permanent**: nothing later can put a removed point
  back into an interior.

## Blueprint

* `Piece`, `cover` — the segment representation and what a list of them occupies.
* `subdivide` and its three properties — the cutting half of Lemma 3.7 (polygonal overlay).
-/

public section

open Metric Set

namespace Schoenflies

/-- A polygonal edge is its pair of endpoints. -/
abbrev Piece := Plane × Plane

namespace Piece

/-- The closed segment a piece occupies. -/
@[expose] def seg (P : Piece) : Set Plane := segment ℝ P.1 P.2

/-- The interior of a piece. -/
@[expose] def interior (P : Piece) : Set Plane := openSegment ℝ P.1 P.2

/-- A piece is nondegenerate when its two ends differ. -/
@[expose] def Nondeg (P : Piece) : Prop := P.1 ≠ P.2

end Piece

/-- What a list of pieces occupies. -/
@[expose] def cover (pieces : List Piece) : Set Plane := ⋃ P ∈ pieces, P.seg

@[simp] theorem cover_nil : cover [] = ∅ := by simp [cover]

@[simp] theorem cover_cons (P : Piece) (ps : List Piece) :
    cover (P :: ps) = P.seg ∪ cover ps := by
  simp [cover]

theorem cover_append (ps qs : List Piece) : cover (ps ++ qs) = cover ps ∪ cover qs := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.cons_append, cover_cons, cover_cons, ih, union_assoc]

theorem cover_flatMap (f : Piece → List Piece) (ps : List Piece) :
    cover (ps.flatMap f) = ⋃ P ∈ ps, cover (f P) := by
  induction ps with
  | nil => simp
  | cons P ps ih => rw [List.flatMap_cons, cover_append, ih]; simp

/-! ### One cut -/

open scoped Classical in
/-- Cut one piece at one point: two pieces if the point is interior to it, and the piece
unchanged otherwise. Cutting at a point that is already an endpoint is a no-op. -/
@[expose] noncomputable def splitAt (p : Plane) (P : Piece) : List Piece :=
  if p ∈ P.interior then [(P.1, p), (p, P.2)] else [P]

theorem splitAt_cover (p : Plane) (P : Piece) : cover (splitAt p P) = P.seg := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    simp only [cover_cons, cover_nil, union_empty]
    exact (segment_split hp).symm
  · simp

/-- Cutting at an interior point leaves both halves nondegenerate: an interior point differs
from both ends. -/
theorem splitAt_ne (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, Q.Nondeg := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    -- `p` is strictly inside, so it is neither end.
    have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact h1
    · rcases List.mem_singleton.1 hQ with rfl
      exact h2
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact hP

/-- Cutting is permanent: each half's interior lies inside the whole's. -/
theorem splitAt_interior_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact openSegment_left_subset h
    · rcases List.mem_singleton.1 hQ with rfl
      exact openSegment_right_subset h
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact subset_rfl

/-- After cutting at `p`, no piece has `p` in its interior.

Nondegeneracy is needed: a degenerate piece `(p, p)` has `p` in its interior and cutting it
produces two more copies of itself. -/
theorem splitAt_avoids (p : Plane) {P : Piece} (hP : P.Nondeg) :
    ∀ Q ∈ splitAt p P, p ∉ Q.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have h1 : P.1 ≠ p := by
      rintro rfl
      exact hP (left_mem_openSegment_iff.1 h)
    have h2 : p ≠ P.2 := by
      rintro rfl
      exact hP (right_mem_openSegment_iff.1 h)
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact fun hmem => h1 (right_mem_openSegment_iff.1 hmem)
    · rcases List.mem_singleton.1 hQ with rfl
      exact fun hmem => h2 (left_mem_openSegment_iff.1 hmem)
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact h

/-! ### One cut, across the whole list -/

/-- Cut every piece of the list at one point. -/
@[expose] noncomputable def splitAllAt (p : Plane) (pieces : List Piece) : List Piece :=
  pieces.flatMap (splitAt p)

theorem splitAllAt_cover (p : Plane) (pieces : List Piece) :
    cover (splitAllAt p pieces) = cover pieces := by
  rw [splitAllAt, cover_flatMap]
  simp only [splitAt_cover]
  rfl

theorem splitAllAt_ne (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, Q.Nondeg := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_ne p (h P hP) Q hQP

theorem splitAllAt_interior_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_interior_subset p P Q hQP⟩

theorem splitAllAt_avoids (p : Plane) {pieces : List Piece} (h : ∀ P ∈ pieces, P.Nondeg) :
    ∀ Q ∈ splitAllAt p pieces, p ∉ Q.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact splitAt_avoids p (h P hP) Q hQP

/-! ### The subdivision -/

/-- Subdivide a list of pieces at a list of points, recursing on the POINT list: cut every
current piece at the head, then carry on with the tail. -/
@[expose] noncomputable def subdivide (pieces : List Piece) : List Plane → List Piece
  | [] => pieces
  | p :: ps => subdivide (splitAllAt p pieces) ps

@[simp] theorem subdivide_nil (pieces : List Piece) : subdivide pieces [] = pieces := rfl

@[simp] theorem subdivide_cons (pieces : List Piece) (p : Plane) (ps : List Plane) :
    subdivide pieces (p :: ps) = subdivide (splitAllAt p pieces) ps := rfl

/-- Cutting loses nothing: a subdivision occupies exactly what it came from. -/
theorem subdivide_cover (pieces : List Piece) (points : List Plane) :
    cover (subdivide pieces points) = cover pieces := by
  induction points generalizing pieces with
  | nil => rfl
  | cons p ps ih => rw [subdivide_cons, ih, splitAllAt_cover]

/-- No piece degenerates. -/
theorem subdivide_ne {pieces : List Piece} (points : List Plane)
    (h : ∀ P ∈ pieces, P.Nondeg) : ∀ Q ∈ subdivide pieces points, Q.Nondeg := by
  induction points generalizing pieces with
  | nil => exact h
  | cons p ps ih => exact ih (splitAllAt_ne p h)

/-- Every piece's interior lies inside the interior of a piece it came from. This is what
makes a cut permanent. -/
theorem subdivide_interior_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP⟩ := splitAllAt_interior_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP⟩

/-- After subdividing, no cut point is interior to any piece. Permanence is what makes this
work: a later cut only shrinks interiors, so a point removed early stays removed. -/
theorem subdivide_avoids {pieces : List Piece} (points : List Plane)
    (hnd : ∀ P ∈ pieces, P.Nondeg) :
    ∀ p ∈ points, ∀ Q ∈ subdivide pieces points, p ∉ Q.interior := by
  induction points generalizing pieces with
  | nil => simp
  | cons p ps ih =>
    intro q hq Q hQ
    rcases List.mem_cons.1 hq with rfl | hq
    · -- `q` was cut out at this step; permanence keeps it out of every later piece.
      obtain ⟨R, hR, hQR⟩ := subdivide_interior_subset (splitAllAt q pieces) ps Q hQ
      exact fun hmem => splitAllAt_avoids q hnd R hR (hQR hmem)
    · exact ih (pieces := splitAllAt p pieces) (splitAllAt_ne p hnd) q hq Q hQ

end Schoenflies
