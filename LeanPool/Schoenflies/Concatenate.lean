/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Curve

/-!
# Gluing arcs

Two arcs meeting only at the endpoint they share glue to one arc; two arcs meeting at *both*
of their ends glue to a Jordan curve. The glued parametrisation runs the first arc over the
lower half of the parameter interval and the second over the upper half, each at double
speed: `t ↦ f (2 * t)` below the midpoint and `t ↦ g (2 * t - 1)` above it. Since the
parameter here is an honest real number, that is literally what the definition says.

The halves are `[0, 1/2]` and `[1/2, 1]`. They cover the interval, and each is closed, so
continuity is Mathlib's pasting lemma `ContinuousOn.union_of_isClosed`. Injectivity splits
four ways — both parameters below the midpoint, both above, and the two mixed orders — and
only the mixed cases use the hypothesis that the two arcs meet nowhere else: there the common
value lies on both arcs, hence is the shared endpoint, and each arc's own injectivity pins
its parameter to the midpoint.

At the midpoint itself both branches of the `if` are meaningful and they agree, precisely
because the first arc finishes where the second starts. That is what makes the glued map well
defined rather than merely continuous, and it is why `concatenate_upperHalf` — the statement
that the glued map *is* the retimed second arc on the whole closed upper half, midpoint
included — carries the shared-endpoint hypothesis.

For the loop the seam analysis gains a second legitimate meeting point: besides the middle,
where the arcs are glued, there are the outer ends, where the loop is allowed to repeat
itself. Pinning those needs the start/finish counterparts of the midpoint lemmas.

## Blueprint

* `concatenate` — §1, the glued parametrisation.
* `IsArc.concatenate`, `IsArcBetween.concatenate` — two arcs meeting only at the endpoint they
  share glue to an arc.
* `IsLoop.concatenate` — two arcs glued along both of their ends make a loop.
* `IsJordanCurve.of_two_arcs` — two arcs meeting exactly at their two shared endpoints make a
  Jordan curve; the converse of the two-arcs decomposition, and the form every *construction*
  of a curve takes.
-/

public section

open Set unitInterval

namespace Schoenflies

/-! ### The two halves of the parameter interval -/

/-- The lower half of the parameter interval, where the first arc runs. -/
def lowerHalf : Set ℝ := Icc 0 (1 / 2)

/-- The upper half of the parameter interval, where the second arc runs. The two halves
overlap in the midpoint: that is the seam. -/
def upperHalf : Set ℝ := Icc (1 / 2) 1

theorem lowerHalf_subset_I : lowerHalf ⊆ I := Icc_subset_Icc le_rfl (by norm_num)

theorem upperHalf_subset_I : upperHalf ⊆ I := Icc_subset_Icc (by norm_num) le_rfl

theorem halves_union : lowerHalf ∪ upperHalf = I :=
  Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)

theorem isClosed_lowerHalf : IsClosed lowerHalf := isClosed_Icc

theorem isClosed_upperHalf : IsClosed upperHalf := isClosed_Icc

/-- Doubling a parameter below the midpoint reaches at most one. -/
theorem double_mem_I {t : ℝ} (ht : t ∈ lowerHalf) : 2 * t ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Doubling a parameter above the midpoint and stepping back reaches at least zero. -/
theorem doubleBack_mem_I {t : ℝ} (ht : t ∈ upperHalf) : 2 * t - 1 ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ### The glued parametrisation -/

/-- Run `f` over the lower half of the interval and `g` over the upper half, each at double
speed. -/
noncomputable def concatenate (f g : ℝ → Plane) : ℝ → Plane :=
  fun t => if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

variable {f g : ℝ → Plane}

theorem concatenate_of_le {t : ℝ} (ht : t ≤ 1 / 2) : concatenate f g t = f (2 * t) :=
  ite_eq_left ht

theorem concatenate_of_not_le {t : ℝ} (ht : ¬t ≤ 1 / 2) :
    concatenate f g t = g (2 * t - 1) :=
  ite_eq_right ht

theorem concatenate_zero : concatenate f g 0 = f 0 := by
  rw [concatenate_of_le (by norm_num)]
  norm_num

theorem concatenate_one : concatenate f g 1 = g 1 := by
  rw [concatenate_of_not_le (by norm_num)]
  norm_num

/-- On the *closed* upper half the glued map is the retimed second arc — at the midpoint
included, where the `if` still takes the first branch. The two branches agree there only
because the first arc finishes where the second starts, which is what makes the glued map
well defined. -/
theorem concatenate_upperHalf (hmid : f 1 = g 0) {t : ℝ} (ht : t ∈ upperHalf) :
    concatenate f g t = g (2 * t - 1) := by
  by_cases h : t ≤ 1 / 2
  · -- The only parameter of the upper half below the midpoint is the midpoint.
    have : t = 1 / 2 := le_antisymm h ht.1
    subst this
    rw [concatenate_of_le h]
    norm_num
    exact hmid
  · exact concatenate_of_not_le h

/-! ### Continuity -/

/-- Continuity of the glued map: each half carries a composition, and the halves are closed
and cover. -/
theorem continuousOn_concatenate (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hmid : f 1 = g 0) : ContinuousOn (concatenate f g) I := by
  rw [← halves_union]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_lowerHalf isClosed_upperHalf
  · -- On the lower half the glued map is `f` doubled.
    have h : ContinuousOn (fun t : ℝ => f (2 * t)) lowerHalf :=
      hf.comp (by fun_prop) fun t ht => double_mem_I ht
    exact h.congr fun t ht => concatenate_of_le ht.2
  · -- On the upper half it is `g`, doubled and stepped back.
    have h : ContinuousOn (fun t : ℝ => g (2 * t - 1)) upperHalf :=
      hg.comp (by fun_prop) fun t ht => doubleBack_mem_I ht
    exact h.congr fun t ht => concatenate_upperHalf hmid ht

/-! ### Pinning a parameter at the seam

At a point where two of the pieces meet, the value is one of the shared points, and the
injectivity of the arc it belongs to pins the parameter. Each half needs its own statement,
since they retime differently; the loop needs the outer ends as well as the middle. -/

theorem lowerHalf_at_finish (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 1) : t = 1 / 2 := by
  have := hfi (double_mem_I ht) one_mem_I h
  linarith

theorem lowerHalf_at_start (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 0) : t = 0 := by
  have := hfi (double_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_start (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 0) : t = 1 / 2 := by
  have := hgi (doubleBack_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_finish (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 1) : t = 1 := by
  have := hgi (doubleBack_mem_I ht) one_mem_I h
  linarith

/-! ### Injectivity -/

/-- Across the seam: the common value lies on both arcs, so it is the shared endpoint, and
each half's injectivity pins its own parameter to the midpoint. Stated for a parameter of
each half rather than for `x` and `y`, so that the two orderings of the case split are the
same theorem. -/
theorem concatenate_seam (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  have hz : f (2 * x) = f 1 :=
    hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩
  have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
  rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs meeting only at the endpoint they share glue to an injective map. -/
theorem injOn_concatenate (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) : InjOn (concatenate f g) I := by
  intro x hx y hy h
  rcases le_or_gt x (1 / 2) with hxl | hxg
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · -- Both parameters run the first arc: its own injectivity, doubled.
      rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
      have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
      linarith
    · exact concatenate_seam hfi hgi hmid hmeet ⟨hx.1, hxl⟩ ⟨hyg.le, hy.2⟩ h
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · exact (concatenate_seam hfi hgi hmid hmeet ⟨hy.1, hyl⟩ ⟨hxg.le, hx.2⟩ h.symm).symm
    · -- Both run the second arc.
      rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
      have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2⟩) (doubleBack_mem_I ⟨hyg.le, hy.2⟩) h
      linarith

/-! ### What the glued map covers -/

/-- Each half retimes *onto* the whole interval, so the glued map's image is exactly the two
arcs together. -/
theorem image_concatenate (hmid : f 1 = g 0) : concatenate f g '' I = f '' I ∪ g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases le_or_gt t (1 / 2) with h | h
    · exact Or.inl ⟨2 * t, double_mem_I ⟨ht.1, h⟩, (concatenate_of_le h).symm⟩
    · exact Or.inr ⟨2 * t - 1, doubleBack_mem_I ⟨h.le, ht.2⟩,
        (concatenate_of_not_le (not_le.2 h)).symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · -- Half a parameter is the one that doubles to it.
      refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_of_le (by linarith [hu.2])]
      congr 1
      ring
    · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_upperHalf hmid ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      congr 1
      ring

/-! ### The set-level gluing theorems

This is the form the rest of the development speaks: a piece is an arc between two named
points, the parametrisations are chosen inside the proofs and never seen again. -/

/-- Two pieces meeting only at the point where they are joined make one piece. -/
theorem IsArcBetween.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) :
    IsArcBetween (A ∪ B) a c := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf1]
    exact hmeet z hz hz'
  refine ⟨_, continuousOn_concatenate hfc hgc hmid, injOn_concatenate hfi hgi hmid hmeet',
    ?_, ?_, ?_⟩
  · rw [image_concatenate hmid, hfim, hgim]
  · rw [concatenate_zero]; exact hf0
  · rw [concatenate_one]; exact hg1

/-- Two arcs meeting only at the endpoint they share glue to an arc. -/
theorem IsArc.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) : IsArc (A ∪ B) :=
  (hA.concatenate hB hmeet).isArc

/-! ### Closing the loop

Two arcs that share *both* of their ends — the second runs back from where the first arrived
to where it set out — glue to a loop rather than to an arc. Everything above carries over
except the seam analysis: a common value now has two ways to be legitimate, at the middle
where the arcs are glued and at the outer ends where the loop closes, and the second of those
is exactly the repetition `IsLoop` allows itself at the finish. -/

/-- Across the seam, when the two arcs also share their outer ends. At the middle the
argument is the one for arcs; at the outer ends the second arc is at its finish, so its
parameter is `1` — which the hypothesis has excluded. -/
theorem concatenate_seam_loop (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf) (hy1 : y ≠ 1)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  rcases hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩ with
    hz | hz
  · -- The value is where the loop closes: the second arc is at its finish, so `y = 1`.
    exact absurd (upperHalf_at_finish hgi hy (by rw [← h, hz]; exact hclose.symm)) hy1
  · have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
    rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

/-- Two arcs glued along both of their ends make a loop. -/
theorem IsLoop.concatenate (hfc : ContinuousOn f I) (hfi : InjOn f I) (hgc : ContinuousOn g I)
    (hgi : InjOn g I) (hmid : f 1 = g 0) (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) :
    IsLoop (Schoenflies.concatenate f g) where
  continuousOn := continuousOn_concatenate hfc hgc hmid
  closes := by rw [concatenate_zero, concatenate_one]; exact hclose.symm
  injOn := by
    intro x hx y hy h
    have hy1 : y ≠ 1 := ne_of_lt hy.2
    have hx1 : x ≠ 1 := ne_of_lt hx.2
    rcases le_or_gt x (1 / 2) with hxl | hxg
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
        have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
        linarith
      · exact concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hx.1, hxl⟩
          ⟨hyg.le, hy.2.le⟩ hy1 h
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · exact (concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hy.1, hyl⟩
          ⟨hxg.le, hx.2.le⟩ hx1 h.symm).symm
      · rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
        have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2.le⟩)
          (doubleBack_mem_I ⟨hyg.le, hy.2.le⟩) h
        linarith

/-- Two pieces meeting exactly at their two shared endpoints make a Jordan curve. This is the
converse of the two-arcs decomposition, and the form every construction of a curve takes: a
cycle of a plane graph arrives as a path and one more edge back to where it started. -/
theorem IsJordanCurve.of_two_arcs {A B : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b a) (hmeet : ∀ z ∈ A, z ∈ B → z = a ∨ z = b) :
    IsJordanCurve (A ∪ B) := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hclose : g 1 = f 0 := by rw [hg1, hf0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf0, hf1]
    exact hmeet z hz hz'
  refine ⟨_, IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet', ?_⟩
  rw [image_concatenate hmid, hfim, hgim]

end Schoenflies
