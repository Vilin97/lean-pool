/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Subarc
public import LeanPool.Schoenflies.Concatenate

/-!
# Two points cut a Jordan curve into two arcs

Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points. This is the converse of
`IsJordanCurve.of_two_arcs`, and the harder direction.

The whole argument is carried by the loop's **parameters**; the circle never appears. Pull the
two points back to parameters `s` and `t` short of the finish — `parameter_before_finish`,
which replaces a parameter at the finish by the start, the only use the closing condition gets
— and order them, say `s < t`. Then the two pieces are what the loop makes of the parameters
*between* `s` and `t` and of the parameters *outside* them:

* the middle piece `f '' Icc s t` is a subarc, produced by `Subarc.lean`'s
  `isArcBetween_subarc`, whose injectivity hypothesis is confined to the traversed interval
  and so survives a loop;
* the outside piece `f '' Icc 0 s ∪ f '' Icc t 1` is two end intervals glued where the loop
  closes up, produced by `Concatenate.lean`'s `IsArcBetween.concatenate`.

That asymmetry — one subarc and one concatenation — is inherent to a parameter interval with
a seam in it, and is not worth fighting. It costs one case split, at `s = 0`, where the front
interval degenerates to a point that the back piece already carries at its far end.

Both halves of the conclusion are then facts about intervals of reals. Covering is the
three-way split of `[0,1]` around two parameters, which is the linearity of the order and
nothing else. Meeting is injectivity off the finish, applied on each of the three pieces; the
one case that needs the loop rather than an arc is an outside parameter *at* the finish, which
carries the same point as the start and so lands back on `s`.

## Blueprint

* `lem:jordan-circle` — "any two distinct points of `C` divide it into two simple arcs having
  exactly those points in common". `IsJordanCurve.two_arcs` is that clause, proved directly
  from the parametrisation instead of through the model curve, so it does not wait on the
  loop-to-circle bridge.
* `IsLoop.two_arcs_at_parameters` — the parameter-level form the clause is assembled from.
-/

public section

open Set unitInterval

namespace Schoenflies

namespace IsLoop

variable {f : ℝ → Plane} {s t : ℝ}

/-! ### Parameters short of the finish

A loop is injective on `[0, 1)` only, so every statement below has to keep its parameters
away from `1`. These two lemmas are the interface to that: one says injectivity holds as soon
as neither parameter is the finish, the other says the finish can always be avoided. -/

/-- Two parameters short of the finish carrying the same point are equal. This is `IsLoop.injOn`
with the half-open interval spelled as "in `[0,1]` and not `1`", which is the form every use
below produces. -/
theorem injective_before_finish (hf : IsLoop f) {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (h : f u = f v) : u = v :=
  hf.injOn ⟨hu.1, hu.2.lt_of_ne hu1⟩ ⟨hv.1, hv.2.lt_of_ne hv1⟩ h

/-- **Every point of the curve has a parameter short of the finish.** A parameter at the finish
is replaced by the start, which carries the same point. This is the only use the closing
condition gets. -/
theorem parameter_before_finish (hf : IsLoop f) {p : Plane} (hp : p ∈ f '' I) :
    ∃ u ∈ I, u ≠ 1 ∧ f u = p := by
  obtain ⟨u, hu, rfl⟩ := hp
  rcases eq_or_ne u 1 with rfl | hu1
  · exact ⟨0, zero_mem_I, one_ne_zero.symm, hf.closes⟩
  · exact ⟨u, hu, hu1, rfl⟩

/-- The start and the finish are the same point of the curve; recorded in the direction the
proofs below read it. -/
theorem finish_eq_start (hf : IsLoop f) : f 1 = f 0 := hf.closes.symm

/-! ### The three pieces of parameters

Two parameters `s < t` cut `[0, 1]` into the middle interval `[s, t]` and the two end
intervals `[0, s]` and `[t, 1]`. Each piece needs the loop to be injective on its own
parameters. On the middle and the front that is injectivity off the finish, since neither
contains it; the back piece *does* contain the finish, and there the extra argument is that
the only other parameter carrying `f 1` is the start, which lies strictly before `t`. -/

theorem front_subset_I (hs : s ∈ I) : Icc 0 s ⊆ I := Icc_subset_Icc le_rfl hs.2

theorem middle_subset_I (hs : s ∈ I) (ht : t ∈ I) : Icc s t ⊆ I := Icc_subset_Icc hs.1 ht.2

theorem back_subset_I (ht : t ∈ I) : Icc t 1 ⊆ I := Icc_subset_Icc ht.1 le_rfl

/-- Injectivity on the front piece: no parameter of `[0, s]` is the finish, because `s` is
not. -/
theorem injective_on_front (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) : InjOn f (Icc 0 s) := by
  have hs' : s < 1 := hs.2.lt_of_ne hs1
  intro u hu v hv h
  exact hf.injective_before_finish (front_subset_I hs hu) (front_subset_I hs hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 hs')) (ne_of_lt (lt_of_le_of_lt hv.2 hs')) h

/-- Injectivity on the middle piece: no parameter of `[s, t]` is the finish, because `t` is
not. -/
theorem injective_on_middle (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1) :
    InjOn f (Icc s t) := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  intro u hu v hv h
  exact hf.injective_before_finish (middle_subset_I hs ht hu) (middle_subset_I hs ht hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 ht')) (ne_of_lt (lt_of_le_of_lt hv.2 ht')) h

/-- On the back piece the finish is the *only* parameter carrying `f 1`. A second one would be
the start, by injectivity off the finish and the closing condition — but the start lies
strictly before `t`. -/
theorem back_at_finish (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) {w : ℝ} (hw : w ∈ Icc t 1)
    (h : f w = f 1) : w = 1 := by
  by_contra hw1
  have : w = 0 :=
    hf.injective_before_finish (back_subset_I ht hw) zero_mem_I hw1 one_ne_zero.symm
      (h.trans hf.finish_eq_start)
  exact absurd (this ▸ hw.1) (not_le.mpr ht0)

/-- Injectivity on the back piece. Unlike the other two this piece contains the finish, so
injectivity off the finish is not enough on its own; `back_at_finish` supplies the rest. -/
theorem injective_on_back (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) : InjOn f (Icc t 1) := by
  intro u hu v hv h
  rcases eq_or_ne u 1 with rfl | hu1
  · exact (hf.back_at_finish ht ht0 hv h.symm).symm
  · rcases eq_or_ne v 1 with rfl | hv1
    · exact hf.back_at_finish ht ht0 hu h
    · exact hf.injective_before_finish (back_subset_I ht hu) (back_subset_I ht hv) hu1 hv1 h

/-! ### The three pieces are arcs -/

/-- The middle piece is an arc between the two cut points. -/
theorem middle_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1)
    (hst : s < t) : IsArcBetween (f '' Icc s t) (f s) (f t) := by
  rw [← uIcc_of_le hst.le]
  refine isArcBetween_subarc hf.continuousOn ?_ hs ht (ne_of_lt hst)
  rw [uIcc_of_le hst.le]
  exact hf.injective_on_middle hs ht ht1

/-- The front piece is an arc from the start to the first cut point. -/
theorem front_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) (hs0 : 0 < s) :
    IsArcBetween (f '' Icc 0 s) (f 0) (f s) := by
  rw [← uIcc_of_le hs0.le]
  refine isArcBetween_subarc hf.continuousOn ?_ zero_mem_I hs (ne_of_lt hs0)
  rw [uIcc_of_le hs0.le]
  exact hf.injective_on_front hs hs1

/-- The back piece is an arc from the second cut point to the finish. -/
theorem back_IsArcBetween (hf : IsLoop f) (ht : t ∈ I) (ht1 : t ≠ 1) (ht0 : 0 < t) :
    IsArcBetween (f '' Icc t 1) (f t) (f 1) := by
  rw [← uIcc_of_le ht.2]
  refine isArcBetween_subarc hf.continuousOn ?_ ht one_mem_I ht1
  rw [uIcc_of_le ht.2]
  exact hf.injective_on_back ht ht0

/-! ### The outside piece

The parameters outside `[s, t]` are two intervals, glued at the point where the loop closes
up: walk from `t` to the finish, then from the start to `s`. When `s` *is* the start the front
interval degenerates to a single parameter, and the outside is the back piece alone — its far
end already carries the point the front piece would have contributed. -/

/-- The back and front pieces meet only where the loop closes up. A point on both comes from a
parameter at or past `t` and from one at or before `s`; two distinct parameters short of the
finish cannot carry the same point, and `t ≤ s` is false, so the back parameter is the
finish. -/
theorem back_meet_front (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1) (hst : s < t)
    {z : Plane} (hzb : z ∈ f '' Icc t 1) (hzf : z ∈ f '' Icc 0 s) : z = f 1 := by
  obtain ⟨b, hb, rfl⟩ := hzb
  obtain ⟨a, ha, hab⟩ := hzf
  have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
  rcases eq_or_ne b 1 with rfl | hb1
  · rfl
  · -- Otherwise both parameters are short of the finish, so they coincide — impossible,
    -- since one is at least `t` and the other at most `s < t`.
    have : b = a :=
      hf.injective_before_finish (back_subset_I ht hb) (front_subset_I hs ha) hb1 ha1 hab.symm
    exact absurd (this ▸ hb.1) (not_le.mpr (lt_of_le_of_lt ha.2 hst))

/-- **The outside piece is an arc between the two cut points.** -/
theorem outside_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    IsArcBetween (f '' Icc 0 s ∪ f '' Icc t 1) (f t) (f s) := by
  have ht0 : 0 < t := lt_of_le_of_lt hs.1 hst
  have hback : IsArcBetween (f '' Icc t 1) (f t) (f 1) := hf.back_IsArcBetween ht ht1 ht0
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- `s` is the start: the front interval is the single parameter `0`, whose point the back
    -- piece already carries at its far end, so the outside is the back piece alone.
    have hfront : f '' Icc 0 s = {f 1} := by
      rw [← hs0, Icc_self, image_singleton, hf.finish_eq_start]
    have hone : f 1 ∈ f '' Icc t 1 := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    rw [hfront, singleton_union, insert_eq_self.mpr hone, ← hs0, ← hf.finish_eq_start]
    exact hback
  · -- Otherwise the two end intervals are genuine arcs, glued where the loop closes up.
    have hfront : IsArcBetween (f '' Icc 0 s) (f 1) (f s) := by
      rw [hf.finish_eq_start]
      exact hf.front_IsArcBetween hs hs1 hs0
    have := hback.concatenate hfront (fun z hzb hzf => hf.back_meet_front hs ht hs1 hst hzb hzf)
    rwa [union_comm] at this

/-! ### Covering, and where the pieces meet -/

/-- The parameter interval splits three ways around any two of its points. Linearity of the
order, and nothing else — the split does not even need the two points ordered, since when they
are not the middle interval is empty and the two end intervals already overlap. -/
theorem parameters_split (hs : s ∈ I) (ht : t ∈ I) :
    I = Icc s t ∪ (Icc 0 s ∪ Icc t 1) := by
  ext x
  constructor
  · rintro ⟨h0, h1⟩
    rcases le_total x s with h | h
    · exact Or.inr (Or.inl ⟨h0, h⟩)
    · rcases le_total x t with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (Or.inr ⟨h', h1⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hs.1.trans h1, h2.trans ht.2⟩
    · exact ⟨h1, h2.trans hs.2⟩
    · exact ⟨ht.1.trans h1, h2⟩

/-- The loop's images of the middle and of the outside cover the curve. -/
theorem pieces_cover (hs : s ∈ I) (ht : t ∈ I) :
    f '' Icc s t ∪ (f '' Icc 0 s ∪ f '' Icc t 1) = f '' I := by
  rw [parameters_split hs ht, image_union, image_union]

/-- **The two pieces meet in exactly the two cut points.**

Three cases, one for each way an outside parameter can be placed. The one that matters is the
outside parameter being the finish: it carries the same point as the start, so the middle
parameter is the start, which forces `s` to be it. That case is why the argument needs a loop
rather than an arc. -/
theorem pieces_meet_at_ends (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    f '' Icc s t ∩ (f '' Icc 0 s ∪ f '' Icc t 1) = {f s, f t} := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  apply Subset.antisymm
  · rintro z ⟨⟨m, hm, rfl⟩, hzout⟩
    have hmI : m ∈ I := middle_subset_I hs ht hm
    have hm1 : m ≠ 1 := ne_of_lt (lt_of_le_of_lt hm.2 ht')
    rcases hzout with ⟨a, ha, hazm⟩ | ⟨b, hb, hbzm⟩
    · -- A front parameter: it is at most `s`, and the middle parameter is at least `s`.
      have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
      have : m = a :=
        hf.injective_before_finish hmI (front_subset_I hs ha) hm1 ha1 hazm.symm
      rw [le_antisymm (this ▸ ha.2) hm.1]
      exact mem_insert _ _
    · rcases eq_or_ne b 1 with rfl | hb1
      · -- The far end carries the same point as the start, and the start is short of the
        -- finish, so the middle parameter is the start — which forces `s` to be it.
        have : m = 0 :=
          hf.injective_before_finish hmI zero_mem_I hm1 one_ne_zero.symm
            (hbzm.symm.trans hf.finish_eq_start)
        have hs0 : s = 0 := le_antisymm (this ▸ hm.1) hs.1
        rw [hs0, ← this]
        exact mem_insert _ _
      · -- Otherwise the outside parameter is at least `t`, and the middle one is at most `t`.
        have : m = b :=
          hf.injective_before_finish hmI (back_subset_I ht hb) hm1 hb1 hbzm.symm
        rw [le_antisymm hm.2 (this ▸ hb.1)]
        exact mem_insert_of_mem _ rfl
  · rintro z (rfl | rfl)
    · exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, Or.inl ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩⟩
    · exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, Or.inr ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩⟩

/-! ### The two arcs, at chosen parameters -/

/-- **Two parameters short of the finish cut the loop's image into two arcs between the points
they carry, which cover it and meet in exactly those two points.**

The pieces are named by the parameters, not chosen: the first is the middle interval's image,
the second the outside's. -/
theorem two_arcs_at_parameters (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    ∃ A B, IsArcBetween A (f s) (f t) ∧ IsArcBetween B (f t) (f s) ∧
      A ∪ B = f '' I ∧ A ∩ B = {f s, f t} :=
  ⟨f '' Icc s t, f '' Icc 0 s ∪ f '' Icc t 1,
    hf.middle_IsArcBetween hs ht ht1 hst,
    hf.outside_IsArcBetween hs ht hs1 ht1 hst,
    pieces_cover hs ht,
    hf.pieces_meet_at_ends hs ht hs1 ht1 hst⟩

end IsLoop

/-! ### The theorem -/

/-- **Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points.**

The parameters carrying the two points come in one order or the other, and the conclusion is
symmetric in the two pieces, so the second case is the first with the roles exchanged: the
union and the intersection commute, and the unordered pair does too.

This is the exact converse of `IsJordanCurve.of_two_arcs`: that theorem's hypotheses are two
arcs between the same two points meeting only there, which is what the two pieces produced
here are — see `IsJordanCurve.two_arcs_of_two_arcs`. -/
theorem IsJordanCurve.two_arcs {C : Set Plane} (hC : IsJordanCurve C) {p q : Plane}
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A B, IsArcBetween A p q ∧ IsArcBetween B p q ∧ A ∪ B = C ∧ A ∩ B = {p, q} := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨s, hs, hs1, rfl⟩ := hf.parameter_before_finish hp
  obtain ⟨t, ht, ht1, rfl⟩ := hf.parameter_before_finish hq
  -- Distinct points, so distinct parameters, so one of the two orders holds.
  rcases lt_or_gt_of_ne (fun h : s = t => hpq (by rw [h])) with hst | hts
  · obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters hs ht hs1 ht1 hst
    exact ⟨A, B, hA, hB.reverse, hcov, hmeet⟩
  · -- The middle piece now runs from `f t` to `f s`, so it is the *second* piece here.
    obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters ht hs ht1 hs1 hts
    refine ⟨B, A, hB, hA.reverse, ?_, ?_⟩
    · rw [union_comm]; exact hcov
    · rw [inter_comm, hmeet, pair_comm]

/-- The composition check: the two arcs `IsJordanCurve.two_arcs` produces are exactly what
`IsJordanCurve.of_two_arcs` consumes, and glue back to the curve one started from. -/
theorem IsJordanCurve.two_arcs_of_two_arcs {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hmeet : A ∩ B = {p, q}) :
    IsJordanCurve (A ∪ B) :=
  IsJordanCurve.of_two_arcs hA hB.reverse fun z hzA hzB => by
    have : z ∈ ({p, q} : Set Plane) := hmeet ▸ ⟨hzA, hzB⟩
    exact this

end Schoenflies
