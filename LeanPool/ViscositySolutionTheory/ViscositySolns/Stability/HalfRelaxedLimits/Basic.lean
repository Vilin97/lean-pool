/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Basic half-relaxed limit definitions and estimates

This file contains the definitions of upper and lower half-relaxed limits and
basic estimates derived from the limsup and liminf definitions.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {ι : Type*}

/--
The product filter used in the definition of half-relaxed limits.

Membership in this product filter means the following: a set of pairs contains
`A × V` for some `A ∈ l` and some `V ∈ nhdsWithin x C`. Thus the index is
restricted by the filter `l`, while the spatial variable is restricted to a
relative neighborhood of `x` in `C`.
-/
def halfRelaxedFilter (l : Filter ι) (C : Set (Point n)) (x : Point n) :
    Filter (ι × Point n) :=
  l ×ˢ nhdsWithin x C

/-- The scalar value whose limsup/liminf defines the half-relaxed limits. -/
def halfRelaxedValue (uᵢ : ι -> Point n -> Real) (q : ι × Point n) : Real :=
  uᵢ q.1 q.2

/--
The upper half-relaxed limit
`\bar u(x) = limsup_{i, y -> x, y ∈ C} u_i(y)`.
-/
def upperHalfRelaxedLimit (uᵢ : ι -> Point n -> Real) (l : Filter ι)
    (C : Set (Point n)) (x : Point n) : Real :=
  limsup (halfRelaxedValue uᵢ) (halfRelaxedFilter l C x)

/--
The lower half-relaxed limit
`\underline u(x) = liminf_{i, y -> x, y ∈ C} u_i(y)`.
-/
def lowerHalfRelaxedLimit (uᵢ : ι -> Point n -> Real) (l : Filter ι)
    (C : Set (Point n)) (x : Point n) : Real :=
  liminf (halfRelaxedValue uᵢ) (halfRelaxedFilter l C x)

theorem halfRelaxedFilter_def (l : Filter ι) (C : Set (Point n)) (x : Point n) :
    halfRelaxedFilter l C x = l ×ˢ nhdsWithin x C :=
  rfl

theorem upperHalfRelaxedLimit_def (uᵢ : ι -> Point n -> Real) (l : Filter ι)
    (C : Set (Point n)) (x : Point n) :
    upperHalfRelaxedLimit uᵢ l C x =
      limsup (fun q : ι × Point n => uᵢ q.1 q.2) (l ×ˢ nhdsWithin x C) :=
  rfl

theorem lowerHalfRelaxedLimit_def (uᵢ : ι -> Point n -> Real) (l : Filter ι)
    (C : Set (Point n)) (x : Point n) :
    lowerHalfRelaxedLimit uᵢ l C x =
      liminf (fun q : ι × Point n => uᵢ q.1 q.2) (l ×ˢ nhdsWithin x C) :=
  rfl

/--
If `uᵢ q.1 q.2 = vᵢ q.1 q.2` for all pairs `q = (i, y)` in some member of
`halfRelaxedFilter l C x`, then the two upper half-relaxed limits at `x`
are equal.
-/
theorem upperHalfRelaxedLimit_congr
    {uᵢ vᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n}
    (h : ∀ᶠ q in halfRelaxedFilter l C x, halfRelaxedValue uᵢ q = halfRelaxedValue vᵢ q) :
    upperHalfRelaxedLimit uᵢ l C x = upperHalfRelaxedLimit vᵢ l C x :=
  limsup_congr h

/--
If `uᵢ q.1 q.2 = vᵢ q.1 q.2` for all pairs `q = (i, y)` in some member of
`halfRelaxedFilter l C x`, then the two lower half-relaxed limits at `x`
are equal.
-/
theorem lowerHalfRelaxedLimit_congr
    {uᵢ vᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n}
    (h : ∀ᶠ q in halfRelaxedFilter l C x, halfRelaxedValue uᵢ q = halfRelaxedValue vᵢ q) :
    lowerHalfRelaxedLimit uᵢ l C x = lowerHalfRelaxedLimit vᵢ l C x :=
  liminf_congr h

/--
If the set of indices `i` for which `uᵢ i` and `vᵢ i` agree at every point
of `C` belongs to `l`, then the two upper half-relaxed limits at `x` are
equal.
-/
theorem upperHalfRelaxedLimit_congr_of_eventually_eqOn
    {uᵢ vᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n}
    (h : ∀ᶠ i in l, Set.EqOn (uᵢ i) (vᵢ i) C) :
    upperHalfRelaxedLimit uᵢ l C x = upperHalfRelaxedLimit vᵢ l C x := by
  refine upperHalfRelaxedLimit_congr ?_
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  have hC : ∀ᶠ q in halfRelaxedFilter l C x, q.2 ∈ C :=
    hCWithin.prod_inr l
  have hi : ∀ᶠ q in halfRelaxedFilter l C x, Set.EqOn (uᵢ q.1) (vᵢ q.1) C :=
    h.prod_inl (nhdsWithin x C)
  filter_upwards [hi, hC] with q hq hqC
  exact hq hqC

/--
If the set of indices `i` for which `uᵢ i` and `vᵢ i` agree at every point
of `C` belongs to `l`, then the two lower half-relaxed limits at `x` are
equal.
-/
theorem lowerHalfRelaxedLimit_congr_of_eventually_eqOn
    {uᵢ vᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n}
    (h : ∀ᶠ i in l, Set.EqOn (uᵢ i) (vᵢ i) C) :
    lowerHalfRelaxedLimit uᵢ l C x = lowerHalfRelaxedLimit vᵢ l C x := by
  refine lowerHalfRelaxedLimit_congr ?_
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  have hC : ∀ᶠ q in halfRelaxedFilter l C x, q.2 ∈ C :=
    hCWithin.prod_inr l
  have hi : ∀ᶠ q in halfRelaxedFilter l C x, Set.EqOn (uᵢ q.1) (vᵢ q.1) C :=
    h.prod_inl (nhdsWithin x C)
  filter_upwards [hi, hC] with q hq hqC
  exact hq hqC

/--
Assume the set of indices `i` such that
`∀ y ∈ C, uᵢ i y <= vᵢ i y` belongs to `l`. Under the boundedness hypotheses
needed to evaluate real-valued limsup, the upper half-relaxed limit of `uᵢ`
at `x` is at most the upper half-relaxed limit of `vᵢ` at `x`.
-/
theorem upperHalfRelaxedLimit_le_of_eventually_leOn
    {uᵢ vᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n}
    (h : ∀ᶠ i in l, ∀ y : Point n, y ∈ C -> uᵢ i y <= vᵢ i y)
    (hu : (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hv : (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue vᵢ)) :
    upperHalfRelaxedLimit uᵢ l C x <= upperHalfRelaxedLimit vᵢ l C x := by
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  have hC : ∀ᶠ q in halfRelaxedFilter l C x, q.2 ∈ C :=
    hCWithin.prod_inr l
  have hi : ∀ᶠ q in halfRelaxedFilter l C x,
      ∀ y : Point n, y ∈ C -> uᵢ q.1 y <= vᵢ q.1 y :=
    h.prod_inl (nhdsWithin x C)
  exact limsup_le_limsup (hi.and hC |>.mono fun q hq => hq.1 q.2 hq.2) hu hv

/--
Assume the set of indices `i` such that
`∀ y ∈ C, uᵢ i y <= vᵢ i y` belongs to `l`. Under the boundedness hypotheses
needed to evaluate real-valued liminf, the lower half-relaxed limit of `uᵢ`
at `x` is at most the lower half-relaxed limit of `vᵢ` at `x`.
-/
theorem lowerHalfRelaxedLimit_le_of_eventually_leOn
    {uᵢ vᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n}
    (h : ∀ᶠ i in l, ∀ y : Point n, y ∈ C -> uᵢ i y <= vᵢ i y)
    (hu : (halfRelaxedFilter l C x).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hv : (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue vᵢ)) :
    lowerHalfRelaxedLimit uᵢ l C x <= lowerHalfRelaxedLimit vᵢ l C x := by
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  have hC : ∀ᶠ q in halfRelaxedFilter l C x, q.2 ∈ C :=
    hCWithin.prod_inr l
  have hi : ∀ᶠ q in halfRelaxedFilter l C x,
      ∀ y : Point n, y ∈ C -> uᵢ q.1 y <= vᵢ q.1 y :=
    h.prod_inl (nhdsWithin x C)
  exact liminf_le_liminf (hi.and hC |>.mono fun q hq => hq.1 q.2 hq.2) hu hv

/--
Events for the half-relaxed product filter at `x` remain events for the
half-relaxed product filter at all nearby points `z ∈ C`.

More explicitly: if `S ∈ l ×ˢ nhdsWithin x C`, then the set of points
`z` such that `S ∈ l ×ˢ nhdsWithin z C` belongs to `nhdsWithin x C`.
-/
theorem eventually_mem_halfRelaxedFilter_of_mem {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {S : Set (ι × Point n)}
    (hS : S ∈ halfRelaxedFilter l C x) :
    ∀ᶠ z in nhdsWithin x C, S ∈ halfRelaxedFilter l C z := by
  rcases Filter.mem_prod_iff.mp hS with ⟨A, hA, B, hB, hsub⟩
  have hx : Tendsto (fun z : Point n => z) (nhdsWithin x C) (nhds x) := by
    rw [Tendsto]
    simp [nhdsWithin]
  have hmem : ∀ᶠ z in nhdsWithin x C, z ∈ C := self_mem_nhdsWithin
  have hBnear : ∀ᶠ z in nhdsWithin x C, B ∈ nhdsWithin z C :=
    eventually_mem_nhdsWithin_of_mem_nhdsWithin_of_tendsto hB hx hmem
  filter_upwards [hBnear] with z hzB
  exact Filter.mem_of_superset (Filter.prod_mem_prod hA hzB) hsub

/--
Upper semicontinuity of the upper half-relaxed limit, with the boundedness
hypotheses needed by real-valued `limsup`.
-/
theorem upperSemicontinuousOn_upperHalfRelaxedLimit
    (uᵢ : ι -> Point n -> Real) (l : Filter ι) (C : Set (Point n))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ)) :
    UpperSemicontinuousOn (upperHalfRelaxedLimit uᵢ l C) C := by
  intro x hxC y hy
  rcases exists_between hy with ⟨y', hxy', hy'y⟩
  have hlocal : ∀ᶠ q in halfRelaxedFilter l C x, halfRelaxedValue uᵢ q < y' :=
    eventually_lt_of_limsup_lt hxy' (hbddAbove x hxC)
  have hnear :
      ∀ᶠ z in nhdsWithin x C,
        {q : ι × Point n | halfRelaxedValue uᵢ q < y'} ∈ halfRelaxedFilter l C z :=
    eventually_mem_halfRelaxedFilter_of_mem hlocal
  have hmemC : ∀ᶠ z in nhdsWithin x C, z ∈ C := self_mem_nhdsWithin
  filter_upwards [hnear, hmemC] with z hz hzc
  have hzle : ∀ᶠ q in halfRelaxedFilter l C z, halfRelaxedValue uᵢ q <= y' := by
    filter_upwards [hz] with q hq
    exact le_of_lt hq
  have hle : upperHalfRelaxedLimit uᵢ l C z <= y' :=
    limsup_le_of_le (hcobddBelow z hzc) hzle
  exact lt_of_le_of_lt hle hy'y

/--
Lower semicontinuity of the lower half-relaxed limit, with the boundedness
hypotheses needed by real-valued `liminf`.
-/
theorem lowerSemicontinuousOn_lowerHalfRelaxedLimit
    (uᵢ : ι -> Point n -> Real) (l : Filter ι) (C : Set (Point n))
    (hbddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hcobddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ)) :
    LowerSemicontinuousOn (lowerHalfRelaxedLimit uᵢ l C) C := by
  intro x hxC y hy
  rcases exists_between hy with ⟨y', hyy', hy'x⟩
  have hlocal : ∀ᶠ q in halfRelaxedFilter l C x, y' < halfRelaxedValue uᵢ q :=
    eventually_lt_of_lt_liminf hy'x (hbddBelow x hxC)
  have hnear :
      ∀ᶠ z in nhdsWithin x C,
        {q : ι × Point n | y' < halfRelaxedValue uᵢ q} ∈ halfRelaxedFilter l C z :=
    eventually_mem_halfRelaxedFilter_of_mem hlocal
  have hmemC : ∀ᶠ z in nhdsWithin x C, z ∈ C := self_mem_nhdsWithin
  filter_upwards [hnear, hmemC] with z hz hzc
  have hzy : ∀ᶠ q in halfRelaxedFilter l C z, y' <= halfRelaxedValue uᵢ q := by
    filter_upwards [hz] with q hq
    exact le_of_lt hq
  have hle : y' <= lowerHalfRelaxedLimit uᵢ l C z :=
    le_liminf_of_le (hcobddAbove z hzc) hzy
  exact lt_of_lt_of_le hyy' hle

/--
Compact upper bound from strict upper half-relaxed bounds.

Assume `E` is compact, `E ⊆ C`, and
`upperHalfRelaxedLimit uᵢ l C x < a` for every `x ∈ E`. Then for every
`b > a`, the set of indices `i` for which `uᵢ i y < b` for all `y ∈ E`
belongs to `l`.
-/
theorem eventually_forall_lt_of_isCompact_upperHalfRelaxedLimit_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C E : Set (Point n)}
    {a b : Real} (hEcompact : IsCompact E) (hEC : E ⊆ C)
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hub : ∀ x ∈ E, upperHalfRelaxedLimit uᵢ l C x < a)
    (hab : a < b) :
    ∀ᶠ i in l, ∀ y ∈ E, uᵢ i y < b := by
  classical
  have hlocal : ∀ x ∈ E, {q : ι × Point n | uᵢ q.1 q.2 < b} ∈
      halfRelaxedFilter l C x := by
    intro x hxE
    have hlt : upperHalfRelaxedLimit uᵢ l C x < b :=
      lt_trans (hub x hxE) hab
    exact eventually_lt_of_limsup_lt hlt (hbddAbove x (hEC hxE))
  choose A hA V hV hsub using fun x hxE => Filter.mem_prod_iff.mp (hlocal x hxE)
  have hVE : ∀ x (hx : x ∈ E), V x hx ∈ nhdsWithin x E := by
    intro x hx
    exact mem_of_superset (nhdsWithin_mono x hEC (hV x hx)) fun y hy => hy
  rcases hEcompact.elim_nhdsWithin_subcover' V hVE with ⟨t, hcover⟩
  have hAfin : (⋂ x ∈ t, A x x.2) ∈ l :=
    (Filter.biInter_finset_mem t).2 fun x _ => hA x x.2
  filter_upwards [hAfin] with i hi y hyE
  rcases Set.mem_iUnion₂.1 (hcover hyE) with ⟨x, hxt, hyV⟩
  have hp : (i, y) ∈ A x x.2 ×ˢ V x x.2 :=
    ⟨Set.mem_iInter₂.1 hi x hxt, hyV⟩
  exact hsub x x.2 hp

/--
Compact lower bound from strict lower half-relaxed bounds.

Assume `E` is compact, `E ⊆ C`, and
`a < lowerHalfRelaxedLimit uᵢ l C x` for every `x ∈ E`. Then for every
`b < a`, the set of indices `i` for which `b < uᵢ i y` for all `y ∈ E`
belongs to `l`.
-/
theorem eventually_forall_lt_of_lt_isCompact_lowerHalfRelaxedLimit
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C E : Set (Point n)}
    {a b : Real} (hEcompact : IsCompact E) (hEC : E ⊆ C)
    (hbddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hlb : ∀ x ∈ E, a < lowerHalfRelaxedLimit uᵢ l C x)
    (hba : b < a) :
    ∀ᶠ i in l, ∀ y ∈ E, b < uᵢ i y := by
  classical
  have hlocal : ∀ x ∈ E, {q : ι × Point n | b < uᵢ q.1 q.2} ∈
      halfRelaxedFilter l C x := by
    intro x hxE
    have hlt : b < lowerHalfRelaxedLimit uᵢ l C x :=
      lt_trans hba (hlb x hxE)
    exact eventually_lt_of_lt_liminf hlt (hbddBelow x (hEC hxE))
  choose A hA V hV hsub using fun x hxE => Filter.mem_prod_iff.mp (hlocal x hxE)
  have hVE : ∀ x (hx : x ∈ E), V x hx ∈ nhdsWithin x E := by
    intro x hx
    exact mem_of_superset (nhdsWithin_mono x hEC (hV x hx)) fun y hy => hy
  rcases hEcompact.elim_nhdsWithin_subcover' V hVE with ⟨t, hcover⟩
  have hAfin : (⋂ x ∈ t, A x x.2) ∈ l :=
    (Filter.biInter_finset_mem t).2 fun x _ => hA x x.2
  filter_upwards [hAfin] with i hi y hyE
  rcases Set.mem_iUnion₂.1 (hcover hyE) with ⟨x, hxt, hyV⟩
  have hp : (i, y) ∈ A x x.2 ×ˢ V x x.2 :=
    ⟨Set.mem_iInter₂.1 hi x hxt, hyV⟩
  exact hsub x x.2 hp

/--
If the upper half-relaxed limit satisfies
`upperHalfRelaxedLimit uᵢ l C x - φ x < a`, then the approximating values
`uᵢ i y - φ y` satisfy the following filter statement for every `b > a`:
the set of pairs `(i, y)` such that `uᵢ i y - φ y < b` belongs to
`halfRelaxedFilter l C x`.
-/
theorem eventually_sub_test_lt_of_upperHalfRelaxedLimit_sub_test_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {a b : Real}
    (hbddAbove :
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x)
    (hlt : upperHalfRelaxedLimit uᵢ l C x - φ x < a) (hab : a < b) :
    ∀ᶠ q in halfRelaxedFilter l C x, uᵢ q.1 q.2 - φ q.2 < b := by
  rcases exists_between (lt_trans hlt hab) with ⟨c, hcU, hcb⟩
  have hU : upperHalfRelaxedLimit uᵢ l C x < c + φ x := by linarith
  have hval : ∀ᶠ q in halfRelaxedFilter l C x, uᵢ q.1 q.2 < c + φ x :=
    eventually_lt_of_limsup_lt hU hbddAbove
  have hgap : 0 < b - c := sub_pos.2 hcb
  have hcoord : Tendsto (fun q : ι × Point n => q.2)
      (halfRelaxedFilter l C x) (nhdsWithin x C) :=
    tendsto_snd
  have hφtendsto : Tendsto (fun q : ι × Point n => φ q.2)
      (halfRelaxedFilter l C x) (nhds (φ x)) :=
    hφ.tendsto.comp hcoord
  have hφevent : ∀ᶠ q in halfRelaxedFilter l C x, φ x - (b - c) < φ q.2 :=
    hφtendsto (Ioi_mem_nhds (by linarith))
  filter_upwards [hval, hφevent] with q hqval hqφ
  linarith

/--
If the lower half-relaxed limit satisfies
`a < lowerHalfRelaxedLimit uᵢ l C x - φ x`, then the approximating values
`uᵢ i y - φ y` satisfy the following filter statement for every `b < a`:
the set of pairs `(i, y)` such that `b < uᵢ i y - φ y` belongs to
`halfRelaxedFilter l C x`.
-/
theorem eventually_lt_sub_test_of_lt_lowerHalfRelaxedLimit_sub_test
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {a b : Real}
    (hbddBelow :
      (halfRelaxedFilter l C x).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x)
    (hlt : a < lowerHalfRelaxedLimit uᵢ l C x - φ x) (hba : b < a) :
    ∀ᶠ q in halfRelaxedFilter l C x, b < uᵢ q.1 q.2 - φ q.2 := by
  rcases exists_between (lt_trans hba hlt) with ⟨c, hbc, hcL⟩
  have hL : c + φ x < lowerHalfRelaxedLimit uᵢ l C x := by linarith
  have hval : ∀ᶠ q in halfRelaxedFilter l C x, c + φ x < uᵢ q.1 q.2 :=
    eventually_lt_of_lt_liminf hL hbddBelow
  have hgap : 0 < c - b := sub_pos.2 hbc
  have hcoord : Tendsto (fun q : ι × Point n => q.2)
      (halfRelaxedFilter l C x) (nhdsWithin x C) :=
    tendsto_snd
  have hφtendsto : Tendsto (fun q : ι × Point n => φ q.2)
      (halfRelaxedFilter l C x) (nhds (φ x)) :=
    hφ.tendsto.comp hcoord
  have hφevent : ∀ᶠ q in halfRelaxedFilter l C x, φ q.2 < φ x + (c - b) :=
    hφtendsto (Iio_mem_nhds (by linarith))
  filter_upwards [hval, hφevent] with q hqval hqφ
  linarith

/--
Compact upper bound for `uᵢ - φ` from strict upper half-relaxed test bounds.

Assume `E` is compact, `E ⊆ C`, and
`upperHalfRelaxedLimit uᵢ l C x - φ x < a` for every `x ∈ E`. If `a < b`,
then the set of indices `i` for which `uᵢ i y - φ y < b` for all `y ∈ E`
belongs to `l`.
-/
theorem eventually_forall_sub_test_lt_of_isCompact_upperHalfRelaxedLimit_sub_test_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C E : Set (Point n)}
    {φ : Point n -> Real} {a b : Real} (hEcompact : IsCompact E) (hEC : E ⊆ C)
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφ : ∀ x ∈ E, ContinuousWithinAt φ C x)
    (hub : ∀ x ∈ E, upperHalfRelaxedLimit uᵢ l C x - φ x < a)
    (hab : a < b) :
    ∀ᶠ i in l, ∀ y ∈ E, uᵢ i y - φ y < b := by
  classical
  have hlocal : ∀ x ∈ E, {q : ι × Point n | uᵢ q.1 q.2 - φ q.2 < b} ∈
      halfRelaxedFilter l C x := by
    intro x hxE
    exact eventually_sub_test_lt_of_upperHalfRelaxedLimit_sub_test_lt
      (hbddAbove x (hEC hxE)) (hφ x hxE) (hub x hxE) hab
  choose A hA V hV hsub using fun x hxE => Filter.mem_prod_iff.mp (hlocal x hxE)
  have hVE : ∀ x (hx : x ∈ E), V x hx ∈ nhdsWithin x E := by
    intro x hx
    exact mem_of_superset (nhdsWithin_mono x hEC (hV x hx)) fun y hy => hy
  rcases hEcompact.elim_nhdsWithin_subcover' V hVE with ⟨t, hcover⟩
  have hAfin : (⋂ x ∈ t, A x x.2) ∈ l :=
    (Filter.biInter_finset_mem t).2 fun x _ => hA x x.2
  filter_upwards [hAfin] with i hi y hyE
  rcases Set.mem_iUnion₂.1 (hcover hyE) with ⟨x, hxt, hyV⟩
  have hp : (i, y) ∈ A x x.2 ×ˢ V x x.2 :=
    ⟨Set.mem_iInter₂.1 hi x hxt, hyV⟩
  exact hsub x x.2 hp

/--
Compact lower bound for `uᵢ - φ` from strict lower half-relaxed test bounds.

Assume `E` is compact, `E ⊆ C`, and
`a < lowerHalfRelaxedLimit uᵢ l C x - φ x` for every `x ∈ E`. If `b < a`,
then the set of indices `i` for which `b < uᵢ i y - φ y` for all `y ∈ E`
belongs to `l`.
-/
theorem eventually_forall_lt_sub_test_of_lt_isCompact_lowerHalfRelaxedLimit_sub_test
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C E : Set (Point n)}
    {φ : Point n -> Real} {a b : Real} (hEcompact : IsCompact E) (hEC : E ⊆ C)
    (hbddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφ : ∀ x ∈ E, ContinuousWithinAt φ C x)
    (hlb : ∀ x ∈ E, a < lowerHalfRelaxedLimit uᵢ l C x - φ x)
    (hba : b < a) :
    ∀ᶠ i in l, ∀ y ∈ E, b < uᵢ i y - φ y := by
  classical
  have hlocal : ∀ x ∈ E, {q : ι × Point n | b < uᵢ q.1 q.2 - φ q.2} ∈
      halfRelaxedFilter l C x := by
    intro x hxE
    exact eventually_lt_sub_test_of_lt_lowerHalfRelaxedLimit_sub_test
      (hbddBelow x (hEC hxE)) (hφ x hxE) (hlb x hxE) hba
  choose A hA V hV hsub using fun x hxE => Filter.mem_prod_iff.mp (hlocal x hxE)
  have hVE : ∀ x (hx : x ∈ E), V x hx ∈ nhdsWithin x E := by
    intro x hx
    exact mem_of_superset (nhdsWithin_mono x hEC (hV x hx)) fun y hy => hy
  rcases hEcompact.elim_nhdsWithin_subcover' V hVE with ⟨t, hcover⟩
  have hAfin : (⋂ x ∈ t, A x x.2) ∈ l :=
    (Filter.biInter_finset_mem t).2 fun x _ => hA x x.2
  filter_upwards [hAfin] with i hi y hyE
  rcases Set.mem_iUnion₂.1 (hcover hyE) with ⟨x, hxt, hyV⟩
  have hp : (i, y) ∈ A x x.2 ×ˢ V x x.2 :=
    ⟨Set.mem_iInter₂.1 hi x hxt, hyV⟩
  exact hsub x x.2 hp

/--
If `a < upperHalfRelaxedLimit uᵢ l C x`, then every member of
`halfRelaxedFilter l C x` intersects the set of pairs `(i, y)` satisfying
`a < uᵢ i y`.
-/
theorem frequently_lt_upperHalfRelaxedLimit
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {a : Real}
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (ha : a < upperHalfRelaxedLimit uᵢ l C x) :
    ∃ᶠ q in halfRelaxedFilter l C x, a < halfRelaxedValue uᵢ q :=
  frequently_lt_of_lt_limsup hcobddBelow ha

/--
If `lowerHalfRelaxedLimit uᵢ l C x < a`, then every member of
`halfRelaxedFilter l C x` intersects the set of pairs `(i, y)` satisfying
`uᵢ i y < a`.
-/
theorem frequently_lowerHalfRelaxedLimit_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {a : Real}
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (ha : lowerHalfRelaxedLimit uᵢ l C x < a) :
    ∃ᶠ q in halfRelaxedFilter l C x, halfRelaxedValue uᵢ q < a :=
  frequently_lt_of_liminf_lt hcobddAbove ha

/--
For every `ε > 0`, every set of indices `A` with `A ∈ l`, and every
`V ∈ nhdsWithin x C`, there exist `i ∈ A` and `y ∈ V` such that
`upperHalfRelaxedLimit uᵢ l C x - ε < uᵢ i y`.
-/
theorem exists_upperHalfRelaxedLimit_sub_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {ε : Real} (hε : 0 < ε)
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhdsWithin x C) :
    ∃ i ∈ A, ∃ y ∈ V,
      upperHalfRelaxedLimit uᵢ l C x - ε < uᵢ i y := by
  have hlt : upperHalfRelaxedLimit uᵢ l C x - ε <
      upperHalfRelaxedLimit uᵢ l C x := by
    linarith
  have hfreq := frequently_lt_upperHalfRelaxedLimit
    (uᵢ := uᵢ) (l := l) (C := C) (x := x)
    (a := upperHalfRelaxedLimit uᵢ l C x - ε) hcobddBelow hlt
  have hbox : A ×ˢ V ∈ halfRelaxedFilter l C x :=
    Filter.prod_mem_prod hA hV
  rcases (hfreq.and_eventually hbox).exists with ⟨q, hqval, hqbox⟩
  exact ⟨q.1, hqbox.1, q.2, hqbox.2, hqval⟩

/--
For every `ε > 0`, every set of indices `A` with `A ∈ l`, and every
`V ∈ nhdsWithin x C`, there exist `i ∈ A` and `y ∈ V` such that
`uᵢ i y < lowerHalfRelaxedLimit uᵢ l C x + ε`.
-/
theorem exists_lt_lowerHalfRelaxedLimit_add
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {ε : Real} (hε : 0 < ε)
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhdsWithin x C) :
    ∃ i ∈ A, ∃ y ∈ V,
      uᵢ i y < lowerHalfRelaxedLimit uᵢ l C x + ε := by
  have hlt : lowerHalfRelaxedLimit uᵢ l C x <
      lowerHalfRelaxedLimit uᵢ l C x + ε := by
    linarith
  have hfreq := frequently_lowerHalfRelaxedLimit_lt
    (uᵢ := uᵢ) (l := l) (C := C) (x := x)
    (a := lowerHalfRelaxedLimit uᵢ l C x + ε) hcobddAbove hlt
  have hbox : A ×ˢ V ∈ halfRelaxedFilter l C x :=
    Filter.prod_mem_prod hA hV
  rcases (hfreq.and_eventually hbox).exists with ⟨q, hqval, hqbox⟩
  exact ⟨q.1, hqbox.1, q.2, hqbox.2, hqval⟩

/--
After subtracting a continuous test function, the approximating family
has the following lower selection property: for every `ε > 0`, every member
of `halfRelaxedFilter l C x` intersects the set of pairs `(i, y)` satisfying
`upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i y - φ y`.
-/
theorem frequently_lt_upperHalfRelaxedLimit_sub_test
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x) :
    ∃ᶠ q in halfRelaxedFilter l C x,
      upperHalfRelaxedLimit uᵢ l C x - φ x - ε <
        uᵢ q.1 q.2 - φ q.2 := by
  have hε2 : 0 < ε / 2 := by positivity
  have hlt : upperHalfRelaxedLimit uᵢ l C x - ε / 2 <
      upperHalfRelaxedLimit uᵢ l C x := by
    linarith
  have hval : ∃ᶠ q in halfRelaxedFilter l C x,
      upperHalfRelaxedLimit uᵢ l C x - ε / 2 < uᵢ q.1 q.2 :=
    frequently_lt_upperHalfRelaxedLimit
      (uᵢ := uᵢ) (l := l) (C := C) (x := x)
      (a := upperHalfRelaxedLimit uᵢ l C x - ε / 2) hcobddBelow hlt
  have hcoord : Tendsto (fun q : ι × Point n => q.2)
      (halfRelaxedFilter l C x) (nhdsWithin x C) :=
    tendsto_snd
  have hφtendsto : Tendsto (fun q : ι × Point n => φ q.2)
      (halfRelaxedFilter l C x) (nhds (φ x)) :=
    hφ.tendsto.comp hcoord
  have hφeventually : ∀ᶠ q in halfRelaxedFilter l C x, φ q.2 < φ x + ε / 2 :=
    hφtendsto (Iio_mem_nhds (by linarith))
  exact (hval.and_eventually hφeventually).mono fun q hq => by
    linarith

/--
After subtracting a continuous test function, the approximating family
has the following upper selection property: for every `ε > 0`, every member
of `halfRelaxedFilter l C x` intersects the set of pairs `(i, y)` satisfying
`uᵢ i y - φ y < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε`.
-/
theorem frequently_lowerHalfRelaxedLimit_sub_test_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x) :
    ∃ᶠ q in halfRelaxedFilter l C x,
      uᵢ q.1 q.2 - φ q.2 <
        lowerHalfRelaxedLimit uᵢ l C x - φ x + ε := by
  have hε2 : 0 < ε / 2 := by positivity
  have hlt : lowerHalfRelaxedLimit uᵢ l C x <
      lowerHalfRelaxedLimit uᵢ l C x + ε / 2 := by
    linarith
  have hval : ∃ᶠ q in halfRelaxedFilter l C x,
      uᵢ q.1 q.2 < lowerHalfRelaxedLimit uᵢ l C x + ε / 2 :=
    frequently_lowerHalfRelaxedLimit_lt
      (uᵢ := uᵢ) (l := l) (C := C) (x := x)
      (a := lowerHalfRelaxedLimit uᵢ l C x + ε / 2) hcobddAbove hlt
  have hcoord : Tendsto (fun q : ι × Point n => q.2)
      (halfRelaxedFilter l C x) (nhdsWithin x C) :=
    tendsto_snd
  have hφtendsto : Tendsto (fun q : ι × Point n => φ q.2)
      (halfRelaxedFilter l C x) (nhds (φ x)) :=
    hφ.tendsto.comp hcoord
  have hφeventually : ∀ᶠ q in halfRelaxedFilter l C x, φ x - ε / 2 < φ q.2 :=
    hφtendsto (Ioi_mem_nhds (by linarith))
  exact (hval.and_eventually hφeventually).mono fun q hq => by
    linarith

/--
For every `ε > 0`, every set of indices `A` with `A ∈ l`, and every
`V ∈ nhdsWithin x C`, there exist `i ∈ A` and `y ∈ V` such that
`upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i y - φ y`.
-/
theorem exists_upperHalfRelaxedLimit_sub_test_sub_lt
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hcobddBelow :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhdsWithin x C) :
    ∃ i ∈ A, ∃ y ∈ V,
      upperHalfRelaxedLimit uᵢ l C x - φ x - ε < uᵢ i y - φ y := by
  have hfreq := frequently_lt_upperHalfRelaxedLimit_sub_test
    (uᵢ := uᵢ) (l := l) (C := C) (x := x) (φ := φ) hε hcobddBelow hφ
  have hbox : A ×ˢ V ∈ halfRelaxedFilter l C x :=
    Filter.prod_mem_prod hA hV
  rcases (hfreq.and_eventually hbox).exists with ⟨q, hqval, hqbox⟩
  exact ⟨q.1, hqbox.1, q.2, hqbox.2, hqval⟩

/--
For every `ε > 0`, every set of indices `A` with `A ∈ l`, and every
`V ∈ nhdsWithin x C`, there exist `i ∈ A` and `y ∈ V` such that
`uᵢ i y - φ y < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε`.
-/
theorem exists_lt_lowerHalfRelaxedLimit_sub_test_add
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} {C : Set (Point n)}
    {x : Point n} {φ : Point n -> Real} {ε : Real} (hε : 0 < ε)
    (hcobddAbove :
      (halfRelaxedFilter l C x).IsCoboundedUnder (· >= ·) (halfRelaxedValue uᵢ))
    (hφ : ContinuousWithinAt φ C x)
    {A : Set ι} (hA : A ∈ l) {V : Set (Point n)} (hV : V ∈ nhdsWithin x C) :
    ∃ i ∈ A, ∃ y ∈ V,
      uᵢ i y - φ y < lowerHalfRelaxedLimit uᵢ l C x - φ x + ε := by
  have hfreq := frequently_lowerHalfRelaxedLimit_sub_test_lt
    (uᵢ := uᵢ) (l := l) (C := C) (x := x) (φ := φ) hε hcobddAbove hφ
  have hbox : A ×ˢ V ∈ halfRelaxedFilter l C x :=
    Filter.prod_mem_prod hA hV
  rcases (hfreq.and_eventually hbox).exists with ⟨q, hqval, hqbox⟩
  exact ⟨q.1, hqbox.1, q.2, hqbox.2, hqval⟩


end ViscositySolns
