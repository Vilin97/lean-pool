/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Envelope infrastructure for Perron's method

This file contains the upper and lower semicontinuous envelopes used in
Section 4 and the first pointwise order facts for the Perron envelope. The
definitions use `nhdsWithin` filters rather than metric balls; in finite
dimension this is the same local operation and is a better fit for the
existing semijet/stability infrastructure.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/-- The upper semicontinuous envelope of `u` relative to the domain `C`. -/
def upperEnvelope (C : Set (Point n)) (u : Point n -> Real) : Point n -> Real :=
  fun x => limsup u (nhdsWithin x C)

/-- The lower semicontinuous envelope of `u` relative to the domain `C`. -/
def lowerEnvelope (C : Set (Point n)) (u : Point n -> Real) : Point n -> Real :=
  fun x => liminf u (nhdsWithin x C)

theorem upperEnvelope_def (C : Set (Point n)) (u : Point n -> Real) (x : Point n) :
    upperEnvelope C u x = limsup u (nhdsWithin x C) :=
  rfl

theorem lowerEnvelope_def (C : Set (Point n)) (u : Point n -> Real) (x : Point n) :
    lowerEnvelope C u x = liminf u (nhdsWithin x C) :=
  rfl

/--
If a level lies strictly below the upper envelope at `x`, then points of `C`
arbitrarily close to `x` have values above that level.
-/
theorem frequently_lt_upperEnvelope
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {a : Real}
    (hcobddBelow : (nhdsWithin x C).IsCoboundedUnder (· <= ·) u)
    (ha : a < upperEnvelope C u x) :
    ∃ᶠ y in nhdsWithin x C, a < u y :=
  frequently_lt_of_lt_limsup hcobddBelow ha

/--
If the lower envelope at `x` lies strictly below a level, then points of `C`
arbitrarily close to `x` have values below that level.
-/
theorem frequently_lowerEnvelope_lt
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {a : Real}
    (hcobddAbove : (nhdsWithin x C).IsCoboundedUnder (· >= ·) u)
    (ha : lowerEnvelope C u x < a) :
    ∃ᶠ y in nhdsWithin x C, u y < a :=
  frequently_lt_of_liminf_lt hcobddAbove ha

/--
Every relative neighborhood of `x` contains a point whose value is above a
strict level below the upper envelope.
-/
theorem exists_mem_nhdsWithin_lt_upperEnvelope
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {a : Real}
    (hcobddBelow : (nhdsWithin x C).IsCoboundedUnder (· <= ·) u)
    (ha : a < upperEnvelope C u x) {V : Set (Point n)}
    (hV : V ∈ nhdsWithin x C) :
    ∃ y ∈ V, a < u y := by
  rcases ((frequently_lt_upperEnvelope hcobddBelow ha).and_eventually hV).exists
    with ⟨y, hyval, hyV⟩
  exact ⟨y, hyV, hyval⟩

/--
Every relative neighborhood of `x` contains a point whose value is below a
strict level above the lower envelope.
-/
theorem exists_mem_nhdsWithin_lowerEnvelope_lt
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {a : Real}
    (hcobddAbove : (nhdsWithin x C).IsCoboundedUnder (· >= ·) u)
    (ha : lowerEnvelope C u x < a) {V : Set (Point n)}
    (hV : V ∈ nhdsWithin x C) :
    ∃ y ∈ V, u y < a := by
  rcases ((frequently_lowerEnvelope_lt hcobddAbove ha).and_eventually hV).exists
    with ⟨y, hyval, hyV⟩
  exact ⟨y, hyV, hyval⟩

/--
For every positive `ε`, every relative neighborhood of `x` contains a point
with value above `upperEnvelope C u x - ε`.
-/
theorem exists_upperEnvelope_sub_lt
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {ε : Real}
    (hε : 0 < ε)
    (hcobddBelow : (nhdsWithin x C).IsCoboundedUnder (· <= ·) u)
    {V : Set (Point n)} (hV : V ∈ nhdsWithin x C) :
    ∃ y ∈ V, upperEnvelope C u x - ε < u y := by
  have hlt : upperEnvelope C u x - ε < upperEnvelope C u x :=
    sub_lt_self _ hε
  exact exists_mem_nhdsWithin_lt_upperEnvelope hcobddBelow hlt hV

/--
For every positive `ε`, every relative neighborhood of `x` contains a point
with value below `lowerEnvelope C u x + ε`.
-/
theorem exists_lt_lowerEnvelope_add
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {ε : Real}
    (hε : 0 < ε)
    (hcobddAbove : (nhdsWithin x C).IsCoboundedUnder (· >= ·) u)
    {V : Set (Point n)} (hV : V ∈ nhdsWithin x C) :
    ∃ y ∈ V, u y < lowerEnvelope C u x + ε := by
  have hlt : lowerEnvelope C u x < lowerEnvelope C u x + ε :=
    lt_add_of_pos_right _ hε
  exact exists_mem_nhdsWithin_lowerEnvelope_lt hcobddAbove hlt hV

/-- The upper envelope is upper semicontinuous on any set where its defining
filters satisfy the real-valued limsup boundedness conditions. In particular,
the set may include boundary points of `C`. -/
theorem upperSemicontinuousOn_upperEnvelope_on
    {C S : Set (Point n)} {u : Point n -> Real}
    (hbddAbove : ∀ x ∈ S, (nhdsWithin x C).IsBoundedUnder (· <= ·) u)
    (hcobddBelow : ∀ x ∈ S, (nhdsWithin x C).IsCoboundedUnder (· <= ·) u) :
    UpperSemicontinuousOn (upperEnvelope C u) S := by
  intro x hx y hy
  rcases exists_between hy with ⟨y', hxy', hy'y⟩
  have hlocal : ∀ᶠ z in nhdsWithin x C, u z < y' :=
    eventually_lt_of_limsup_lt hxy' (hbddAbove x hx)
  have hnear : ∀ᶠ z in nhdsWithin x S, ∀ᶠ q in nhdsWithin z C, u q < y' :=
    (eventually_nhds_nhdsWithin.mpr hlocal).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, self_mem_nhdsWithin] with z hz hzS
  exact lt_of_le_of_lt
    (limsup_le_of_le (hcobddBelow z hzS) (hz.mono fun _ h => le_of_lt h)) hy'y

/-- The lower envelope is lower semicontinuous also at boundary points,
provided its defining filters satisfy the real-valued liminf bounds. -/
theorem lowerSemicontinuousOn_lowerEnvelope_on
    {C S : Set (Point n)} {u : Point n -> Real}
    (hbddBelow : ∀ x ∈ S, (nhdsWithin x C).IsBoundedUnder (· >= ·) u)
    (hcobddAbove : ∀ x ∈ S, (nhdsWithin x C).IsCoboundedUnder (· >= ·) u) :
    LowerSemicontinuousOn (lowerEnvelope C u) S := by
  intro x hx y hy
  rcases exists_between hy with ⟨y', hyy', hy'x⟩
  have hlocal : ∀ᶠ z in nhdsWithin x C, y' < u z :=
    eventually_lt_of_lt_liminf hy'x (hbddBelow x hx)
  have hnear : ∀ᶠ z in nhdsWithin x S, ∀ᶠ q in nhdsWithin z C, y' < u q :=
    (eventually_nhds_nhdsWithin.mpr hlocal).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, self_mem_nhdsWithin] with z hz hzS
  exact lt_of_lt_of_le hyy'
    (le_liminf_of_le (hcobddAbove z hzS) (hz.mono fun _ h => le_of_lt h))

/-- The upper envelope is upper semicontinuous on `C`, under local boundedness. -/
theorem upperSemicontinuousOn_upperEnvelope
    {C : Set (Point n)} {u : Point n -> Real}
    (hbddAbove : ∀ x ∈ C, (nhdsWithin x C).IsBoundedUnder (· <= ·) u)
    (hcobddBelow : ∀ x ∈ C, (nhdsWithin x C).IsCoboundedUnder (· <= ·) u) :
    UpperSemicontinuousOn (upperEnvelope C u) C :=
  upperSemicontinuousOn_upperEnvelope_on hbddAbove hcobddBelow

/-- The lower envelope is lower semicontinuous on `C`, under local boundedness. -/
theorem lowerSemicontinuousOn_lowerEnvelope
    {C : Set (Point n)} {u : Point n -> Real}
    (hbddBelow : ∀ x ∈ C, (nhdsWithin x C).IsBoundedUnder (· >= ·) u)
    (hcobddAbove : ∀ x ∈ C, (nhdsWithin x C).IsCoboundedUnder (· >= ·) u) :
    LowerSemicontinuousOn (lowerEnvelope C u) C :=
  lowerSemicontinuousOn_lowerEnvelope_on hbddBelow hcobddAbove

/-- Lower semicontinuous boundary trace of a function relative to `C`. -/
def BoundaryLowerTraceOn (C boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> lowerEnvelope C u x = g x

/-- Upper semicontinuous boundary trace of a function relative to `C`. -/
def BoundaryUpperTraceOn (C boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> upperEnvelope C u x = g x

theorem upperEnvelope_le_of_eventually_le
    {C : Set (Point n)} {u v : Point n -> Real} {x : Point n}
    (h : ∀ᶠ y in nhdsWithin x C, u y <= v y)
    (hu : (nhdsWithin x C).IsCoboundedUnder (· <= ·) u)
    (hv : (nhdsWithin x C).IsBoundedUnder (· <= ·) v) :
    upperEnvelope C u x <= upperEnvelope C v x := by
  exact limsup_le_limsup h hu hv

theorem lowerEnvelope_le_of_eventually_le
    {C : Set (Point n)} {u v : Point n -> Real} {x : Point n}
    (h : ∀ᶠ y in nhdsWithin x C, u y <= v y)
    (hu : (nhdsWithin x C).IsBoundedUnder (· >= ·) u)
    (hv : (nhdsWithin x C).IsCoboundedUnder (· >= ·) v) :
    lowerEnvelope C u x <= lowerEnvelope C v x := by
  exact liminf_le_liminf h hu hv

theorem lowerEnvelope_le_upperEnvelope
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n}
    [NeBot (nhdsWithin x C)]
    (hbddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) u)
    (hbddBelow : (nhdsWithin x C).IsBoundedUnder (· >= ·) u) :
    lowerEnvelope C u x <= upperEnvelope C u x := by
  exact liminf_le_limsup hbddAbove hbddBelow

theorem le_upperEnvelope
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n}
    (hx : x ∈ C)
    (hbddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) u) :
    u x <= upperEnvelope C u x := by
  have hfreqPure : ∃ᶠ y in pure x, u x <= u y := by
    simp
  have hfreq : ∃ᶠ y in nhdsWithin x C, u x <= u y :=
    hfreqPure.filter_mono (pure_le_nhdsWithin hx)
  exact le_limsup_of_frequently_le hfreq hbddAbove

theorem lowerEnvelope_le
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n}
    (hx : x ∈ C)
    (hbddBelow : (nhdsWithin x C).IsBoundedUnder (· >= ·) u) :
    lowerEnvelope C u x <= u x := by
  have hfreqPure : ∃ᶠ y in pure x, u y <= u x := by
    simp
  have hfreq : ∃ᶠ y in nhdsWithin x C, u y <= u x :=
    hfreqPure.filter_mono (pure_le_nhdsWithin hx)
  exact liminf_le_of_frequently_le hfreq hbddBelow

theorem DirichletBarrierPair.lower_le_perronEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hx : x ∈ C ∪ boundary) :
    B.lower x <= perronEnvelope C boundary F g B.lower B.upper x := by
  let S : Set Real := {r : Real | ∃ w : Point n -> Real,
    PerronClass C boundary F g B.lower B.upper w ∧ r = w x}
  have hbdd : BddAbove S := by
    refine ⟨B.upper x, ?_⟩
    intro r hr
    rcases hr with ⟨w, hw, rfl⟩
    exact hw.le_upper hx
  have hmem : B.lower x ∈ S :=
    ⟨B.lower, B.lower_mem_perronClass, rfl⟩
  exact le_csSup hbdd hmem

theorem DirichletBarrierPair.perronEnvelope_le_upper
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hx : x ∈ C ∪ boundary) :
    perronEnvelope C boundary F g B.lower B.upper x <= B.upper x := by
  let S : Set Real := {r : Real | ∃ w : Point n -> Real,
    PerronClass C boundary F g B.lower B.upper w ∧ r = w x}
  have hne : S.Nonempty :=
    ⟨B.lower x, B.lower, B.lower_mem_perronClass, rfl⟩
  have hle : ∀ r ∈ S, r <= B.upper x := by
    intro r hr
    rcases hr with ⟨w, hw, rfl⟩
    exact hw.le_upper hx
  exact csSup_le hne hle

theorem DirichletBarrierPair.lowerEnvelope_le_perronEnvelope_lowerEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hlower : (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hperron : (nhdsWithin x C).IsCoboundedUnder (· >= ·)
      (perronEnvelope C boundary F g B.lower B.upper)) :
    lowerEnvelope C B.lower x <=
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x := by
  refine lowerEnvelope_le_of_eventually_le ?_ hlower hperron
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact B.lower_le_perronEnvelope (Or.inl hy)

theorem DirichletBarrierPair.perronEnvelope_upperEnvelope_le_upperEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hperron : (nhdsWithin x C).IsCoboundedUnder (· <= ·)
      (perronEnvelope C boundary F g B.lower B.upper))
    (hupper : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper) :
    upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
      upperEnvelope C B.upper x := by
  refine upperEnvelope_le_of_eventually_le ?_ hperron hupper
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact B.perronEnvelope_le_upper (Or.inl hy)

theorem DirichletBarrierPair.perronEnvelope_isBoundedUnder_le
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hupper : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper) :
    (nhdsWithin x C).IsBoundedUnder (· <= ·)
      (perronEnvelope C boundary F g B.lower B.upper) := by
  refine hupper.mono_le ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact B.perronEnvelope_le_upper (Or.inl hy)

theorem DirichletBarrierPair.perronEnvelope_isBoundedUnder_ge
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hlower : (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    (nhdsWithin x C).IsBoundedUnder (· >= ·)
      (perronEnvelope C boundary F g B.lower B.upper) := by
  refine hlower.mono_ge ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact B.lower_le_perronEnvelope (Or.inl hy)

theorem DirichletBarrierPair.perronEnvelope_isCoboundedUnder_le
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    [NeBot (nhdsWithin x C)]
    (hlower : (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    (nhdsWithin x C).IsCoboundedUnder (· <= ·)
      (perronEnvelope C boundary F g B.lower B.upper) :=
  (B.perronEnvelope_isBoundedUnder_ge hlower).isCoboundedUnder_le

theorem DirichletBarrierPair.perronEnvelope_isCoboundedUnder_ge
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    [NeBot (nhdsWithin x C)]
    (hupper : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper) :
    (nhdsWithin x C).IsCoboundedUnder (· >= ·)
      (perronEnvelope C boundary F g B.lower B.upper) :=
  (B.perronEnvelope_isBoundedUnder_le hupper).isCoboundedUnder_ge

/-- Barrier bounds give upper semicontinuity of the Perron upper envelope
throughout the domain and boundary. -/
theorem DirichletBarrierPair.perronUpperEnvelope_upperSemicontinuousOn
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x ∈ C ∪ boundary, (nhdsWithin x C).NeBot)
    (hupper : ∀ x ∈ C ∪ boundary,
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlower : ∀ x ∈ C ∪ boundary,
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    UpperSemicontinuousOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary) := by
  refine upperSemicontinuousOn_upperEnvelope_on
    (fun x hx => B.perronEnvelope_isBoundedUnder_le (hupper x hx)) ?_
  intro x hx
  let : (nhdsWithin x C).NeBot := hne x hx
  exact B.perronEnvelope_isCoboundedUnder_le (hlower x hx)

/-- Barrier bounds give lower semicontinuity of the Perron lower envelope
throughout the domain and boundary. -/
theorem DirichletBarrierPair.perronLowerEnvelope_lowerSemicontinuousOn
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x ∈ C ∪ boundary, (nhdsWithin x C).NeBot)
    (hupper : ∀ x ∈ C ∪ boundary,
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlower : ∀ x ∈ C ∪ boundary,
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    LowerSemicontinuousOn
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary) := by
  refine lowerSemicontinuousOn_lowerEnvelope_on
    (fun x hx => B.perronEnvelope_isBoundedUnder_ge (hlower x hx)) ?_
  intro x hx
  let : (nhdsWithin x C).NeBot := hne x hx
  exact B.perronEnvelope_isCoboundedUnder_ge (hupper x hx)

theorem DirichletBarrierPair.perronUpperEnvelope_boundarySubsolution
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (htrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hperron : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hupper : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper) :
    BoundarySubsolutionOn boundary g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  intro x hx
  have hle :
      upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
        upperEnvelope C B.upper x :=
    B.perronEnvelope_upperEnvelope_le_upperEnvelope (hperron x hx) (hupper x hx)
  exact hle.trans_eq (htrace x hx)

theorem DirichletBarrierPair.perronLowerEnvelope_boundarySupersolution
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (htrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hlower : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hperron : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper)) :
    BoundarySupersolutionOn boundary g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  intro x hx
  have hle :
      lowerEnvelope C B.lower x <=
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
    B.lowerEnvelope_le_perronEnvelope_lowerEnvelope (hlower x hx) (hperron x hx)
  exact (htrace x hx).symm.le.trans hle

end ViscositySolns
