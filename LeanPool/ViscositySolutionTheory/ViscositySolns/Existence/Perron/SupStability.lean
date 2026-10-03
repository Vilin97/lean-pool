/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Envelopes
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.HalfRelaxedLimits.Stability

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Supremum stability for Perron's method

This file should house the formal version of Section 4, Lemma 4.1: the upper
semicontinuous envelope of a locally bounded supremum of subsolutions is again
a subsolution. It may reuse the half-relaxed-limit semijet approximation
machinery, but it must not depend on the concrete comparison proof.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {ι : Type*}

/-- Pointwise supremum of an indexed family of real-valued functions. -/
def pointwiseSup (uᵢ : ι -> Point n -> Real) : Point n -> Real :=
  fun x => sSup {r : Real | ∃ i : ι, r = uᵢ i x}

theorem le_pointwiseSup
    {uᵢ : ι -> Point n -> Real} {x : Point n} {i : ι}
    (hbdd : BddAbove {r : Real | ∃ j : ι, r = uᵢ j x}) :
    uᵢ i x <= pointwiseSup uᵢ x := by
  exact le_csSup hbdd ⟨i, rfl⟩

theorem pointwiseSup_le
    {uᵢ : ι -> Point n -> Real} {x : Point n} {a : Real}
    (hne : (Set.range fun i : ι => uᵢ i x).Nonempty)
    (hle : ∀ i : ι, uᵢ i x <= a) :
    pointwiseSup uᵢ x <= a := by
  let S : Set Real := {r : Real | ∃ i : ι, r = uᵢ i x}
  have hneS : S.Nonempty := by
    rcases hne with ⟨r, i, rfl⟩
    exact ⟨uᵢ i x, i, rfl⟩
  have hleS : ∀ r ∈ S, r <= a := by
    intro r hr
    rcases hr with ⟨i, rfl⟩
    exact hle i
  exact csSup_le hneS hleS

/--
Taking the limsup of the pointwise supremum along `nhdsWithin` is the same as
taking the limsup of its pullback along the second projection of the
top-index product filter.
-/
theorem limsup_pointwiseSup_comp_snd_top
    [Nonempty ι] (uᵢ : ι -> Point n -> Real) (C : Set (Point n)) (x : Point n) :
    limsup (fun q : ι × Point n => pointwiseSup uᵢ q.2)
        ((⊤ : Filter ι) ×ˢ nhdsWithin x C) =
      upperEnvelope C (pointwiseSup uᵢ) x := by
  change limsup ((pointwiseSup uᵢ) ∘ Prod.snd)
        ((⊤ : Filter ι) ×ˢ nhdsWithin x C) =
      limsup (pointwiseSup uᵢ) (nhdsWithin x C)
  rw [Filter.top_prod, Filter.limsup_comp]
  rw [Filter.map_comap_of_surjective Prod.snd_surjective]

/--
If the pointwise supremum is frequently above a level, then the indexed family
is frequently above that level along the `⊤`-index half-relaxed filter.
-/
theorem frequently_lt_halfRelaxedValue_top_of_frequently_lt_pointwiseSup
    [Nonempty ι] {uᵢ : ι -> Point n -> Real} {C : Set (Point n)}
    {x : Point n} {a : Real}
    (hbddPoint : ∀ᶠ y in nhdsWithin x C,
      BddAbove {r : Real | ∃ i : ι, r = uᵢ i y})
    (hfreq : ∃ᶠ y in nhdsWithin x C, a < pointwiseSup uᵢ y) :
    ∃ᶠ q in (⊤ : Filter ι) ×ˢ nhdsWithin x C, a < uᵢ q.1 q.2 := by
  rw [Filter.frequently_iff]
  intro S hS
  rcases Filter.mem_prod_iff.mp hS with ⟨A, hA, V, hV, hsub⟩
  have hfreq' := hfreq.and_eventually hbddPoint
  rcases (hfreq'.and_eventually hV).exists with ⟨y, hydata, hyV⟩
  rcases hydata with ⟨hpsup, hbdd⟩
  have hne : ({r : Real | ∃ i : ι, r = uᵢ i y}).Nonempty := by
    rcases (inferInstance : Nonempty ι) with ⟨i0⟩
    exact ⟨uᵢ i0 y, i0, rfl⟩
  rcases (lt_csSup_iff hbdd hne).1 hpsup with ⟨r, hr, har⟩
  rcases hr with ⟨i, rfl⟩
  exact ⟨(i, y), hsub ⟨hA i, hyV⟩, har⟩

/--
The upper half-relaxed limit over the `⊤` index filter is bounded above by
the upper envelope of the indexed pointwise supremum.
-/
theorem upperHalfRelaxedLimit_top_le_upperEnvelope_pointwiseSup
    [Nonempty ι] {uᵢ : ι -> Point n -> Real} {C : Set (Point n)}
    {x : Point n}
    (hbddPoint : ∀ᶠ y in nhdsWithin x C,
      BddAbove {r : Real | ∃ i : ι, r = uᵢ i y})
    (hpointBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) (pointwiseSup uᵢ))
    (hhrCobddBelow :
      (halfRelaxedFilter (⊤ : Filter ι) C x).IsCoboundedUnder (· <= ·)
        (halfRelaxedValue uᵢ)) :
    upperHalfRelaxedLimit uᵢ (⊤ : Filter ι) C x <=
      upperEnvelope C (pointwiseSup uᵢ) x := by
  have hle : ∀ᶠ q in (⊤ : Filter ι) ×ˢ nhdsWithin x C,
      halfRelaxedValue uᵢ q <= pointwiseSup uᵢ q.2 := by
    filter_upwards [hbddPoint.prod_inr (⊤ : Filter ι)] with q hbdd
    exact le_pointwiseSup hbdd
  have hcompBdd :
      ((⊤ : Filter ι) ×ˢ nhdsWithin x C).IsBoundedUnder (· <= ·)
        (fun q : ι × Point n => pointwiseSup uᵢ q.2) := by
    rcases hpointBddAbove with ⟨a, ha⟩
    exact ⟨a, eventually_map.2 ((eventually_map.1 ha).prod_inr (⊤ : Filter ι))⟩
  have hlim : upperHalfRelaxedLimit uᵢ (⊤ : Filter ι) C x <=
      limsup (fun q : ι × Point n => pointwiseSup uᵢ q.2)
        ((⊤ : Filter ι) ×ˢ nhdsWithin x C) :=
    limsup_le_limsup hle hhrCobddBelow hcompBdd
  exact hlim.trans_eq (limsup_pointwiseSup_comp_snd_top uᵢ C x)

/--
The upper envelope of the indexed pointwise supremum is bounded above by the
upper half-relaxed limit over the `⊤` index filter.
-/
theorem upperEnvelope_pointwiseSup_le_upperHalfRelaxedLimit_top
    [Nonempty ι] {uᵢ : ι -> Point n -> Real} {C : Set (Point n)}
    {x : Point n}
    (hbddPoint : ∀ᶠ y in nhdsWithin x C,
      BddAbove {r : Real | ∃ i : ι, r = uᵢ i y})
    (hpointCobddBelow : (nhdsWithin x C).IsCoboundedUnder (· <= ·) (pointwiseSup uᵢ))
    (hhrCobddBelow :
      (halfRelaxedFilter (⊤ : Filter ι) C x).IsCoboundedUnder (· <= ·)
        (halfRelaxedValue uᵢ))
    (hhrBddAbove :
      (halfRelaxedFilter (⊤ : Filter ι) C x).IsBoundedUnder (· <= ·)
        (halfRelaxedValue uᵢ)) :
    upperEnvelope C (pointwiseSup uᵢ) x <=
      upperHalfRelaxedLimit uᵢ (⊤ : Filter ι) C x := by
  refine (le_limsup_iff hhrCobddBelow hhrBddAbove).2 ?_
  intro a ha
  have hfreq : ∃ᶠ y in nhdsWithin x C, a < pointwiseSup uᵢ y :=
    frequently_lt_upperEnvelope hpointCobddBelow ha
  exact frequently_lt_halfRelaxedValue_top_of_frequently_lt_pointwiseSup
    hbddPoint hfreq

/--
The upper envelope of a nonempty pointwise supremum is canonically represented
as an upper half-relaxed limit over the top filter on the index type.
-/
theorem upperEnvelope_pointwiseSup_eq_upperHalfRelaxedLimit_top
    [Nonempty ι] {uᵢ : ι -> Point n -> Real} {C : Set (Point n)}
    {x : Point n}
    (hbddPoint : ∀ᶠ y in nhdsWithin x C,
      BddAbove {r : Real | ∃ i : ι, r = uᵢ i y})
    (hpointBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) (pointwiseSup uᵢ))
    (hpointCobddBelow : (nhdsWithin x C).IsCoboundedUnder (· <= ·) (pointwiseSup uᵢ))
    (hhrCobddBelow :
      (halfRelaxedFilter (⊤ : Filter ι) C x).IsCoboundedUnder (· <= ·)
        (halfRelaxedValue uᵢ))
    (hhrBddAbove :
      (halfRelaxedFilter (⊤ : Filter ι) C x).IsBoundedUnder (· <= ·)
        (halfRelaxedValue uᵢ)) :
    upperEnvelope C (pointwiseSup uᵢ) x =
      upperHalfRelaxedLimit uᵢ (⊤ : Filter ι) C x :=
  le_antisymm
    (upperEnvelope_pointwiseSup_le_upperHalfRelaxedLimit_top
      hbddPoint hpointCobddBelow hhrCobddBelow hhrBddAbove)
    (upperHalfRelaxedLimit_top_le_upperEnvelope_pointwiseSup
      hbddPoint hpointBddAbove hhrCobddBelow)

/-- The subtype indexing the Perron family between a fixed barrier pair. -/
def PerronFamily (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (lower upper : Point n -> Real) : Type _ :=
  {w : Point n -> Real // PerronClass C boundary F g lower upper w}

/-- The function represented by an indexed Perron-family member. -/
def PerronFamily.fun
    {C boundary : Set (Point n)} {F : Operator n} {g lower upper : Point n -> Real}
    (w : PerronFamily C boundary F g lower upper) : Point n -> Real :=
  w.1

theorem PerronFamily.mem
    {C boundary : Set (Point n)} {F : Operator n} {g lower upper : Point n -> Real}
    (w : PerronFamily C boundary F g lower upper) :
    PerronClass C boundary F g lower upper w.fun :=
  w.2

/-- The Perron family is nonempty because it contains the lower barrier. -/
theorem DirichletBarrierPair.perronFamily_nonempty
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) :
    Nonempty (PerronFamily C boundary F g B.lower B.upper) :=
  ⟨⟨B.lower, B.lower_mem_perronClass⟩⟩

/--
The pointwise Perron envelope is the indexed pointwise supremum over the
subtype of Perron-class members.
-/
theorem perronEnvelope_eq_pointwiseSup_perronFamily
    (C boundary : Set (Point n)) (F : Operator n) (g lower upper : Point n -> Real) :
    perronEnvelope C boundary F g lower upper =
      pointwiseSup (fun w : PerronFamily C boundary F g lower upper => w.fun) := by
  funext x
  let S : Set Real := {r : Real | ∃ w : Point n -> Real,
    PerronClass C boundary F g lower upper w ∧ r = w x}
  let T : Set Real := {r : Real | ∃ w : PerronFamily C boundary F g lower upper,
    r = w.fun x}
  have hST : S = T := by
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.fun, w.mem, rfl⟩
  change sSup S = sSup T
  rw [hST]

theorem perronFamily_eventually_viscositySubsolution
    {C boundary : Set (Point n)} {F : Operator n} {g lower upper : Point n -> Real}
    {l : Filter (PerronFamily C boundary F g lower upper)} :
    ∀ᶠ w in l, ViscositySubsolution C F (w.fun) :=
  Filter.Eventually.of_forall fun w => w.mem.dirichletSubsolution.viscosity

/--
The upper barrier pointwise-bounds the Perron-family values near every point
of `C`, hence the family supremum is pointwise bounded above there.
-/
theorem DirichletBarrierPair.perronFamily_pointwise_bddAbove_eventually
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n} :
    ∀ᶠ y in nhdsWithin x C,
      BddAbove {r : Real |
        ∃ w : PerronFamily C boundary F g B.lower B.upper, r = w.fun y} := by
  filter_upwards [self_mem_nhdsWithin] with y hyC
  refine ⟨B.upper y, ?_⟩
  intro r hr
  rcases hr with ⟨w, rfl⟩
  exact w.mem.le_upper (Or.inl hyC)

/-- Local upper-barrier boundedness bounds the Perron-family half-relaxed values above. -/
theorem DirichletBarrierPair.perronFamily_halfRelaxed_isBoundedUnder_le_top
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hupper : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper) :
    (halfRelaxedFilter
        (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x).IsBoundedUnder
      (· <= ·)
      (halfRelaxedValue
        (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)) := by
  rcases hupper with ⟨a, ha⟩
  refine ⟨a, eventually_map.2 ?_⟩
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  have hC : ∀ᶠ q in halfRelaxedFilter
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x, q.2 ∈ C :=
    hCWithin.prod_inr
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper))
  have hUpper : ∀ᶠ q in halfRelaxedFilter
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x,
      B.upper q.2 <= a :=
    (eventually_map.1 ha).prod_inr
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper))
  filter_upwards [hC, hUpper] with q hqC hqUpper
  exact (q.1.mem.le_upper (Or.inl hqC)).trans hqUpper

/-- Local lower-barrier boundedness bounds the Perron-family half-relaxed values below. -/
theorem DirichletBarrierPair.perronFamily_halfRelaxed_isBoundedUnder_ge_top
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hlower : (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    (halfRelaxedFilter
        (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x).IsBoundedUnder
      (· >= ·)
      (halfRelaxedValue
        (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)) := by
  rcases hlower with ⟨a, ha⟩
  refine ⟨a, eventually_map.2 ?_⟩
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  have hC : ∀ᶠ q in halfRelaxedFilter
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x, q.2 ∈ C :=
    hCWithin.prod_inr
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper))
  have hLower : ∀ᶠ q in halfRelaxedFilter
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x,
      a <= B.lower q.2 :=
    (eventually_map.1 ha).prod_inr
      (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper))
  filter_upwards [hC, hLower] with q hqC hqLower
  exact hqLower.trans (q.1.mem.lower_le (Or.inl hqC))

/--
The Perron-family pointwise supremum has the same local upper bound as the
upper barrier.
-/
theorem DirichletBarrierPair.pointwiseSup_perronFamily_isBoundedUnder_le
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hupper : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper) :
    (nhdsWithin x C).IsBoundedUnder (· <= ·)
      (pointwiseSup
        (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)) := by
  let : Nonempty (PerronFamily C boundary F g B.lower B.upper) :=
    B.perronFamily_nonempty
  rcases hupper with ⟨a, ha⟩
  refine ⟨a, eventually_map.2 ?_⟩
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  filter_upwards [eventually_map.1 ha, hCWithin] with y hyUpper hyC
  have hleUpper :
      pointwiseSup (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun) y <=
        B.upper y := by
    refine pointwiseSup_le (Set.range_nonempty _) ?_
    intro w
    exact w.mem.le_upper (Or.inl hyC)
  exact hleUpper.trans hyUpper

/--
The Perron-family pointwise supremum has the same local lower bound as the
lower barrier.
-/
theorem DirichletBarrierPair.pointwiseSup_perronFamily_isBoundedUnder_ge
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hlower : (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    (nhdsWithin x C).IsBoundedUnder (· >= ·)
      (pointwiseSup
        (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)) := by
  let : Nonempty (PerronFamily C boundary F g B.lower B.upper) :=
    B.perronFamily_nonempty
  rcases hlower with ⟨a, ha⟩
  refine ⟨a, eventually_map.2 ?_⟩
  have hCWithin : ∀ᶠ y in nhdsWithin x C, y ∈ C := self_mem_nhdsWithin
  filter_upwards [eventually_map.1 ha, hCWithin,
      B.perronFamily_pointwise_bddAbove_eventually] with y hyLower hyC hbdd
  have hLowerLe :
      B.lower y <=
        pointwiseSup (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun) y :=
    le_pointwiseSup (uᵢ := fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)
      (x := y) (i := ⟨B.lower, B.lower_mem_perronClass⟩) hbdd
  exact hyLower.trans hLowerLe

/--
The Perron upper envelope is the upper half-relaxed limit of the Perron family
with the top filter on the Perron class.
-/
theorem DirichletBarrierPair.upperEnvelope_perronEnvelope_eq_upperHalfRelaxedLimit_top
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupper : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlower : (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x =
      upperHalfRelaxedLimit
        (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)
        (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x := by
  let : Nonempty (PerronFamily C boundary F g B.lower B.upper) :=
    B.perronFamily_nonempty
  let : (nhdsWithin x C).NeBot := hne
  have hhrBddAbove :=
    B.perronFamily_halfRelaxed_isBoundedUnder_le_top (x := x) hupper
  have hhrBddBelow :=
    B.perronFamily_halfRelaxed_isBoundedUnder_ge_top (x := x) hlower
  have : NeBot
      (halfRelaxedFilter
        (⊤ : Filter (PerronFamily C boundary F g B.lower B.upper)) C x) := by
    rw [halfRelaxedFilter_def]
    infer_instance
  rw [perronEnvelope_eq_pointwiseSup_perronFamily]
  refine upperEnvelope_pointwiseSup_eq_upperHalfRelaxedLimit_top
    (B.perronFamily_pointwise_bddAbove_eventually (x := x))
    (B.pointwiseSup_perronFamily_isBoundedUnder_le (x := x) hupper)
    ?_
    hhrBddBelow.isCoboundedUnder_le
    hhrBddAbove
  exact (B.pointwiseSup_perronFamily_isBoundedUnder_ge (x := x) hlower).isCoboundedUnder_le

/--
Supremum stability in the form consumed by Perron's method.

If the upper envelope of a candidate `w` is identified with an upper
half-relaxed limit of eventually subsolution approximants, then the envelope
is a viscosity subsolution. The separate equality hypothesis lets later Perron
code choose whatever enumeration/selection of the Perron family is most
convenient.
-/
theorem ViscositySubsolution.upperEnvelope_of_eq_upperHalfRelaxedLimit
    {C : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {w : Point n -> Real} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C w = ViscositySolns.upperHalfRelaxedLimit uᵢ l C) :
    ViscositySubsolution C F (upperEnvelope C w) := by
  rw [hEq]
  exact ViscositySubsolution.upperHalfRelaxedLimit hF hsub hbddAbove hcobddBelow

/--
The same stability adapter specialized to the Perron envelope. The substantive
selection work is isolated in the equality with an upper half-relaxed limit;
once that representation is available, the viscosity inequality is supplied by
the existing stability theorem.
-/
theorem DirichletBarrierPair.perronUpperEnvelope_viscositySubsolution
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real} (B : DirichletBarrierPair C boundary F g)
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C) :
    ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  ViscositySubsolution.upperEnvelope_of_eq_upperHalfRelaxedLimit
    hF hsub hbddAbove hcobddBelow hEq

/--
Perron upper-envelope stability specialized to the Perron family as the
approximating index type. The eventual subsolution hypothesis is automatic
from membership in the Perron class.
-/
theorem DirichletBarrierPair.perronUpperEnvelope_viscositySubsolution_of_perronFamily
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real} (B : DirichletBarrierPair C boundary F g)
    {l : Filter (PerronFamily C boundary F g B.lower B.upper)}
    (hF : OperatorContinuous F)
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·)
        (halfRelaxedValue (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·)
        (halfRelaxedValue (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun)))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit
        (fun w : PerronFamily C boundary F g B.lower B.upper => w.fun) l C) :
    ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronUpperEnvelope_viscositySubsolution hF
    perronFamily_eventually_viscositySubsolution hbddAbove hcobddBelow hEq

/--
Perron upper-envelope stability using the Perron family itself, indexed by the
top filter. This removes the need for callers to provide a separate
half-relaxed-limit representation of the Perron envelope on `C`.
-/
theorem DirichletBarrierPair.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real} (B : DirichletBarrierPair C boundary F g)
    (hF : OperatorContinuous F)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  let ιP := PerronFamily C boundary F g B.lower B.upper
  let uP : ιP -> Point n -> Real := fun w => w.fun
  let : Nonempty ιP := B.perronFamily_nonempty
  have hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter (⊤ : Filter ιP) C x).IsBoundedUnder (· <= ·)
        (halfRelaxedValue uP) := by
    intro x hx
    exact B.perronFamily_halfRelaxed_isBoundedUnder_le_top
      (x := x) (hupperBddAbove x hx)
  have hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter (⊤ : Filter ιP) C x).IsCoboundedUnder (· <= ·)
        (halfRelaxedValue uP) := by
    intro x hx
    let : (nhdsWithin x C).NeBot := hne x hx
    have : NeBot (halfRelaxedFilter (⊤ : Filter ιP) C x) := by
      rw [halfRelaxedFilter_def]
      infer_instance
    exact (B.perronFamily_halfRelaxed_isBoundedUnder_ge_top
      (x := x) (hlowerBddBelow x hx)).isCoboundedUnder_le
  have hupperHR : ViscositySubsolution C F
      (upperHalfRelaxedLimit uP (⊤ : Filter ιP) C) :=
    ViscositySubsolution.upperHalfRelaxedLimit hF
      perronFamily_eventually_viscositySubsolution hbddAbove hcobddBelow
  refine hupperHR.congr_eqOn ?_
  intro x hx
  symm
  exact B.upperEnvelope_perronEnvelope_eq_upperHalfRelaxedLimit_top
    (x := x) (hne x hx) (hupperBddAbove x hx) (hlowerBddBelow x hx)

/--
Dirichlet version of Perron upper-envelope stability.

The viscosity subsolution property comes from the half-relaxed-limit
representation, while the boundary inequality is inherited from the upper
barrier trace.
-/
theorem DirichletBarrierPair.perronUpperEnvelope_dirichletSubsolution
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real} (B : DirichletBarrierPair C boundary F g)
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hperronCobddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hupperBddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hupperSemi : UpperSemicontinuousOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary)) :
    DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  ⟨B.perronUpperEnvelope_viscositySubsolution
      hF hsub hbddAbove hcobddBelow hEq,
      B.perronUpperEnvelope_boundarySubsolution hupperTrace
      hperronCobddBelowOnBoundary hupperBddAboveOnBoundary,
    hupperSemi⟩

/--
Dirichlet Perron upper-envelope stability with boundary coboundedness inherited
from the lower barrier.
-/
theorem DirichletBarrierPair.perronUpperEnvelope_dirichletSubsolution_of_barrierLocalBounded
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real} (B : DirichletBarrierPair C boundary F g)
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hneBoundary : ∀ x : Point n, x ∈ boundary -> (nhdsWithin x C).NeBot)
    (hlowerBddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hupperBddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hupperSemi : UpperSemicontinuousOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary)) :
    DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine B.perronUpperEnvelope_dirichletSubsolution hF hsub hbddAbove
    hcobddBelow hEq hupperTrace ?_ hupperBddAboveOnBoundary hupperSemi
  intro x hx
  let : (nhdsWithin x C).NeBot := hneBoundary x hx
  exact B.perronEnvelope_isCoboundedUnder_le (hlowerBddBelowOnBoundary x hx)

end ViscositySolns
