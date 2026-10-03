/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Data.Rat.Denumerable
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Localized one-dimensional maximal functions

This file records the source-proof localized maximal-function notation used in the one-dimensional
measure estimate. The analytic weak-type proof is intentionally kept as a named statement
boundary; later work should prove it using Mathlib's one-dimensional Vitali covering machinery.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Average mass of a measure over the open interval `(a,b)`, using the Euclidean length `b-a`.
The source only uses this when `a < b`. -/
def openIntervalMeasureAverage (μ : Measure ℝ) (a b : ℝ) : ℝ :=
  μ.real (Set.Ioo a b) / (b - a)

/-- Real-valued continuity from below for an increasing sequence of sets with finite union
mass. -/
theorem tendsto_measureReal_iUnion_atTop
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : ℕ → Set α}
    (hm : Monotone s) (hfin : μ (⋃ n, s n) < ⊤) :
    Tendsto (fun n : ℕ => μ.real (s n)) atTop
      (nhds (μ.real (⋃ n, s n))) := by
  change Tendsto (fun n : ℕ => (μ (s n)).toReal) atTop
    (nhds ((μ (⋃ n, s n)).toReal))
  rw [ENNReal.tendsto_toReal_iff
    (fun n : ℕ => measure_ne_top_of_subset (Set.subset_iUnion s n) hfin.ne) hfin.ne]
  exact tendsto_measure_iUnion_atTop (μ := μ) hm

/-- If a monotone sequence of open intervals exhausts `(a,b)` and the limiting interval has
finite mass, then the real masses converge to the limiting real mass. -/
theorem tendsto_measureReal_Ioo_of_iUnion_eq
    {μ : Measure ℝ} {a b : ℝ} {q r : ℕ → ℝ}
    (hmono : Monotone fun n : ℕ => Set.Ioo (q n) (r n))
    (hUnion : (⋃ n : ℕ, Set.Ioo (q n) (r n)) = Set.Ioo a b)
    (hfin : μ (Set.Ioo a b) < ⊤) :
    Tendsto (fun n : ℕ => μ.real (Set.Ioo (q n) (r n))) atTop
      (nhds (μ.real (Set.Ioo a b))) := by
  have hfinUnion : μ (⋃ n : ℕ, Set.Ioo (q n) (r n)) < ⊤ := by
    simpa [hUnion] using hfin
  simpa [hUnion] using
    tendsto_measureReal_iUnion_atTop (μ := μ)
      (s := fun n : ℕ => Set.Ioo (q n) (r n)) hmono hfinUnion

/-- Open intervals are monotone under decreasing left endpoints and increasing right endpoints. -/
theorem monotone_Ioo_of_antitone_left_monotone_right
    {q r : ℕ → ℝ} (hq : Antitone q) (hr : Monotone r) :
    Monotone fun n : ℕ => Set.Ioo (q n) (r n) := by
  intro m n hmn x hx
  exact ⟨lt_of_le_of_lt (hq hmn) hx.1, lt_of_lt_of_le hx.2 (hr hmn)⟩

/-- Inner open intervals whose endpoints tend to the endpoints of `(a,b)` exhaust `(a,b)`. -/
theorem iUnion_Ioo_eq_Ioo_of_forall_mem_tendsto
    {a b : ℝ} {q r : ℕ → ℝ}
    (hqmem : ∀ n : ℕ, a < q n) (hrmem : ∀ n : ℕ, r n < b)
    (hq : Tendsto q atTop (nhds a)) (hr : Tendsto r atTop (nhds b)) :
    (⋃ n : ℕ, Set.Ioo (q n) (r n)) = Set.Ioo a b := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
    exact ⟨(hqmem n).trans hxn.1, hxn.2.trans (hrmem n)⟩
  · intro hx
    have hqevent : ∀ᶠ n : ℕ in atTop, q n < x :=
      hq (Iio_mem_nhds hx.1)
    have hrevent : ∀ᶠ n : ℕ in atTop, x < r n :=
      hr (Ioi_mem_nhds hx.2)
    rcases Filter.eventually_atTop.1 (hqevent.and hrevent) with ⟨N, hN⟩
    exact Set.mem_iUnion.2 ⟨N, hN N le_rfl⟩

/-- Mass convergence for nested inner intervals whose endpoints tend to the limiting endpoints. -/
theorem tendsto_measureReal_Ioo_of_antitone_left_monotone_right_tendsto
    {μ : Measure ℝ} {a b : ℝ} {q r : ℕ → ℝ}
    (hqmem : ∀ n : ℕ, a < q n) (hrmem : ∀ n : ℕ, r n < b)
    (hqanti : Antitone q) (hrmono : Monotone r)
    (hqtend : Tendsto q atTop (nhds a)) (hrtend : Tendsto r atTop (nhds b))
    (hfin : μ (Set.Ioo a b) < ⊤) :
    Tendsto (fun n : ℕ => μ.real (Set.Ioo (q n) (r n))) atTop
      (nhds (μ.real (Set.Ioo a b))) := by
  exact tendsto_measureReal_Ioo_of_iUnion_eq
    (μ := μ) (a := a) (b := b) (q := q) (r := r)
    (monotone_Ioo_of_antitone_left_monotone_right hqanti hrmono)
    (iUnion_Ioo_eq_Ioo_of_forall_mem_tendsto hqmem hrmem hqtend hrtend) hfin

/-- Rational points decreasing to the left endpoint from inside a prescribed interval. -/
theorem exists_rat_strictAnti_tendsto_within
    {a s : ℝ} (has : a < s) :
    ∃ q : ℕ → ℚ,
      StrictAnti q ∧
        (∀ n : ℕ, a < (q n : ℝ) ∧ (q n : ℝ) < s) ∧
          Tendsto (fun n : ℕ => (q n : ℝ)) atTop (nhds a) := by
  rcases Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
      Rat.cast_strictMono.monotone has with
    ⟨q, hqmono, hqmem, hqtend⟩
  exact ⟨q, hqmono, hqmem, by simpa [Function.comp_def] using hqtend⟩

/-- Rational points increasing to the right endpoint from inside a prescribed interval. -/
theorem exists_rat_strictMono_tendsto_within
    {s b : ℝ} (hsb : s < b) :
    ∃ r : ℕ → ℚ,
      StrictMono r ∧
        (∀ n : ℕ, s < (r n : ℝ) ∧ (r n : ℝ) < b) ∧
          Tendsto (fun n : ℕ => (r n : ℝ)) atTop (nhds b) := by
  rcases Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
      Rat.cast_strictMono.monotone hsb with
    ⟨r, hrmono, hrmem, hrtend⟩
  exact ⟨r, hrmono, hrmem, by simpa [Function.comp_def] using hrtend⟩

/-- Generic rational inner-interval mass approximation by continuity from below. -/
theorem exists_rat_inner_tendsto_measureReal_Ioo
    {μ : Measure ℝ} {a s b : ℝ} (has : a < s) (hsb : s < b)
    (hfin : μ (Set.Ioo a b) < ⊤) :
    ∃ q r : ℕ → ℚ,
      (∀ n : ℕ,
        a < (q n : ℝ) ∧
          (q n : ℝ) < s ∧ s < (r n : ℝ) ∧ (r n : ℝ) < b) ∧
        Tendsto (fun n : ℕ => (q n : ℝ)) atTop (nhds a) ∧
          Tendsto (fun n : ℕ => (r n : ℝ)) atTop (nhds b) ∧
            Tendsto (fun n : ℕ => μ.real (Set.Ioo (q n : ℝ) (r n : ℝ))) atTop
              (nhds (μ.real (Set.Ioo a b))) := by
  rcases exists_rat_strictAnti_tendsto_within has with
    ⟨q, hqanti, hqmem, hqtend⟩
  rcases exists_rat_strictMono_tendsto_within hsb with
    ⟨r, hrmono, hrmem, hrtend⟩
  have hqantiReal : Antitone fun n : ℕ => (q n : ℝ) := by
    intro m n hmn
    change ((q n : ℚ) : ℝ) ≤ ((q m : ℚ) : ℝ)
    exact_mod_cast hqanti.antitone hmn
  have hrmonoReal : Monotone fun n : ℕ => (r n : ℝ) := by
    intro m n hmn
    change ((r m : ℚ) : ℝ) ≤ ((r n : ℚ) : ℝ)
    exact_mod_cast hrmono.monotone hmn
  refine ⟨q, r, ?_, hqtend, hrtend, ?_⟩
  · intro n
    exact ⟨(hqmem n).1, (hqmem n).2, (hrmem n).1, (hrmem n).2⟩
  · exact tendsto_measureReal_Ioo_of_antitone_left_monotone_right_tendsto
      (μ := μ) (a := a) (b := b)
      (q := fun n : ℕ => (q n : ℝ)) (r := fun n : ℕ => (r n : ℝ))
      (fun n => (hqmem n).1) (fun n => (hrmem n).2)
      hqantiReal hrmonoReal hqtend hrtend hfin

/-- Interval averages converge if the numerator masses converge and the endpoint lengths
converge to a nonzero length. -/
theorem tendsto_openIntervalMeasureAverage_of_tendsto_measureReal
    {μ : Measure ℝ} {a b : ℝ} {q r : ℕ → ℝ}
    (hmass :
      Tendsto (fun n : ℕ => μ.real (Set.Ioo (q n) (r n))) atTop
        (nhds (μ.real (Set.Ioo a b))))
    (hq : Tendsto q atTop (nhds a)) (hr : Tendsto r atTop (nhds b)) (hab : a < b) :
    Tendsto (fun n : ℕ => openIntervalMeasureAverage μ (q n) (r n)) atTop
      (nhds (openIntervalMeasureAverage μ a b)) := by
  rw [openIntervalMeasureAverage]
  have hden : Tendsto (fun n : ℕ => r n - q n) atTop (nhds (b - a)) := hr.sub hq
  exact hmass.div hden (sub_ne_zero.mpr hab.ne')

/-- Rational endpoint version of `tendsto_openIntervalMeasureAverage_of_tendsto_measureReal`. -/
theorem tendsto_openIntervalMeasureAverage_of_tendsto_measureReal_rat
    {μ : Measure ℝ} {a b : ℝ} {q r : ℕ → ℚ}
    (hmass :
      Tendsto (fun n : ℕ => μ.real (Set.Ioo (q n : ℝ) (r n : ℝ))) atTop
        (nhds (μ.real (Set.Ioo a b))))
    (hq : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (nhds a))
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)) atTop (nhds b)) (hab : a < b) :
    Tendsto (fun n : ℕ => openIntervalMeasureAverage μ (q n : ℝ) (r n : ℝ)) atTop
      (nhds (openIntervalMeasureAverage μ a b)) :=
  tendsto_openIntervalMeasureAverage_of_tendsto_measureReal hmass hq hr hab

/-- The set of interval averages used in the localized maximal function. Naming this set keeps
later endpoint-control lemmas from repeatedly unfolding the `sSup` expression. -/
def localizedIntervalAverageSet (μ : Measure ℝ) (domain : Set ℝ) (s : ℝ) : Set ℝ :=
  {m : ℝ |
    ∃ a b : ℝ,
      a < b ∧ Set.Ioo a b ⊆ domain ∧ s ∈ Set.Ioo a b ∧
        m = openIntervalMeasureAverage μ a b}

/-- Localized one-dimensional Hardy-Littlewood maximal function over open intervals contained in
`domain`.

This matches the source expression
`sup { μ(I) / |I| : I ⊂ domain open interval, s ∈ I }`, written with endpoints `a < b`. -/
def localizedMaximalFunction (μ : Measure ℝ) (domain : Set ℝ) (s : ℝ) : ℝ :=
  sSup (localizedIntervalAverageSet μ domain s)

/-- Pointwise localized maximal bad predicate.

The first disjunct records the extended-valued case: if the interval averages through `s` are
unbounded, the maximal function is effectively infinite and `s` is bad for every finite
threshold. -/
def localizedMaximalBadPredicate (μ : Measure ℝ) (domain : Set ℝ) (s t : ℝ) : Prop :=
  ¬ BddAbove (localizedIntervalAverageSet μ domain s) ∨
    t < localizedMaximalFunction μ domain s

/-- Bad set for a localized one-dimensional maximal function, restricted to a window. -/
def localizedMaximalBadSet (μ : Measure ℝ) (domain window : Set ℝ) (t : ℝ) : Set ℝ :=
  {s | s ∈ window ∧ localizedMaximalBadPredicate μ domain s t}

/-- Source domain `(-2,2)` for the localized maximal estimate. -/
def sourceMaximalDomain : Set ℝ :=
  Set.Ioo (-2 : ℝ) 2

/-- Source conclusion window `(-1,1)` for the localized maximal estimate. -/
def sourceMaximalWindow : Set ℝ :=
  Set.Ioo (-1 : ℝ) 1

/-- Source localized maximal bad set `{s ∈ (-1,1) : M μ(s) > t}`. -/
def sourceLocalizedMaximalBadSet (μ : Measure ℝ) (t : ℝ) : Set ℝ :=
  localizedMaximalBadSet μ sourceMaximalDomain sourceMaximalWindow t

/-- Pointwise source localized maximal bad predicate, without the `(-1,1)` window restriction.
The cube bad sets already impose `x ∈ Q_1`, so they use this predicate form. -/
def sourceLocalizedMaximalBadPredicate (μ : Measure ℝ) (s t : ℝ) : Prop :=
  localizedMaximalBadPredicate μ sourceMaximalDomain s t

/-- Product-coordinate measurability of a parameterized source-local maximal bad predicate.

Here `μparam a` is the one-dimensional measure attached to parameter `a`, and the product
coordinate is `(a,s)`. This is the natural measurability target for sliced Fubini arguments. -/
def SourceLocalizedMaximalBadPredicateMeasurable
    {α : Type*} [MeasurableSpace α] (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  MeasurableSet {p : α × ℝ | sourceLocalizedMaximalBadPredicate (μparam p.1) p.2 t}

/-- Source-window-restricted product-coordinate measurability of a parameterized source-local
maximal bad predicate. This is the exact form needed by the source cube proof, where the
coordinate parameter is already known to lie in `(-1,1)`. -/
def SourceLocalizedMaximalBadPredicateMeasurableOnWindow
    {α : Type*} [MeasurableSpace α] (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  MeasurableSet
    {p : α × ℝ |
      p.2 ∈ sourceMaximalWindow ∧ sourceLocalizedMaximalBadPredicate (μparam p.1) p.2 t}

/-- Source-window interval-average existence set for a parameterized one-dimensional measure
family. -/
def sourceLocalizedMaximalAverageExceedsSet
    {α : Type*} (μparam : α → Measure ℝ) (t : ℝ) : Set (α × ℝ) :=
  {p : α × ℝ |
    p.2 ∈ sourceMaximalWindow ∧
      ∃ a b : ℝ,
        a < b ∧ Set.Ioo a b ⊆ sourceMaximalDomain ∧ p.2 ∈ Set.Ioo a b ∧
          t < openIntervalMeasureAverage (μparam p.1) a b}

/-- Fixed-interval piece of the source-window interval-average existence set. -/
def sourceLocalizedMaximalAverageExceedsFixedIntervalSet
    {α : Type*} (μparam : α → Measure ℝ) (a b t : ℝ) : Set (α × ℝ) :=
  {p : α × ℝ |
    p.2 ∈ sourceMaximalWindow ∧
      a < b ∧ Set.Ioo a b ⊆ sourceMaximalDomain ∧ p.2 ∈ Set.Ioo a b ∧
        t < openIntervalMeasureAverage (μparam p.1) a b}

/-- Countable fixed-interval model for the source-window interval-average existence set. Later
Stieltjes work should instantiate this with a rational interval family and prove that it agrees
with `sourceLocalizedMaximalAverageExceedsSet`. -/
def sourceLocalizedMaximalAverageExceedsCountableIntervalSet
    {α : Type*} (μparam : α → Measure ℝ) (a b : ℕ → ℝ) (t : ℝ) : Set (α × ℝ) :=
  ⋃ k : ℕ, sourceLocalizedMaximalAverageExceedsFixedIntervalSet μparam (a k) (b k) t

/-- An enumerated interval family is admissible for the source-local maximal construction if
each interval is nondegenerate and contained in the source maximal domain. -/
def SourceAdmissibleIntervalEnumeration (a b : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, a k < b k ∧ Set.Ioo (a k) (b k) ⊆ sourceMaximalDomain

/-- An enumerated interval family contains every rational source-admissible interval. This is
the countability part of the source-local maximal measurability reduction; the analytic
approximation step is kept separate below. -/
def SourceRationalIntervalEnumeration (a b : ℕ → ℝ) : Prop :=
  SourceAdmissibleIntervalEnumeration a b ∧
    ∀ q r : ℚ,
      (q : ℝ) < (r : ℝ) →
        Set.Ioo (q : ℝ) (r : ℝ) ⊆ sourceMaximalDomain →
          ∃ k : ℕ, a k = (q : ℝ) ∧ b k = (r : ℝ)

/-- The type of rational source-admissible intervals. This is the countable subtype whose
surjective enumeration supplies `SourceRationalIntervalEnumeration`. -/
def SourceRationalAdmissibleInterval : Type :=
  {p : ℚ × ℚ //
    (p.1 : ℝ) < (p.2 : ℝ) ∧ Set.Ioo (p.1 : ℝ) (p.2 : ℝ) ⊆ sourceMaximalDomain}

/-- The source rational-admissible interval type is nonempty, for instance by `(-1,1)`. -/
theorem nonempty_sourceRationalAdmissibleInterval :
    Nonempty SourceRationalAdmissibleInterval := by
  refine ⟨⟨((-1 : ℚ), (1 : ℚ)), ?_, ?_⟩⟩
  · norm_num
  · intro x hx
    rcases hx with ⟨hxleft, hxright⟩
    rw [sourceMaximalDomain]
    constructor <;> norm_num at hxleft hxright ⊢ <;> linarith

/-- There exists a sequence of real endpoints enumerating every rational source-admissible
interval and only source-admissible intervals. -/
theorem exists_sourceRationalIntervalEnumeration :
    ∃ a b : ℕ → ℝ, SourceRationalIntervalEnumeration a b := by
  classical
  have : Nonempty SourceRationalAdmissibleInterval :=
    nonempty_sourceRationalAdmissibleInterval
  have : Countable SourceRationalAdmissibleInterval := by
    dsimp [SourceRationalAdmissibleInterval]
    infer_instance
  rcases exists_surjective_nat SourceRationalAdmissibleInterval with ⟨e, he⟩
  refine
    ⟨fun k : ℕ => ((e k).1.1 : ℝ), fun k : ℕ => ((e k).1.2 : ℝ), ?_⟩
  constructor
  · intro k
    exact (e k).2
  · intro q r hqr hsub
    rcases he ⟨(q, r), hqr, hsub⟩ with ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · simp [hk]
    · simp [hk]

/-- The admissibility part of a rational source interval enumeration. -/
theorem SourceRationalIntervalEnumeration.admissible
    {a b : ℕ → ℝ} (henum : SourceRationalIntervalEnumeration a b) :
    SourceAdmissibleIntervalEnumeration a b :=
  henum.1

/-- A rational source interval enumeration contains any rational admissible interval. -/
theorem SourceRationalIntervalEnumeration.exists_index
    {a b : ℕ → ℝ} (henum : SourceRationalIntervalEnumeration a b)
    {q r : ℚ} (hqr : (q : ℝ) < (r : ℝ))
    (hsub : Set.Ioo (q : ℝ) (r : ℝ) ⊆ sourceMaximalDomain) :
    ∃ k : ℕ, a k = (q : ℝ) ∧ b k = (r : ℝ) :=
  henum.2 q r hqr hsub

/-- A rational subinterval of a source-admissible real interval is source-admissible. -/
theorem rat_Ioo_subset_sourceMaximalDomain_of_subset
    {a b : ℝ} {q r : ℚ}
    (hsub : Set.Ioo a b ⊆ sourceMaximalDomain)
    (haq : a < (q : ℝ)) (hrb : (r : ℝ) < b) :
    Set.Ioo (q : ℝ) (r : ℝ) ⊆ sourceMaximalDomain := by
  intro y hy
  rcases hy with ⟨hqy, hyr⟩
  exact hsub ⟨by linarith, by linarith⟩

/-- Pure geometry: every source-admissible real interval through `s` contains a rational
source-admissible subinterval through `s`. -/
theorem exists_rat_sourceInterval_subset_of_mem
    {a b s : ℝ} (hsub : Set.Ioo a b ⊆ sourceMaximalDomain)
    (hs : s ∈ Set.Ioo a b) :
    ∃ q r : ℚ,
      a < (q : ℝ) ∧ (q : ℝ) < s ∧ s < (r : ℝ) ∧ (r : ℝ) < b ∧
        (q : ℝ) < (r : ℝ) ∧ Set.Ioo (q : ℝ) (r : ℝ) ⊆ sourceMaximalDomain := by
  rcases hs with ⟨has, hsb⟩
  rcases exists_rat_btwn has with ⟨q, haq, hqs⟩
  rcases exists_rat_btwn hsb with ⟨r, hsr, hrb⟩
  exact ⟨q, r, haq, hqs, hsr, hrb, by linarith,
    rat_Ioo_subset_sourceMaximalDomain_of_subset hsub haq hrb⟩

/-- Reverse cover obligation for a countable interval model of the source average-exceeds set.

This is the analytic density/approximation direction: every real admissible interval with average
strictly above the threshold must be replaceable by one of the enumerated intervals. -/
def SourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover
    {α : Type*} (μparam : α → Measure ℝ) (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  sourceLocalizedMaximalAverageExceedsSet μparam t ⊆
    sourceLocalizedMaximalAverageExceedsCountableIntervalSet μparam a b t

/-- Rational refinement of the source average-exceeds set: every point witnessed by some real
admissible interval has a rational source-admissible interval witness with the same strict
average inequality. -/
def SourceLocalizedMaximalAverageExceedsRationalRefinement
    {α : Type*} (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  ∀ p : α × ℝ,
    p ∈ sourceLocalizedMaximalAverageExceedsSet μparam t →
      ∃ q r : ℚ,
        (q : ℝ) < (r : ℝ) ∧
          Set.Ioo (q : ℝ) (r : ℝ) ⊆ sourceMaximalDomain ∧
            p.2 ∈ Set.Ioo (q : ℝ) (r : ℝ) ∧
              t < openIntervalMeasureAverage (μparam p.1) (q : ℝ) (r : ℝ)

/-- Real-interval form of the rational refinement obligation. This is the form closest to the
source proof: start from one admissible real interval with average above the threshold and
shrink/perturb to a rational admissible interval preserving the strict inequality. -/
def SourceRealIntervalAverageExceedsRationalRefinement
    {α : Type*} (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  ∀ (p : α × ℝ) {a b : ℝ},
    a < b →
      Set.Ioo a b ⊆ sourceMaximalDomain →
        p.2 ∈ Set.Ioo a b →
          t < openIntervalMeasureAverage (μparam p.1) a b →
            ∃ q r : ℚ,
              (q : ℝ) < (r : ℝ) ∧
                Set.Ioo (q : ℝ) (r : ℝ) ⊆ sourceMaximalDomain ∧
                  p.2 ∈ Set.Ioo (q : ℝ) (r : ℝ) ∧
                    t < openIntervalMeasureAverage (μparam p.1) (q : ℝ) (r : ℝ)

/-- Inner-rational refinement form of the average-exceeds obligation. This is the exact
source-continuity step: the rational witness is a subinterval of the original real witness and
still contains the base point. -/
def SourceRealIntervalAverageExceedsInnerRationalRefinement
    {α : Type*} (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  ∀ (p : α × ℝ) {a b : ℝ},
    a < b →
      Set.Ioo a b ⊆ sourceMaximalDomain →
        p.2 ∈ Set.Ioo a b →
          t < openIntervalMeasureAverage (μparam p.1) a b →
            ∃ q r : ℚ,
              a < (q : ℝ) ∧
                (q : ℝ) < p.2 ∧
                  p.2 < (r : ℝ) ∧
                    (r : ℝ) < b ∧
                      t < openIntervalMeasureAverage (μparam p.1) (q : ℝ) (r : ℝ)

/-- Sequential inner-rational average approximation. This is the continuity-from-below form
which should be proved for the Stieltjes slice measures: choose rational inner intervals through
`p.2` whose averages converge to the original interval average. -/
def SourceRealIntervalAverageExceedsInnerRationalTendsto
    {α : Type*} (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  ∀ (p : α × ℝ) {a b : ℝ},
    a < b →
      Set.Ioo a b ⊆ sourceMaximalDomain →
        p.2 ∈ Set.Ioo a b →
          t < openIntervalMeasureAverage (μparam p.1) a b →
            ∃ q r : ℕ → ℚ,
              (∀ n : ℕ,
                a < (q n : ℝ) ∧
                  (q n : ℝ) < p.2 ∧ p.2 < (r n : ℝ) ∧ (r n : ℝ) < b) ∧
                Tendsto
                  (fun n : ℕ =>
                    openIntervalMeasureAverage (μparam p.1) (q n : ℝ) (r n : ℝ))
                  atTop
                  (nhds (openIntervalMeasureAverage (μparam p.1) a b))

/-- Sequential inner-rational mass approximation. This is the measure-continuity part of the
source-local rational refinement: rational inner intervals through `p.2` have masses converging
to the original interval mass. -/
def SourceRealIntervalAverageExceedsInnerRationalMassTendsto
    {α : Type*} (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  ∀ (p : α × ℝ) {a b : ℝ},
    a < b →
      Set.Ioo a b ⊆ sourceMaximalDomain →
        p.2 ∈ Set.Ioo a b →
          t < openIntervalMeasureAverage (μparam p.1) a b →
            ∃ q r : ℕ → ℚ,
              (∀ n : ℕ,
                a < (q n : ℝ) ∧
                  (q n : ℝ) < p.2 ∧ p.2 < (r n : ℝ) ∧ (r n : ℝ) < b) ∧
                Tendsto (fun n : ℕ => (q n : ℝ)) atTop (nhds a) ∧
                  Tendsto (fun n : ℕ => (r n : ℝ)) atTop (nhds b) ∧
                    Tendsto
                      (fun n : ℕ => (μparam p.1).real (Set.Ioo (q n : ℝ) (r n : ℝ)))
                      atTop
                      (nhds ((μparam p.1).real (Set.Ioo a b)))

/-- Finite mass on every source-admissible real interval gives the sequential inner-rational
mass approximation target. -/
theorem SourceRealIntervalAverageExceedsInnerRationalMassTendsto.of_finiteOnAdmissibleIntervals
    {α : Type*} {μparam : α → Measure ℝ} {t : ℝ}
    (hfinite :
      ∀ (x : α) {a b : ℝ},
        a < b →
          Set.Ioo a b ⊆ sourceMaximalDomain →
            μparam x (Set.Ioo a b) < ⊤) :
    SourceRealIntervalAverageExceedsInnerRationalMassTendsto μparam t := by
  intro p a b hab hsub hpinterval _havg
  exact exists_rat_inner_tendsto_measureReal_Ioo hpinterval.1 hpinterval.2
    (hfinite p.1 hab hsub)

/-- Mass convergence along rational inner intervals gives average convergence along those
intervals. -/
theorem SourceRealIntervalAverageExceedsInnerRationalTendsto.of_massTendsto
    {α : Type*} {μparam : α → Measure ℝ} {t : ℝ}
    (hmassApprox : SourceRealIntervalAverageExceedsInnerRationalMassTendsto μparam t) :
    SourceRealIntervalAverageExceedsInnerRationalTendsto μparam t := by
  intro p a b hab hsub hpinterval havg
  rcases hmassApprox p hab hsub hpinterval havg with
    ⟨q, r, hbounds, hq, hr, hmass⟩
  refine ⟨q, r, hbounds, ?_⟩
  exact tendsto_openIntervalMeasureAverage_of_tendsto_measureReal_rat hmass hq hr hab

/-- Sequential inner-rational approximation gives the existential inner-rational refinement
because the original average inequality is strict. -/
theorem SourceRealIntervalAverageExceedsInnerRationalRefinement.of_tendsto
    {α : Type*} {μparam : α → Measure ℝ} {t : ℝ}
    (happrox : SourceRealIntervalAverageExceedsInnerRationalTendsto μparam t) :
    SourceRealIntervalAverageExceedsInnerRationalRefinement μparam t := by
  intro p a b hab hsub hpinterval havg
  rcases happrox p hab hsub hpinterval havg with ⟨q, r, hbounds, htend⟩
  have hev :
      ∀ᶠ n : ℕ in atTop,
        t < openIntervalMeasureAverage (μparam p.1) (q n : ℝ) (r n : ℝ) :=
    htend.eventually_const_lt havg
  rcases (Filter.eventually_atTop.1 hev) with ⟨N, hN⟩
  rcases hbounds N with ⟨haq, hqs, hsr, hrb⟩
  exact ⟨q N, r N, haq, hqs, hsr, hrb, hN N le_rfl⟩

/-- The inner-rational refinement form gives the real-interval rational refinement form. -/
theorem SourceRealIntervalAverageExceedsRationalRefinement.of_inner
    {α : Type*} {μparam : α → Measure ℝ} {t : ℝ}
    (hrefine : SourceRealIntervalAverageExceedsInnerRationalRefinement μparam t) :
    SourceRealIntervalAverageExceedsRationalRefinement μparam t := by
  intro p a b hab hsub hpinterval havg
  rcases hrefine p hab hsub hpinterval havg with ⟨q, r, haq, hqs, hsr, hrb, hqravg⟩
  refine ⟨q, r, by linarith, ?_, ⟨hqs, hsr⟩, hqravg⟩
  exact rat_Ioo_subset_sourceMaximalDomain_of_subset hsub haq hrb

/-- The real-interval refinement form gives the set-level rational refinement form. -/
theorem SourceLocalizedMaximalAverageExceedsRationalRefinement.of_realInterval
    {α : Type*} {μparam : α → Measure ℝ} {t : ℝ}
    (hrefine : SourceRealIntervalAverageExceedsRationalRefinement μparam t) :
    SourceLocalizedMaximalAverageExceedsRationalRefinement μparam t := by
  intro p hp
  rcases hp with ⟨_hwindow, a, b, hab, hsub, hpinterval, havg⟩
  exact hrefine p hab hsub hpinterval havg

/-- A rational interval enumeration converts rational average refinement into the reverse-cover
direction needed for countable fixed-interval measurability. -/
theorem SourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover.of_rationalRefinement
    {α : Type*} {μparam : α → Measure ℝ} {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine : SourceLocalizedMaximalAverageExceedsRationalRefinement μparam t) :
    SourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover μparam a b t := by
  intro p hp
  have hp_set : p ∈ sourceLocalizedMaximalAverageExceedsSet μparam t := hp
  rcases hp with ⟨hwindow, _hwitness⟩
  rcases hrefine p hp_set with ⟨q, r, hqr, hsub, hpinterval, havg⟩
  rcases henum.exists_index hqr hsub with ⟨k, hak, hbk⟩
  rw [sourceLocalizedMaximalAverageExceedsCountableIntervalSet]
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  rw [sourceLocalizedMaximalAverageExceedsFixedIntervalSet, hak, hbk]
  exact ⟨hwindow, hqr, hsub, hpinterval, havg⟩

/-- The countable interval model is contained in the real-existential average-exceeds set as
soon as every enumerated interval is source-admissible. -/
theorem sourceLocalizedMaximalAverageExceedsCountableIntervalSet_subset
    {α : Type*} {μparam : α → Measure ℝ} {a b : ℕ → ℝ} {t : ℝ}
    (hadm : SourceAdmissibleIntervalEnumeration a b) :
    sourceLocalizedMaximalAverageExceedsCountableIntervalSet μparam a b t ⊆
      sourceLocalizedMaximalAverageExceedsSet μparam t := by
  intro p hp
  rw [sourceLocalizedMaximalAverageExceedsCountableIntervalSet] at hp
  rcases Set.mem_iUnion.mp hp with ⟨k, hk⟩
  rcases hk with ⟨hwindow, _hab, _hsub, hpinterval, havg⟩
  exact ⟨hwindow, a k, b k, (hadm k).1, (hadm k).2, hpinterval, havg⟩

/-- An admissible countable interval family represents the source average-exceeds set once the
analytic reverse-cover direction has been proved. -/
theorem sourceLocalizedMaximalAverageExceedsCountableIntervalCover_of_reverseCover
    {α : Type*} {μparam : α → Measure ℝ} {a b : ℕ → ℝ} {t : ℝ}
    (hadm : SourceAdmissibleIntervalEnumeration a b)
    (hreverse :
      SourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover μparam a b t) :
    sourceLocalizedMaximalAverageExceedsSet μparam t =
      sourceLocalizedMaximalAverageExceedsCountableIntervalSet μparam a b t :=
  le_antisymm hreverse
    (sourceLocalizedMaximalAverageExceedsCountableIntervalSet_subset hadm)

/-- Source-window interval-average existence measurability for a parameterized one-dimensional
measure family. -/
def SourceLocalizedMaximalAverageExceedsMeasurable
    {α : Type*} [MeasurableSpace α] (μparam : α → Measure ℝ) (t : ℝ) : Prop :=
  MeasurableSet (sourceLocalizedMaximalAverageExceedsSet μparam t)

/-- Measurability of every fixed-interval piece in a countable interval model. -/
def SourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable
    {α : Type*} [MeasurableSpace α] (μparam : α → Measure ℝ) (a b : ℕ → ℝ)
    (t : ℝ) : Prop :=
  ∀ k : ℕ,
    MeasurableSet
      (sourceLocalizedMaximalAverageExceedsFixedIntervalSet μparam (a k) (b k) t)

/-- A fixed-interval source-window average-exceeds piece is measurable if the corresponding
fixed-interval average is measurable in the parameter. -/
theorem measurableSet_sourceLocalizedMaximalAverageExceedsFixedIntervalSet
    {α : Type*} [MeasurableSpace α] {μparam : α → Measure ℝ} {a b t : ℝ}
    (havg : Measurable fun y : α => openIntervalMeasureAverage (μparam y) a b) :
    MeasurableSet (sourceLocalizedMaximalAverageExceedsFixedIntervalSet μparam a b t) := by
  by_cases hab : a < b
  · by_cases hsub : Set.Ioo a b ⊆ sourceMaximalDomain
    · have hwindow :
        MeasurableSet {p : α × ℝ | p.2 ∈ sourceMaximalWindow} :=
          measurableSet_Ioo.preimage measurable_snd
      have hinterval :
        MeasurableSet {p : α × ℝ | p.2 ∈ Set.Ioo a b} :=
          measurableSet_Ioo.preimage measurable_snd
      have hsuper :
        MeasurableSet {p : α × ℝ | t < openIntervalMeasureAverage (μparam p.1) a b} :=
          measurableSet_lt measurable_const (havg.comp measurable_fst)
      convert hinterval.inter (hwindow.inter hsuper) using 1
      ext p
      simp [sourceLocalizedMaximalAverageExceedsFixedIntervalSet, hab, hsub, and_left_comm,
        and_assoc]
    · have hempty :
        sourceLocalizedMaximalAverageExceedsFixedIntervalSet μparam a b t = ∅ := by
          ext p
          simp [sourceLocalizedMaximalAverageExceedsFixedIntervalSet, hsub]
      rw [hempty]
      exact MeasurableSet.empty
  · have hempty :
      sourceLocalizedMaximalAverageExceedsFixedIntervalSet μparam a b t = ∅ := by
        ext p
        simp [sourceLocalizedMaximalAverageExceedsFixedIntervalSet, hab]
    rw [hempty]
    exact MeasurableSet.empty

/-- A countable family of fixed intervals is measurable if each fixed-interval average is
measurable in the parameter. -/
theorem SourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable.of_measurableAverage
    {α : Type*} [MeasurableSpace α] {μparam : α → Measure ℝ} {a b : ℕ → ℝ} {t : ℝ}
    (havg :
      ∀ k : ℕ,
        Measurable fun y : α => openIntervalMeasureAverage (μparam y) (a k) (b k)) :
    SourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable μparam a b t :=
  fun k => measurableSet_sourceLocalizedMaximalAverageExceedsFixedIntervalSet (havg k)

/-- If the source-window interval-average existence set is represented by a countable fixed
interval family, then measurability of the fixed-interval pieces gives measurability of the full
source-window interval-average existence set. -/
theorem SourceLocalizedMaximalAverageExceedsMeasurable.of_countableIntervalFamily
    {α : Type*} [MeasurableSpace α] {μparam : α → Measure ℝ} {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      SourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable μparam a b t)
    (hcover :
      sourceLocalizedMaximalAverageExceedsSet μparam t =
        sourceLocalizedMaximalAverageExceedsCountableIntervalSet μparam a b t) :
    SourceLocalizedMaximalAverageExceedsMeasurable μparam t := by
  rw [SourceLocalizedMaximalAverageExceedsMeasurable, hcover,
    sourceLocalizedMaximalAverageExceedsCountableIntervalSet]
  exact MeasurableSet.iUnion hfixed

@[simp]
theorem mem_localizedMaximalBadSet {μ : Measure ℝ} {domain window : Set ℝ} {t s : ℝ} :
    s ∈ localizedMaximalBadSet μ domain window t ↔
      s ∈ window ∧ localizedMaximalBadPredicate μ domain s t :=
  Iff.rfl

@[simp]
theorem mem_sourceLocalizedMaximalBadSet {μ : Measure ℝ} {t s : ℝ} :
    s ∈ sourceLocalizedMaximalBadSet μ t ↔
      s ∈ sourceMaximalWindow ∧ sourceLocalizedMaximalBadPredicate μ s t :=
  Iff.rfl

theorem localizedMaximalFunction_eq_sSup_intervalAverageSet
    (μ : Measure ℝ) (domain : Set ℝ) (s : ℝ) :
    localizedMaximalFunction μ domain s =
      sSup (localizedIntervalAverageSet μ domain s) := by
  rfl

/-- The localized maximal bad predicate is equivalent to the existence of one admissible interval
through the point whose average is larger than the threshold. The explicit unbounded-average
case in the definition is exactly what makes this equivalence valid without a boundedness
hypothesis. -/
theorem localizedMaximalBadPredicate_iff_exists_average_gt
    {μ : Measure ℝ} {domain : Set ℝ} {s t : ℝ}
    (hne : (localizedIntervalAverageSet μ domain s).Nonempty) :
    localizedMaximalBadPredicate μ domain s t ↔
      ∃ a b : ℝ,
        a < b ∧ Set.Ioo a b ⊆ domain ∧ s ∈ Set.Ioo a b ∧
          t < openIntervalMeasureAverage μ a b := by
  constructor
  · intro hbad
    rcases hbad with hunbdd | hsup
    · rcases (not_bddAbove_iff.mp hunbdd) t with ⟨m, hm, htm⟩
      rcases hm with ⟨a, b, hab, hsub, hs, rfl⟩
      exact ⟨a, b, hab, hsub, hs, htm⟩
    · rw [localizedMaximalFunction] at hsup
      rcases exists_lt_of_lt_csSup hne hsup with ⟨m, hm, htm⟩
      rcases hm with ⟨a, b, hab, hsub, hs, rfl⟩
      exact ⟨a, b, hab, hsub, hs, htm⟩
  · rintro ⟨a, b, hab, hsub, hs, havg⟩
    let m := openIntervalMeasureAverage μ a b
    have hm : m ∈ localizedIntervalAverageSet μ domain s :=
      ⟨a, b, hab, hsub, hs, rfl⟩
    by_cases hbdd : BddAbove (localizedIntervalAverageSet μ domain s)
    · exact Or.inr (by
        rw [localizedMaximalFunction]
        exact lt_csSup_of_lt hbdd hm havg)
    · exact Or.inl hbdd

/-- A source-window point has at least one admissible interval in the source maximal domain. -/
theorem localizedIntervalAverageSet_source_nonempty_of_mem_window
    (μ : Measure ℝ) {s : ℝ} (hs : s ∈ sourceMaximalWindow) :
    (localizedIntervalAverageSet μ sourceMaximalDomain s).Nonempty := by
  refine ⟨openIntervalMeasureAverage μ (s - (1 / 2 : ℝ)) (s + (1 / 2 : ℝ)), ?_⟩
  refine ⟨s - (1 / 2 : ℝ), s + (1 / 2 : ℝ), by linarith, ?_, ?_, rfl⟩
  · intro y hy
    rcases hs with ⟨hs_left, hs_right⟩
    rcases hy with ⟨hy_left, hy_right⟩
    constructor <;> linarith
  · constructor <;> linarith

/-- Source-window version of
`localizedMaximalBadPredicate_iff_exists_average_gt`. -/
theorem sourceLocalizedMaximalBadPredicate_iff_exists_average_gt_of_mem_window
    {μ : Measure ℝ} {s t : ℝ} (hs : s ∈ sourceMaximalWindow) :
    sourceLocalizedMaximalBadPredicate μ s t ↔
      ∃ a b : ℝ,
        a < b ∧ Set.Ioo a b ⊆ sourceMaximalDomain ∧ s ∈ Set.Ioo a b ∧
          t < openIntervalMeasureAverage μ a b := by
  exact localizedMaximalBadPredicate_iff_exists_average_gt
    (localizedIntervalAverageSet_source_nonempty_of_mem_window μ hs)

end AleksandrovDifferentiability
