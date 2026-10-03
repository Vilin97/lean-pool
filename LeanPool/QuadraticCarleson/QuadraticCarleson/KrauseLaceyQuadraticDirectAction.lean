/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectPartition
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingRecursion
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPositiveCorrelation

/-!
# Finite offset grouping for the direct quadratic action

The direct proof groups the input assigned to the smallest selected interval
by the gap between the output kernel scale and the input scale. This file
records only finite, exact identities. No maximal estimate or frequency
projection is used here.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectAction

open KrauseLaceyBadScale KrauseLaceyQuadraticDirectPartition
open KrauseLaceyStoppingExtraction KrauseLaceyStoppingRecursion


noncomputable
section

/-- Classical decidable equality for the finite interval families in the direct quadratic
action. -/
local instance : DecidableEq RealInterval := Classical.decEq _

/-- The selected intervals at or above the source's fixed lower length
cutoff. The direct smallest-region partition is formed from this active
family: intervals below the cutoff never occur in any admissible tail and
must not create artificial smaller regions. -/
def activeHighCollection (ell₀ : ℤ) (S : Finset RealInterval) :
    Finset RealInterval :=
  S.filter fun I ↦ (2 : ℝ) ^ ell₀ ≤ I.length

theorem mem_activeHighCollection_iff
    {ell₀ : ℤ} {S : Finset RealInterval} {I : RealInterval} :
    I ∈ activeHighCollection ell₀ S ↔
      I ∈ S ∧ (2 : ℝ) ^ ell₀ ≤ I.length := by
  simp [activeHighCollection]

/-- At every admissible tail threshold, deleting intervals below the fixed
cutoff changes no summand. -/
theorem localizedTailAction_activeHighCollection
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (f : ℝ → ℂ) {ell : ℤ} (hell : ell₀ ≤ ell) :
    localizedTailAction scale (activeHighCollection ell₀ S) f ell =
      localizedTailAction scale S f ell := by
  classical
  have hp : (2 : ℝ) ^ ell₀ ≤ (2 : ℝ) ^ ell :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hell
  funext x
  unfold localizedTailAction activeHighCollection
  apply Finset.sum_subset (Finset.filter_subset _ S)
  intro I hIS hInot
  have hnot0 : ¬(2 : ℝ) ^ ell₀ ≤ I.length := by
    intro hI0
    exact hInot (Finset.mem_filter.mpr ⟨hIS, hI0⟩)
  have hnotell : ¬(2 : ℝ) ^ ell ≤ I.length := by
    intro hIell
    exact hnot0 (hp.trans hIell)
  rw [ite_eq_right hnotell]

/-- Hence the genuine maximal operator is exactly the one obtained from the
active high-scale selected collection. -/
theorem localizedTailMaximal_activeHighCollection
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (f : ℝ → ℂ) :
    localizedTailMaximal ell₀ scale (activeHighCollection ell₀ S) f =
      localizedTailMaximal ell₀ scale S f := by
  funext x
  unfold localizedTailMaximal
  apply iSup_congr
  intro ell
  rw [localizedTailAction_activeHighCollection ell₀ scale S f ell.2]

/-- Exact dyadic length labels convert active-family membership into the
paper's lower scale inequality. -/
theorem scale_add_two_ge_cutoff_of_mem_activeHighCollection
    {ell₀ : ℤ} {S : Finset RealInterval} {scale : RealInterval → ℤ}
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    {I : RealInterval} (hI : I ∈ activeHighCollection ell₀ S) :
    ell₀ ≤ scale I + 2 := by
  have hmem := mem_activeHighCollection_iff.mp hI
  rw [hscale I hmem.1] at hmem
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hmem.2

private theorem memLp_two_l0Infinity (f : L0Infinity) :
    MemLp (f : ℝ → ℂ) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm f.measurable_toFun.aestronglyMeasurable]
  obtain ⟨C, hC⟩ := f.bounded_toFun
  have hi := f.integrable_finiteSparseProof.norm.bdd_mul
    f.measurable_toFun.norm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by simpa only [norm_norm] using hC x)
  simpa only [pow_two] using hi

/-- All scale offsets which can occur in a finite selected collection. -/
def offsetSet (S : Finset RealInterval) (scale : RealInterval → ℤ) : Finset ℤ :=
  (S.product S).image (fun p ↦ scale p.1 - scale p.2)

/-- The finite input assigned to an output interval `I` at offset `s`.
This is the finite version of the paper's `F_{j,s}`: each summand is the
smallest-selected-region input, restricted to the output central third. -/
def offsetGroupedInput
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (I : RealInterval) (s : ℤ) (x : ℝ) : ℂ :=
  ∑ J ∈ (selectedSubintervals S I).filter
      (fun J ↦ scale I - scale J = s),
    I.centralThird.indicator ((smallestSelectedRegion S J).indicator f) x

/-- The finite quadratic action of one offset group. -/
def offsetLocalizedAction
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ S.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
    krauseLaceyLocalizedPiece 1 (scale I) I
      (offsetGroupedInput S scale f I s) x

/-- The maximal partial-sum operator associated with one finite offset group.
This is only a definition; its estimate is the analytic part of the direct
proof and is deliberately not asserted here. -/
def offsetTailMaximal
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ ell : {ell : ℤ // ell₀ ≤ ell},
    ‖offsetLocalizedAction S scale f ell.1 s x‖ₑ

/-- The fixed-offset action with two distinct collections. `S` is the
ambient selected family which defines the smallest-region partition, while
`A` is the subcollection of output intervals retained in the action. This
distinction is essential for the regular/exceptional split in the direct
proof: passing to a subcollection must not repartition the input. -/
def offsetLocalizedActionOn
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
    krauseLaceyLocalizedPiece 1 (scale I) I
      (offsetGroupedInput S scale f I s) x

/-- The genuine maximal tail for an output subcollection `A`, with the
smallest-selected regions still formed using the ambient family `S`. -/
def offsetTailMaximalOn
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ ell : {ell : ℤ // ell₀ ≤ ell},
    ‖offsetLocalizedActionOn S A scale f ell.1 s x‖ₑ

/-- If every ambient selected scale is nonnegative, then an output interval
whose scale lies below `s - 2` has no input at offset `s`. Such intervals
must be removed before invoking the frequency-radius estimate, rather than
being burdened with a false gap hypothesis. -/
theorem offsetGroupedInput_eq_zero_of_scale_add_two_sub_neg
    {S : Finset RealInterval} {scale : RealInterval → ℤ}
    (hscaleNonneg : ∀ J ∈ S, 0 ≤ scale J)
    (f : ℝ → ℂ) (I : RealInterval) (s : ℤ)
    (hgap : scale I + 2 - s < 0) :
    offsetGroupedInput S scale f I s = 0 := by
  classical
  funext x
  unfold offsetGroupedInput
  apply Finset.sum_eq_zero
  intro J hJ
  have hselected := Finset.mem_filter.mp hJ
  have hJS : J ∈ S := (mem_selectedSubintervals_iff.mp hselected.1).1
  have hJnonneg : 0 ≤ scale J := hscaleNonneg J hJS
  have hoffset : scale I - scale J = s := hselected.2
  exfalso
  omega

/-- The output intervals on which the offset-`s` frequency-radius condition
is valid. All omitted outputs have zero grouped input under nonnegative
ambient scales. -/
def relevantOffsetOutputs (A : Finset RealInterval)
    (scale : RealInterval → ℤ) (s : ℤ) : Finset RealInterval :=
  A.filter fun I ↦ 0 ≤ scale I + 2 - s

theorem mem_relevantOffsetOutputs_iff
    {A : Finset RealInterval} {scale : RealInterval → ℤ}
    {s : ℤ} {I : RealInterval} :
    I ∈ relevantOffsetOutputs A scale s ↔
      I ∈ A ∧ 0 ≤ scale I + 2 - s := by
  simp [relevantOffsetOutputs]

/-- Removing the irrelevant outputs changes no fixed-offset action. -/
theorem offsetLocalizedActionOn_relevantOffsetOutputs
    {S A : Finset RealInterval} {scale : RealInterval → ℤ}
    (hscaleNonneg : ∀ J ∈ S, 0 ≤ scale J)
    (f : ℝ → ℂ) (ell s : ℤ) :
    offsetLocalizedActionOn S (relevantOffsetOutputs A scale s)
        scale f ell s =
      offsetLocalizedActionOn S A scale f ell s := by
  classical
  funext x
  unfold offsetLocalizedActionOn
  apply Finset.sum_subset
  · intro I hI
    have hm := Finset.mem_filter.mp hI
    exact Finset.mem_filter.mpr
      ⟨(mem_relevantOffsetOutputs_iff.mp hm.1).1, hm.2⟩
  · intro I hI hInot
    have hm := Finset.mem_filter.mp hI
    have hgapneg : scale I + 2 - s < 0 := by
      apply lt_of_not_ge
      intro hgap
      exact hInot (Finset.mem_filter.mpr
        ⟨mem_relevantOffsetOutputs_iff.mpr ⟨hm.1, hgap⟩, hm.2⟩)
    rw [offsetGroupedInput_eq_zero_of_scale_add_two_sub_neg
      hscaleNonneg f I s hgapneg]
    simp [krauseLaceyLocalizedPiece]

/-- Removing irrelevant zero outputs also preserves the genuine maximal
tail exactly. -/
theorem offsetTailMaximalOn_relevantOffsetOutputs
    {S A : Finset RealInterval} {scale : RealInterval → ℤ}
    (hscaleNonneg : ∀ J ∈ S, 0 ≤ scale J)
    (f : ℝ → ℂ) (ell₀ s : ℤ) :
    offsetTailMaximalOn S (relevantOffsetOutputs A scale s)
        scale f ell₀ s =
      offsetTailMaximalOn S A scale f ell₀ s := by
  funext x
  unfold offsetTailMaximalOn
  apply iSup_congr
  intro ell
  rw [offsetLocalizedActionOn_relevantOffsetOutputs hscaleNonneg f ell.1 s]

/-- The genuine ambient/subcollection offset tail is measurable for every
measurable input. -/
theorem measurable_offsetTailMaximalOn
    (S A : Finset RealInterval) (scale : RealInterval → ℤ)
    {f : ℝ → ℂ} (hf : Measurable f) (ell₀ s : ℤ) :
    Measurable (offsetTailMaximalOn S A scale f ell₀ s) := by
  classical
  have hinput (I : RealInterval) :
      Measurable (offsetGroupedInput S scale f I s) := by
    unfold offsetGroupedInput
    apply Finset.measurable_fun_sum
    intro J hJ
    exact (hf.indicator (measurableSet_smallestSelectedRegion S J)).indicator
      I.measurableSet_centralThird
  have haction (ell : ℤ) :
      Measurable (offsetLocalizedActionOn S A scale f ell s) := by
    unfold offsetLocalizedActionOn
    apply Finset.measurable_fun_sum
    intro I hI
    exact measurable_localizedPiece (scale I) I (hinput I)
  exact Measurable.iSup fun ell ↦ (haction ell.1).enorm

@[simp] theorem offsetLocalizedActionOn_self
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) :
    offsetLocalizedActionOn S S scale f ell s =
      offsetLocalizedAction S scale f ell s := rfl

@[simp] theorem offsetTailMaximalOn_self
    (S : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) :
    offsetTailMaximalOn S S scale f ell₀ s =
      offsetTailMaximal S scale f ell₀ s := rfl

/-- Every finite grouped input remains an `L²` function. -/
theorem memLp_two_offsetGroupedInput
    (S : Finset RealInterval) (scale : RealInterval → ℤ)
    (f : L0Infinity) (I : RealInterval) (s : ℤ) :
    MemLp (offsetGroupedInput S scale f I s) 2 volume := by
  classical
  let T := (selectedSubintervals S I).filter
    (fun J ↦ scale I - scale J = s)
  have hsum :
      MemLp (∑ J ∈ T,
        I.centralThird.indicator ((smallestSelectedRegion S J).indicator f))
        2 volume := by
    induction T using Finset.induction_on with
    | empty =>
        simp
    | @insert J T hJ ih =>
        have hterm : MemLp
            (I.centralThird.indicator
              ((smallestSelectedRegion S J).indicator f)) 2 volume :=
          (memLp_two_l0Infinity f).indicator
            (measurableSet_smallestSelectedRegion S J) |>.indicator
              I.measurableSet_centralThird
        simpa [Finset.sum_insert, hJ] using hterm.add ih
  unfold offsetGroupedInput
  have hsum' : MemLp
      (fun y ↦ ∑ J ∈ T,
        I.centralThird.indicator ((smallestSelectedRegion S J).indicator f) y)
      2 volume := by
    convert hsum using 1
    funext y
    simp only [Finset.sum_apply]
  dsimp [T] at hsum'
  exact hsum'

/-- The scale of a selected subinterval cannot exceed the scale of its
selected parent. This is the exact monotonicity supplied by the length
identity, not an additional dyadic assumption. -/
theorem scale_le_of_carrier_subset
    {S : Finset RealInterval} {scale : RealInterval → ℤ}
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    {I J : RealInterval} (hI : I ∈ S) (hJ : J ∈ S)
    (hsub : J.carrier ⊆ I.carrier) :
    scale J ≤ scale I := by
  have hlen : J.length ≤ I.length := by
    have he := (Ioc_subset_Ioc_iff J.left_lt_right).mp hsub
    dsimp [RealInterval.length]
    linarith [he.1, he.2]
  rw [hscale J hJ, hscale I hI] at hlen
  have hsc : scale J + 2 ≤ scale I + 2 :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlen
  omega

theorem offset_nonneg_of_selectedSubinterval
    {S : Finset RealInterval} {scale : RealInterval → ℤ}
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    {I J : RealInterval} (hI : I ∈ S)
    (hJ : J ∈ selectedSubintervals S I) :
    0 ≤ scale I - scale J := by
  exact sub_nonneg.mpr (scale_le_of_carrier_subset hscale hI
    (mem_selectedSubintervals_iff.mp hJ).1
    (mem_selectedSubintervals_iff.mp hJ).2)

/-- For a nonnegative offset, the interval-dependent grouped input is
exactly the central-third restriction of the global smallest-region scale
piece `b_{j-s}`. This is the bridge from the finite reconstruction to the
one-piece energy estimate. -/
theorem offsetGroupedInput_eq_indicator_smallestScaleInput
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    {I : RealInterval} (hI : I ∈ S) (f : ℝ → ℂ)
    {s : ℤ} (hs : 0 ≤ s) :
    offsetGroupedInput S scale f I s =
      I.centralThird.indicator
        (smallestScaleInput S scale f (scale I - s)) := by
  classical
  funext x
  by_cases hxI : x ∈ I.centralThird
  · simp only [offsetGroupedInput, smallestScaleInput,
      Set.indicator_of_mem hxI]
    apply Finset.sum_subset
    · intro J hJ
      have hsel := Finset.mem_filter.mp hJ
      have hsub := mem_selectedSubintervals_iff.mp hsel.1
      apply Finset.mem_filter.mpr
      refine ⟨hsub.1, ?_⟩
      omega
    · intro J hJS hJnot
      have hJdata := Finset.mem_filter.mp hJS
      have hnotSub : ¬J.carrier ⊆ I.carrier := by
        intro hJI
        apply hJnot
        apply Finset.mem_filter.mpr
        refine ⟨mem_selectedSubintervals_iff.mpr ⟨hJdata.1, hJI⟩, ?_⟩
        omega
      have hne : I ≠ J := by
        intro hIJ
        apply hnotSub
        rw [hIJ]
      have hdis : Disjoint I.carrier J.carrier := by
        rcases hlam hI hJdata.1 hne with hIJ | hJI | hdis
        · have hleJI : scale J ≤ scale I := by omega
          have hleIJ : scale I ≤ scale J :=
            scale_le_of_carrier_subset hscale hJdata.1 hI hIJ
          have heqScale : scale I = scale J := le_antisymm hleIJ hleJI
          have hlen : J.length ≤ I.length := by
            rw [hscale J hJdata.1, hscale I hI, heqScale]
          have heq : I = J :=
            interval_eq_of_carrier_subset_of_length_le hIJ hlen
          exact (hne heq).elim
        · exact (hnotSub hJI).elim
        · exact hdis
      apply Set.indicator_of_notMem
      intro hxJ
      exact Set.disjoint_left.mp hdis
        (I.centralThird_subset_carrier hxI)
        (smallestSelectedRegion_subset_carrier S J hxJ)
  · simp [offsetGroupedInput, Set.indicator_of_notMem hxI]

/-- Every offset arising below `I` belongs to the global finite offset set. -/
theorem offset_mem_offsetSet
    {S : Finset RealInterval} {scale : RealInterval → ℤ}
    {I J : RealInterval} (hI : I ∈ S)
    (hJ : J ∈ selectedSubintervals S I) :
    scale I - scale J ∈ offsetSet S scale := by
  apply Finset.mem_image.mpr
  refine ⟨(I, J), Finset.mem_product.mpr ⟨hI,
    (mem_selectedSubintervals_iff.mp hJ).1⟩, rfl⟩

/-- The grouped inputs sum exactly to the central-third restriction of `f`.
The outer offset set may contain irrelevant offsets; their groups are zero. -/
theorem sum_offsetGroupedInput_centralThird_eq
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) {I : RealInterval} (hI : I ∈ S)
    (f : ℝ → ℂ) (x : ℝ) :
    ∑ s ∈ offsetSet S scale,
      offsetGroupedInput S scale f I s x =
      I.centralThird.indicator f x := by
  classical
  let T := selectedSubintervals S I
  let localOffsets := T.image (fun J ↦ scale I - scale J)
  have hlocal :
      ∑ s ∈ localOffsets, offsetGroupedInput S scale f I s x =
        I.centralThird.indicator f x := by
    dsimp [localOffsets, offsetGroupedInput]
    rw [Finset.sum_fiberwise_of_maps_to
      (fun J hJ ↦ Finset.mem_image.mpr ⟨J, hJ, rfl⟩)]
    exact sum_indicator_smallestSelectedRegion_centralThird_eq hlam hI f x
  have hlocalSub : localOffsets ⊆ offsetSet S scale := by
    intro s hs
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hs
    exact offset_mem_offsetSet hI (by simpa only [T] using hJ)
  have hzero : ∀ s ∈ offsetSet S scale, s ∉ localOffsets →
      offsetGroupedInput S scale f I s x = 0 := by
    intro s hs hslocal
    unfold offsetGroupedInput
    apply Finset.sum_eq_zero
    intro J hJ
    have hJs : J ∈ T := (Finset.mem_filter.mp hJ).1
    have hoff : scale I - scale J = s := (Finset.mem_filter.mp hJ).2
    exact (hslocal (Finset.mem_image.mpr ⟨J, hJs, hoff⟩)).elim
  calc
    ∑ s ∈ offsetSet S scale, offsetGroupedInput S scale f I s x =
        ∑ s ∈ localOffsets, offsetGroupedInput S scale f I s x := by
      symm
      apply Finset.sum_subset hlocalSub
      intro s hs hslocal
      exact hzero s hs hslocal
    _ = I.centralThird.indicator f x := hlocal

/-- Negative offsets do not occur below a selected output interval. -/
theorem offsetGroupedInput_eq_zero_of_neg
    {S : Finset RealInterval} {scale : RealInterval → ℤ}
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    {I : RealInterval} (hI : I ∈ S) (f : L0Infinity) {s : ℤ}
    (hs : s < 0) : offsetGroupedInput S scale f I s = 0 := by
  unfold offsetGroupedInput
  funext x
  apply Finset.sum_eq_zero
  intro J hJ
  have hoff := offset_nonneg_of_selectedSubinterval hscale hI
    (Finset.mem_filter.mp hJ).1
  have heq := (Finset.mem_filter.mp hJ).2
  exfalso
  omega

/-- At one output interval, the localized quadratic piece is the finite sum
of the quadratic pieces applied to all offset groups. -/
theorem localizedPiece_eq_sum_offset
    {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ) {I : RealInterval} (hI : I ∈ S)
    (f : L0Infinity) (x : ℝ) :
    krauseLaceyLocalizedPiece 1 (scale I) I f x =
      ∑ s ∈ offsetSet S scale,
        krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x := by
  classical
  let κ : ℝ → ℂ :=
    annularQuadraticKernel (positiveDyadicAmplitude (scale I)) 1
  have hκc : Continuous κ := by
    have ha : Continuous (positiveDyadicAmplitude (scale I)) :=
      continuous_iff_continuousAt.mpr
        (fun t ↦ (hasDerivAt_positiveDyadicAmplitude (scale I) t).continuousAt)
    unfold κ annularQuadraticKernel phase
    fun_prop
  have hκs : HasCompactSupport κ := by
    let R : ℝ := (2 : ℝ) ^ (scale I - 1)
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (R / 4) R))
    intro t ht
    apply positiveDyadicAmplitude_support_subset (scale I)
    intro hz
    exact ht (by simp [κ, annularQuadraticKernel, hz])
  have hint (s : ℤ) :
      Integrable (fun t ↦ κ (x - t) *
        offsetGroupedInput S scale f I s t) :=
    integrable_convolution_row_of_memLp hκc hκs
      (memLp_two_offsetGroupedInput S scale f I s) x
  have hsum (t : ℝ) :
      ∑ s ∈ offsetSet S scale, offsetGroupedInput S scale f I s t =
        I.centralThird.indicator f t :=
    sum_offsetGroupedInput_centralThird_eq hlam scale hI f t
  have hcentral (s : ℤ) (t : ℝ) :
      I.centralThird.indicator (offsetGroupedInput S scale f I s) t =
        offsetGroupedInput S scale f I s t := by
    by_cases ht : t ∈ I.centralThird
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      unfold offsetGroupedInput
      symm
      apply Finset.sum_eq_zero
      intro J hJ
      simp only [Set.indicator_of_notMem ht]
  calc
    krauseLaceyLocalizedPiece 1 (scale I) I f x =
        ∫ t, κ (x - t) * I.centralThird.indicator f t := by
      exact krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution
        (scale I) I f x
    _ = ∫ t, κ (x - t) *
        (∑ s ∈ offsetSet S scale,
          offsetGroupedInput S scale f I s t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hsum t]
    _ = ∑ s ∈ offsetSet S scale,
        ∫ t, κ (x - t) * offsetGroupedInput S scale f I s t := by
      calc
        _ = ∫ t, ∑ s ∈ offsetSet S scale,
            κ (x - t) * offsetGroupedInput S scale f I s t := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [Finset.mul_sum]
        _ = ∑ s ∈ offsetSet S scale,
            ∫ t, κ (x - t) * offsetGroupedInput S scale f I s t :=
          (integral_finsetSum (offsetSet S scale)
            (fun s hs ↦ hint s))
    _ = ∑ s ∈ offsetSet S scale,
        krauseLaceyLocalizedPiece 1 (scale I) I
          (offsetGroupedInput S scale f I s) x := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hcentral s t]

/-- The localized tail action decomposes exactly into the finitely many
offset-grouped quadratic pieces. The physical cutoff is unchanged. -/
theorem localizedTailAction_eq_sum_offsetLocalizedAction
    {S : Finset RealInterval} (scale : RealInterval → ℤ) (f : L0Infinity)
    (ell : ℤ) (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (_hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2)) (x : ℝ) :
    localizedTailAction scale S f ell x =
      ∑ s ∈ offsetSet S scale,
        offsetLocalizedAction S scale f ell s x := by
  classical
  have hpiece (I : RealInterval) (hI : I ∈ S) :
      krauseLaceyLocalizedPiece 1 (scale I) I f x =
        ∑ s ∈ offsetSet S scale,
          krauseLaceyLocalizedPiece 1 (scale I) I
            (offsetGroupedInput S scale f I s) x :=
    localizedPiece_eq_sum_offset hlam scale hI f x
  unfold localizedTailAction offsetLocalizedAction
  rw [← Finset.sum_filter]
  calc
    (∑ I ∈ S.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
        krauseLaceyLocalizedPiece 1 (scale I) I f x) =
        ∑ I ∈ S.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
          ∑ s ∈ offsetSet S scale,
            krauseLaceyLocalizedPiece 1 (scale I) I
              (offsetGroupedInput S scale f I s) x := by
      apply Finset.sum_congr rfl
      intro I hI
      exact hpiece I (Finset.mem_filter.mp hI).1
    _ = ∑ s ∈ offsetSet S scale,
        ∑ I ∈ S.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length),
          krauseLaceyLocalizedPiece 1 (scale I) I
            (offsetGroupedInput S scale f I s) x := by
      exact Finset.sum_comm

/-- The same exact decomposition with the paper's natural nonnegative offset
range. The scale/length relation proves that all negative offset groups
vanish, so no analytic estimate is hidden in this truncation. -/
theorem localizedTailAction_eq_sum_nonnegativeOffsetLocalizedAction
    {S : Finset RealInterval} (scale : RealInterval → ℤ) (f : L0Infinity)
    (ell : ℤ) (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2)) (x : ℝ) :
    localizedTailAction scale S f ell x =
      ∑ s ∈ (offsetSet S scale).filter (fun s ↦ 0 ≤ s),
        offsetLocalizedAction S scale f ell s x := by
  classical
  rw [localizedTailAction_eq_sum_offsetLocalizedAction scale f ell hlam
    hscale x]
  symm
  apply Finset.sum_subset
    (s₁ := (offsetSet S scale).filter (fun s ↦ 0 ≤ s))
    (s₂ := offsetSet S scale) (Finset.filter_subset _ _)
  intro s hs hsn
  have hsneg : s < 0 := by
    have : ¬ 0 ≤ s := by
      intro hpos
      exact hsn (Finset.mem_filter.mpr ⟨hs, hpos⟩)
    omega
  unfold offsetLocalizedAction
  apply Finset.sum_eq_zero
  intro I hI
  rw [offsetGroupedInput_eq_zero_of_neg hscale
    (Finset.mem_filter.mp hI).1 f hsneg]
  simp [krauseLaceyLocalizedPiece]

/-- The exact finite decomposition feeds into the genuine maximal operator:
the maximal tail is bounded by the finite sum of the offset maximal tails.
This is the only deterministic step needed before proving the per-offset
analytic bound. -/
theorem localizedTailMaximal_le_sum_offsetTailMaximal
    {S : Finset RealInterval} (scale : RealInterval → ℤ) (f : L0Infinity)
    (ell₀ : ℤ) (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2)) (x : ℝ) :
    localizedTailMaximal ell₀ scale S f x ≤
      ∑ s ∈ (offsetSet S scale).filter (fun s ↦ 0 ≤ s),
        offsetTailMaximal S scale f ell₀ s x := by
  classical
  unfold localizedTailMaximal
  apply iSup_le
  intro ell
  rw [localizedTailAction_eq_sum_nonnegativeOffsetLocalizedAction
    scale f ell.1 hlam hscale x]
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  exact le_iSup (fun q : {q : ℤ // ell₀ ≤ q} ↦
    ‖offsetLocalizedAction S scale f q.1 s x‖ₑ) ell


end
end KrauseLaceyQuadraticDirectAction
end QuadraticCarleson
