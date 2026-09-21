/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointTail
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointCofinality
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.OrderedUnion
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The residual-point tail order type

The order-type computation in Berarducci, Lemma 6.8: on a stable interval, the ordinary order type
of a residual-point tail is exactly `v_J^p(b)`.

The support of `b` restricted to the stable interval is covered by the truncations at the residual
points of the tail. Every residual point has translated-truncation value `v_J^r(b)`, so every
nonempty final segment of each piece has order type at least `v_J^r(b)`, and consecutive pieces
are strictly separated because the truncation at a residual point has support supremum zero. The
ordered-union estimate of Berarducci, Lemma 4.7 then bounds `v_J^r(b) * λ` by the order type of
the stable interval, which is `v_J^r(b) * v_J^p(b)`, and left cancellation gives `λ ≤ v_J^p(b)`.

The residual value one is treated separately: the pieces are then closed at their right endpoint,
since a residual point of value one is an isolated support point and admits no support point
immediately below it, and the final-segment hypothesis is the trivial nonemptiness bound.

For the reverse bound the source constructs, for each `α < v_J^p(b)`, the supremum of the first
`v_J^r(b) * (α + 1)` elements of the stable interval and asserts that it is a residual point. That
construction can fail when `v_J^r(b) = 1` and `α` is a limit: the supremum is then the `α`-th
support point, which need not be isolated from below. If it is a limit of earlier support points,
as at the final point of a support block of order type `ω + 1`, its translated truncation has
value above one. Thus the printed construction does not establish the asserted residuality in
general. The conclusion is unaffected, and this module proves it by splitting on the residual
value. For residual value above one the printed construction is used, and the first
`v_J^r(b) * (α + 1)` elements have limit order type, so their supremum is not attained and every
window below it is a nonempty final segment of order type at least `v_J^r(b)`. For residual value
one the residual points are exactly the isolated support points, and the successor-indexed support
points supply a strictly increasing family of the required order type, which is Berarducci,
Lemma 4.6.
-/

universe v

public noncomputable section

open Ordinal HahnSeries

namespace Berarducci

variable {K : Type v} [Field K]

/-- The residual points of a tail accumulate at `0`, so every residual point of the tail has a
larger one, and the ordinary order type of the tail is a limit ordinal. -/
private theorem residualPointTail_orderType_isSuccLimit
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO)
    {η : ℝ} (hη : η < 0) :
    Order.IsSuccLimit (residualPointTail_isPWO b η hX).orderType := by
  obtain ⟨htailNe, htailLUB⟩ :=
    residualPointTail_nonempty_and_isLUB b hη (residualPointSet_isLUB_zero b)
  refine Set.IsPWO.isSuccLimit_orderType_of_forall_exists_gt _ htailNe fun x hx ↦ ?_
  have hx0 : x < 0 :=
    residualPointSet_subset_Iio b (residualPointTail_subset_residualPointSet b η hx)
  obtain ⟨y, hy, hxy, _⟩ := htailLUB.exists_between hx0
  exact ⟨y, hy, hxy⟩

/-- Between a point `θ` and a residual point `γ' > θ` there is a support point of `b` in the
half-open interval `(θ, γ']`, because the translated truncation at a residual point has support
supremum `0`. -/
private theorem exists_mem_support_Ioc_of_lt_of_mem_residualPointSet
    (b : SeriesWithOrdinalValueAboveOne K) {θ γ' : ℝ} (hγ' : γ' ∈ residualPointSet b)
    (hθ : θ < γ') : ∃ y ∈ (b.1 : K⟦ℝ⟧).support, θ < y ∧ y ≤ γ' := by
  have hsup := supportSup_translatedTruncation_eq_zero_of_mem_residualPointSet hγ'
  have hLUB := (HahnSeries.Nonpositive.supportSup_eq_coe_iff.mp hsup).2
  have hcut : θ - γ' < 0 := sub_neg.mpr hθ
  obtain ⟨δ, hδ, hδabove, _⟩ := hLUB.exists_between hcut
  rw [support_translatedTruncation] at hδ
  obtain ⟨y, hy, hyeq⟩ := hδ
  rw [← hyeq] at hδabove
  refine ⟨y, hy.1, ?_, hy.2⟩
  change -γ' + y > θ - γ' at hδabove
  linarith

/-- If the translated truncation at `γ'` has ordinal value above one, then between a point
`θ < γ'` and `γ'` there is a support point of `b` in the open interval `(θ, γ')`, because the
negative support of that truncation has supremum `0`. -/
private theorem exists_mem_support_Ioo_of_lt_of_one_lt_ordinalValue
    (b : SeriesWithOrdinalValueAboveOne K) {θ γ' : ℝ}
    (hγ' : 1 < ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ')) (hθ : θ < γ') :
    ∃ y ∈ (b.1 : K⟦ℝ⟧).support, θ < y ∧ y < γ' := by
  have hLUB := isLUB_negativeSupport_zero_of_one_lt_ordinalValue hγ'
  have hcut : θ - γ' < 0 := sub_neg.mpr hθ
  obtain ⟨δ, hδ, hδabove, _⟩ := hLUB.exists_between hcut
  rw [support_translatedTruncation] at hδ
  obtain ⟨⟨y, hy, hyeq⟩, hδneg⟩ := hδ
  rw [← hyeq] at hδabove hδneg
  refine ⟨y, hy.1, ?_, ?_⟩
  · change -γ' + y > θ - γ' at hδabove
    linarith
  · change -γ' + y < 0 at hδneg
    linarith

/-- A nonempty final segment of the support of `b` in `(η, γ')`, for a residual point `γ'`, has
order type at least the residual value: it is a final segment of the support below `γ'`, and
those have order type at least the value of the translated truncation at `γ'`. -/
private theorem residualValue_le_orderType_of_isRelUpperSet_support_Ioo
    (b : SeriesWithOrdinalValueAboveOne K) {η γ' : ℝ} (hγ' : γ' ∈ residualPointSet b)
    {C : Set ℝ} (hC : IsRelUpperSet C (· ∈ (b.1 : K⟦ℝ⟧).support ∩ Set.Ioo η γ'))
    (hCne : C.Nonempty) :
    b.residualValue.val ≤
      ((b.1 : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hC hx).1.1).orderType := by
  have hC' : IsRelUpperSet C (· ∈ (b.1 : K⟦ℝ⟧).support ∩ Set.Iio γ') := by
    intro a ha
    obtain ⟨haB, hup⟩ := hC ha
    refine ⟨⟨haB.1, haB.2.2⟩, ?_⟩
    intro d had hd
    exact hup had ⟨hd.1, haB.2.1.trans_le had, hd.2⟩
  have hbound :=
    le_orderType_of_le_ordinalValue_translatedTruncation_of_isRelUpperSet_supportBelow
      (b.1 : K⟦ℝ⟧) γ' (ρ := b.residualValue.val)
      (by rw [(mem_residualPointSet_iff.mp hγ').2]; simp) hC' hCne
  exact hbound.trans_eq (Set.IsPWO.orderType_proof_irrel _ _)

/-- The ordered-union estimate of Berarducci, Lemma 4.7, for residual value one. Given a strictly
increasing family `γ : l.ToType → ℝ` of residual points of the tail above `η`, with `l` a limit,
the pieces `supp(b) ∩ (η, γ i]` are nonempty and strictly separated, since between two residual
points there is a support point; so `1 ⬝ l` is at most the order type of the support of `b` on
`(η, 0)`. -/
private theorem residualValue_mul_le_orderType_negativeSupportTail_of_eq_one
    (b : SeriesWithOrdinalValueAboveOne K) {η : ℝ} (hρ1 : b.residualValue = 1)
    {l : Ordinal} (hl : Order.IsSuccLimit l) (γ : l.ToType → ℝ) (hγmono : StrictMono γ)
    (hγtail : ∀ i, γ i ∈ residualPointTail b η) :
    b.residualValue.val * l ≤
      ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType := by
  have hγX : ∀ i, γ i ∈ residualPointSet b := fun i ↦
    residualPointTail_subset_residualPointSet b η (hγtail i)
  have hγneg : ∀ i, γ i < 0 := fun i ↦ residualPointSet_subset_Iio b (hγX i)
  have hγη : ∀ i, η < γ i := fun i ↦ (mem_residualPointTail_iff.mp (hγtail i)).2
  set B : l.ToType → Set ℝ :=
    fun i ↦ (b.1 : K⟦ℝ⟧).support ∩ Set.Ioc η (γ i) with hBdef
  have hB : ∀ i, (B i).IsPWO := fun _ ↦
    (b.1 : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have hUnionSub : (⋃ i, B i) ⊆ negativeSupportTail b.1 η := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem_negativeSupportTail_iff.mpr
      ⟨hi.1, hi.2.1, hi.2.2.trans_lt (hγneg i)⟩
  have hUnion : (⋃ i, B i).IsPWO :=
    (b.1 : K⟦ℝ⟧).isPWO_support.mono
      (hUnionSub.trans (negativeSupportTail_subset_support b.1 η))
  have hsep : ∀ {i j : l.ToType}, i < j → ∃ y ∈ B j, ∀ x ∈ B i, x < y := by
    intro i j hij
    obtain ⟨y, hy, hγiy, hyγj⟩ :=
      exists_mem_support_Ioc_of_lt_of_mem_residualPointSet b (hγX j) (hγmono hij)
    exact ⟨y, ⟨hy, (hγη i).trans hγiy, hyγj⟩, fun x hx ↦ hx.2.2.trans_lt hγiy⟩
  have hfinal : ∀ (i : l.ToType) (C : Set ℝ)
      (hC : IsRelUpperSet C (· ∈ B i)), C.Nonempty →
        b.residualValue.val ≤ ((hB i).mono fun _ hx ↦ (hC hx).1).orderType := by
    intro i C hC hCne
    rw [hρ1]
    change (1 : Ordinal) ≤ _
    rw [Order.one_le_iff_ne_zero]
    intro hzero
    obtain ⟨x, hx⟩ := hCne
    have := ((hB i).mono fun _ hx ↦ (hC hx).1).orderType_eq_zero.mp hzero
    rw [this] at hx
    exact hx
  calc b.residualValue.val * l
      ≤ hUnion.orderType :=
        Set.IsPWO.mul_le_orderType_iUnion_of_isSuccLimit hl B hB hsep hfinal hUnion
    _ ≤ ((b.1 : K⟦ℝ⟧).isPWO_support.mono
          (negativeSupportTail_subset_support b.1 η)).orderType :=
        hUnion.orderType_mono _ hUnionSub

/-- The ordered-union estimate of Berarducci, Lemma 4.7, for residual value above one. Given a
strictly increasing family `γ : l.ToType → ℝ` of residual points of the tail above `η`, with `l`
a limit, the pieces `supp(b) ∩ (η, γ i)` are strictly separated, since the negative support of
the truncation at a residual point accumulates at `0`, and every nonempty final segment of a
piece has order type at least the residual value; so `v_J^r(b) ⬝ l` is at most the order type of
the support of `b` on `(η, 0)`. -/
private theorem residualValue_mul_le_orderType_negativeSupportTail_of_one_lt
    (b : SeriesWithOrdinalValueAboveOne K) {η : ℝ} (h1ρ : 1 < b.residualValue)
    {l : Ordinal} (hl : Order.IsSuccLimit l) (γ : l.ToType → ℝ) (hγmono : StrictMono γ)
    (hγtail : ∀ i, γ i ∈ residualPointTail b η) :
    b.residualValue.val * l ≤
      ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType := by
  have hγX : ∀ i, γ i ∈ residualPointSet b := fun i ↦
    residualPointTail_subset_residualPointSet b η (hγtail i)
  have hγneg : ∀ i, γ i < 0 := fun i ↦ residualPointSet_subset_Iio b (hγX i)
  have hγη : ∀ i, η < γ i := fun i ↦ (mem_residualPointTail_iff.mp (hγtail i)).2
  have hvalueOne : ∀ i, 1 < ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) (γ i)) := by
    intro i
    rw [(mem_residualPointSet_iff.mp (hγX i)).2]
    exact h1ρ
  set B : l.ToType → Set ℝ :=
    fun i ↦ (b.1 : K⟦ℝ⟧).support ∩ Set.Ioo η (γ i) with hBdef
  have hB : ∀ i, (B i).IsPWO := fun _ ↦
    (b.1 : K⟦ℝ⟧).isPWO_support.mono Set.inter_subset_left
  have hUnionSub : (⋃ i, B i) ⊆ negativeSupportTail b.1 η := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact mem_negativeSupportTail_iff.mpr
      ⟨hi.1, hi.2.1, hi.2.2.trans (hγneg i)⟩
  have hUnion : (⋃ i, B i).IsPWO :=
    (b.1 : K⟦ℝ⟧).isPWO_support.mono
      (hUnionSub.trans (negativeSupportTail_subset_support b.1 η))
  have hsep : ∀ {i j : l.ToType}, i < j → ∃ y ∈ B j, ∀ x ∈ B i, x < y := by
    intro i j hij
    obtain ⟨y, hy, hγiy, hyγj⟩ :=
      exists_mem_support_Ioo_of_lt_of_one_lt_ordinalValue b (hvalueOne j) (hγmono hij)
    exact ⟨y, ⟨hy, (hγη i).trans hγiy, hyγj⟩, fun x hx ↦ hx.2.2.trans hγiy⟩
  have hfinal : ∀ (i : l.ToType) (C : Set ℝ)
      (hC : IsRelUpperSet C (· ∈ B i)), C.Nonempty →
        b.residualValue.val ≤ ((hB i).mono fun _ hx ↦ (hC hx).1).orderType :=
    fun i C hC hCne ↦
      (residualValue_le_orderType_of_isRelUpperSet_support_Ioo b (hγX i) hC hCne).trans_eq
        (Set.IsPWO.orderType_proof_irrel _ _)
  calc b.residualValue.val * l
      ≤ hUnion.orderType :=
        Set.IsPWO.mul_le_orderType_iUnion_of_isSuccLimit hl B hB hsep hfinal hUnion
    _ ≤ ((b.1 : K⟦ℝ⟧).isPWO_support.mono
          (negativeSupportTail_subset_support b.1 η)).orderType :=
        hUnion.orderType_mono _ hUnionSub

/-- The ordered-union estimate for a residual-point tail: the residual value times the ordinary
order type of the tail is at most the order type of the support of `b` on `(η, 0)`. The tail is
enumerated by its order type, a limit, and the estimate splits on the residual value. -/
private theorem residualValue_mul_residualPointTail_orderType_le
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO)
    {η : ℝ} (hη : η < 0) :
    b.residualValue.val * (residualPointTail_isPWO b η hX).orderType ≤
      ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType := by
  classical
  have hlimit := residualPointTail_orderType_isSuccLimit b hX hη
  obtain ⟨e⟩ := (residualPointTail_isPWO b η hX).nonempty_orderIso_toType
  have hγmono : StrictMono fun i ↦ (e i).1 := fun i j hij ↦ e.strictMono hij
  have hγtail : ∀ i, (e i).1 ∈ residualPointTail b η := fun i ↦ (e i).2
  rcases (Order.one_le_iff_ne_zero.mpr b.residualValue_ne_zero).lt_or_eq with hρ | hρ
  · exact residualValue_mul_le_orderType_negativeSupportTail_of_one_lt b hρ hlimit _
      hγmono hγtail
  · exact residualValue_mul_le_orderType_negativeSupportTail_of_eq_one b hρ.symm hlimit _
      hγmono hγtail

/-- The upper bound of Berarducci, Lemma 6.8: on a stable interval the residual-point tail has
ordinary order type at most the principal value. The ordered-union estimate bounds
`v_J^r(b) ⬝ λ` by the order type `v_J^r(b) ⬝ v_J^p(b)` of the stable interval, and left
multiplication by the nonzero residual value is strictly increasing. -/
theorem residualPointTail_orderType_le
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO)
    {η : ℝ} (hη : η < 0)
    (hstable : ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType = (ordinalValue b.1).val) :
    (residualPointTail_isPWO b η hX).orderType ≤ b.principalValue.val := by
  have hρpos : 0 < b.residualValue.val := by
    rw [pos_iff_ne_zero]
    intro h
    exact b.residualValue_ne_zero (NatOrdinal.val.injective (by simpa using h))
  have hkey := residualValue_mul_residualPointTail_orderType_le b hX hη
  rw [hstable, ← b.residualValue_val_mul_principalValue_val] at hkey
  exact (Ordinal.isNormal_mul_right hρpos).strictMono.le_iff_le.mp hkey

/-- The supremum of a proper initial segment of limit order type. Let `S ⊆ ℝ` be partially
well-ordered and `κ < ot(S)` a limit ordinal. The initial segment of `S` of order type `κ` has
no greatest element, so its supremum `γ` is not attained: the segment is `S ∩ (-∞, γ)`, it is
nonempty, `γ` is its least upper bound, and some element of `S` lies weakly above `γ`. -/
private theorem exists_isLUB_orderType_inter_Iio_eq_of_isSuccLimit
    {S : Set ℝ} (hS : S.IsPWO) {κ : Ordinal} (hκ : Order.IsSuccLimit κ)
    (hκlt : κ < hS.orderType) :
    ∃ γ : ℝ, (S ∩ Set.Iio γ).Nonempty ∧ IsLUB (S ∩ Set.Iio γ) γ ∧ (∃ y ∈ S, γ ≤ y) ∧
      (hS.mono (s := S ∩ Set.Iio γ) Set.inter_subset_left).orderType = κ := by
  obtain ⟨x, hxS, hxot⟩ := hS.exists_orderType_inter_Iio_eq hκlt
  set I := S ∩ Set.Iio x with hIdef
  set hI := hS.mono (s := I) Set.inter_subset_left with hIpwo
  have hIot : hI.orderType = κ := hxot
  have hIne : I.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hzero : hI.orderType = 0 := hI.orderType_eq_zero.mpr hempty
    rw [hIot] at hzero
    exact hκ.ne_bot (by simpa using hzero)
  have hInomax : ∀ y ∈ I, ∃ z ∈ I, y < z := fun y hy ↦
    hI.exists_gt_of_isSuccLimit_orderType (by rw [hIot]; exact hκ) hy
  have hIbdd : BddAbove I := ⟨x, fun y hy ↦ le_of_lt hy.2⟩
  set γ := sSup I with hγdef
  have hle : ∀ y ∈ I, y ≤ γ := fun y hy ↦ le_csSup hIbdd hy
  have hlt : ∀ y ∈ I, y < γ := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hInomax y hy
    exact hyz.trans_le (hle z hz)
  have hSIio : S ∩ Set.Iio γ = I := by
    ext y
    constructor
    · rintro ⟨hyS, hyγ⟩
      by_contra hyI
      have hub : ∀ z ∈ I, z ≤ y := by
        intro z hz
        by_contra hzy
        exact hyI ⟨hyS, lt_trans (lt_of_not_ge hzy) hz.2⟩
      exact absurd (csSup_le hIne hub) (not_le.mpr hyγ)
    · exact fun hy ↦ ⟨hy.1, hlt y hy⟩
  refine ⟨γ, ?_, ?_, ⟨x, hxS, csSup_le hIne fun y hy ↦ le_of_lt hy.2⟩, ?_⟩
  · rw [hSIio]
    exact hIne
  · rw [hSIio]
    exact isLUB_csSup hIne hIbdd
  · rw [Set.IsPWO.orderType_congr _ hI hSIio, hIot]

/-- The upper bound on the value at the supremum. Let `I = S ∩ (-∞, γ)` be an initial segment
of the stable interval `S` of order type `ρ ⬝ (α + 1)`, with `ρ` a limit and `γ ≤ 0`. Then `I`
splits at the point `w` with `ot(S ∩ (-∞, w)) = ρ ⬝ α` into its first `ρ ⬝ α` elements and a
final segment of order type `ρ`; the window `S ∩ (w, γ)` is therefore a nonempty final segment of
the support below `γ` of order type at most `ρ`, which bounds the value of the translated
truncation at `γ`. -/
private theorem ordinalValue_translatedTruncation_val_le_of_orderType_inter_Iio_eq
    (b : SeriesWithOrdinalValueAboveOne K) {η γ : ℝ} {ρ α : Ordinal}
    (hρ0 : 0 < ρ) (hρlimit : Order.IsSuccLimit ρ) (hγ0 : γ ≤ 0)
    (hIot : (((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).mono
      (s := negativeSupportTail b.1 η ∩ Set.Iio γ) Set.inter_subset_left).orderType =
        ρ * (α + 1)) :
    (ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ)).val ≤ ρ := by
  classical
  set S := negativeSupportTail b.1 η with hSdef
  set hS := ((b.1 : K⟦ℝ⟧).isPWO_support.mono
    (negativeSupportTail_subset_support b.1 η)) with hSpwo
  set I := S ∩ Set.Iio γ with hIdef
  set hI := hS.mono (s := I) Set.inter_subset_left with hIpwo
  have hsucc : ρ * α < ρ * (α + 1) :=
    (Ordinal.isNormal_mul_right hρ0).strictMono (lt_add_one α)
  have hραlt : ρ * α < hS.orderType :=
    hsucc.trans_le (hIot.symm.le.trans (hI.orderType_mono hS Set.inter_subset_left))
  obtain ⟨w, hwS, hwot⟩ := hS.exists_orderType_inter_Iio_eq hραlt
  have hwγ : w < γ := by
    by_contra hγw
    have hsub : I ⊆ S ∩ Set.Iio w :=
      fun y hy ↦ ⟨hy.1, lt_of_lt_of_le hy.2 (not_lt.mp hγw)⟩
    have := hI.orderType_mono (hS.mono (s := S ∩ Set.Iio w) Set.inter_subset_left) hsub
    rw [hIot, hwot] at this
    exact absurd this (not_le.mpr hsucc)
  have hwI : w ∈ I := ⟨hwS, hwγ⟩
  have hIiow : I ∩ Set.Iio w = S ∩ Set.Iio w := by
    ext y
    exact ⟨fun hy ↦ ⟨hy.1.1, hy.2⟩, fun hy ↦ ⟨⟨hy.1, lt_trans hy.2 hwγ⟩, hy.2⟩⟩
  letI : WellFoundedLT I := hI.isWF
  have hsplit := hI.orderType_inter_Iio_add_inter_Ici hwI
  have hIiowot : (hI.mono (s := I ∩ Set.Iio w) Set.inter_subset_left).orderType = ρ * α := by
    rw [Set.IsPWO.orderType_congr _ (hS.mono (s := S ∩ Set.Iio w) Set.inter_subset_left) hIiow]
    exact hwot
  rw [hIiowot, hIot, mul_add_one] at hsplit
  have hIciwot : (hI.mono (s := I ∩ Set.Ici w) Set.inter_subset_left).orderType = ρ :=
    (add_left_cancel hsplit)
  have hCeq : S ∩ Set.Ioo w γ = I ∩ Set.Ioi w := by
    ext y
    exact ⟨fun ⟨hyS, hwy, hyγ⟩ ↦ ⟨⟨hyS, hyγ⟩, hwy⟩, fun ⟨hyI, hwy⟩ ↦ ⟨hyI.1, hwy, hyI.2⟩⟩
  have hCne : (S ∩ Set.Ioo w γ).Nonempty := by
    have hwT : w ∈ I ∩ Set.Ici w := ⟨hwI, le_refl w⟩
    obtain ⟨z, hz, hwz⟩ := Set.IsPWO.exists_gt_of_isSuccLimit_orderType
      (hI.mono (s := I ∩ Set.Ici w) Set.inter_subset_left)
      (by rw [hIciwot]; exact hρlimit) hwT
    exact ⟨z, by rw [hCeq]; exact ⟨hz.1, hwz⟩⟩
  have hCupper : IsRelUpperSet (S ∩ Set.Ioo w γ)
      (· ∈ (b.1 : K⟦ℝ⟧).support ∩ Set.Iio γ) := by
    rintro a ⟨haS, hwa, haγ⟩
    refine ⟨⟨(mem_negativeSupportTail_iff.mp haS).1, haγ⟩, ?_⟩
    rintro d had ⟨hdsupp, hdγ⟩
    exact ⟨mem_negativeSupportTail_iff.mpr
      ⟨hdsupp, lt_of_lt_of_le (mem_negativeSupportTail_iff.mp haS).2.1 had,
        lt_of_lt_of_le hdγ hγ0⟩, lt_of_lt_of_le hwa had, hdγ⟩
  refine (ordinalValue_translatedTruncation_le_orderType_of_isRelUpperSet_supportBelow
    (b.1 : K⟦ℝ⟧) γ hCupper hCne).trans ?_
  have hCsub : S ∩ Set.Ioo w γ ⊆ I ∩ Set.Ici w := by
    rw [hCeq]
    exact fun y hy ↦ ⟨hy.1, Set.mem_Ici.mpr (le_of_lt hy.2)⟩
  calc ((b.1 : K⟦ℝ⟧).isPWO_support.mono fun _ hx ↦ (hCupper hx).1.1).orderType
      ≤ (hI.mono (s := I ∩ Set.Ici w) Set.inter_subset_left).orderType :=
        Set.IsPWO.orderType_mono _ _ hCsub
    _ = ρ := hIciwot

/-- The lower bound on the value at the supremum. Let `γ` be the least upper bound of the initial
segment `I = S ∩ (-∞, γ)` of the stable interval `S`, of order type `ρ ⬝ (α + 1)` with `ρ`
additive principal. Every window `(θ, γ)` contains a final segment `I ∩ [z, γ)` of `I`, whose
order type is at least `ρ`, because `ot(I ∩ (-∞, z)) + ot(I ∩ [z, γ)) = ρ ⬝ (α + 1)` with the
first summand strictly smaller; so the value of the translated truncation at `γ` is at least
`ρ`. -/
private theorem le_ordinalValue_translatedTruncation_of_isLUB_of_orderType_inter_Iio_eq
    (b : SeriesWithOrdinalValueAboveOne K) {η γ : ℝ} {ρ α : Ordinal}
    (hρprin : Ordinal.IsAdditivelyPrincipal ρ)
    (hLUB : IsLUB (negativeSupportTail b.1 η ∩ Set.Iio γ) γ)
    (hIot : (((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).mono
      (s := negativeSupportTail b.1 η ∩ Set.Iio γ) Set.inter_subset_left).orderType =
        ρ * (α + 1)) :
    NatOrdinal.of ρ ≤ ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) := by
  classical
  set S := negativeSupportTail b.1 η with hSdef
  set hS := ((b.1 : K⟦ℝ⟧).isPWO_support.mono
    (negativeSupportTail_subset_support b.1 η)) with hSpwo
  set I := S ∩ Set.Iio γ with hIdef
  set hI := hS.mono (s := I) Set.inter_subset_left with hIpwo
  letI : WellFoundedLT I := hI.isWF
  apply le_ordinalValue_translatedTruncation_of_forall_le_orderType
  intro θ hθ
  obtain ⟨z, hzI, hθz, _⟩ := hLUB.exists_between hθ
  have hsplit2 := hI.orderType_inter_Iio_add_inter_Ici hzI
  have hlt2 : (hI.mono (s := I ∩ Set.Iio z) Set.inter_subset_left).orderType
      < hI.orderType := hI.orderType_inter_Iio_lt hzI
  rw [hIot] at hsplit2 hlt2
  refine (hρprin.le_of_add_eq_mul_succ hlt2 hsplit2).trans
    (Set.IsPWO.orderType_mono _ _ ?_)
  rintro y ⟨hyI, hzy⟩
  exact ⟨(mem_negativeSupportTail_iff.mp hyI.1).1, lt_of_lt_of_le hθz hzy, hyI.2⟩

/-- The printed construction of Berarducci, Lemma 6.8, for residual value above one. For each
`α` below the principal value, the supremum `γ` of the first `v_J^r(b) ⬝ (α + 1)` elements of the
stable interval is a residual point of the tail: that order type is a limit, so `γ` is not
attained, and the two value bounds at the supremum pin the translated truncation at `γ` to value
exactly `v_J^r(b)`. -/
theorem exists_residualPoint_orderType_eq
    (b : SeriesWithOrdinalValueAboveOne K) {η : ℝ}
    (hstable : ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType = (ordinalValue b.1).val)
    (hρ : 1 < b.residualValue) (i : b.principalValue.val.ToType) :
    ∃ γ : ℝ, γ ∈ residualPointTail b η ∧
      (((b.1 : K⟦ℝ⟧).isPWO_support.mono
          (negativeSupportTail_subset_support b.1 η)).mono
        (s := negativeSupportTail b.1 η ∩ Set.Iio γ) Set.inter_subset_left).orderType
        = b.residualValue.val *
        (Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i + 1) := by
  classical
  set S := negativeSupportTail b.1 η with hSdef
  set hS := ((b.1 : K⟦ℝ⟧).isPWO_support.mono
    (negativeSupportTail_subset_support b.1 η)) with hSpwo
  set ρ := b.residualValue.val with hρdef
  set α := Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i with hαdef
  have hρprin : Ordinal.IsAdditivelyPrincipal ρ := b.residualValue_isAdditivelyPrincipal
  have hρ0 : 0 < ρ := by
    rw [pos_iff_ne_zero]
    exact NatOrdinal.val_ne_zero.mpr b.residualValue_ne_zero
  have hρlimit : Order.IsSuccLimit ρ :=
    hρprin.isSuccLimit_of_one_lt (NatOrdinal.val.lt_iff_lt.mpr hρ)
  have hκlimit : Order.IsSuccLimit (ρ * (α + 1)) := by
    rw [mul_add_one]
    exact Ordinal.isSuccLimit_add _ hρlimit
  have hκlt : ρ * (α + 1) < hS.orderType := by
    rw [hstable, ← b.residualValue_val_mul_principalValue_val]
    exact (Ordinal.isNormal_mul_right hρ0).strictMono
      (b.principalValue_isInfiniteMultiplicativelyPrincipal.isSuccLimit.succ_lt
        (Ordinal.typein_lt_self i))
  obtain ⟨γ, ⟨y, hy⟩, hLUB, ⟨x, hxS, hγx⟩, hIot⟩ :=
    exists_isLUB_orderType_inter_Iio_eq_of_isSuccLimit hS hκlimit hκlt
  have hγneg : γ < 0 := hγx.trans_lt (mem_negativeSupportTail_iff.mp hxS).2.2
  have hγη : η < γ := lt_of_lt_of_le (mem_negativeSupportTail_iff.mp hy.1).2.1 (hLUB.1 hy)
  have hveq : ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) γ) = b.residualValue := by
    apply NatOrdinal.val.injective
    refine le_antisymm
      (ordinalValue_translatedTruncation_val_le_of_orderType_inter_Iio_eq b hρ0 hρlimit
        hγneg.le hIot) ?_
    have hmono := NatOrdinal.val.monotone
      (le_ordinalValue_translatedTruncation_of_isLUB_of_orderType_inter_Iio_eq b hρprin
        hLUB hIot)
    rwa [NatOrdinal.val_of] at hmono
  exact ⟨γ, mem_residualPointTail_iff.mpr
    ⟨mem_residualPointSet_iff.mpr ⟨hγneg, hveq⟩, hγη⟩, hIot⟩

private theorem principalValue_le_of_exists_residualPoint
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO) {η : ℝ}
    (g : b.principalValue.val.ToType → Ordinal) (hg : StrictMono g)
    (h : ∀ i, ∃ γ : ℝ, γ ∈ residualPointTail b η ∧
      ((((b.1 : K⟦ℝ⟧).isPWO_support.mono
          (negativeSupportTail_subset_support b.1 η)).mono
        (s := negativeSupportTail b.1 η ∩ Set.Iio γ) Set.inter_subset_left)).orderType = g i) :
    b.principalValue.val ≤ (residualPointTail_isPWO b η hX).orderType := by
  classical
  choose f hf hfot using h
  set hS := ((b.1 : K⟦ℝ⟧).isPWO_support.mono
    (negativeSupportTail_subset_support b.1 η)) with hSpwo
  have hmono : StrictMono f := by
    intro i j hij
    by_contra hle
    rw [not_lt] at hle
    have hsub : negativeSupportTail b.1 η ∩ Set.Iio (f j) ⊆
        negativeSupportTail b.1 η ∩ Set.Iio (f i) :=
      fun y hy ↦ ⟨hy.1, lt_of_lt_of_le hy.2 hle⟩
    have hcmp := Set.IsPWO.orderType_mono
      (hS.mono (s := negativeSupportTail b.1 η ∩ Set.Iio (f j)) Set.inter_subset_left)
      (hS.mono (s := negativeSupportTail b.1 η ∩ Set.Iio (f i)) Set.inter_subset_left) hsub
    rw [hfot i, hfot j] at hcmp
    exact absurd hcmp (not_le.mpr (hg hij))
  have hrange : Set.range f ⊆ residualPointTail b η := by
    rintro _ ⟨i, rfl⟩
    exact hf i
  have hRPWO : (Set.range f).IsPWO := (residualPointTail_isPWO b η hX).mono hrange
  have hRot : hRPWO.orderType = b.principalValue.val := by
    rw [hRPWO.orderType_eq_typeLT_of_orderIso (hmono.orderIso f).symm]
    exact Ordinal.type_toType _
  calc b.principalValue.val = hRPWO.orderType := hRot.symm
    _ ≤ (residualPointTail_isPWO b η hX).orderType :=
        hRPWO.orderType_mono _ hrange

theorem principalValue_le_residualPointTail_orderType_of_one_lt
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO) {η : ℝ}
    (hstable : ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType = (ordinalValue b.1).val)
    (hρ : 1 < b.residualValue) :
    b.principalValue.val ≤ (residualPointTail_isPWO b η hX).orderType := by
  have hρ0 : 0 < b.residualValue.val := by
    rw [pos_iff_ne_zero]
    exact NatOrdinal.val_ne_zero.mpr b.residualValue_ne_zero
  refine principalValue_le_of_exists_residualPoint b hX
    (fun i ↦ b.residualValue.val *
      (Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i + 1)) ?_
    (exists_residualPoint_orderType_eq b hstable hρ)
  intro i j hij
  have hlt : Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i <
      Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) j :=
    (Ordinal.typein_lt_typein (· < ·)).mpr hij
  exact (Ordinal.isNormal_mul_right hρ0).strictMono
    ((Order.add_one_le_iff.mpr hlt).trans_lt (lt_add_one _))

theorem exists_residualPoint_orderType_eq_of_residualValue_eq_one
    (b : SeriesWithOrdinalValueAboveOne K) {η : ℝ}
    (hstable : ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType = (ordinalValue b.1).val)
    (hρ : b.residualValue = 1) (i : b.principalValue.val.ToType) :
    ∃ γ : ℝ, γ ∈ residualPointTail b η ∧
      (((b.1 : K⟦ℝ⟧).isPWO_support.mono
          (negativeSupportTail_subset_support b.1 η)).mono
        (s := negativeSupportTail b.1 η ∩ Set.Iio γ) Set.inter_subset_left).orderType
        = Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i + 1 := by
  classical
  set S := negativeSupportTail b.1 η with hSdef
  set hS := ((b.1 : K⟦ℝ⟧).isPWO_support.mono
    (negativeSupportTail_subset_support b.1 η)) with hSpwo
  set α := Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i with hαdef
  have hαπ : α < b.principalValue.val := Ordinal.typein_lt_self i
  have hπlimit : Order.IsSuccLimit b.principalValue.val :=
    b.principalValue_isInfiniteMultiplicativelyPrincipal.isSuccLimit
  have hSot : hS.orderType = b.principalValue.val := by
    rw [hstable, ← b.residualValue_val_mul_principalValue_val, hρ]
    simp
  have hsucclt : α + 1 < b.principalValue.val := hπlimit.succ_lt hαπ
  obtain ⟨y, hyS, hyot⟩ := hS.exists_orderType_inter_Iio_eq (by rw [hSot]; exact hsucclt)
  set T := S ∩ Set.Iio y with hTdef
  set hT := hS.mono (s := T) Set.inter_subset_left with hTpwo
  have hTot : hT.orderType = α + 1 := hyot
  have hTmax : ∃ z ∈ T, ∀ u ∈ T, u ≤ z := by
    by_contra hcon
    push Not at hcon
    have hne : T.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      have := hT.orderType_eq_zero.mpr hempty
      rw [hTot] at this
      rw [← Order.succ_eq_add_one] at this
      exact Order.succ_ne_bot α this
    have hgt : ∀ u ∈ T, ∃ v ∈ T, u < v := by
      intro u hu
      obtain ⟨v, hv, hvu⟩ := hcon u hu
      exact ⟨v, hv, hvu⟩
    have := Set.IsPWO.isSuccLimit_orderType_of_forall_exists_gt hT hne hgt
    rw [hTot, ← Order.succ_eq_add_one] at this
    exact Order.not_isSuccLimit_succ α this
  obtain ⟨z, hzT, hzmax⟩ := hTmax
  have hzy : z < y := hzT.2
  have hgap : ∀ u : ℝ, z < u → u < y → u ∉ (b.1 : K⟦ℝ⟧).support := by
    intro u hzu huy hu
    have huS : u ∈ S := mem_negativeSupportTail_iff.mpr
      ⟨hu, lt_trans (mem_negativeSupportTail_iff.mp hzT.1).2.1 hzu,
        lt_trans huy (mem_negativeSupportTail_iff.mp hyS).2.2⟩
    exact absurd (hzmax u ⟨huS, huy⟩) (not_le.mpr hzu)
  have hycoeff : (b.1 : K⟦ℝ⟧).coeff y ≠ 0 :=
    (HahnSeries.mem_support _ _).mp (mem_negativeSupportTail_iff.mp hyS).1
  have hyneg : y < 0 := (mem_negativeSupportTail_iff.mp hyS).2.2
  have hyη : η < y := (mem_negativeSupportTail_iff.mp hyS).2.1
  have hnear : translatedTruncation (b.1 : K⟦ℝ⟧) y ∈ nearConstantSubgroup K := by
    refine mem_nearConstantSubgroup_iff_exists_germ_eq_constant.mpr
      ⟨(b.1 : K⟦ℝ⟧).coeff y, ?_⟩
    refine toGerm_eq_toGerm_iff_exists_coeff_eq.mpr
      ⟨z - y, by linarith, fun δ hδlow hδ0 ↦ ?_⟩
    rw [coeff_translatedTruncation, ite_eq_left hδ0, HahnSeries.Nonpositive.coe_C]
    rcases hδ0.eq_or_lt with rfl | hδneg
    · simp
    · rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by linarith : δ ≠ (0 : ℝ))]
      by_contra hne
      exact hgap (y + δ) (by linarith) (by linarith)
        ((HahnSeries.mem_support _ _).mpr hne)
  have hnotJ : translatedTruncation (b.1 : K⟦ℝ⟧) y ∉
      HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    intro hmem
    have hzero := constantCoeff_eq_zero_of_mem_negativeMonomialIdeal hmem
    rw [HahnSeries.Nonpositive.constantCoeff_apply, coeff_translatedTruncation,
      ite_eq_left le_rfl] at hzero
    exact hycoeff (by simpa using hzero)
  have hveq : ordinalValue (translatedTruncation (b.1 : K⟦ℝ⟧) y) = b.residualValue := by
    rw [hρ]
    exact ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal hnear hnotJ
  exact ⟨y, mem_residualPointTail_iff.mpr
    ⟨mem_residualPointSet_iff.mpr ⟨hyneg, hveq⟩, hyη⟩, hyot⟩

theorem principalValue_le_residualPointTail_orderType_of_eq_one
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO) {η : ℝ}
    (hstable : ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType = (ordinalValue b.1).val)
    (hρ : b.residualValue = 1) :
    b.principalValue.val ≤ (residualPointTail_isPWO b η hX).orderType := by
  refine principalValue_le_of_exists_residualPoint b hX
    (fun i ↦ Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i + 1) ?_
    (exists_residualPoint_orderType_eq_of_residualValue_eq_one b hstable hρ)
  intro i j hij
  have hlt : Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) i <
      Ordinal.typein (α := b.principalValue.val.ToType) (· < ·) j :=
    (Ordinal.typein_lt_typein (· < ·)).mpr hij
  exact (Order.add_one_le_iff.mpr hlt).trans_lt (lt_add_one _)

/-- The order-type computation in Berarducci, Lemma 6.8: on a stable interval the residual-point
tail has ordinary order type exactly the principal value. -/
theorem residualPointTail_orderType_eq
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO)
    {η : ℝ} (hη : η < 0)
    (hstable : ((b.1 : K⟦ℝ⟧).isPWO_support.mono
        (negativeSupportTail_subset_support b.1 η)).orderType = (ordinalValue b.1).val) :
    (residualPointTail_isPWO b η hX).orderType = b.principalValue.val := by
  refine le_antisymm (residualPointTail_orderType_le b hX hη hstable) ?_
  rcases (Order.one_le_iff_ne_zero.mpr b.residualValue_ne_zero).lt_or_eq with hρ | hρ
  · exact principalValue_le_residualPointTail_orderType_of_one_lt b hX hstable hρ
  · exact principalValue_le_residualPointTail_orderType_of_eq_one b hX hstable hρ.symm

/-- Berarducci, Lemma 6.8, order-type half: sufficiently high residual-point tails have ordinary
order type equal to the principal value. -/
theorem residualPointTail_orderType_eventually
    (b : SeriesWithOrdinalValueAboveOne K) (hX : (residualPointSet b).IsPWO) :
    ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Iio 0),
      (residualPointTail_isPWO b η hX).orderType = b.principalValue.val := by
  obtain ⟨η₀, hη₀, hstable⟩ :=
    exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue b.1 b.2
  rw [eventually_nhdsLT_iff_exists]
  exact ⟨η₀, hη₀, fun ξ hlow hhigh ↦
    residualPointTail_orderType_eq b hX hhigh (hstable ξ hlow hhigh)⟩

end Berarducci
