/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAt
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAtInjective

/-!
# The support of a derivative has order type at most `ω`

Let `α` be a successor ordinal, `δ := α ⊖ 1`, and `p` a principal series of degree `α`:
`v_J(p) = ω^α` and the support of `p` has order type `ω^α`. The set of cutoffs `ξ < 0` at which
the ordinal value of `p` is at least `ω^δ`, that is `ω^δ ≤ v_J(p^{|ξ})` (`cutoffsGE δ p`), is well
ordered with finite initial segments, hence of order type at most `ω`. Indeed, for a cutoff `ξ` of
this set, every interval `(θ, ξ]` with `θ < ξ` carries support of order type at least `ω^δ`; a
strictly increasing sequence of such cutoffs bounded by `ξ₀ < 0` would therefore force support of
order type at least `ω^δ · ω = ω^α` below `ξ₀`, while `v_J(p) = ω^α` already needs support of
order type `ω^α` above `ξ₀`, more than the order type `ω^α` of the whole support.

Consequently the derivative `∂(x)` of a nonzero `x ∈ P_α` is the class of a function at `0⁻`
vanishing outside a strictly increasing sequence of cutoffs with supremum `0`: `∂(x)` vanishes
outside the cutoffs at which the ordinal value of a principal representative is at least `ω^δ`.
This is the form used by `mem_span_of_principalSubringDerivation_eq_coe`.
-/

universe v

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-! ### Support between two cutoffs -/

/-- If `p^{|γ}` has ordinal value at least `ω^δ`, the support of `p` in any interval `(θ, γ]`
has order type at least `ω^δ`. -/
theorem wpow_le_supportOrderType_truncGT_truncLE {δ : NatOrdinal} (p : Series K) {γ θ : ℝ}
    (hθγ : θ < γ) (hγ : ω^ δ ≤ ordinalValue (translatedTruncation (p : K⟦ℝ⟧) γ)) :
    ω^ δ ≤ NatOrdinal.of (truncGT θ (truncLE γ (p : K⟦ℝ⟧))).supportOrderType := by
  -- the part of `p^{|γ}` beyond `θ - γ`, as a nonpositive series
  let r : Series K := ⟨translate (-γ) (truncGT θ (truncLE γ (p : K⟦ℝ⟧))), by
    rw [mem_nonpositiveSubring]
    intro x hx
    rw [support_translate] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ≤ γ := by
      have := support_truncGT_subset θ _ hy
      rw [support_truncLE] at this
      exact this.2
    change -γ + y ≤ 0
    linarith⟩
  have hgerm : toGerm (translatedTruncation (p : K⟦ℝ⟧) γ) = toGerm r := by
    rw [toGerm_eq_toGerm_iff_exists_coeff_eq]
    refine ⟨θ - γ, by linarith, fun η hη1 hη2 ↦ ?_⟩
    rw [coeff_translatedTruncation, if_pos hη2]
    change _ = (translate (-γ) (truncGT θ (truncLE γ (p : K⟦ℝ⟧)))).coeff η
    rw [coeff_translate, sub_neg_eq_add, coeff_truncGT_of_lt (by linarith),
      HahnSeries.coeff_truncLE, if_pos (by linarith), add_comm]
  calc ω^ δ ≤ ordinalValue (translatedTruncation (p : K⟦ℝ⟧) γ) := hγ
    _ = ordinalValue r :=
        ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm)
    _ ≤ NatOrdinal.of (r : K⟦ℝ⟧).supportOrderType := ordinalValue_le_supportOrderType r
    _ = NatOrdinal.of (truncGT θ (truncLE γ (p : K⟦ℝ⟧))).supportOrderType := by
        change NatOrdinal.of
          (translate (-γ) (truncGT θ (truncLE γ (p : K⟦ℝ⟧)))).supportOrderType = _
        rw [supportOrderType_translate]

/-- The support of `p` in `(θ, γ]` is nonempty when `p^{|γ}` has ordinal value at least `ω^δ`. -/
theorem exists_mem_support_Ioc_of_wpow_le {δ : NatOrdinal} (p : Series K) {γ θ : ℝ}
    (hθγ : θ < γ) (hγ : ω^ δ ≤ ordinalValue (translatedTruncation (p : K⟦ℝ⟧) γ)) :
    ∃ x ∈ (p : K⟦ℝ⟧).support, θ < x ∧ x ≤ γ := by
  have h := wpow_le_supportOrderType_truncGT_truncLE p hθγ hγ
  have hne : (truncGT θ (truncLE γ (p : K⟦ℝ⟧))).support.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have h0 : (truncGT θ (truncLE γ (p : K⟦ℝ⟧))).supportOrderType = 0 := by
      rw [supportOrderType_eq_setOrderType]
      exact (Set.IsPWO.orderType_eq_zero _).mpr hempty
    rw [h0] at h
    exact absurd h (not_le.mpr (NatOrdinal.wpow_pos δ))
  obtain ⟨x, hx⟩ := hne
  rw [support_truncGT, support_truncLE] at hx
  exact ⟨x, hx.1.1, hx.2, hx.1.2⟩

/-! ### The cutoffs at which the ordinal value is at least `ω^δ` -/

/-- The set of cutoffs `ξ < 0` at which the ordinal value of `p` is at least `ω^δ`:
`ω^δ ≤ v_J(p^{|ξ})`. For `p` principal of degree `δ + 1` this is the set of cutoffs at which
`∂(p + J_{ω^{δ+1}})` does not vanish and, `v_J^r(p)` being `ω^δ`, it is the set `Res(p) = X(p)` of
residual points of [FLLM, Def. 2.7], [Ber00, Def. 6.6]; for arbitrary `p` and `δ` it is the set
`Big^δ(p)` of [FLLM, Def. 2.7] *without* FLLM's clause `ξ > crit_J(p)`, which is not imposed
here. -/
def cutoffsGE (δ : NatOrdinal) (p : Series K) : Set ℝ :=
  {ξ | ξ < 0 ∧ ω^ δ ≤ ordinalValue (translatedTruncation (p : K⟦ℝ⟧) ξ)}

theorem mem_cutoffsGE_iff {δ : NatOrdinal} {p : Series K} {ξ : ℝ} :
    ξ ∈ cutoffsGE δ p ↔ ξ < 0 ∧ ω^ δ ≤ ordinalValue (translatedTruncation (p : K⟦ℝ⟧) ξ) :=
  (Iff.rfl)

/-- The cutoffs at which the ordinal value of `p` is at least `ω^δ` form a well-ordered set. -/
theorem cutoffsGE_isPWO (δ : NatOrdinal) (p : Series K) : (cutoffsGE δ p).IsPWO := by
  rw [Set.isPWO_iff_isWF, Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  have hpick : ∀ k, ∃ x ∈ (p : K⟦ℝ⟧).support, f (k + 1) < x ∧ x ≤ f k := fun k ↦
    exists_mem_support_Ioc_of_wpow_le p (hf (Nat.lt_succ_self k)) (hmem k).2
  choose x hx hx1 hx2 using hpick
  refine (Set.isWF_iff_no_descending_seq.mp (p : K⟦ℝ⟧).isPWO_support.isWF) x ?_ hx
  exact strictAnti_nat_of_succ_lt fun k ↦ (hx2 (k + 1)).trans_lt (hx1 k)

/-- Truncating below `c` and then below `c'` with `c ≤ c'` truncates below `c`. -/
theorem truncLE_truncLE_of_le {c c' : ℝ} (h : c ≤ c') (x : K⟦ℝ⟧) :
    truncLE c (truncLE c' x) = truncLE c x := by
  ext g
  simp only [HahnSeries.coeff_truncLE]
  split_ifs with h1 h2 <;> first | rfl | exact absurd (h1.trans h) h2

/-- A strictly increasing sequence of cutoffs at which the ordinal value of `p` is at least `ω^δ`
forces support of order type at least `ω^δ · n` below its `n`-th member. -/
theorem wpow_mul_le_supportOrderType_truncLE {δ : NatOrdinal} (p : Series K) (γ : ℕ → ℝ)
    (hγ : StrictMono γ) (hmem : ∀ k, γ k ∈ cutoffsGE δ p) (n : ℕ) :
    Ordinal.omega0 ^ δ.val * n ≤ (truncLE (γ n) (p : K⟦ℝ⟧)).supportOrderType := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit := supportOrderType_eq_truncLE_add_truncGT (γ n) (truncLE (γ (n + 1)) (p : K⟦ℝ⟧))
    rw [truncLE_truncLE_of_le (hγ.monotone (Nat.le_succ n))] at hsplit
    have hblock : Ordinal.omega0 ^ δ.val ≤
        (truncGT (γ n) (truncLE (γ (n + 1)) (p : K⟦ℝ⟧))).supportOrderType := by
      have := wpow_le_supportOrderType_truncGT_truncLE (δ := δ) p (hγ (Nat.lt_succ_self n))
        (hmem (n + 1)).2
      rw [← NatOrdinal.val_wpow]
      exact NatOrdinal.val.monotone this
    rw [hsplit, Nat.cast_add_one, ← Order.succ_eq_add_one, Ordinal.mul_succ]
    exact add_le_add ih hblock

/-- A strictly increasing sequence of cutoffs at which the ordinal value of `p` is at least `ω^δ`,
bounded by `ξ₀`, forces support of order type at least `ω^(δ+1)` below `ξ₀`. -/
theorem wpow_add_one_le_supportOrderType_truncLE {δ : NatOrdinal} (p : Series K) (γ : ℕ → ℝ)
    (hγ : StrictMono γ) (hmem : ∀ k, γ k ∈ cutoffsGE δ p) {ξ₀ : ℝ} (hξ₀ : ∀ k, γ k ≤ ξ₀) :
    ω^ (δ + 1) ≤ NatOrdinal.of (truncLE ξ₀ (p : K⟦ℝ⟧)).supportOrderType := by
  rw [NatOrdinal.wpow_add_one_le_iff]
  intro n
  rw [NatOrdinal.wpow_mul_natCast]
  refine NatOrdinal.of.monotone ?_
  refine (wpow_mul_le_supportOrderType_truncLE p γ hγ hmem n).trans ?_
  rw [supportOrderType_eq_setOrderType, supportOrderType_eq_setOrderType]
  refine Set.IsPWO.orderType_mono _ _ ?_
  rw [support_truncLE, support_truncLE]
  exact Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr (hξ₀ n))

/-- For `p` with ordinal value and support order type `ω^(δ+1)`, only finitely many translated
truncations at or below a fixed negative exponent have ordinal value at least `ω^δ`. -/
@[blueprint "lem:finite-successor-value-cutoffs"
  (phase := "Translated truncations")
  (title := "Local finiteness of translated truncations at successor ordinal value")
  (statement := /--
    Let $K$ be a field, let $\delta<\omega_1$, and let
    $p\in K((\mathbb R^{\le0}))$ satisfy
    \[
      v_J(p)=\operatorname{ot}(p)=\omega^{\delta+1}.
    \]
    For every $\xi_0<0$, the set
    \[
      \{\xi\le\xi_0:v_J(p^{|\xi})\ge\omega^\delta\}
    \]
    is finite.
  -/)
  (proof := /--
  Otherwise choose a strictly increasing sequence $(\gamma_n)$ in this set.
  The support between consecutive $\gamma_n$ has order type at least
  $\omega^\delta$, so the support at or below $\xi_0$ has order type at least
  $\omega^\delta\cdot\omega=\omega^{\delta+1}$. Removing that part does not
  change the series modulo $J$, hence the remaining support above $\xi_0$ also
  has order type at least $\omega^{\delta+1}$. Splitting the support at
  $\xi_0$ would therefore give
  \[
    \operatorname{ot}(p)\ge
      \omega^{\delta+1}+\omega^{\delta+1}>\omega^{\delta+1},
  \]
  a contradiction.
  -/)]
theorem cutoffsGE_inter_Iic_finite_of_neg {δ : NatOrdinal} (p : Series K)
    (hv : ordinalValue p = ω^ (δ + 1)) (hot : (p : K⟦ℝ⟧).supportOrderType = (ω^ (δ + 1)).val)
    {ξ₀ : ℝ} (hξ₀ : ξ₀ < 0) : (cutoffsGE δ p ∩ Set.Iic ξ₀).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  -- a strictly increasing sequence in `cutoffsGE δ p` bounded by `ξ₀`
  let f := hinf.natEmbedding
  obtain ⟨g, hg⟩ := (cutoffsGE_isPWO δ p).exists_monotone_subseq
    (f := fun n ↦ ((f n : ↥(cutoffsGE δ p ∩ Set.Iic ξ₀)) : ℝ)) fun n ↦ (f n).2.1
  set γ : ℕ → ℝ := fun k ↦ ((f (g k) : ↥(cutoffsGE δ p ∩ Set.Iic ξ₀)) : ℝ) with hγdef
  have hmono : StrictMono γ := by
    refine Monotone.strictMono_of_injective (fun ⦃_ _⦄ hmn ↦ hg hmn) ?_
    intro m n hmn
    exact g.injective (f.injective (Subtype.val_injective hmn))
  have hmem : ∀ k, γ k ∈ cutoffsGE δ p := fun k ↦ (f (g k)).2.1
  have hle : ∀ k, γ k ≤ ξ₀ := fun k ↦ (f (g k)).2.2
  -- support of order type `ω^(δ+1)` below `ξ₀` …
  have hbelow : (ω^ (δ + 1)).val ≤ (truncLE ξ₀ (p : K⟦ℝ⟧)).supportOrderType :=
    NatOrdinal.val.monotone (wpow_add_one_le_supportOrderType_truncLE p γ hmono hmem hle)
  -- … and above `ξ₀`
  have habove : (ω^ (δ + 1)).val ≤ (truncGT ξ₀ (p : K⟦ℝ⟧)).supportOrderType := by
    let r : Series K := ⟨truncGT ξ₀ (p : K⟦ℝ⟧), by
      rw [mem_nonpositiveSubring]
      exact (support_truncGT_subset ξ₀ _).trans (HahnSeries.Nonpositive.support_subset p)⟩
    have hgerm : toGerm p = toGerm r := by
      rw [toGerm_eq_toGerm_iff_exists_coeff_eq]
      refine ⟨ξ₀, hξ₀, fun η hη1 _ ↦ ?_⟩
      change _ = (truncGT ξ₀ (p : K⟦ℝ⟧)).coeff η
      rw [coeff_truncGT_of_lt hη1]
    have := ordinalValue_le_supportOrderType r
    rw [← ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm),
      hv] at this
    exact NatOrdinal.val.monotone this
  have hsplit := supportOrderType_eq_truncLE_add_truncGT ξ₀ (p : K⟦ℝ⟧)
  rw [hot] at hsplit
  have hpos : 0 < (ω^ (δ + 1)).val := Ordinal.opow_pos _ Ordinal.omega0_pos
  exact absurd hsplit (ne_of_lt ((lt_add_of_pos_right _ hpos).trans_le (add_le_add hbelow habove)))

/-- **Finite initial segments.** For `p` with `v_J(p) = ω^(δ+1)` and support of order type
`ω^(δ+1)` (a principal series of degree `δ + 1`), the cutoffs of `cutoffsGE δ p` below any
`ξ₀ ∈ cutoffsGE δ p` are finitely many. -/
theorem cutoffsGE_inter_Iic_finite {δ : NatOrdinal} (p : Series K)
    (hv : ordinalValue p = ω^ (δ + 1)) (hot : (p : K⟦ℝ⟧).supportOrderType = (ω^ (δ + 1)).val)
    {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ cutoffsGE δ p) : (cutoffsGE δ p ∩ Set.Iic ξ₀).Finite :=
  cutoffsGE_inter_Iic_finite_of_neg p hv hot hξ₀.1

/-- **Finitely many cutoffs of ordinal value at least `ω^δ`.** A series `p` whose support has
order type below `ω^(δ+1)` has only finitely many cutoffs `ξ < 0` with `ω^δ ≤ v_J(p^{|ξ})`. -/
theorem cutoffsGE_finite_of_supportOrderType_lt {δ : NatOrdinal} (p : Series K)
    (hot : (p : K⟦ℝ⟧).supportOrderType < (ω^ (δ + 1)).val) : (cutoffsGE δ p).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  let f := hinf.natEmbedding
  obtain ⟨g, hg⟩ := (cutoffsGE_isPWO δ p).exists_monotone_subseq
    (f := fun n ↦ ((f n : ↥(cutoffsGE δ p)) : ℝ)) fun n ↦ (f n).2
  set γ : ℕ → ℝ := fun k ↦ ((f (g k) : ↥(cutoffsGE δ p)) : ℝ) with hγdef
  have hmono : StrictMono γ := by
    refine Monotone.strictMono_of_injective (fun ⦃_ _⦄ hmn ↦ hg hmn) ?_
    intro m n hmn
    exact g.injective (f.injective (Subtype.val_injective hmn))
  have hmem : ∀ k, γ k ∈ cutoffsGE δ p := fun k ↦ (f (g k)).2
  have hle : ∀ k, γ k ≤ 0 := fun k ↦ (mem_cutoffsGE_iff.mp (hmem k)).1.le
  have h := wpow_add_one_le_supportOrderType_truncLE p γ hmono hmem hle
  have htrunc : truncLE (0 : ℝ) (p : K⟦ℝ⟧) = p := by
    ext i
    rw [HahnSeries.coeff_truncLE]
    split_ifs with hi
    · rfl
    · by_contra h
      exact hi (HahnSeries.Nonpositive.support_subset p
        ((HahnSeries.mem_support _ _).mpr fun h0 ↦ h h0.symm))
  rw [htrunc] at h
  exact absurd (NatOrdinal.val.monotone h) (not_le.mpr hot)

/-! ### Enumerating a well-ordered set with finite initial segments -/

/-- An infinite well-ordered set of reals with finite initial segments is the range of a strictly
increasing sequence. -/
theorem exists_strictMono_range_eq {Z : Set ℝ} (hZ : Z.IsPWO)
    (hfin : ∀ z ∈ Z, (Z ∩ Set.Iic z).Finite) (hinf : Z.Infinite) :
    ∃ γ : ℕ → ℝ, StrictMono γ ∧ Set.range γ = Z := by
  classical
  have hne : Z.Nonempty := hinf.nonempty
  -- the least element of `Z` above a point
  let next : ℝ → ℝ := fun x ↦
    if h : (Z ∩ Set.Ioi x).Nonempty then (hZ.isWF.mono Set.inter_subset_left).min h else x
  have hnext_mem : ∀ x, (Z ∩ Set.Ioi x).Nonempty → next x ∈ Z ∧ x < next x := fun x h ↦ by
    simp only [next, dif_pos h]
    exact Set.IsWF.min_mem _ h
  have hnext_le : ∀ x, ∀ z ∈ Z, x < z → next x ≤ z := fun x z hz hxz ↦ by
    have h : (Z ∩ Set.Ioi x).Nonempty := ⟨z, hz, hxz⟩
    simp only [next, dif_pos h]
    exact Set.IsWF.min_le _ h ⟨hz, hxz⟩
  -- every point of `Z` has a point of `Z` above it
  have hZne : ∀ x ∈ Z, (Z ∩ Set.Ioi x).Nonempty := fun x hx ↦ by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    refine hinf ((hfin x hx).subset fun z hz ↦ ⟨hz, ?_⟩)
    by_contra hlt
    rw [Set.mem_Iic, not_le] at hlt
    exact Set.eq_empty_iff_forall_notMem.mp hcon z ⟨hz, hlt⟩
  let γ : ℕ → ℝ := fun k ↦ next^[k] (hZ.isWF.min hne)
  have hγsucc : ∀ k, γ (k + 1) = next (γ k) := fun k ↦ Function.iterate_succ_apply' next k _
  have hγmem : ∀ k, γ k ∈ Z := by
    intro k
    induction k with
    | zero => exact Set.IsWF.min_mem _ _
    | succ k ih =>
      rw [hγsucc]
      exact (hnext_mem _ (hZne _ ih)).1
  have hmono : StrictMono γ := strictMono_nat_of_lt_succ fun k ↦ by
    rw [hγsucc]
    exact (hnext_mem _ (hZne _ (hγmem k))).2
  refine ⟨γ, hmono, Set.Subset.antisymm ?_ fun z hz ↦ ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact hγmem k
  · by_contra hz'
    -- a point of `Z` missed by the enumeration lies above every term
    have hlt : ∀ k, γ k < z := by
      intro k
      induction k with
      | zero => exact lt_of_le_of_ne (Set.IsWF.min_le _ _ hz) fun h ↦ hz' ⟨0, h⟩
      | succ k ih =>
        rw [hγsucc]
        exact lt_of_le_of_ne (hnext_le _ z hz ih) fun h ↦ hz' ⟨k + 1, by rw [hγsucc]; exact h⟩
    exact (hfin z hz).not_infinite ((Set.infinite_range_of_injective hmono.injective).mono
      (Set.range_subset_iff.mpr fun k ↦ ⟨hγmem k, (hlt k).le⟩))

/-! ### The derivative of a nonzero class vanishes outside a sequence `γ_k ↑ 0` -/

/-- A nonzero class in `P_α`, for successor `α`, has a principal representative whose
translated-truncation function is supported on a sequence increasing to zero. -/
@[blueprint "lem:successor-principal-rv-countable-support"
  (phase := "Translated truncations")
  (title := "Countable-support representatives of $\\mathrm P_\\alpha$")
  (statement := /--
    Let $K$ be a field, let $\alpha=\beta+1<\omega_1$, and let
    $0\ne x\in\mathrm P_\alpha$. Then $x$ has a principal representative $p$
    of degree $\alpha$. Let $D_p:\mathbb R\to\mathrm P_\beta$ be the function
    used to represent $\partial_\alpha(x)$: whenever
    $v_J(p^{|\xi})<\omega^{\beta+1}$, put $D_p(\xi)=[p^{|\xi}]$, and put
    $D_p(\xi)=0$ otherwise. There is a strictly increasing sequence of negative
    reals $(\gamma_k)_{k\in\mathbb N}$, cofinal in $0$, such that
    \[
      \{\xi<0:D_p(\xi)\ne0\}\subseteq
        \{\gamma_k:k\in\mathbb N\}.
    \]
  -/)
  (proof := /--
  By \ref{fact:principal-series-representatives}, choose a principal
  representative $p$ of $x$ of degree $\alpha$. The set
  \[
    Z:=\{\xi<0:D_p(\xi)\ne0\}
  \]
  is well ordered because a decreasing sequence in $Z$ would induce a
  decreasing sequence in $\operatorname{supp}(p)$. By
  \ref{lem:finite-successor-value-cutoffs}, each initial segment of $Z$ is
  finite. By
  \ref{prop:successor-principal-rv-injective}, $D_p$ cannot vanish throughout
  any interval $(\eta,0)$, since that would give
  $\partial_\alpha(x)=0$ and hence $x=0$. Thus $Z$ is infinite and cofinal in
  $0$. Enumerating $Z$ in increasing order gives the required sequence.
  -/)]
theorem exists_principal_representative_derivAt (α : NatOrdinal) (hα : 0 < α.constantCoeff)
    {x : PrincipalComponent K α} (hx : x ≠ 0) :
    ∃ (p : Series K) (hp : ordinalValue p < ω^ (α + 1)),
      HahnSeries.Nonpositive.IsPrincipal p ∧
        (p : K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) ∧
        principalComponentMk α p hp = x ∧
        ∃ γ : ℕ → ℝ, StrictMono γ ∧ (∀ k, γ k < 0) ∧
          (∀ η < (0 : ℝ), ∃ k, η < γ k) ∧
          ∀ ξ, ξ < 0 → derivAt α p ξ ≠ 0 → ∃ k, γ k = ξ := by
  classical
  obtain ⟨p, hp, hprin, hdeg, hpx⟩ := exists_principal_representative_of_ne_zero α x hx
  refine ⟨p, hp, hprin, hdeg, hpx, ?_⟩
  set δ := α.removeNat 1 with hδdef
  have hδ : δ + 1 = α := by
    have := NatOrdinal.removeNat_add_natCast (a := α) (n := 1) hα
    rwa [Nat.cast_one] at this
  have hv : ordinalValue p = ω^ (δ + 1) := by
    rw [hδ]
    exact ordinalValue_eq_wpow_of_principalComponentMk_ne_zero α p hp (hpx ▸ hx)
  have hot : (p : K⟦ℝ⟧).supportOrderType = (ω^ (δ + 1)).val := by
    rw [hδ]
    exact hprin.supportOrderType_eq_wpow_of_degree_eq hdeg
  -- the cutoffs where the derivative is nonzero
  set Z : Set ℝ := {ξ | ξ < 0 ∧ derivAt α p ξ ≠ 0} with hZdef
  have hZsub : Z ⊆ cutoffsGE δ p := by
    rintro ξ ⟨hξ0, hξ⟩
    refine ⟨hξ0, ?_⟩
    by_cases h : ordinalValue (translatedTruncation (p : K⟦ℝ⟧) ξ) < ω^ (δ + 1)
    · rw [derivAt_eq α p ξ h] at hξ
      exact (ordinalValue_eq_wpow_of_principalComponentMk_ne_zero δ _ h hξ).ge
    · exact (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one δ)).le.trans (not_lt.mp h)
  have hZpwo : Z.IsPWO := (cutoffsGE_isPWO δ p).mono hZsub
  have hZfin : ∀ z ∈ Z, (Z ∩ Set.Iic z).Finite := fun z hz ↦
    (cutoffsGE_inter_Iic_finite p hv hot (hZsub hz)).subset
      (Set.inter_subset_inter_left _ hZsub)
  have hcof : ∀ η < (0 : ℝ), ∃ ξ, η < ξ ∧ ξ < 0 ∧ derivAt α p ξ ≠ 0 := by
    intro η hη
    by_contra h
    push Not at h
    have hzero : principalComponentDerivAt K α hα x = 0 := by
      rw [← hpx, principalComponentDerivAt_principalComponentMk,
        FunAtZeroMinus.coe_eq_zero_iff_exists]
      exact ⟨η, hη, h⟩
    apply hx
    apply principalComponentDerivAt_injective K α hα
    simpa using hzero
  have hinf : Z.Infinite := by
    intro hfin
    rcases Z.eq_empty_or_nonempty with hempty | hne
    · obtain ⟨ξ, -, hξ2, hξ3⟩ := hcof (-1) (by norm_num)
      exact Set.eq_empty_iff_forall_notMem.mp hempty ξ ⟨hξ2, hξ3⟩
    · obtain ⟨m, hm, hmax⟩ := Set.exists_max_image Z id hfin hne
      obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := hcof m hm.1
      exact absurd (hmax ξ ⟨hξ2, hξ3⟩) (not_le.mpr hξ1)
  obtain ⟨γ, hmono, hrange⟩ := exists_strictMono_range_eq hZpwo hZfin hinf
  have hγZ : ∀ k, γ k ∈ Z := fun k ↦ hrange ▸ Set.mem_range_self k
  refine ⟨γ, hmono, fun k ↦ (hγZ k).1, fun η hη ↦ ?_, fun ξ hξ0 hξ ↦ ?_⟩
  · obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := hcof η hη
    have hξZ : ξ ∈ Z := ⟨hξ2, hξ3⟩
    rw [← hrange] at hξZ
    obtain ⟨k, hk⟩ := hξZ
    exact ⟨k, hk ▸ hξ1⟩
  · have hξZ : ξ ∈ Z := ⟨hξ0, hξ⟩
    rwa [← hrange] at hξZ

end Berarducci
