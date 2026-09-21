/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.OmegaSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationPolynomial
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.Components
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueFinalSegment
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportSupremum
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ

/-!
# Ordinal-value bounds at translated-truncation cutoffs

For a series `D` and an ordinal `ρ`, consider the cutoffs `ξ < 0` at which the translated
truncation `D^{|ξ}` has ordinal value at least `ω^ρ`. Two
facts drive the induction over degrees by cutting into pieces: a series whose support has order
type below `ω^(ρ+1)` has finitely many cutoffs with `ω^ρ ≤ v_J(D^{|ξ})`
(`cutoffsGE_finite_of_supportOrderType_lt`), and, conversely, a series supported in `(c, 0]` whose
support has order type at least `ω^ρ` has a cutoff `ξ ∈ (c, 0]` with `ω^ρ ≤ v_J(D^{|ξ})`: the
supremum of an initial segment of the support of order type `ω^ρ`.

We also record how the class of a series `u ∈ J_{ω^(β+1)}` in `P_β` is read off its polynomial
when evaluation is injective below `α`: it is `pol(u)_β(𝓑)`, the evaluation of the degree-`β`
component of `pol(u)`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- If the support of `D` has order type at least `ω^ρ` with `ρ ≠ 0`, then at some cutoff `ξ ≤ 0`,
at or above some support point, the ordinal value of `D` is at least `ω^ρ`:
`ω^ρ ≤ v_J(D^{|ξ})`. -/
@[blueprint "lem:cutoff-detects-support-order"
  (phase := "Translated truncations")
  (title := "Detection of support order type by a translated truncation")
  (statement := /--
    Let $K$ be a field, let $b\in K((\mathbb R^{\le0}))$, and let
    $\rho<\omega_1$ be nonzero. If
    \[
      \operatorname{ot}(\operatorname{supp}(b))\ge\omega^\rho,
    \]
    then there are $\xi\le0$ and $y\in\operatorname{supp}(b)$ such that
    $y\le\xi$ and
    \[
      v_J(b^{|\xi})\ge\omega^\rho.
    \]
  -/)
  (proof := /--
  Choose an initial segment $B$ of $\operatorname{supp}(b)$ of order type
  $\omega^\rho$, and let $\xi=\sup B$. Then $\xi\le0$ and lies above every point of the
  nonempty set $B$.

  Since $\rho\ne0$, the ordinal $\omega^\rho$ is additively principal and at least $\omega$.
  For every $\theta<\xi$, the part of $B$ above $\theta$ still has order type
  $\omega^\rho$. At most one of its points is at or above $\xi$, so its part in
  $(\theta,\xi)$ also has order type at least $\omega^\rho$. Thus every support interval
  immediately below $\xi$ has order type at least $\omega^\rho$, which gives
  $v_J(b^{|\xi})\ge\omega^\rho$.
  -/)]
theorem exists_le_wpow_le_ordinalValue_translatedTruncation_of_le_supportOrderType (D : Series K)
    {ρ : NatOrdinal} (hρ : ρ ≠ 0) (hot : (ω^ ρ).val ≤ (D : K⟦ℝ⟧).supportOrderType) :
    ∃ ξ, ξ ≤ 0 ∧ (∃ y ∈ (D : K⟦ℝ⟧).support, y ≤ ξ) ∧
      ω^ ρ ≤ ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ) := by
  classical
  -- an initial segment `S₀` of the support of order type exactly `ω^ρ`
  obtain ⟨D₀, hD₀sub, hD₀ot⟩ : ∃ D₀ : K⟦ℝ⟧, D₀.support ⊆ (D : K⟦ℝ⟧).support ∧
      D₀.supportOrderType = (ω^ ρ).val := by
    rcases hot.lt_or_eq with hlt | heq
    · rw [supportOrderType_eq_setOrderType] at hlt
      obtain ⟨x, _, hx⟩ := Set.IsPWO.exists_orderType_inter_Iio_eq _ hlt
      refine ⟨truncLT x (D : K⟦ℝ⟧), support_truncLT_subset x _, ?_⟩
      rw [supportOrderType_eq_setOrderType]
      rw [← hx]
      apply Set.IsPWO.orderType_congr
      rw [support_truncLT]
      ext y
      simp [and_comm]
    · exact ⟨D, le_rfl, heq.symm⟩
  have hne : D₀.support.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : D₀.supportOrderType = 0 := by
      rw [supportOrderType_eq_setOrderType]
      exact (Set.IsPWO.orderType_eq_zero _).mpr h
    rw [h0] at hD₀ot
    exact absurd hD₀ot.symm (ne_of_gt (Ordinal.opow_pos _ Ordinal.omega0_pos))
  have hbdd : BddAbove D₀.support :=
    ⟨0, fun y hy ↦ HahnSeries.Nonpositive.support_subset D (hD₀sub hy)⟩
  -- `ξ`, the supremum of `S₀`
  set ξ := sSup D₀.support with hξdef
  have hξle : ξ ≤ 0 := csSup_le hne fun y hy ↦ HahnSeries.Nonpositive.support_subset D (hD₀sub hy)
  have hyξ : ∃ y ∈ (D : K⟦ℝ⟧).support, y ≤ ξ := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, hD₀sub hy, le_csSup hbdd hy⟩
  refine ⟨ξ, hξle, hyξ, ?_⟩
  have hprin : Ordinal.IsPrincipal (· + ·) (ω^ ρ).val := by
    rw [NatOrdinal.val_wpow]
    exact Ordinal.isPrincipal_add_omega0_opow _
  have hω : Ordinal.omega0 ≤ (ω^ ρ).val := by
    rw [NatOrdinal.val_wpow]
    exact Ordinal.left_le_opow _ (pos_iff_ne_zero.mpr (by simpa using hρ))
  -- the support on every interval `(θ, ξ)` has order type at least `ω^ρ`
  have htail : ∀ θ, θ < ξ → (ω^ ρ).val ≤ ((D : K⟦ℝ⟧).isPWO_support.mono
      (s := (D : K⟦ℝ⟧).support ∩ Set.Ioo θ ξ) Set.inter_subset_left).orderType := by
    intro θ hθ
    -- the part of `S₀` above `θ` has order type `ω^ρ`
    have hsplit := supportOrderType_eq_truncLE_add_truncGT θ D₀
    rw [hD₀ot] at hsplit
    obtain ⟨y, hy, hθy⟩ := exists_lt_of_lt_csSup hne hθ
    have hpos : (truncGT θ D₀).supportOrderType ≠ 0 := by
      rw [supportOrderType_eq_setOrderType, Ne, Set.IsPWO.orderType_eq_zero, support_truncGT]
      exact Set.nonempty_iff_ne_empty.mp ⟨y, hy, hθy⟩
    have hlow : (truncLE θ D₀).supportOrderType < (ω^ ρ).val := by
      by_contra hge
      rw [not_lt] at hge
      have : (ω^ ρ).val < (truncLE θ D₀).supportOrderType + (truncGT θ D₀).supportOrderType :=
        lt_of_lt_of_le (lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hpos))
          (add_le_add hge le_rfl)
      rw [← hsplit] at this
      exact lt_irrefl _ this
    have hhigh : (truncGT θ D₀).supportOrderType = (ω^ ρ).val := by
      refine le_antisymm (by rw [hsplit]; exact le_add_self) (le_of_not_gt fun hlt ↦ ?_)
      have := hprin hlow hlt
      beta_reduce at this
      rw [← hsplit] at this
      exact lt_irrefl _ this
    -- split the part above `θ` at `ξ`: at most one point is at or above `ξ`
    set E := truncGT θ D₀ with hEdef
    have hsplitE := supportOrderType_eq_truncLT_add_truncGE ξ E
    rw [hhigh] at hsplitE
    have hfin : (truncGE ξ E).supportOrderType < Ordinal.omega0 := by
      rw [supportOrderType_eq_setOrderType, ← Set.IsPWO.finite_iff_orderType_lt_omega]
      refine (Set.finite_singleton ξ).subset fun z hz ↦ ?_
      rw [support_truncGE] at hz
      have hzξ : z ≤ ξ := le_csSup hbdd (support_truncGT_subset θ _ hz.1)
      exact le_antisymm hzξ hz.2
    have hA : (ω^ ρ).val ≤ (truncLT ξ E).supportOrderType := by
      by_contra hlt
      rw [not_le] at hlt
      have := hprin hlt (hfin.trans_le hω)
      beta_reduce at this
      rw [← hsplitE] at this
      exact lt_irrefl _ this
    refine hA.trans ?_
    rw [supportOrderType_eq_setOrderType]
    refine Set.IsPWO.orderType_mono _ _ fun z hz ↦ ?_
    rw [support_truncLT, hEdef, support_truncGT] at hz
    exact ⟨hD₀sub hz.1.1, hz.1.2, hz.2⟩
  have := le_ordinalValue_translatedTruncation_of_forall_le_orderType (D : K⟦ℝ⟧) ξ htail
  rwa [NatOrdinal.of_val] at this

/-- For a series supported in `(c, 0]` whose support has order type at least `ω^ρ`, `ρ ≠ 0`, there
is a cutoff `ξ ∈ (c, 0]` with `ω^ρ ≤ v_J(D^{|ξ})`. -/
@[blueprint "lem:cutoff-detects-support-order-in-interval"
  (phase := "Translated truncations")
  (title := "Detection of interval support order type by a translated truncation")
  (statement := /--
    Let $K$ be a field, let $b\in K((\mathbb R^{\le0}))$, let $c\in\mathbb R$,
    and let $\rho<\omega_1$ be nonzero. If
    \[
      \operatorname{supp}(b)\subseteq(c,0],\qquad
      \operatorname{ot}(\operatorname{supp}(b))\ge\omega^\rho,
    \]
    then there is $\xi\in(c,0]$ such that
    $v_J(b^{|\xi})\ge\omega^\rho$.
  -/)
  (proof := /--
  Apply \ref{lem:cutoff-detects-support-order}. Its cutoff $\xi$ lies above a point
  $y\in\operatorname{supp}(b)$. Since $c<y\le\xi\le0$, the same cutoff belongs to
  $(c,0]$.
  -/)]
theorem exists_wpow_le_ordinalValue_translatedTruncation_of_le_supportOrderType (D : Series K)
    {c : ℝ} (hD : (D : K⟦ℝ⟧).support ⊆ Set.Ioc c 0) {ρ : NatOrdinal} (hρ : ρ ≠ 0)
    (hot : (ω^ ρ).val ≤ (D : K⟦ℝ⟧).supportOrderType) :
    ∃ ξ, c < ξ ∧ ξ ≤ 0 ∧ ω^ ρ ≤ ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ) := by
  obtain ⟨ξ, hξ0, ⟨y, hy, hyξ⟩, hξ⟩ :=
    exists_le_wpow_le_ordinalValue_translatedTruncation_of_le_supportOrderType D hρ hot
  exact ⟨ξ, (hD hy).1.trans_le hyξ, hξ0, hξ⟩

/-- If the translated truncation of `D` at every cutoff `ξ ≤ 0` has ordinal value below `ω^ρ`,
`ρ ≠ 0`, the support of `D` has order type below `ω^ρ`. -/
@[blueprint "cor:small-truncations-small-support"
  (phase := "Translated truncations")
  (title := "Support-order bound from uniformly small translated truncations")
  (statement := /--
    Let $K$ be a field, let $b\in K((\mathbb R^{\le0}))$, and let
    $\rho<\omega_1$ be nonzero. If
    \[
      v_J(b^{|\xi})<\omega^\rho\qquad\text{for every }\xi\le0,
    \]
    then
    \[
      \operatorname{ot}(\operatorname{supp}(b))<\omega^\rho.
    \]
  -/)
  (proof := /--
  Otherwise \ref{lem:cutoff-detects-support-order} supplies some $\xi\le0$ with
  $v_J(b^{|\xi})\ge\omega^\rho$, contradicting the hypothesis.
  -/)]
theorem supportOrderType_lt_of_forall_ordinalValue_translatedTruncation_lt (D : Series K)
    {ρ : NatOrdinal} (hρ : ρ ≠ 0)
    (h : ∀ ξ, ξ ≤ 0 → ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ) < ω^ ρ) :
    (D : K⟦ℝ⟧).supportOrderType < (ω^ ρ).val := by
  by_contra hge
  rw [not_lt] at hge
  obtain ⟨ξ, hξ0, -, hξ⟩ :=
    exists_le_wpow_le_ordinalValue_translatedTruncation_of_le_supportOrderType D hρ hge
  exact absurd (h ξ hξ0) (not_lt.mpr hξ)

/-! ### Translated truncations of a principal series -/

/-- For `p` principal of degree `g` and every cutoff `ζ < 0`, `v_J(p^{|ζ}) < ω^g`: the translated
truncations of a principal series at cutoffs `ζ < 0` have ordinal value below `ω^(deg p)`. -/
@[blueprint "lem:principal-truncations-lower-value"
  (phase := "Translated truncations")
  (title := "Ordinal-value bound for proper translated truncations of a principal series")
  (statement := /--
    Let $K$ be a field and let $b\in K((\mathbb R^{\le0}))$ be a principal
    series of degree $\sigma<\omega_1$. For every $\zeta<0$,
    \[
      v_J(b^{|\zeta})<\omega^\sigma.
    \]
  -/)
  (proof := /--
  The support of $b$ has order type $\omega^\sigma$ and supremum $0$. Choose
  $y\in\operatorname{supp}(b)$ with $\zeta<y<0$. The support of the truncation
  $b_{|\zeta}$ embeds in the proper initial segment
  $\operatorname{supp}(b)\cap(-\infty,y)$, so its order type is strictly below
  $\omega^\sigma$. Translation preserves order type, and the ordinal value of
  a series is at most the order type of its support. Hence
  $v_J(b^{|\zeta})<\omega^\sigma$.
  -/)]
theorem ordinalValue_translatedTruncation_lt_of_isPrincipal {p : Series K}
    (hp : HahnSeries.Nonpositive.IsPrincipal p) {g : NatOrdinal}
    (hdeg : (p : K⟦ℝ⟧).degree = (g : WithBot NatOrdinal)) {ζ : ℝ} (hζ : ζ < 0) :
    ordinalValue (translatedTruncation (p : K⟦ℝ⟧) ζ) < ω^ g := by
  classical
  have hot := hp.supportOrderType_eq_wpow_of_degree_eq hdeg
  -- an element of the support above `ζ`
  have hlub : IsLUB (p : K⟦ℝ⟧).support 0 :=
    (HahnSeries.Nonpositive.supportSup_eq_coe_iff.mp hp.supportSup_eq_zero).2
  obtain ⟨y, hy, hζy, _⟩ := hlub.exists_between hζ
  -- the translated truncation is the translate of the part of `p` below `ζ`, of order type
  -- below `ω^g`
  let r : Series K := ⟨translate (-ζ) (truncLE ζ (p : K⟦ℝ⟧)), by
    rw [mem_nonpositiveSubring]
    intro x hx
    rw [support_translate] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hz' : z ≤ ζ := by
      rw [support_truncLE] at hz
      exact hz.2
    change -ζ + z ≤ 0
    linarith⟩
  have hr : translatedTruncation (p : K⟦ℝ⟧) ζ = r := by
    apply Subtype.ext
    ext δ
    rw [coeff_translatedTruncation]
    change _ = (translate (-ζ) (truncLE ζ (p : K⟦ℝ⟧))).coeff δ
    rw [coeff_translate, sub_neg_eq_add, HahnSeries.coeff_truncLE]
    split_ifs with h1 h2 h2
    · rw [add_comm]
    · exact absurd (by linarith : δ + ζ ≤ ζ) h2
    · exact absurd (by linarith : δ ≤ 0) h1
    · rfl
  rw [hr]
  calc ordinalValue r ≤ NatOrdinal.of (r : K⟦ℝ⟧).supportOrderType :=
        ordinalValue_le_supportOrderType r
    _ = NatOrdinal.of (truncLE ζ (p : K⟦ℝ⟧)).supportOrderType := by
        change NatOrdinal.of (translate (-ζ) (truncLE ζ (p : K⟦ℝ⟧))).supportOrderType = _
        rw [supportOrderType_translate]
    _ < ω^ g := by
        rw [← NatOrdinal.of_val (ω^ g), ← hot, supportOrderType_eq_setOrderType,
          supportOrderType_eq_setOrderType]
        refine NatOrdinal.of.lt_iff_lt.mpr ?_
        refine lt_of_le_of_lt (Set.IsPWO.orderType_mono _ _ ?_)
          (Set.IsPWO.orderType_inter_Iio_lt (p : K⟦ℝ⟧).isPWO_support hy)
        rw [support_truncLE]
        exact fun z hz ↦ ⟨hz.1, hz.2.trans_lt hζy⟩

/-! ### The class of a series read off its polynomial -/

/-- A series of ordinal value below `ω^β` represents `0` in `P_β`. -/
theorem represents_zero_of_ordinalValue_lt {u : Series K} {β : NatOrdinal}
    (hu : ordinalValue u < ω^ β) : Represents u β 0 :=
  represents_iff.mpr ⟨hu.trans (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one β)), by
    rw [(principalComponentMk_eq_zero_iff β u _).mpr hu, map_zero]⟩

/-- Representing is a property of the class modulo `J`. -/
theorem Represents.congr {u u' : Series K} {β : NatOrdinal} {e : PrincipalSubring K}
    (h : Represents u β e) (huu' : toGerm u = toGerm u') : Represents u' β e := by
  obtain ⟨hu, rfl⟩ := represents_iff.mp h
  have hval := ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp huu')
  refine represents_iff.mpr ⟨hval ▸ hu, ?_⟩
  congr 1
  rw [principalComponentMk_eq_iff,
    ordinalValue_eq_zero_iff.mpr (toGerm_eq_toGerm_iff.mp huu'.symm)]
  exact NatOrdinal.wpow_pos β

/-- The class represented is determined. -/
theorem Represents.of_principalComponentMk' {u : Series K} {β : NatOrdinal} {e : PrincipalSubring K}
    (h : Represents u β e) (hu : ordinalValue u < ω^ (β + 1)) :
    DirectSum.of (PrincipalComponent K) β (principalComponentMk β u hu) = e :=
  (represents_iff.mp h).2

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
include hinj

/-- **The class of a series from its polynomial.** When evaluation is injective below `α`, a series
`u ∈ J_{ω^(β+1)}` with `β < α` represents in `P_β` the evaluation `pol(u)_β(𝓑)` of the degree-`β`
component of its polynomial modulo `J`. -/
@[blueprint "lem:polynomial-homogeneous-component-represents-class"
  (phase := "Translated truncations")
  (title := "Homogeneous component representing a class in $\\mathrm P_\\beta$")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$ with
    $x_i\in\mathrm P_{w_i}$, and choose representatives
    $b_i\in K((\mathbb R^{\le0}))$. Fix $\alpha<\omega_1$, and suppose that
    evaluation at $(x_i)$ is injective on weighted-homogeneous polynomials of
    every degree below $\alpha$.

    For $v_J(u)<\omega^\alpha$, let $P_u$ be the unique polynomial whose
    monomials have weight below $\alpha$ and for which
    $P_u(b_i)\equiv u\pmod J$. If $\beta<\alpha$ and
    $v_J(u)<\omega^{\beta+1}$, then the weighted-homogeneous component
    $(P_u)_\beta$ satisfies
    \[
      (P_u)_\beta(x_i)=u+J_{\omega^\beta}\quad\text{in }\mathrm P_\beta.
    \]
  -/)
  (proof := /--
  By \ref{prop:polynomial-representative-exists}, choose $P_u$; then
  \ref{prop:polynomial-evaluation-ordinal-value} makes it unique.
  Applying \ref{prop:polynomial-representative-exists} at $\beta+1$ and using
  this uniqueness shows
  that every monomial of $P_u$ has weight below $\beta+1$. Therefore evaluation
  of its degree-$\beta$ weighted-homogeneous component at $(b_i)$ represents
  the degree-$\beta$ class of $P_u(b_i)$. Finally
  $P_u(b_i)\equiv u\pmod J$, so the same component represents the class of $u$.
  -/)]
theorem represents_aeval_weightedHomogeneousComponent_pol {u : Series K} {β : NatOrdinal}
    (hβ : β < α) (hu : ordinalValue u < ω^ (β + 1)) :
    Represents u β (aeval x (weightedHomogeneousComponent wt β (σ.pol hx α u))) := by
  classical
  have hβ1 : β + 1 ≤ α := Order.add_one_le_of_lt hβ
  have huα : ordinalValue u < ω^ α := hu.trans_le (NatOrdinal.wpow_le_wpow.mpr hβ1)
  set P := σ.pol hx α u with hPdef
  have hP : DegreeLT wt P (β + 1) := σ.pol_degreeLT_of_lt hx hinj hβ1 hu
  have h3 : Represents (aeval σ.lift P) β
      (aeval x (weightedHomogeneousComponent wt β P)) :=
    (ordinalValueDegreeValuation K).represents_aeval_weightedHomogeneousComponent
      represents_C σ.represents
      fun d hd ↦ Order.lt_add_one_iff.mp ((degreeLT_iff.mp hP) d hd)
  exact h3.congr (σ.toGerm_aeval_pol hx huα)

end Lifts

end Berarducci
