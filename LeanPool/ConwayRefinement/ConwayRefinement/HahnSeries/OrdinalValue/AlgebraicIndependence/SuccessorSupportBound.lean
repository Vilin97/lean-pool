/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationsIdeal
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Shift
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.HomogeneousSpan

/-!
# Lowering the order type of the support below `ω^(τ+1)`

Let the polynomials `q j ∈ K[X]` be homogeneous of degrees `c j` (the degrees `σ_j` of the
generators) that are zero or limits, with `b j ⊕ c j = τ + 1` (`b j` the cofactor degrees `ρ_j`),
and let the separation condition (n) hold for every `(b j, c j, τ)`: `b j ⊕ θ < τ` for every
`θ < c j`. Let `τ + 1 < α` and assume evaluation injective below `α`. Let `D` be a series whose
support has order type below `ω^(τ+2)` and whose translated truncations `D^{|ξ}`, `ξ ≤ 0`,
satisfy (p) for `(q_1, …, q_m; τ)`: above the degree `τ`, the polynomial of every translated
truncation of `D` lies in the ideal `(q_1, …, q_m)`.

The cutoffs `ξ` at which the ordinal value of `D` is at least `ω^(τ+1)` are finitely many. At
each of them the class of `D^{|ξ}` in `P_{τ+1}` lies in the ideal `(q_1(𝓑), …, q_m(𝓑))` — ideal
membership of a class from the condition (p) on its translated truncations, in degree `τ + 1`
(`of_principalComponentMk_mem_span_of_forall_componentsGE_mem`) — so
`D^{|ξ} ≡ ∑_j u_{ξj} · q_j(b_𝓑)`
modulo `J_{ω^(τ+1)}` with `u_{ξj}` principal representatives of classes in `P_{b j}`; subtract the
terms `t^ξ u_{ξj} · q_j(b_𝓑)`. Every translated truncation of the result has ordinal value below
`ω^(τ+1)`: at `ξ` the class vanishes, and the other terms contribute translated truncations of
`u_{ξj} · q_j(b_𝓑)` at cutoffs `ζ < 0` (of ordinal value below `ω^(τ+1)`) or elements of `J`; at
every other cutoff `D^{|ζ}` itself has ordinal value below `ω^(τ+1)`. Hence the support of the
result has order type below `ω^(τ+1)`, and the cofactors `∑_ξ t^ξ u_{ξj}` have support of order
type below `ω^(b j + 1)`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial DirectSum OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- **Finiteness of translated truncations above an ordinal-value bound.** The cutoffs `ξ ≤ 0`
at which the ordinal value of `d^{|ξ}` is at least `ω^ρ` are finite when the support of `d` has
order type below `ω^(ρ+1)`. -/
@[blueprint "lem:successor-large-truncations-finite"
  (phase := "Limit ordinals in the degree induction")
  (title := "Finiteness of translated truncations above an ordinal-value bound")
  (statement := /--
    Let $K$ be a field, let $d\in\Kser$, and let $\rho<\omega_1$. If
    \[
      \ot(\supp d)<\omega^{\rho+1},
    \]
    then the set
    \[
      \{\xi\le0:\vJ(\trunc d\xi)\ge\omega^\rho\}
    \]
    is finite.
  -/)
  (proof := /--
  Among negative cutoffs, infinitely many such points would contain a strictly
  increasing sequence. The support in every interval between consecutive
  points would have order type at least $\omega^\rho$, so these disjoint
  successive blocks would force the support at or below $0$ to have order type
  at least $\omega^\rho\cdot\omega=\omega^{\rho+1}$, a contradiction. Adding
  the possible cutoff $0$ preserves finiteness.
  -/)]
theorem finite_setOf_wpow_le_ordinalValue_translatedTruncation {ρ : NatOrdinal} (D : Series K)
    (hD : (D : K⟦ℝ⟧).supportOrderType < (ω^ (ρ + 1)).val) :
    {ξ : ℝ | ξ ≤ 0 ∧ ω^ ρ ≤ ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ)}.Finite := by
  refine ((cutoffsGE_finite_of_supportOrderType_lt D hD).union (Set.finite_singleton 0)).subset
    fun ξ ⟨hξ, h⟩ ↦ ?_
  rcases hξ.lt_or_eq with hlt | rfl
  · exact Or.inl (mem_cutoffsGE_iff.mpr ⟨hlt, h⟩)
  · exact Or.inr rfl

/-- Below a point, a finite set of reals leaves a gap. -/
theorem exists_pos_forall_le_sub_of_finite {S : Set ℝ} (hS : S.Finite) (ξ : ℝ) :
    ∃ ε > 0, ∀ ξ' ∈ S, ξ' < ξ → ξ' ≤ ξ - ε := by
  classical
  set T := hS.toFinset.filter (· < ξ) with hTdef
  by_cases hT : T.Nonempty
  · refine ⟨ξ - T.max' hT, ?_, fun ξ' hξ' hlt ↦ ?_⟩
    · have := (Finset.mem_filter.mp (T.max'_mem hT)).2
      linarith
    · have : ξ' ≤ T.max' hT :=
        T.le_max' ξ' (Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hξ', hlt⟩)
      linarith
  · refine ⟨1, one_pos, fun ξ' hξ' hlt ↦ ?_⟩
    exact absurd ⟨ξ', Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hξ', hlt⟩⟩ hT

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (principalGrading K) wt x) {α : NatOrdinal}
  (hinj : ∀ β < α, InjectiveAt K wt x β)
include hinj

/-- **The class of `D^{|ξ}` modulo `J_{ω^(τ+1)}`.** If the translated truncations of `D` satisfy
(p) for `(q_1, …, q_m; τ)` and those at the cutoffs of some interval `(ξ - ε, ξ)`, `ξ ≤ 0`, have
ordinal value below `ω^(τ+1)`, then `D^{|ξ}` is, modulo `J_{ω^(τ+1)}`, a combination
`∑_j w_j · q_j(b_𝓑)` in which each `w j` has ordinal value below `ω^(b j + 1)`, support of order
type at most `ω^(b j)` and translated truncations at cutoffs `ζ < 0` of ordinal value below
`ω^(b j)` (a principal representative of a class in `P_{b j}`, or zero). -/
theorem exists_forall_ordinalValue_translatedTruncation_sub_sum_mul_aeval_lt {ι' : Type*}
    [Fintype ι'] {q : ι' → MvPolynomial ι K} {c : ι' → NatOrdinal}
    (hq : ∀ j, IsWeightedHomogeneous wt (q j) (c j)) (hc : ∀ j, (c j).constantCoeff = 0)
    {τ : NatOrdinal} (hτ : τ + 1 < α) {b : ι' → NatOrdinal} (hb : ∀ j, b j + c j = τ + 1)
    {D : Series K} (hD : (D : K⟦ℝ⟧).supportOrderType < (ω^ (τ + 1 + 1)).val)
    (htrunc : ∀ ξ : ℝ, ξ ≤ 0 →
      componentsGE wt τ (σ.pol hx α (translatedTruncation (D : K⟦ℝ⟧) ξ)) ∈
        Ideal.span (Set.range q))
    {ξ : ℝ} (hξ : ξ ≤ 0) {ε : ℝ} (hε : 0 < ε) (hgap : ∀ δ : ℝ, -ε < δ → δ < 0 →
      ordinalValue (translatedTruncation (D : K⟦ℝ⟧) (ξ + δ)) < ω^ (τ + 1)) :
    ∃ w : ι' → Series K, (∀ j, ((w j : Series K) : K⟦ℝ⟧).supportOrderType ≤ (ω^ (b j)).val) ∧
      (∀ j, ∀ ζ : ℝ, ζ < 0 → ordinalValue (translatedTruncation (w j : K⟦ℝ⟧) ζ) < ω^ (b j)) ∧
      (∀ j, ordinalValue (w j) < ω^ (b j + 1)) ∧
      ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ - ∑ j, w j * aeval σ.lift (q j)) <
        ω^ (τ + 1) := by
  classical
  have hu : ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ) < ω^ (τ + 1 + 1) :=
    ordinalValue_translatedTruncation_lt_of_supportOrderType_lt hD ξ
  -- the class of `D^{|ξ}` lies in the ideal
  have hmem := σ.of_principalComponentMk_mem_span_of_forall_componentsGE_mem hx hinj hq hc hτ hu hε
    (fun δ h1 h2 ↦ by
      rw [translatedTruncation_translatedTruncation _ _ h2.le]
      exact hgap δ h1 h2)
    (fun δ h1 h2 ↦ by
      rw [translatedTruncation_translatedTruncation _ _ h2.le]
      exact htrunc (ξ + δ) (by linarith))
  have hq' : ∀ j, aeval x (q j) ∈ principalGrading K (c j) :=
    fun j ↦ aeval_mem_of_forall_mem hx.mem (hq j)
  obtain ⟨w', hw', -, hsum⟩ := OrdinalGraded.exists_eq_sum_mul_of_mem_span
    (𝒜 := principalGrading K) hq' (of_mem_principalGrading _ _) hmem
  -- principal representatives of the cofactors
  have hrep : ∀ j, ∃ p : Series K, Represents p (b j) (w' j) ∧
      (p : K⟦ℝ⟧).supportOrderType ≤ (ω^ (b j)).val ∧
      ∀ ζ : ℝ, ζ < 0 → ordinalValue (translatedTruncation (p : K⟦ℝ⟧) ζ) < ω^ (b j) :=
    fun j ↦ exists_represents_of_mem_principalGrading (hw' j (b j) (hb j))
  choose w hwrep hwot hwcut using hrep
  refine ⟨w, hwot, hwcut, fun j ↦ (hwrep j).ordinalValue_lt, ?_⟩
  -- both `D^{|ξ}` and `∑_j w_j · q_j(b_𝓑)` represent the same class
  have hrepS : Represents (∑ j, w j * aeval σ.lift (q j)) (τ + 1)
      (∑ j, w' j * aeval x (q j)) :=
    represents_sum _ _ _ _ fun j _ ↦ ((hwrep j).mul (σ.aeval_represents (hq j))).of_eq (hb j)
  have hX : DirectSum.of (PrincipalComponent K) (τ + 1)
      (principalComponentMk (τ + 1) (translatedTruncation (D : K⟦ℝ⟧) ξ) hu) =
        ∑ j, w' j * aeval x (q j) := by
    rw [hsum]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hmk := DirectSum.of_injective (τ + 1) (hX.trans hrepS.of_principalComponentMk.symm)
  exact (principalComponentMk_eq_iff _ _ _ hu hrepS.ordinalValue_lt).mp hmk

variable (hσ : σ.IsPrincipal)
include hσ

/-- **Support-order reduction at a successor degree.** For weighted homogeneous `q j` of degrees
`c j` that are zero or limits, suppose `b j ⊕ c j = τ + 1` and
`b j ⊕ θ < τ` whenever `θ < c j`. If `τ + 1 < α`, the chosen representatives are principal,
the support of `D` has order type below `ω^(τ+2)`, and every translated truncation has its
degree-at-least-`τ` polynomial part in `(q_1, …, q_m)`, then suitable cofactors lower the support
order type of the remainder below `ω^(τ+1)`. -/
@[blueprint "lem:successor-support-lowering"
  (phase := "Limit ordinals in the degree induction")
  (title := "Support-order reduction at a successor degree")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\Ph$, with $x_i\in\Prin_{w_i}$, and choose principal
    series $b_i$ representing the $x_i$. Fix $\alpha<\omega_1$, and assume
    that evaluation at $(x_i)$ is injective in every weighted degree below
    $\alpha$.

    Let $Q_1,\ldots,Q_m\in K[X_i:i\in I]$ be weighted homogeneous of degrees
    $\sigma_1,\ldots,\sigma_m$, each a limit ordinal or $0$. Let
    $\rho_1,\ldots,\rho_m$ and $\tau$ satisfy
    \[
      \rho_j\nsum\sigma_j=\tau+1,\qquad
      \rho_j\nsum\theta<\tau\quad(\theta<\sigma_j),\qquad
      \tau+1<\alpha.
    \]
    Let $d\in\Kser$ satisfy
    $\ot(\supp d)<\omega^{\tau+2}$, and suppose that, for every $\xi\le0$,
    \[
      \partGE{\pol(\trunc d\xi)}{\tau}\in(Q_1,\ldots,Q_m).
    \]
    Then there are $u_1,\ldots,u_m\in\Kser$ such that
    $\ot(\supp u_j)<\omega^{\rho_j+1}$ for every $j$ and
    \[
      \ot\!\left(\supp\left(d-\sum_j u_jQ_j(b_i)\right)\right)
        <\omega^{\tau+1}.
    \]
  -/)
  (proof := /--
  By \ref{lem:successor-large-truncations-finite}, the set $L$ of cutoffs
  $\xi\le0$ for which $\vJ(\trunc d\xi)\ge\omega^{\tau+1}$ is finite. For
  each $\xi\in L$, choose an interval immediately below $\xi$ containing no
  other point of $L$. Applying \ref{lem:lower-below-successor} to
  $\trunc d\xi$ places its class in $\Prin_{\tau+1}$ in the ideal generated
  by the $Q_j(x_i)$. By
  \ref{lem:homogeneous-element-of-generated-ideal}, there are cofactor classes
  of degrees $\rho_j$; choose principal representatives $w_{\xi j}$, shift them
  to $\xi$, and sum over the finite set $L$.

  At a cutoff in $L$, the term placed there cancels its class. At every other
  placement, the translated truncation either lies in $J$, because its cutoff
  is positive, or is a proper translated truncation bounded by
  \ref{lem:principal-representatives-homogeneous-polynomial-truncation} and the
  separation hypothesis. Thus every translated truncation of the remainder
  has ordinal value below $\omega^{\tau+1}$.
  By \ref{cor:small-truncations-small-support}, its support has order type
  below $\omega^{\tau+1}$. Each $u_j$ is a finite sum of shifts of series with
  support order type at most $\omega^{\rho_j}$, so its support has order type
  below $\omega^{\rho_j+1}$.
  -/)]
theorem IsPrincipal.exists_supportOrderType_sub_sum_mul_aeval_lt {ι' : Type*} [Fintype ι']
    {q : ι' → MvPolynomial ι K} {c : ι' → NatOrdinal}
    (hq : ∀ j, IsWeightedHomogeneous wt (q j) (c j)) (hc : ∀ j, (c j).constantCoeff = 0)
    {τ : NatOrdinal} (hτ : τ + 1 < α) {b : ι' → NatOrdinal} (hb : ∀ j, b j + c j = τ + 1)
    (hsep : ∀ j, ∀ θ, θ < c j → b j + θ < τ)
    {D : Series K} (hD : (D : K⟦ℝ⟧).supportOrderType < (ω^ (τ + 1 + 1)).val)
    (htrunc : ∀ ξ : ℝ, ξ ≤ 0 →
      componentsGE wt τ (σ.pol hx α (translatedTruncation (D : K⟦ℝ⟧) ξ)) ∈
        Ideal.span (Set.range q)) :
    ∃ u : ι' → Series K, (∀ j, ((u j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (b j + 1)).val) ∧
      ((D - ∑ j, u j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧).supportOrderType <
        (ω^ (τ + 1)).val := by
  classical
  have hwt : ∀ i, wt i ≠ 0 := hx.ne_zero
  -- the cutoffs at which the ordinal value of `D` is at least `ω^(τ+1)`
  set L : Set ℝ := {ξ | ξ ≤ 0 ∧ ω^ (τ + 1) ≤ ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ)}
    with hLdef
  have hL : L.Finite := finite_setOf_wpow_le_ordinalValue_translatedTruncation D hD
  have hmemL : ∀ ξ, ξ ∈ hL.toFinset ↔
      ξ ≤ 0 ∧ ω^ (τ + 1) ≤ ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ) :=
    fun ξ ↦ hL.mem_toFinset
  -- at each of them, representatives of the cofactors of its class
  have hpt : ∀ ξ ∈ hL.toFinset, ∃ w : ι' → Series K,
      (∀ j, ((w j : Series K) : K⟦ℝ⟧).supportOrderType ≤ (ω^ (b j)).val) ∧
      (∀ j, ∀ ζ : ℝ, ζ < 0 → ordinalValue (translatedTruncation (w j : K⟦ℝ⟧) ζ) < ω^ (b j)) ∧
      (∀ j, ordinalValue (w j) < ω^ (b j + 1)) ∧
      ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ - ∑ j, w j * aeval σ.lift (q j)) <
        ω^ (τ + 1) := by
    intro ξ hξ
    obtain ⟨hξ0, -⟩ := (hmemL ξ).mp hξ
    obtain ⟨ε, hε, hgap⟩ := exists_pos_forall_le_sub_of_finite hL ξ
    refine σ.exists_forall_ordinalValue_translatedTruncation_sub_sum_mul_aeval_lt hx hinj hq hc hτ
      hb hD htrunc hξ0 hε fun δ h1 h2 ↦ ?_
    by_contra hge
    rw [not_lt] at hge
    have : ξ + δ ∈ L := ⟨by linarith, hge⟩
    have := hgap _ this (by linarith)
    linarith
  choose! w hw using hpt
  -- the cofactors
  refine ⟨fun j ↦ ∑ ξ ∈ hL.toFinset, shift ξ (w ξ j), fun j ↦ ?_, ?_⟩
  · refine supportOrderType_sum_lt_wpow _ _ fun ξ hξ ↦ ?_
    rw [supportOrderType_shift ((hmemL ξ).mp hξ).1]
    exact ((hw ξ hξ).1 j).trans_lt (NatOrdinal.val.lt_iff_lt.mpr
      (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)))
  -- the corrected series and its translated truncations
  have heq : (D - ∑ j, (∑ ξ ∈ hL.toFinset, shift ξ (w ξ j)) * aeval σ.lift (q j) : Series K) =
      D - ∑ ξ ∈ hL.toFinset, ∑ j, shift ξ (w ξ j * aeval σ.lift (q j)) := by
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ξ hξ ↦ shift_mul ((hmemL ξ).mp hξ).1 _ _
  beta_reduce
  rw [heq]
  have hcut : ∀ ζ : ℝ,
      translatedTruncation ((D - ∑ ξ ∈ hL.toFinset, ∑ j, shift ξ (w ξ j * aeval σ.lift (q j)) :
          Series K) : K⟦ℝ⟧) ζ =
        translatedTruncation (D : K⟦ℝ⟧) ζ - ∑ ξ ∈ hL.toFinset, ∑ j,
          translatedTruncation ((w ξ j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) (ζ - ξ) := by
    intro ζ
    rw [← translatedTruncationAddMonoidHom_apply, AddSubgroupClass.coe_sub, map_sub,
      AddSubmonoidClass.coe_finsetSum, map_sum, translatedTruncationAddMonoidHom_apply ζ (D : K⟦ℝ⟧),
      sub_right_inj]
    refine Finset.sum_congr rfl fun ξ hξ ↦ ?_
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [translatedTruncationAddMonoidHom_apply, translatedTruncation_shift ((hmemL ξ).mp hξ).1]
  -- every translated truncation of the corrected series has value below `ω^(τ+1)`
  refine supportOrderType_lt_of_forall_ordinalValue_translatedTruncation_lt _
    (lt_of_le_of_lt zero_le (lt_add_one τ)).ne' fun ζ hζ ↦ ?_
  rw [hcut ζ]
  -- the terms placed at cutoffs other than `ζ` have small translated truncations at `ζ`
  have hblock : ∀ ξ ∈ hL.toFinset, ξ ≠ ζ → ∀ j,
      ordinalValue (translatedTruncation ((w ξ j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) (ζ - ξ))
        < ω^ (τ + 1) := by
    intro ξ hξ hne j
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `ζ - ξ > 0`: the translated truncation lies in `J`
      rw [ordinalValue_translatedTruncation_eq_zero_of_forall_support_le (s := 0)
        (fun y hy ↦ Nonpositive.support_subset _ hy) (by linarith)]
      exact NatOrdinal.wpow_pos _
    · -- `ζ - ξ < 0`: a translated truncation of `w_{ξj} · q_j(b_𝓑)` at a cutoff below `0`
      exact hσ.ordinalValue_translatedTruncation_mul_aeval_lt hwt (hq j) ((hw ξ hξ).2.2.1 j)
        ((hw ξ hξ).2.1 j) (hb j) (lt_add_one τ).le (hsep j) (by linarith)
  have hsmall : ∀ (s : Finset ℝ), (∀ ξ ∈ s, ξ ≠ ζ) → s ⊆ hL.toFinset →
      ordinalValue (∑ ξ ∈ s, ∑ j,
        translatedTruncation ((w ξ j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) (ζ - ξ)) <
          ω^ (τ + 1) := fun s hs hsub ↦
    ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) fun ξ hξ ↦
      ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) fun j _ ↦ hblock ξ (hsub hξ) (hs ξ hξ) j
  by_cases hζL : ζ ∈ hL.toFinset
  · -- at a cutoff where the ordinal value of `D` reaches `ω^(τ+1)`: the class vanishes
    rw [← Finset.add_sum_erase _ _ hζL, ← sub_sub]
    have h1 := (hw ζ hζL).2.2.2
    have h2 := hsmall (hL.toFinset.erase ζ) (fun ξ hξ ↦ (Finset.mem_erase.mp hξ).1)
      (Finset.erase_subset _ _)
    have h3 : ∑ j, translatedTruncation ((w ζ j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) (ζ - ζ) =
        ∑ j, w ζ j * aeval σ.lift (q j) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [sub_self, translatedTruncation_zero]
    rw [h3, sub_eq_add_neg _ (∑ ξ ∈ _, _)]
    refine (ordinalValue_add_le_max _ _).trans_lt (max_lt h1 ?_)
    rwa [ordinalValue_neg]
  · -- elsewhere `D^{|ζ}` is small
    have h1 : ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ζ) < ω^ (τ + 1) := by
      by_contra hge
      rw [not_lt] at hge
      exact hζL ((hmemL ζ).mpr ⟨hζ, hge⟩)
    have h2 := hsmall hL.toFinset (fun ξ hξ hne ↦ hζL (hne ▸ hξ)) subset_rfl
    rw [sub_eq_add_neg]
    refine (ordinalValue_add_le_max _ _).trans_lt (max_lt h1 ?_)
    rwa [ordinalValue_neg]

end Lifts

end Berarducci
