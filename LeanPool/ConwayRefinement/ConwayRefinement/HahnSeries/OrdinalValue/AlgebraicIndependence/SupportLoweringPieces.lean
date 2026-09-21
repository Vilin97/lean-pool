/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SuccessorSupportBound
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.CombinedCofactors
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.ProductCondition

/-!
# Lowering the order type of the support below `ω^ρ`, `ρ ≥ τ + 2`, by cutting into pieces

Let the polynomials `q j ∈ K[X]` be homogeneous of degrees `c j` (the degrees `σ_j` of the
generators) with `e j ⊕ c j = ρ` (`e j` the cofactor degrees), `τ + 1 < ρ < α`, and let the
separation condition (n) hold for every `(e j, c j, τ)`: `e j ⊕ θ < τ` for every `θ < c j`.
Assume evaluation injective below `α`. Let `D` be a series whose support has order type below
`ω^(ρ+1)` and whose translated truncations satisfy (p) for `(q_1, …, q_m; τ)`. Suppose
(induction hypothesis) that every series `E` with support of order type below `ω^ρ` whose
translated truncations satisfy (p) admits cofactors `w j`, with supports of order type below
`ω^(e j)`, such that all translated truncations of `E - ∑_j w_j · q_j(b_𝓑)` have ordinal value
below `ω^(τ+1)`.

At each of the finitely many cutoffs `ξ` at which the ordinal value of `D` is at least `ω^ρ`,
take an interval `(ξ - ε, ξ)` containing no such cutoff and the piece `E_ξ` of `D` on
`(ξ - ε, ξ]`, translated to `0`, and cut it into the pieces on `(γ_k, γ_{k+1}]`,
`γ_k := -ε/(k+1)`; each piece has support of order type below `ω^ρ` and translated truncations
satisfying (p), so the induction hypothesis applies; combine the cofactors of the pieces into the
combined cofactors `C^ξ_j` (`CombinedCofactors`). The difference `E_ξ - ∑_j C^ξ_j · q_j(b_𝓑)`
has translated truncations of ordinal value below `ω^(τ+1)` at every cutoff in `(-ε, 0)`, hence
ordinal value below `ω^(τ+2) ≤ ω^ρ`
(`ordinalValue_lt_wpow_add_one_of_forall_translatedTruncation_lt`). Subtracting the terms
`t^ξ C^ξ_j · q_j(b_𝓑)` leaves a series all of whose translated truncations have ordinal value
below `ω^ρ` — so its support has order type below `ω^ρ` — and whose translated truncations still
satisfy (p) (`ProductCondition`).
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial DirectSum OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- A point of the support of the piece of `E` on `(a, b]`, translated to `0`, lies above
`a - b`. -/
theorem lt_of_mem_support_piece {a b : ℝ} {E : K⟦ℝ⟧} {y : ℝ}
    (hy : y ∈ ((piece a b E : Series K) : K⟦ℝ⟧).support) : a - b < y := by
  rw [HahnSeries.mem_support, coeff_piece] at hy
  by_contra h
  rw [not_lt] at h
  exact hy (ite_eq_right fun h' ↦ absurd h'.1 (not_lt.mpr (by linarith)))

/-- The sequence `γ_k := -ε/(k+1)`: strictly increasing, negative, with supremum `0`. -/
theorem strictMono_neg_div_succ {ε : ℝ} (hε : 0 < ε) :
    StrictMono fun k : ℕ ↦ -ε / ((k : ℝ) + 1) := fun k l hkl ↦ by
  simp only
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left hε (by positivity) (by exact_mod_cast Nat.succ_lt_succ hkl)

theorem neg_div_succ_neg {ε : ℝ} (hε : 0 < ε) (k : ℕ) : -ε / ((k : ℝ) + 1) < 0 := by
  rw [neg_div, neg_lt_zero]
  exact div_pos hε (by positivity)

theorem exists_lt_neg_div_succ (ε : ℝ) {η : ℝ} (hη : η < 0) :
    ∃ k : ℕ, η < -ε / ((k : ℝ) + 1) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (ε / -η)
  refine ⟨k, ?_⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hη' : 0 < -η := neg_pos.mpr hη
  rw [div_lt_iff₀ hη'] at hk
  rw [neg_div, lt_neg, div_lt_iff₀ hk1]
  nlinarith

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (principalGrading K) wt x) {α : NatOrdinal}
  (hinj : ∀ β < α, InjectiveAt K wt x β) (hσ : σ.IsPrincipal)
include hinj

/-- The polynomial of a difference. -/
theorem pol_sub {u u' : Series K} (hu : ordinalValue u < ω^ α) (hu' : ordinalValue u' < ω^ α) :
    σ.pol hx α (u - u') = σ.pol hx α u - σ.pol hx α u' := by
  have hneg : ordinalValue (-u') < ω^ α := by rwa [ordinalValue_neg]
  rw [sub_eq_add_neg, σ.pol_add hx hinj hu hneg, sub_eq_add_neg]
  congr 1
  have : (-u' : Series K) = (HahnSeries.Nonpositive.C : K →+* Series K) (-1) * u' := by
    rw [map_neg, map_one, neg_one_mul]
  rw [this, σ.pol_C_mul hx hinj (-1) hu', map_neg, map_one, neg_one_mul]

include hσ

/-- **Support-order reduction by interval decomposition.** Under the stated homogeneous-degree,
separation, and translated-truncation ideal hypotheses, cofactors reduce the support order type
below `ω^ρ` while preserving the translated-truncation ideal condition. -/
@[blueprint "lem:lower-by-pieces"
  (phase := "Limit ordinals in the degree induction")
  (title := "Support-order reduction by interval decomposition")
  (statement := /--
    Let $K$ be a field and let $\mathcal B$ be a minimal homogeneous generating
    system of $\widehat{\mathrm P}$ with principal representatives $b_B$.
    Assume evaluation is injective below $\alpha$. Let $I$ be a finite index
    set, and let $Q_j\in K[X_B:B\in\mathcal B]$ be weighted homogeneous of
    degree $\sigma_j$, for $j\in I$. Let
    $\tau+1<\mu<\alpha$, and suppose
    \[
      \rho_j\oplus\sigma_j=\mu,\qquad
      \rho_j\oplus\theta<\tau\quad(\theta<\sigma_j)
    \]
    for every $j$.

    Let $u\in K((\mathbb R^{\le0}))$ satisfy
    \[
      \operatorname{ot}(\operatorname{supp}(u))<\omega^{\mu+1}
    \]
    and, for every $\xi\le0$,
    \[
      \operatorname{pol}_{<\alpha}(u^{|\xi})_{\ge\tau}
        \in (Q_j:j\in I).
    \]
    Suppose every series $c$ with
    $\operatorname{ot}(\operatorname{supp}(c))<\omega^\mu$ and the same
    high-degree ideal condition admits series $w_j$ such that
    \[
      \operatorname{ot}(\operatorname{supp}(w_j))<\omega^{\rho_j}
    \]
    and
    \[
      v_J\!\left((c-\sum_jw_jQ_j(b_B))^{|\xi}\right)
        <\omega^{\tau+1}\quad(\xi\le0).
    \]
    Then there are series $u_j$ such that
    \[
      \operatorname{ot}(\operatorname{supp}(u_j))<\omega^{\rho_j+1},
    \]
    \[
      \operatorname{ot}\!\left(
        \operatorname{supp}(u-\sum_ju_jQ_j(b_B))\right)<\omega^\mu,
    \]
    and every translated truncation of the remainder satisfies the same
    high-degree ideal condition.
  -/)
  (proof := /--
  By \ref{lem:successor-large-truncations-finite}, only finitely many cutoffs
  $\xi\le0$ have $v_J(u^{|\xi})\ge\omega^\mu$. Around each such cutoff choose
  an interval containing no other large cutoff.
  \ref{lem:window-truncation} transfers the high-degree ideal condition to the
  corresponding interval piece, and
  \ref{cor:small-truncations-small-support} gives support order below
  $\omega^\mu$ for its successive subpieces. Apply the assumed induction
  hypothesis to those subpieces.

  Assemble their cofactors as sums along cutoffs.
  \ref{lem:cutoff-sum-truncation} identifies their translated truncations,
  while \ref{lem:cutoff-sum-support} bounds each local combined cofactor by
  $\omega^{\rho_j}$. This non-strict bound is sufficient: there are only
  finitely many exceptional cutoffs, so the finite sum of their shifted local
  corrections has support order strictly below $\omega^{\rho_j+1}$. The
  contrapositive consequence of
  \ref{lem:truncation-values} bounds the local residual value by
  $\omega^{\tau+2}\le\omega^\mu$, since $\tau+1<\mu$.

  Shift the local corrections back to their exceptional cutoffs and add
  them. The corrections preserve the high-degree ideal
  condition by \ref{lem:term-truncation-condition}. They cancel all large
  cutoffs, so \ref{cor:small-truncations-small-support} gives support order
  below $\omega^\mu$ for the final remainder.
  -/)]
theorem IsPrincipal.exists_supportOrderType_sub_sum_mul_aeval_lt_of_pieces {ι' : Type*}
    [Fintype ι'] {q : ι' → MvPolynomial ι K} {c : ι' → NatOrdinal}
    (hq : ∀ j, IsWeightedHomogeneous wt (q j) (c j)) {τ ρ : NatOrdinal} (hτρ : τ + 1 < ρ)
    (hρα : ρ < α) {e : ι' → NatOrdinal} (he : ∀ j, e j + c j = ρ)
    (hsep : ∀ j, ∀ θ, θ < c j → e j + θ < τ)
    {D : Series K} (hD : (D : K⟦ℝ⟧).supportOrderType < (ω^ (ρ + 1)).val)
    (htrunc : ∀ ξ : ℝ, ξ ≤ 0 →
      componentsGE wt τ (σ.pol hx α (translatedTruncation (D : K⟦ℝ⟧) ξ)) ∈
        Ideal.span (Set.range q))
    (hIH : ∀ E : Series K, (E : K⟦ℝ⟧).supportOrderType < (ω^ ρ).val →
      (∀ ξ : ℝ, ξ ≤ 0 →
        componentsGE wt τ (σ.pol hx α (translatedTruncation (E : K⟦ℝ⟧) ξ)) ∈
          Ideal.span (Set.range q)) →
      ∃ w : ι' → Series K, (∀ j, ((w j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (e j)).val) ∧
        ∀ ξ : ℝ, ξ ≤ 0 → ordinalValue (translatedTruncation
          ((E - ∑ j, w j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) ξ) < ω^ (τ + 1)) :
    ∃ u : ι' → Series K, (∀ j, ((u j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (e j + 1)).val) ∧
      ((D - ∑ j, u j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ ρ).val ∧
      ∀ ζ : ℝ, ζ ≤ 0 → componentsGE wt τ (σ.pol hx α (translatedTruncation
        ((D - ∑ j, u j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) ζ)) ∈ Ideal.span (Set.range q) := by
  classical
  have hwt : ∀ i, wt i ≠ 0 := hx.ne_zero
  have hρ0 : ρ ≠ 0 := (lt_of_le_of_lt zero_le hτρ).ne'
  have hτ2ρ : τ + 1 + 1 ≤ ρ := Order.add_one_le_of_lt hτρ
  have hρα' : ρ + 1 ≤ α := Order.add_one_le_of_lt hρα
  have hDα : ∀ ζ, ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ζ) < ω^ α := fun ζ ↦
    (ordinalValue_translatedTruncation_lt_of_supportOrderType_lt hD ζ).trans_le
      (NatOrdinal.wpow_le_wpow.mpr hρα')
  -- the generators evaluated at the lifts, `q_j(b_𝓑)`
  set qt : ι' → Series K := fun j ↦ aeval σ.lift (q j) with hqtdef
  have hqv : ∀ j, ordinalValue (qt j) < ω^ (c j + 1) := fun j ↦
    (σ.aeval_represents (hq j)).ordinalValue_lt
  have hqcut : ∀ j, ∀ β : ℝ, β < 0 →
      ordinalValue (translatedTruncation (qt j : K⟦ℝ⟧) β) < ω^ (c j) := fun j β hβ ↦
    hσ.ordinalValue_translatedTruncation_aeval_lt hwt (hq j) hβ
  -- the cutoffs at which the ordinal value of `D` is at least `ω^ρ`
  set L : Set ℝ := {ξ | ξ ≤ 0 ∧ ω^ ρ ≤ ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ)} with hLdef
  have hL : L.Finite := finite_setOf_wpow_le_ordinalValue_translatedTruncation D hD
  have hmemL : ∀ ξ, ξ ∈ hL.toFinset ↔
      ξ ≤ 0 ∧ ω^ ρ ≤ ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ) := fun ξ ↦ hL.mem_toFinset
  -- at each of them, combined cofactors lowering the ordinal value of `D^{|ξ}` below `ω^ρ`
  have hpt : ∀ ξ ∈ hL.toFinset, ∃ C : ι' → Series K,
      (∀ j, ((C j : Series K) : K⟦ℝ⟧).supportOrderType ≤ (ω^ (e j)).val) ∧
      (∀ j, ∀ ζ : ℝ, ζ < 0 → ordinalValue (translatedTruncation (C j : K⟦ℝ⟧) ζ) < ω^ (e j)) ∧
      ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ - ∑ j, C j * qt j) < ω^ ρ := by
    intro ξ hξ
    obtain ⟨hξ0, -⟩ := (hmemL ξ).mp hξ
    obtain ⟨ε, hε, hgap⟩ := exists_pos_forall_le_sub_of_finite hL ξ
    have hnolevel : ∀ θ, ξ - ε < θ → θ < ξ →
        ordinalValue (translatedTruncation (D : K⟦ℝ⟧) θ) < ω^ ρ := by
      intro θ h1 h2
      by_contra hge
      rw [not_lt] at hge
      have := hgap θ ⟨by linarith, hge⟩ h2
      linarith
    -- the piece `E` of `D` on `(ξ - ε, ξ]`, translated to `0`
    set E : Series K := piece (ξ - ε) ξ (D : K⟦ℝ⟧) with hEdef
    have hEcut : ∀ θ : ℝ, -ε < θ → θ ≤ 0 →
        translatedTruncation (E : K⟦ℝ⟧) θ - translatedTruncation (D : K⟦ℝ⟧) (ξ + θ) ∈
          Nonpositive.negativeMonomialIdeal K := fun θ h1 h2 ↦
      translatedTruncation_window_sub_mem (ξ - ε) ξ (D : K⟦ℝ⟧) (by linarith) h2
    -- the pieces on `(γ k, γ (k+1)]`
    set γ : ℕ → ℝ := fun k ↦ -ε / ((k : ℝ) + 1) with hγdef
    have hγ : StrictMono γ := strictMono_neg_div_succ hε
    have hneg : ∀ k, γ k < 0 := neg_div_succ_neg hε
    have hcof : ∀ η < (0 : ℝ), ∃ k, η < γ k := fun η hη ↦ exists_lt_neg_div_succ ε hη
    have hγ0 : γ 0 = -ε := by simp [hγdef]
    have hγ0le : ∀ k, -ε ≤ γ k := fun k ↦ hγ0 ▸ hγ.monotone (Nat.zero_le k)
    -- each piece has support of order type below `ω^ρ` and translated truncations satisfying (p)
    have hwin : ∀ k, ∃ w : ι' → Series K,
        (∀ j, ((w j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (e j)).val) ∧
        ∀ θ : ℝ, θ ≤ 0 → ordinalValue (translatedTruncation
          ((piece (γ k) (γ (k + 1)) (E : K⟦ℝ⟧) - ∑ j, w j * qt j : Series K) : K⟦ℝ⟧) θ) <
            ω^ (τ + 1) := by
      intro k
      set Dk : Series K := piece (γ k) (γ (k + 1)) (E : K⟦ℝ⟧) with hDkdef
      have hDkzero : ∀ θ, θ ≤ γ k - γ (k + 1) → translatedTruncation (Dk : K⟦ℝ⟧) θ = 0 :=
        fun θ hθ ↦ translatedTruncation_eq_zero_of_forall_lt fun y hy ↦
          lt_of_le_of_lt hθ (lt_of_mem_support_piece hy)
      have hDkcut : ∀ θ, γ k - γ (k + 1) < θ → θ ≤ 0 →
          translatedTruncation (Dk : K⟦ℝ⟧) θ -
            translatedTruncation (D : K⟦ℝ⟧) (ξ + (γ (k + 1) + θ)) ∈
              Nonpositive.negativeMonomialIdeal K := by
        intro θ h1 h2
        have h3 := translatedTruncation_window_sub_mem (γ k) (γ (k + 1)) (E : K⟦ℝ⟧) h1 h2
        have h4 := hEcut (γ (k + 1) + θ) (by linarith [hγ0le k]) (by linarith [hneg (k + 1)])
        have := add_mem h3 h4
        rwa [sub_add_sub_cancel] at this
      have hin : ∀ θ, γ k - γ (k + 1) < θ → θ ≤ 0 →
          ξ - ε < ξ + (γ (k + 1) + θ) ∧ ξ + (γ (k + 1) + θ) < ξ := fun θ h1 h2 ↦
        ⟨by linarith [hγ0le k], by linarith [hneg (k + 1)]⟩
      have hDkot : (Dk : K⟦ℝ⟧).supportOrderType < (ω^ ρ).val := by
        refine supportOrderType_lt_of_forall_ordinalValue_translatedTruncation_lt Dk hρ0
          fun θ hθ ↦ ?_
        rcases le_or_gt θ (γ k - γ (k + 1)) with h | h
        · rw [hDkzero θ h, ordinalValue_zero]
          exact NatOrdinal.wpow_pos _
        · rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (hDkcut θ h hθ)]
          exact hnolevel _ (hin θ h hθ).1 (hin θ h hθ).2
      have hDkctrl : ∀ θ : ℝ, θ ≤ 0 →
          componentsGE wt τ (σ.pol hx α (translatedTruncation (Dk : K⟦ℝ⟧) θ)) ∈
            Ideal.span (Set.range q) := by
        intro θ hθ
        rcases le_or_gt θ (γ k - γ (k + 1)) with h | h
        · rw [hDkzero θ h, σ.pol_zero hx hinj, componentsGE_zero]
          exact Ideal.zero_mem _
        · have hval : ordinalValue (translatedTruncation (Dk : K⟦ℝ⟧) θ) < ω^ α := by
            rw [ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (hDkcut θ h hθ)]
            exact hDα _
          rw [σ.pol_congr hx hinj hval (toGerm_eq_toGerm_iff.mpr (hDkcut θ h hθ))]
          exact htrunc _ (by linarith [hneg (k + 1)])
      exact hIH Dk hDkot hDkctrl
    choose w hw1 hw2 using hwin
    -- combine the cofactors of the pieces
    refine ⟨fun j ↦ combinedCofactor γ hγ hneg w j,
      fun j ↦ supportOrderType_combinedCofactor_le γ hγ hneg w hw1 j,
      fun j ζ hζ ↦
        ordinalValue_translatedTruncation_combinedCofactor_lt γ hγ hneg hcof w hw1 j hζ, ?_⟩
    have hres : ∀ ζ, -ε < ζ → ζ < 0 → ordinalValue (translatedTruncation
        ((E - ∑ j, combinedCofactor γ hγ hneg w j * qt j : Series K) : K⟦ℝ⟧) ζ) < ω^ (τ + 1) :=
      fun ζ h1 h2 ↦
        ordinalValue_translatedTruncation_sub_sum_combinedCofactor_mul_lt E γ hγ hneg hcof w
        hw1 hqcut hsep (fun k θ _ h2 ↦ hw2 k θ h2) (by rw [hγ0]; exact h1) h2
    have hwhole : ordinalValue (E - ∑ j, combinedCofactor γ hγ hneg w j * qt j) < ω^ (τ + 1 + 1) :=
      ordinalValue_lt_wpow_add_one_of_forall_translatedTruncation_lt (neg_neg_of_pos hε) hres
    have hE0 : translatedTruncation (D : K⟦ℝ⟧) ξ - E ∈ Nonpositive.negativeMonomialIdeal K := by
      have := hEcut 0 (by linarith) le_rfl
      rw [translatedTruncation_zero, add_zero] at this
      rw [← neg_sub]
      exact neg_mem this
    have hsame : ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ -
        ∑ j, combinedCofactor γ hγ hneg w j * qt j) =
          ordinalValue (E - ∑ j, combinedCofactor γ hγ hneg w j * qt j) := by
      apply ordinalValue_eq_of_sub_mem_negativeMonomialIdeal
      rw [sub_sub_sub_cancel_right]
      exact hE0
    rw [hsame]
    exact hwhole.trans_le (NatOrdinal.wpow_le_wpow.mpr hτ2ρ)
  choose! C hC using hpt
  -- the terms `C^ξ_j · q_j(b_𝓑)`: translated truncations of small ordinal value, satisfying (p)
  have hCv : ∀ ξ ∈ hL.toFinset, ∀ j, ordinalValue (C ξ j) < ω^ (e j + 1) := fun ξ hξ j ↦
    (ordinalValue_le_supportOrderType _).trans_lt (by
      rw [← NatOrdinal.of_val (ω^ (e j + 1)), NatOrdinal.of.lt_iff_lt]
      exact ((hC ξ hξ).1 j).trans_lt
        (NatOrdinal.val.lt_iff_lt.mpr (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _))))
  have hblock : ∀ ξ ∈ hL.toFinset, ∀ j, ∀ θ : ℝ,
      ordinalValue (translatedTruncation ((C ξ j * qt j : Series K) : K⟦ℝ⟧) θ) < ω^ (ρ + 1) := by
    intro ξ hξ j θ
    rcases lt_trichotomy θ 0 with h | rfl | h
    · exact (hσ.ordinalValue_translatedTruncation_mul_aeval_lt hwt (hq j) (hCv ξ hξ j)
        ((hC ξ hξ).2.1 j) (he j) ((lt_add_one τ).le.trans hτρ.le) (hsep j) h).trans
        (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one ρ))
    · rw [translatedTruncation_zero, ← he j]
      exact ordinalValue_mul_lt_wpow_add_one (hCv ξ hξ j) (hqv j)
    · rw [ordinalValue_translatedTruncation_eq_zero_of_forall_support_le (s := 0)
        (fun y hy ↦ Nonpositive.support_subset _ hy) h]
      exact NatOrdinal.wpow_pos _
  have hblockρ : ∀ ξ ∈ hL.toFinset, ξ ≠ 0 → ∀ j, ∀ θ : ℝ, θ ≠ 0 →
      ordinalValue (translatedTruncation ((C ξ j * qt j : Series K) : K⟦ℝ⟧) θ) < ω^ ρ := by
    intro ξ hξ _ j θ hθ
    rcases lt_or_gt_of_ne hθ with h | h
    · exact hσ.ordinalValue_translatedTruncation_mul_aeval_lt hwt (hq j) (hCv ξ hξ j)
        ((hC ξ hξ).2.1 j) (he j) ((lt_add_one τ).le.trans hτρ.le) (hsep j) h
    · rw [ordinalValue_translatedTruncation_eq_zero_of_forall_support_le (s := 0)
        (fun y hy ↦ Nonpositive.support_subset _ hy) h]
      exact NatOrdinal.wpow_pos _
  have hblockctrl : ∀ ξ ∈ hL.toFinset, ∀ j, ∀ θ : ℝ,
      componentsGE wt τ (σ.pol hx α (translatedTruncation ((C ξ j * qt j : Series K) : K⟦ℝ⟧) θ))
        ∈ Ideal.span (Set.range q) := by
    intro ξ hξ j θ
    rcases le_or_gt θ 0 with h | h
    · have := σ.componentsGE_pol_translatedTruncation_mul_aeval_mem hx hinj hσ (hq j) (hCv ξ hξ j)
        ((hC ξ hξ).2.1 j) (he j ▸ hρα) (hsep j) h
      exact Ideal.span_mono (by rintro _ ⟨_, rfl⟩; exact ⟨j, rfl⟩) this
    · rw [σ.pol_eq_zero_of_mem hx hinj
        (translatedTruncation_mem_negativeMonomialIdeal_of_forall_support_le (s := 0)
          (fun y hy ↦ Nonpositive.support_subset _ hy) h), componentsGE_zero]
      exact Ideal.zero_mem _
  -- the cofactors and the corrected series
  refine ⟨fun j ↦ ∑ ξ ∈ hL.toFinset, shift ξ (C ξ j), fun j ↦ ?_, ?_⟩
  · refine supportOrderType_sum_lt_wpow _ _ fun ξ hξ ↦ ?_
    rw [supportOrderType_shift ((hmemL ξ).mp hξ).1]
    exact ((hC ξ hξ).1 j).trans_lt (NatOrdinal.val.lt_iff_lt.mpr
      (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)))
  have heq : (D - ∑ j, (∑ ξ ∈ hL.toFinset, shift ξ (C ξ j)) * qt j : Series K) =
      D - ∑ ξ ∈ hL.toFinset, ∑ j, shift ξ (C ξ j * qt j) := by
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ξ hξ ↦ shift_mul ((hmemL ξ).mp hξ).1 _ _
  beta_reduce
  rw [heq]
  have hcut : ∀ ζ : ℝ,
      translatedTruncation
          ((D - ∑ ξ ∈ hL.toFinset, ∑ j, shift ξ (C ξ j * qt j) : Series K) : K⟦ℝ⟧) ζ =
        translatedTruncation (D : K⟦ℝ⟧) ζ - ∑ ξ ∈ hL.toFinset, ∑ j,
          translatedTruncation ((C ξ j * qt j : Series K) : K⟦ℝ⟧) (ζ - ξ) := by
    intro ζ
    rw [← translatedTruncationAddMonoidHom_apply, AddSubgroupClass.coe_sub, map_sub,
      AddSubmonoidClass.coe_finsetSum, map_sum, translatedTruncationAddMonoidHom_apply ζ (D : K⟦ℝ⟧),
      sub_right_inj]
    refine Finset.sum_congr rfl fun ξ hξ ↦ ?_
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [translatedTruncationAddMonoidHom_apply, translatedTruncation_shift ((hmemL ξ).mp hξ).1]
  refine ⟨?_, ?_⟩
  · -- every translated truncation of the corrected series has value below `ω^ρ`
    refine supportOrderType_lt_of_forall_ordinalValue_translatedTruncation_lt _ hρ0 fun ζ hζ ↦ ?_
    rw [hcut ζ]
    have hsmall : ∀ (s : Finset ℝ), (∀ ξ ∈ s, ξ ≠ ζ) → s ⊆ hL.toFinset →
        ordinalValue (∑ ξ ∈ s, ∑ j,
          translatedTruncation ((C ξ j * qt j : Series K) : K⟦ℝ⟧) (ζ - ξ)) < ω^ ρ := fun s hs hsub ↦
      ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) fun ξ hξ ↦
        ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) fun j _ ↦ by
          rcases lt_or_gt_of_ne (hs ξ hξ) with h | h
          · rw [ordinalValue_translatedTruncation_eq_zero_of_forall_support_le (s := 0)
              (fun y hy ↦ Nonpositive.support_subset _ hy) (by linarith)]
            exact NatOrdinal.wpow_pos _
          · exact hσ.ordinalValue_translatedTruncation_mul_aeval_lt hwt (hq j) (hCv ξ (hsub hξ) j)
              ((hC ξ (hsub hξ)).2.1 j) (he j) ((lt_add_one τ).le.trans hτρ.le) (hsep j)
              (by linarith)
    by_cases hζL : ζ ∈ hL.toFinset
    · rw [← Finset.add_sum_erase _ _ hζL, ← sub_sub]
      have h1 := (hC ζ hζL).2.2
      have h2 := hsmall (hL.toFinset.erase ζ) (fun ξ hξ ↦ (Finset.mem_erase.mp hξ).1)
        (Finset.erase_subset _ _)
      have h3 : ∑ j, translatedTruncation ((C ζ j * qt j : Series K) : K⟦ℝ⟧) (ζ - ζ) =
          ∑ j, C ζ j * qt j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [sub_self, translatedTruncation_zero]
      rw [h3, sub_eq_add_neg _ (∑ ξ ∈ _, _)]
      refine (ordinalValue_add_le_max _ _).trans_lt (max_lt h1 ?_)
      rwa [ordinalValue_neg]
    · have h1 : ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ζ) < ω^ ρ := by
        by_contra hge
        rw [not_lt] at hge
        exact hζL ((hmemL ζ).mpr ⟨hζ, hge⟩)
      have h2 := hsmall hL.toFinset (fun ξ hξ hne ↦ hζL (hne ▸ hξ)) subset_rfl
      rw [sub_eq_add_neg]
      refine (ordinalValue_add_le_max _ _).trans_lt (max_lt h1 ?_)
      rwa [ordinalValue_neg]
  · -- the translated truncations of the corrected series still satisfy (p)
    intro ζ hζ
    rw [hcut ζ]
    have hbα : ∀ ξ ∈ hL.toFinset, ∀ j, ordinalValue
        (translatedTruncation ((C ξ j * qt j : Series K) : K⟦ℝ⟧) (ζ - ξ)) < ω^ α :=
      fun ξ hξ j ↦ (hblock ξ hξ j _).trans_le (NatOrdinal.wpow_le_wpow.mpr hρα')
    rw [σ.pol_sub hx hinj (hDα ζ) (ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) fun ξ hξ ↦
        ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) fun j _ ↦ hbα ξ hξ j),
      σ.pol_sum hx hinj _ _ fun ξ hξ ↦ ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _)
        fun j _ ↦ hbα ξ hξ j,
      componentsGE_sub, componentsGE_sum]
    refine Ideal.sub_mem _ (htrunc ζ hζ) (Ideal.sum_mem _ fun ξ hξ ↦ ?_)
    rw [σ.pol_sum hx hinj _ _ fun j _ ↦ hbα ξ hξ j, componentsGE_sum]
    exact Ideal.sum_mem _ fun j _ ↦ hblockctrl ξ hξ j _

end Lifts

end Berarducci
