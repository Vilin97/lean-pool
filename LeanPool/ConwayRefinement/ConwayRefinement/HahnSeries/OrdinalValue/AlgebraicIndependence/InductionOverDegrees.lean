/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.SupportLoweringPieces
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Separation

/-!
# The induction over degrees

Let the polynomials `q j ∈ K[X]` be homogeneous of nonzero degrees `c j` that are limit ordinals
(the degrees
`σ_j` of the generators), let `h = b j ⊕ c j` (`h` the degree `μ` of the series being reduced,
`b j` the cofactor degrees `ρ_j`), and let the degree `τ` satisfy the separation condition (n) for
every `(b j, c j, τ)`: `b j ⊕ θ < τ` for every `θ < c j`. Let `h < α` and assume evaluation
injective below `α`. For every degree `h'` with `τ < h' ≤ h` — then `h' = e j ⊕ c j` with
`e j ≤ b j` (`Separation.lean`) — and every series `D` whose support has order type below
`ω^(h'+1)` and whose translated truncations satisfy (p) for `(q_1, …, q_m; τ)`, there are
cofactors `u j` with supports of order type below `ω^(e j + 1)` such that every translated
truncation of `D - ∑_j u_j · q_j(b_𝓑)` has ordinal value below `ω^(τ+1)`.

The proof is a well-founded induction on `h'`: the order type of the support of `D` is lowered
below `ω^{h'}` in one step when `h' = τ + 1` (the successor-degree bound) and by cutting into
pieces when `h' ≥ τ + 2` (`SupportLoweringPieces`, with the induction hypothesis at the degrees
of the pieces); the result has support of order type below `ω^{h'}`, hence below `ω^(h''+1)` for
some `h'' < h'`, and the induction hypothesis at `h''` finishes (or the bound is already below
`ω^(τ+1)`).
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- The order type of the support of a nonpositive series, as a natural ordinal below `ω^g`, lies
below `ω^(h''+1)` for some `h''` with `h'' + 1 ≤ g`. -/
theorem exists_supportOrderType_lt_wpow_add_one {D : Series K} {g : NatOrdinal} (hg : g ≠ 0)
    (hD : (D : K⟦ℝ⟧).supportOrderType < (ω^ g).val) :
    ∃ h'', h'' + 1 ≤ g ∧ (D : K⟦ℝ⟧).supportOrderType < (ω^ (h'' + 1)).val := by
  have h : NatOrdinal.of (D : K⟦ℝ⟧).supportOrderType < ω^ g := by
    rw [← NatOrdinal.of_val (ω^ g)]
    exact NatOrdinal.of.lt_iff_lt.mpr hD
  obtain ⟨h'', h1, h2⟩ := exists_lt_wpow_add_one_of_lt_wpow hg h
  refine ⟨h'', h1, ?_⟩
  rw [← NatOrdinal.of_val (ω^ (h'' + 1)), NatOrdinal.of.lt_iff_lt] at h2
  exact h2

/-- A series whose support has order type below `ω^(τ+1)` has all translated truncations of value
below `ω^(τ+1)`. -/
theorem ordinalValue_translatedTruncation_lt_of_supportOrderType_lt' {D : Series K}
    {τ : NatOrdinal} (hD : (D : K⟦ℝ⟧).supportOrderType < (ω^ (τ + 1)).val) (ξ : ℝ) :
    ordinalValue (translatedTruncation (D : K⟦ℝ⟧) ξ) < ω^ (τ + 1) :=
  ordinalValue_translatedTruncation_lt_of_supportOrderType_lt hD ξ

variable {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (principalGrading K) wt x) {α : NatOrdinal}
  (hinj : ∀ β < α, InjectiveAt K wt x β) (hσ : σ.IsPrincipal)
include hinj hσ

/-- **Cofactor reduction at intermediate degrees.** For every intermediate degree and compatible
cofactor degrees, the stated translated-truncation ideal condition yields cofactors whose
remainder has translated truncations of ordinal value below `ω^(τ+1)`. -/
@[blueprint "lem:induction-over-degrees"
  (phase := "Limit ordinals in the degree induction")
  (title := "Translated-truncation approximation at intermediate degrees")
  (statement := /--
    Let $K$ be a field and let $\mathcal B$ be a minimal homogeneous generating
    system of $\widehat{\mathrm P}$ with principal representatives $b_B$.
    Assume evaluation is injective below $\alpha$. Let $I$ be a finite index
    set, and let $Q_j\in K[X_B:B\in\mathcal B]$ be weighted homogeneous of
    nonzero degree $\sigma_j$ that is a limit ordinal. Let $\mu<\alpha$, and suppose
    \[
      \rho_j\oplus\sigma_j=\mu,\qquad
      \rho_j\oplus\theta<\tau\quad(\theta<\sigma_j)
    \]
    for every $j$.

    For every $\mu'$ with $\tau<\mu'\le\mu$, every family $(\rho'_j)_{j\in I}$
    satisfying $\rho'_j\oplus\sigma_j=\mu'$, and every series
    $u\in K((\mathbb R^{\le0}))$ such that
    \[
      \operatorname{ot}(\operatorname{supp}(u))<\omega^{\mu'+1}
    \]
    and
    \[
      \operatorname{pol}_{<\alpha}(u^{|\xi})_{\ge\tau}
        \in (Q_j:j\in I)\quad(\xi\le0),
    \]
    there are series $u_j$ with
    \[
      \operatorname{ot}(\operatorname{supp}(u_j))<\omega^{\rho'_j+1}
    \]
    and
    \[
      v_J\!\left((u-\sum_ju_jQ_j(b_B))^{|\xi}\right)
        <\omega^{\tau+1}\quad(\xi\le0).
    \]
  -/)
  (proof := /--
  Use well-founded induction on $\mu'$. By
  \ref{lem:intermediate-ordinal-hessenberg-decomposition}, each
  $\rho'_j\le\rho_j$, so the separation inequalities remain valid; the same
  result supplies cofactor degrees at every smaller degree used below.

  For a series with support order below $\omega^{\mu'}$, choose $\mu''<\mu'$
  such that its support order is below $\omega^{\mu''+1}$. If
  $\mu''\le\tau$, zero cofactors suffice. Otherwise apply the induction
  hypothesis at $\mu''$.

  If $\mu'=\tau+1$, apply \ref{lem:successor-support-lowering}, then convert
  its support bound into the required translated-truncation bound. If
  $\tau+1<\mu'$, apply \ref{lem:lower-by-pieces} to obtain first cofactors
  whose remainder has support order below $\omega^{\mu'}$ and retains the
  high-degree ideal condition. Apply the auxiliary induction hypothesis to
  this remainder and add the two cofactor families. The natural-sum support
  estimate gives the required bounds.
  -/)]
theorem IsPrincipal.exists_forall_ordinalValue_translatedTruncation_sub_sum_mul_aeval_lt
    {ι' : Type*} [Fintype ι'] {q : ι' → MvPolynomial ι K} {c : ι' → NatOrdinal}
    (hq : ∀ j, IsWeightedHomogeneous wt (q j) (c j)) (hc : ∀ j, (c j).constantCoeff = 0)
    (hc0 : ∀ j, c j ≠ 0) {τ h : NatOrdinal} {b : ι' → NatOrdinal} (hb : ∀ j, b j + c j = h)
    (hsep : ∀ j, ∀ θ, θ < c j → b j + θ < τ) (hhα : h < α) :
    ∀ h' : NatOrdinal, τ < h' → h' ≤ h → ∀ e : ι' → NatOrdinal, (∀ j, e j + c j = h') →
      ∀ D : Series K, (D : K⟦ℝ⟧).supportOrderType < (ω^ (h' + 1)).val →
      (∀ ξ : ℝ, ξ ≤ 0 →
        componentsGE wt τ (σ.pol hx α (translatedTruncation (D : K⟦ℝ⟧) ξ)) ∈
          Ideal.span (Set.range q)) →
      ∃ u : ι' → Series K, (∀ j, ((u j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (e j + 1)).val) ∧
        ∀ ξ : ℝ, ξ ≤ 0 → ordinalValue (translatedTruncation
          ((D - ∑ j, u j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) ξ) < ω^ (τ + 1) := by
  classical
  intro h'
  induction h' using WellFoundedLT.induction with
  | _ h' ih =>
  intro hτh' hh'h e he D hD htrunc
  have hh'α : h' < α := hh'h.trans_lt hhα
  -- the cofactor degrees at `h'` are at most those at `h`
  have heb : ∀ j, e j ≤ b j := fun j ↦ by
    obtain ⟨b', hb'b, hb'⟩ := NatOrdinal.exists_le_add_eq_of_forall_add_lt (hc0 j) (hsep j) hτh'
      (hh'h.trans_eq (hb j).symm)
    have : e j = b' := add_right_cancel ((he j).trans hb'.symm)
    rw [this]
    exact hb'b
  have hsep' : ∀ j, ∀ θ, θ < c j → e j + θ < τ := fun j θ hθ ↦
    (add_le_add_left (heb j) θ).trans_lt (hsep j θ hθ)
  -- the induction hypothesis, in the form used when cutting into pieces
  have hIH : ∀ E : Series K, (E : K⟦ℝ⟧).supportOrderType < (ω^ h').val →
      (∀ ξ : ℝ, ξ ≤ 0 →
        componentsGE wt τ (σ.pol hx α (translatedTruncation (E : K⟦ℝ⟧) ξ)) ∈
          Ideal.span (Set.range q)) →
      ∃ w : ι' → Series K, (∀ j, ((w j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (e j)).val) ∧
        ∀ ξ : ℝ, ξ ≤ 0 → ordinalValue (translatedTruncation
          ((E - ∑ j, w j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) ξ) < ω^ (τ + 1) := by
    intro E hE hEctrl
    obtain ⟨h'', hh''1, hE''⟩ := exists_supportOrderType_lt_wpow_add_one
      (lt_of_le_of_lt zero_le hτh').ne' hE
    have hh''h' : h'' < h' := Order.add_one_le_iff.mp hh''1
    rcases le_or_gt h'' τ with hτ'' | hτ''
    · -- the support of `E` is already small
      refine ⟨fun _ ↦ 0, fun j ↦ ?_, fun ξ _ ↦ ?_⟩
      · rw [Subring.coe_zero, supportOrderType_eq_setOrderType]
        simp only [HahnSeries.support_zero]
        rw [(Set.isPWO_empty.orderType_eq_zero).mpr rfl]
        exact Ordinal.opow_pos _ Ordinal.omega0_pos
      · simp only [zero_mul, Finset.sum_const_zero, sub_zero]
        exact (ordinalValue_translatedTruncation_lt_of_supportOrderType_lt hE'' ξ).trans_le
          (NatOrdinal.wpow_le_wpow.mpr (add_le_add_left hτ'' 1))
    · -- the induction hypothesis at `h''`
      have he'' : ∀ j, ∃ e'', e'' + c j = h'' := fun j ↦ by
        obtain ⟨b', -, hb'⟩ := NatOrdinal.exists_le_add_eq_of_forall_add_lt (hc0 j) (hsep j) hτ''
          ((hh''h'.le.trans hh'h).trans_eq (hb j).symm)
        exact ⟨b', hb'⟩
      choose e'' he'' using he''
      obtain ⟨w, hw1, hw2⟩ := ih h'' hh''h' hτ'' (hh''h'.le.trans hh'h) e'' he'' E hE'' hEctrl
      refine ⟨w, fun j ↦ (hw1 j).trans_le (NatOrdinal.val.le_iff_le.mpr
        (NatOrdinal.wpow_le_wpow.mpr ?_)), hw2⟩
      -- `e'' j < e j` since `e'' j ⊕ c j = h'' < h' = e j ⊕ c j`
      have : e'' j < e j := by
        have := (he'' j).trans_lt (hh''h'.trans_eq (he j).symm)
        exact lt_of_add_lt_add_right this
      exact Order.add_one_le_of_lt this
  -- lower the order type of the support below `ω^{h'}`
  rcases eq_or_lt_of_le (Order.add_one_le_of_lt hτh') with hsucc | hlt
  · -- `h' = τ + 1`: one step; the result has support of order type below `ω^(τ+1)`
    subst hsucc
    obtain ⟨u₀, hu₀, hD'⟩ := IsPrincipal.exists_supportOrderType_sub_sum_mul_aeval_lt σ hx hinj
      hσ hq hc hh'α he hsep' hD htrunc
    exact ⟨u₀, hu₀, fun ξ _ ↦ ordinalValue_translatedTruncation_lt_of_supportOrderType_lt hD' ξ⟩
  · -- `h' ≥ τ + 2`: cutting into pieces, then the induction hypothesis on the result
    obtain ⟨u₀, hu₀, hD', hD'ctrl⟩ :=
      IsPrincipal.exists_supportOrderType_sub_sum_mul_aeval_lt_of_pieces σ hx hinj hσ hq hlt
        hh'α he hsep' hD htrunc hIH
    obtain ⟨w, hw1, hw2⟩ := hIH _ hD' hD'ctrl
    refine ⟨fun j ↦ u₀ j + w j, fun j ↦ ?_, fun ξ hξ ↦ ?_⟩
    · rw [Subring.coe_add]
      refine (supportOrderType_add_le_naturalAdd _ _).trans_lt ?_
      have h1 : NatOrdinal.of ((u₀ j : Series K) : K⟦ℝ⟧).supportOrderType < ω^ (e j + 1) := by
        rw [← NatOrdinal.of_val (ω^ (e j + 1))]
        exact NatOrdinal.of.lt_iff_lt.mpr (hu₀ j)
      have h2 : NatOrdinal.of ((w j : Series K) : K⟦ℝ⟧).supportOrderType < ω^ (e j + 1) := by
        rw [← NatOrdinal.of_val (ω^ (e j + 1))]
        exact NatOrdinal.of.lt_iff_lt.mpr ((hw1 j).trans (NatOrdinal.val.lt_iff_lt.mpr
          (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _))))
      exact NatOrdinal.val.lt_iff_lt.mpr (NatOrdinal.add_lt_wpow h1 h2)
    · have heq : (D - ∑ j, (u₀ j + w j) * aeval σ.lift (q j) : Series K) =
          (D - ∑ j, u₀ j * aeval σ.lift (q j)) - ∑ j, w j * aeval σ.lift (q j) := by
        simp only [add_mul, Finset.sum_add_distrib]
        ring
      rw [heq]
      exact hw2 ξ hξ

end Lifts

end Berarducci
