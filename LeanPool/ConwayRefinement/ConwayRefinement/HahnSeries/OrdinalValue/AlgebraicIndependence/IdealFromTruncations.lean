/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.InductionOverDegrees
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval

/-!
# Ideal membership of a class from the condition (p) on its translated truncations

Let the polynomials `q j ∈ K[X]` be finitely many homogeneous polynomials of non-zero limit
degrees `c j` (the degrees `σ_j` of the generators), let `h = b j ⊕ c j < α` (`h` the degree `μ`
of the series being reduced, `b j` the cofactor degrees `ρ_j`) and assume evaluation injective
below `α`; let the degree `τ` satisfy `τ + 1 < h` and the separation condition (n) for every
`(b j, c j, τ)`: `b j ⊕ θ < τ` for every `θ < c j`. Let `u` be a series with `v_J(u) = ω^h` whose
translated truncations `u^{|γ}` at the cutoffs `γ` of some interval `(η, 0)` satisfy (p) for
`(q_1, …, q_m; τ)`: above the degree `τ`, the polynomial of every such translated truncation lies
in the ideal `(q_1, …, q_m) ⊆ K[X]`. Then the class of `u` in `P_h` lies in the ideal
`(q_1(𝓑), …, q_m(𝓑)) ⊆ P̂`.

*Proof.* On an interval `(η, 0)` on which `ot(supp u ∩ (γ, 0)) = v_J(u)` for all `γ ∈ [η, 0)`
(Berarducci's remark after [Ber00, Def. 5.2];
`exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue`), every piece of `u` on
`(γ_k, γ_{k+1}]`, translated to `0`, with `γ_k ↑ 0`, has support of order type below `ω^h` and
translated truncations satisfying (p); the induction over degrees (`InductionOverDegrees.lean`)
yields for each piece cofactors such that every translated truncation of the difference has
ordinal value below `ω^(τ+1)`; the combined cofactors (`CombinedCofactors.lean`) are series `C_j`
of ordinal value below `ω^(b j + 1)` with `u - ∑_j C_j · q_j(b_𝓑)` of translated truncations of
ordinal value below `ω^(τ+1)` at every cutoff in `(η, 0)`, whence
`v_J(u - ∑_j C_j · q_j(b_𝓑)) < ω^(τ+2) ≤ ω^h`
(`ordinalValue_lt_wpow_add_one_of_forall_translatedTruncation_lt`): in `P_h`, the class of `u` is
the sum over `j` of the class of `C_j` in `P_{b j}` times `q_j(𝓑)`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial DirectSum OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (principalGrading K) wt x) {α : NatOrdinal}
  (hinj : ∀ β < α, InjectiveAt K wt x β) (hσ : σ.IsPrincipal)
include hinj hσ

/-- **Ideal membership from translated truncations.** If the high-degree components of the
polynomial representatives of the translated truncations of `u` lie in the indicated polynomial
ideal sufficiently close to zero, then the degree-`h` class of `u` lies in the evaluated ideal. -/
@[blueprint "prop:ideal-from-truncations"
  (phase := "Limit ordinals in the degree induction")
  (title := "Ideal membership from translated truncations")
  (statement := /--
    Let $K$ be a field and let $\mathcal B$ be a minimal homogeneous generating
    system of $\widehat{\mathrm P}$ with principal representatives $b_B$.
    Assume evaluation is injective below $\alpha$. Let $I$ be a finite index
    set, and let $Q_j\in K[X_B:B\in\mathcal B]$ be weighted homogeneous of
    nonzero degree $\sigma_j$ that is a limit ordinal. Suppose
    \[
      \rho_j\oplus\sigma_j=\mu<\alpha,\qquad
      \tau+1<\mu,\qquad
      \rho_j\oplus\theta<\tau\quad(\theta<\sigma_j)
    \]
    for every $j$.

    Let $u\in K((\mathbb R^{\le0}))$ have ordinal value
    $v_J(u)=\omega^\mu$. Suppose there is $\eta<0$ such that
    \[
      \operatorname{pol}_{<\alpha}(u^{|\gamma})_{\ge\tau}
        \in (Q_j:j\in I)
    \]
    for every $\eta<\gamma<0$. Then the degree-$\mu$ class
    $u+J_{\omega^\mu}\in\mathrm P_\mu$, embedded in
    $\widehat{\mathrm P}$, lies in
    \[
      (Q_j(\mathcal B):j\in I)\subseteq\widehat{\mathrm P}.
    \]
  -/)
  (proof := /--
  Choose a negative interval on which every support tail of $u$ has order type
  $v_J(u)=\omega^\mu$, and cut that tail along a sequence $\gamma_k\uparrow0$.
  Each interval piece has support order strictly below $\omega^\mu$ and
  inherits the high-degree ideal condition. For a piece whose support degree is
  at most $\tau$, take zero cofactors; otherwise apply
  \ref{lem:induction-over-degrees} at that degree.

  Combine the piecewise cofactors into series $C_j$. Their support bounds give
  $v_J(C_j)<\omega^{\rho_j+1}$, while every translated truncation sufficiently
  close to zero of $u-\sum_jC_jQ_j(b_B)$ has ordinal value below
  $\omega^{\tau+1}$. Consequently the residual series has ordinal value below
  $\omega^{\tau+2}$. Since $\tau+1<\mu$, one has $\tau+2\le\mu$, and hence
  this value is at most $\omega^\mu$. Thus $u$ and
  $\sum_jC_jQ_j(b_B)$ define the same degree-$\mu$ class. Multiplicativity of
  representatives then places this class in $(Q_j(\mathcal B):j\in I)$.
  -/)]
theorem IsPrincipal.of_principalComponentMk_mem_span_of_forall_componentsGE_mem
    {ι' : Type*} [Finite ι'] {q : ι' → MvPolynomial ι K} {c : ι' → NatOrdinal}
    (hq : ∀ j, IsWeightedHomogeneous wt (q j) (c j)) (hc : ∀ j, (c j).constantCoeff = 0)
    (hc0 : ∀ j, c j ≠ 0) {τ h : NatOrdinal} {b : ι' → NatOrdinal} (hb : ∀ j, b j + c j = h)
    (hsep : ∀ j, ∀ θ, θ < c j → b j + θ < τ) (hτh : τ + 1 < h) (hhα : h < α) {u : Series K}
    (hu : ordinalValue u = ω^ h) (hu' : ordinalValue u < ω^ (h + 1)) {η : ℝ} (hη : η < 0)
    (htrunc : ∀ γ : ℝ, η < γ → γ < 0 →
      componentsGE wt τ (σ.pol hx α (translatedTruncation (u : K⟦ℝ⟧) γ)) ∈
        Ideal.span (Set.range q)) :
    DirectSum.of (PrincipalComponent K) h (principalComponentMk h u hu') ∈
      Ideal.span (Set.range fun j ↦ aeval x (q j)) := by
  classical
  cases nonempty_fintype ι'
  have hwt : ∀ i, wt i ≠ 0 := hx.ne_zero
  have h0 : 0 < h := lt_of_le_of_lt zero_le hτh
  have hτ2 : τ + 1 + 1 ≤ h := Order.add_one_le_of_lt hτh
  have hhα' : h ≤ α := hhα.le
  have hqcut : ∀ j, ∀ β : ℝ, β < 0 →
      ordinalValue (translatedTruncation (aeval σ.lift (q j) : K⟦ℝ⟧) β) < ω^ (c j) := fun j β hβ ↦
    hσ.ordinalValue_translatedTruncation_aeval_lt hwt (hq j) hβ
  -- an interval `(η₀, 0)` on which `ot(supp u ∩ (ξ, 0)) = v_J(u) = ω^h` for all `ξ ∈ (η₀, 0)`
  have hone : 1 < ordinalValue u := by
    rw [hu, ← NatOrdinal.wpow_zero]
    exact NatOrdinal.wpow_lt_wpow.mpr h0
  obtain ⟨η₀, hη₀, hstable⟩ :=
    exists_forall_later_negativeSupportTail_orderType_eq_ordinalValue u hone
  set η₁ : ℝ := max η η₀ with hη₁def
  have hη₁ : η₁ < 0 := max_lt hη hη₀
  set ε : ℝ := -η₁ / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- the pieces on `(γ k, γ (k+1)]`
  set γ : ℕ → ℝ := fun k ↦ -ε / ((k : ℝ) + 1) with hγdef
  have hγ : StrictMono γ := strictMono_neg_div_succ hε
  have hneg : ∀ k, γ k < 0 := neg_div_succ_neg hε
  have hcof : ∀ η' < (0 : ℝ), ∃ k, η' < γ k := fun η' hη' ↦ exists_lt_neg_div_succ ε hη'
  have hγ0 : γ 0 = -ε := by simp [hγdef]
  have hγ0gt : η₁ < γ 0 := by rw [hγ0, hεdef]; linarith
  have hγle : ∀ k, γ 0 ≤ γ k := fun k ↦ hγ.monotone (Nat.zero_le k)
  have hηγ : ∀ k, η < γ k := fun k ↦ (le_max_left η η₀).trans_lt (hγ0gt.trans_le (hγle k))
  have hη₀γ : ∀ k, η₀ < γ k := fun k ↦ (le_max_right η η₀).trans_lt (hγ0gt.trans_le (hγle k))
  -- every piece has support of order type below `ω^h`
  have hwinot : ∀ k, ((piece (γ k) (γ (k + 1)) (u : K⟦ℝ⟧) : Series K) : K⟦ℝ⟧).supportOrderType <
      (ω^ h).val := by
    intro k
    -- `T`, the part of `u` on `(γ k, 0)`, has support of order type `ω^h`
    set T : K⟦ℝ⟧ := truncGT (γ k) (truncLT 0 (u : K⟦ℝ⟧)) with hTdef
    have hTsupp : T.support = negativeSupportTail u (γ k) := by
      ext y
      rw [hTdef, support_truncGT, support_truncLT, mem_negativeSupportTail_iff]
      simp only [Set.mem_setOf_eq]
      tauto
    have hTot : T.supportOrderType = (ω^ h).val := by
      rw [supportOrderType_eq_setOrderType, ← hu]
      rw [← hstable (γ k) (hη₀γ k) (hneg k)]
      exact Set.IsPWO.orderType_congr _ _ hTsupp
    -- split `T` at `γ (k+1)`; the part above is nonempty
    have hsplit := supportOrderType_eq_truncLE_add_truncGT (γ (k + 1)) T
    have hhigh : (truncGT (γ (k + 1)) T).supportOrderType ≠ 0 := by
      rw [supportOrderType_eq_setOrderType, Ne, Set.IsPWO.orderType_eq_zero]
      have hne : (negativeSupportTail u (γ (k + 1))).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hemp
        have := hstable (γ (k + 1)) (hη₀γ (k + 1)) (hneg (k + 1))
        rw [Set.IsPWO.orderType_congr _ Set.isPWO_empty hemp,
          (Set.isPWO_empty (α := ℝ)).orderType_eq_zero.mpr rfl, hu] at this
        exact absurd this.symm (ne_of_gt (Ordinal.opow_pos _ Ordinal.omega0_pos))
      obtain ⟨y, hy⟩ := hne
      rw [mem_negativeSupportTail_iff] at hy
      refine Set.nonempty_iff_ne_empty.mp ⟨y, ?_⟩
      rw [support_truncGT, hTdef, support_truncGT, support_truncLT]
      exact ⟨⟨⟨hy.1, hy.2.2⟩, by linarith [hγ (Nat.lt_succ_self k), hy.2.1]⟩, hy.2.1⟩
    have hlow : (truncLE (γ (k + 1)) T).supportOrderType < (ω^ h).val := by
      by_contra hge
      rw [not_lt] at hge
      have : (ω^ h).val < (truncLE (γ (k + 1)) T).supportOrderType +
          (truncGT (γ (k + 1)) T).supportOrderType :=
        lt_of_lt_of_le (lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hhigh)) (add_le_add hge le_rfl)
      rw [← hsplit, hTot] at this
      exact lt_irrefl _ this
    -- the piece is the part of `T` below `γ (k+1)`, translated
    have hset : (truncGT (γ k) (truncLE (γ (k + 1)) (u : K⟦ℝ⟧))).support =
        (truncLE (γ (k + 1)) T).support := by
      ext y
      rw [support_truncGT, support_truncLE, support_truncLE, hTdef, support_truncGT,
        support_truncLT]
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨⟨h1, by linarith [hneg (k + 1)]⟩, h3⟩, h2⟩
      · rintro ⟨⟨⟨h1, -⟩, h3⟩, h2⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    rw [coe_piece, supportOrderType_translate, supportOrderType_eq_setOrderType,
      Set.IsPWO.orderType_congr _ (truncLE (γ (k + 1)) T).isPWO_support hset,
      ← supportOrderType_eq_setOrderType]
    exact hlow
  -- the translated truncations of every piece satisfy (p)
  have hwinctrl : ∀ k, ∀ θ : ℝ, θ ≤ 0 →
      componentsGE wt τ (σ.pol hx α (translatedTruncation
        ((piece (γ k) (γ (k + 1)) (u : K⟦ℝ⟧) : Series K) : K⟦ℝ⟧) θ)) ∈
          Ideal.span (Set.range q) := by
    intro k θ hθ
    rcases le_or_gt θ (γ k - γ (k + 1)) with h | h
    · rw [translatedTruncation_eq_zero_of_forall_lt fun y hy ↦
        lt_of_le_of_lt h (lt_of_mem_support_piece hy), σ.pol_zero hx hinj, componentsGE_zero]
      exact Ideal.zero_mem _
    · have hmem := translatedTruncation_window_sub_mem (γ k) (γ (k + 1)) (u : K⟦ℝ⟧) h hθ
      have hval : ordinalValue (translatedTruncation
          ((piece (γ k) (γ (k + 1)) (u : K⟦ℝ⟧) : Series K) : K⟦ℝ⟧) θ) < ω^ α :=
        (ordinalValue_translatedTruncation_lt_of_supportOrderType_lt (hwinot k) θ).trans_le
          (NatOrdinal.wpow_le_wpow.mpr hhα')
      rw [σ.pol_congr hx hinj hval (toGerm_eq_toGerm_iff.mpr hmem)]
      exact htrunc _ (by linarith [hηγ k]) (by linarith [hneg (k + 1)])
  -- the induction over degrees in every piece
  have hwin : ∀ k, ∃ w : ι' → Series K,
      (∀ j, ((w j : Series K) : K⟦ℝ⟧).supportOrderType < (ω^ (b j)).val) ∧
      ∀ θ : ℝ, θ ≤ 0 → ordinalValue (translatedTruncation
        ((piece (γ k) (γ (k + 1)) (u : K⟦ℝ⟧) - ∑ j, w j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧)
          θ) < ω^ (τ + 1) := by
    intro k
    obtain ⟨hk, hhk1, hDk⟩ := exists_supportOrderType_lt_wpow_add_one h0.ne' (hwinot k)
    have hhkh : hk < h := Order.add_one_le_iff.mp hhk1
    rcases le_or_gt hk τ with hτk | hτk
    · refine ⟨fun _ ↦ 0, fun j ↦ ?_, fun θ _ ↦ ?_⟩
      · rw [Subring.coe_zero, supportOrderType_eq_setOrderType]
        simp only [HahnSeries.support_zero]
        rw [(Set.isPWO_empty.orderType_eq_zero).mpr rfl]
        exact Ordinal.opow_pos _ Ordinal.omega0_pos
      · simp only [zero_mul, Finset.sum_const_zero, sub_zero]
        exact (ordinalValue_translatedTruncation_lt_of_supportOrderType_lt hDk θ).trans_le
          (NatOrdinal.wpow_le_wpow.mpr (add_le_add_left hτk 1))
    · have he : ∀ j, ∃ e, e + c j = hk := fun j ↦ by
        obtain ⟨b', -, hb'⟩ := NatOrdinal.exists_le_add_eq_of_forall_add_lt (hc0 j) (hsep j) hτk
          (hhkh.le.trans_eq (hb j).symm)
        exact ⟨b', hb'⟩
      choose e he using he
      obtain ⟨w, hw1, hw2⟩ :=
        IsPrincipal.exists_forall_ordinalValue_translatedTruncation_sub_sum_mul_aeval_lt
          σ hx hinj hσ hq hc hc0 hb hsep hhα hk hτk hhkh.le e he _ hDk (hwinctrl k)
      refine ⟨w, fun j ↦ (hw1 j).trans_le (NatOrdinal.val.le_iff_le.mpr
        (NatOrdinal.wpow_le_wpow.mpr ?_)), hw2⟩
      have : e j < b j := lt_of_add_lt_add_right ((he j).trans_lt (hhkh.trans_eq (hb j).symm))
      exact Order.add_one_le_of_lt this
  choose w hw1 hw2 using hwin
  -- the combined cofactors
  set C : ι' → Series K := fun j ↦ combinedCofactor γ hγ hneg w j with hCdef
  have hCot : ∀ j, ((C j : Series K) : K⟦ℝ⟧).supportOrderType ≤ (ω^ (b j)).val :=
    fun j ↦ supportOrderType_combinedCofactor_le γ hγ hneg w hw1 j
  have hCv : ∀ j, ordinalValue (C j) < ω^ (b j + 1) := fun j ↦
    (ordinalValue_le_supportOrderType _).trans_lt (by
      rw [← NatOrdinal.of_val (ω^ (b j + 1)), NatOrdinal.of.lt_iff_lt]
      exact (hCot j).trans_lt (NatOrdinal.val.lt_iff_lt.mpr
        (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _))))
  have hres : ∀ ζ, γ 0 < ζ → ζ < 0 → ordinalValue (translatedTruncation
      ((u - ∑ j, C j * aeval σ.lift (q j) : Series K) : K⟦ℝ⟧) ζ) < ω^ (τ + 1) :=
    fun ζ h1 h2 ↦
      ordinalValue_translatedTruncation_sub_sum_combinedCofactor_mul_lt u γ hγ hneg hcof w
      hw1 hqcut hsep (fun k θ _ h2 ↦ hw2 k θ h2) h1 h2
  have hsmall : ordinalValue (u - ∑ j, C j * aeval σ.lift (q j)) < ω^ h :=
    (ordinalValue_lt_wpow_add_one_of_forall_translatedTruncation_lt (hneg 0) hres).trans_le
      (NatOrdinal.wpow_le_wpow.mpr hτ2)
  -- the classes
  have hrepS : Represents (∑ j, C j * aeval σ.lift (q j)) h
      (∑ j, DirectSum.of (PrincipalComponent K) (b j) (principalComponentMk (b j) (C j) (hCv j)) *
        aeval x (q j)) :=
    represents_sum _ _ _ _ fun j _ ↦
      ((represents_iff.mpr ⟨hCv j, rfl⟩).mul (σ.aeval_represents (hq j))).of_eq (hb j)
  have hmk : principalComponentMk h u hu' =
      principalComponentMk h (∑ j, C j * aeval σ.lift (q j)) hrepS.ordinalValue_lt :=
    (principalComponentMk_eq_iff h _ _ hu' hrepS.ordinalValue_lt).mpr hsmall
  rw [hmk, hrepS.of_principalComponentMk]
  exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

end Lifts

end Berarducci
