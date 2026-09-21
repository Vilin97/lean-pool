/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.OrdinalValueCutoffs
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationExpansion

/-!
# Translated truncations of polynomials in principal representatives

Let the lifts `b_B` of the generators be principal series of degree `deg B` (Lean: `σ.lift i`
principal of degree `wt i`, `Lifts.IsPrincipal`). Every translated truncation of a monomial
`X^d(b_𝓑)` at a cutoff `ζ < 0` has ordinal value below `ω^(deg d)`: by the convolution formula
[Ber00, Lem. 7.5], `(X^{d'}(b_𝓑) b_B)^{|ζ}` is congruent modulo `J` to a finite sum of products of
translated truncations, and in every product at least one factor is a translated truncation at a
cutoff `< 0`, whose ordinal value is below `ω^(degree of the factor)` — for `b_B` because it is
principal, for `X^{d'}(b_𝓑)` by induction. Hence, with principal-series representatives,
`v_J(Q(b_𝓑)^{|ζ}) < ω^(deg Q)` for every `ζ < 0` and `Q` homogeneous.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

/-- Below `ω^g` one is below some `ω^(b+1)` with `b + 1 ≤ g`. -/
theorem exists_lt_wpow_add_one_of_lt_wpow {y g : NatOrdinal} (hg : g ≠ 0) (h : y < ω^ g) :
    ∃ b, b + 1 ≤ g ∧ y < ω^ (b + 1) := by
  obtain ⟨z, hz, n, hn⟩ := (NatOrdinal.lt_wpow_iff hg).mp h
  exact ⟨z, Order.add_one_le_of_lt hz, hn.trans (NatOrdinal.wpow_mul_natCast_lt (lt_add_one z) n)⟩

namespace Lifts

/-- The lifts are principal series of the degrees of the generators. -/
def IsPrincipal (σ : Lifts wt x) : Prop :=
  ∀ i, HahnSeries.Nonpositive.IsPrincipal (σ.lift i) ∧
    (σ.lift i : K⟦ℝ⟧).degree = (wt i : WithBot NatOrdinal)

/-- A lift family is principal exactly when each lift is principal of its assigned degree. -/
theorem isPrincipal_iff (σ : Lifts wt x) :
    IsPrincipal σ ↔ ∀ i, HahnSeries.Nonpositive.IsPrincipal (σ.lift i) ∧
      (σ.lift i : K⟦ℝ⟧).degree = (wt i : WithBot NatOrdinal) :=
  Iff.rfl

/-- Principal-series representatives exist for a minimal system of homogeneous generators. -/
theorem exists_isPrincipal
    (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x) :
    ∃ σ : Lifts wt x, σ.IsPrincipal := by
  classical
  have hne : ∀ i, x i ≠ 0 := fun i h0 ↦ by
    have := hx.independent (wt i) (Finsupp.single i 1) (fun j hj ↦ by
      rw [Finsupp.mem_support_single] at hj
      rw [hj.1]) (by rw [Finsupp.linearCombination_single, h0, smul_zero]; exact zero_mem _)
    exact one_ne_zero (Finsupp.single_eq_zero.mp this)
  have h : ∀ i, ∃ p : Series K, Represents p (wt i) (x i) ∧
      HahnSeries.Nonpositive.IsPrincipal p ∧ (p : K⟦ℝ⟧).degree = (wt i : WithBot NatOrdinal) := by
    intro i
    obtain ⟨a, ha⟩ := (DirectSum.mem_rangeLof_iff K _ _ _).mp (hx.mem i)
    rw [DirectSum.lof_eq_of] at ha
    have ha0 : a ≠ 0 := fun h ↦ hne i (by rw [← ha, h, map_zero])
    obtain ⟨p, hp, hprin, hdeg, hpa⟩ := exists_principal_representative_of_ne_zero (wt i) a ha0
    exact ⟨p, represents_iff.mpr ⟨hp, by rw [hpa, ha]⟩, hprin, hdeg⟩
  choose p hp hprin hdeg using h
  exact ⟨⟨p, hp⟩, fun i ↦ ⟨hprin i, hdeg i⟩⟩

variable {σ : Lifts wt x} (hσ : σ.IsPrincipal)
include hσ

/-- A translated truncation of a principal-series representative at a cutoff `ζ < 0` has ordinal
value below `ω^(wt i)`. -/
theorem IsPrincipal.ordinalValue_translatedTruncation_lift_lt (i : ι) {ζ : ℝ} (hζ : ζ < 0) :
    ordinalValue (translatedTruncation (σ.lift i : K⟦ℝ⟧) ζ) < ω^ (wt i) :=
  ordinalValue_translatedTruncation_lt_of_isPrincipal (hσ i).1 (hσ i).2 hζ

omit hσ in
/-- The product of a series of ordinal value below `ω^(a+1)` and one of ordinal value below `ω^g`,
`g ≠ 0`, has ordinal value below `ω^(a ⊕ g)`. -/
theorem ordinalValue_mul_lt_wpow_add {u v : Series K} {a g : NatOrdinal} (hg : g ≠ 0)
    (hu : ordinalValue u < ω^ (a + 1)) (hv : ordinalValue v < ω^ g) :
    ordinalValue (u * v) < ω^ (a + g) := by
  obtain ⟨b, hb, hvb⟩ := exists_lt_wpow_add_one_of_lt_wpow hg hv
  refine (ordinalValue_mul_lt_wpow_add_one hu hvb).trans_le (NatOrdinal.wpow_le_wpow.mpr ?_)
  rw [add_assoc]
  exact add_le_add_right hb a

/-- With principal-series representatives, `v_J((X^d(b_𝓑))^{|ζ}) < ω^(deg d)` for every
cutoff `ζ < 0`. -/
@[blueprint "lem:principal-representatives-truncation"
  (phase := "Translated truncations")
  (title := "Translated truncations of monomials in principal series")
  (statement := /--
    Let $K$ be a field. For each $i\in I$, let
    $x_i\in\mathrm P_{w_i}\subseteq\widehat{\mathrm P}$ and choose a principal
    series $b_i$ of degree $w_i$ representing $x_i$, where $w_i\ne0$. Then,
    for every monomial $X^d$ and every $\zeta<0$,
    \[
      v_J((X^d(b_i))^{|\zeta})<\omega^{\operatorname{wt}(d)}.
    \]
  -/)
  (proof := /--
  Argue by strong induction on the number of factors of $X^d$. The constant
  monomial has zero translated truncation. Otherwise write
  $X^d=X^{d'}X_i$. By \ref{lem:homogeneous-evaluation-represents},
  $X^{d'}(b_i)$ and $b_i$ satisfy the ordinary ordinal-value bounds, and
  \ref{lem:convolution-formula} expresses the translated truncation of their
  product as a finite sum modulo $J$.

  Since $\zeta<0$, each convolution summand contains a proper translated
  truncation. If its first cutoff is negative, the induction hypothesis lowers
  the first factor. At cutoff $0$, the second factor is lowered by
  \ref{lem:principal-truncations-lower-value}. Multiplicativity and strict
  monotonicity of Hessenberg's natural sum put every product below
  $\omega^{\operatorname{wt}(d)}$; the ultrametric inequality gives the same
  bound for the finite sum.
  -/)]
theorem IsPrincipal.ordinalValue_translatedTruncation_aeval_monomial_lt
    (hwt : ∀ i, wt i ≠ 0) (d : ι →₀ ℕ) {ζ : ℝ} (hζ : ζ < 0) :
    ordinalValue (translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) ζ) <
      ω^ (Finsupp.weight wt d) := by
  classical
  suffices h : ∀ n : ℕ, ∀ d : ι →₀ ℕ, Finsupp.degree d = n → ∀ ζ : ℝ, ζ < 0 →
      ordinalValue (translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) ζ)
        < ω^ (Finsupp.weight wt d) from h _ d rfl ζ hζ
  clear hζ ζ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hdn ζ hζ
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [monomial_zero', C_1, map_one]
    have htr : translatedTruncation ((1 : Series K) : K⟦ℝ⟧) ζ = 0 := by
      rw [Subring.coe_one, ← HahnSeries.C_one]
      exact translatedTruncation_C_of_neg 1 hζ
    rw [htr, ordinalValue_zero]
    exact NatOrdinal.wpow_pos _
  · -- peel one occurrence `X_i`
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
    set d' := d - Finsupp.single i 1 with hd'def
    have hdd' : d' + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)
    have hwd : Finsupp.weight wt d' + wt i = Finsupp.weight wt d := by
      rw [← hdd', map_add, Finsupp.weight_single, one_smul]
    have hdeg : Finsupp.degree d' < n := by
      rw [← hdn, ← hdd', map_add, Finsupp.degree_single]
      omega
    set M' : Series K := aeval σ.lift (monomial d' (1 : K)) with hM'def
    have hprod : aeval σ.lift (monomial d (1 : K)) = M' * σ.lift i := by
      rw [← hdd', monomial_add_single_one, map_mul, aeval_X]
    -- the a priori bounds on the factors and their translated truncations
    have hM' : ordinalValue M' < ω^ (Finsupp.weight wt d' + 1) :=
      Berarducci.Represents.ordinalValue_lt
        (σ.aeval_represents (isWeightedHomogeneous_monomial wt d' (1 : K) rfl))
    have hli : ordinalValue (σ.lift i) < ω^ (wt i + 1) :=
      Berarducci.Represents.ordinalValue_lt (σ.represents i)
    have hterm : ∀ β ∈ convolutionIndex (M' : K⟦ℝ⟧) (σ.lift i : K⟦ℝ⟧) ζ,
        ordinalValue (translatedTruncation (M' : K⟦ℝ⟧) β *
          translatedTruncation (σ.lift i : K⟦ℝ⟧) (ζ - β)) < ω^ (Finsupp.weight wt d) := by
      intro β hβ
      obtain ⟨hζβ, hβ0⟩ := mem_Icc_of_mem_convolutionIndex hβ
      rcases lt_or_eq_of_le hβ0 with hβneg | rfl
      · -- the first factor is a translated truncation at the cutoff `β < 0`
        have h1 := ih _ hdeg d' rfl β hβneg
        have h2 : ordinalValue (translatedTruncation (σ.lift i : K⟦ℝ⟧) (ζ - β)) <
            ω^ (wt i + 1) := by
          rcases lt_or_eq_of_le (sub_nonpos.mpr hζβ) with hneg | h0
          · exact (hσ.ordinalValue_translatedTruncation_lift_lt i hneg).trans
              (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _))
          · rw [h0, translatedTruncation_zero]
            exact hli
        rcases eq_or_ne d' 0 with hd'0 | hd'0
        · -- `X^{d'} = 1`: its translated truncation at `β < 0` vanishes
          have h0 : translatedTruncation (M' : K⟦ℝ⟧) β = 0 := by
            rw [hM'def, hd'0, monomial_zero', C_1, map_one, Subring.coe_one, ← HahnSeries.C_one]
            exact translatedTruncation_C_of_neg 1 hβneg
          rw [h0, zero_mul, ordinalValue_zero]
          exact NatOrdinal.wpow_pos _
        · have hw0 : Finsupp.weight wt d' ≠ 0 := by
            obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hd'0
            intro h0
            have := Finsupp.le_weight_of_mem_support wt d' hj
            rw [h0] at this
            exact hwt j (le_antisymm this zero_le)
          have := ordinalValue_mul_lt_wpow_add (u := translatedTruncation (σ.lift i : K⟦ℝ⟧) (ζ - β))
            (v := translatedTruncation ((aeval σ.lift (monomial d' (1 : K)) : Series K) : K⟦ℝ⟧) β)
            (a := wt i) (g := Finsupp.weight wt d') hw0 h2 h1
          rw [mul_comm, add_comm, hwd] at this
          exact this
      · -- `β = 0`: the second factor is a translated truncation at the cutoff `ζ < 0`
        rw [translatedTruncation_zero, sub_zero]
        have := ordinalValue_mul_lt_wpow_add (hwt i) hM'
          (hσ.ordinalValue_translatedTruncation_lift_lt i hζ)
        rwa [hwd] at this
    -- the translated truncation of the product is congruent modulo `J` to the convolution sum
    have hgerm : toGerm (translatedTruncation ((M' * σ.lift i : Series K) : K⟦ℝ⟧) ζ) =
        toGerm (∑ β ∈ convolutionIndex (M' : K⟦ℝ⟧) (σ.lift i : K⟦ℝ⟧) ζ,
          translatedTruncation (M' : K⟦ℝ⟧) β * translatedTruncation (σ.lift i : K⟦ℝ⟧) (ζ - β)) := by
      rw [← germAt_apply, Subring.coe_mul, germAt_mul_of_subset M' (σ.lift i) ζ subset_rfl, map_sum]
      simp only [germAt_apply, map_mul]
    rw [hprod, ordinalValue_eq_of_sub_mem_negativeMonomialIdeal (toGerm_eq_toGerm_iff.mp hgerm)]
    exact ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) hterm

/-- With principal-series representatives, `v_J(q(b_𝓑)^{|ζ}) < ω^c` for `q ∈ K[X]`
homogeneous of degree `c` and every cutoff `ζ < 0`. -/
@[blueprint "lem:principal-representatives-homogeneous-polynomial-truncation"
  (phase := "Translated truncations")
  (title := "Translated truncations of weighted-homogeneous polynomials")
  (statement := /--
    Let $K$ be a field. For each $i\in I$, let
    $x_i\in\mathrm P_{w_i}\subseteq\widehat{\mathrm P}$ and choose a principal
    series $b_i$ of degree $w_i$ representing $x_i$, where $w_i\ne0$. If
    $Q\in K[X_i:i\in I]$ is weighted homogeneous of degree $\sigma$, then, for
    every $\zeta<0$,
    \[
      v_J((Q(b_i))^{|\zeta})<\omega^\sigma.
    \]
  -/)
  (proof := /--
  Expand $Q$ over its finite monomial support. Every occurring monomial has
  weight $\sigma$, so
  \ref{lem:principal-representatives-truncation} bounds the ordinal value of its
  translated truncation by $\omega^\sigma$. Multiplication by its scalar
  coefficient preserves this bound, and the ultrametric inequality gives it
  for the finite sum.
  -/)]
theorem IsPrincipal.ordinalValue_translatedTruncation_aeval_lt (hwt : ∀ i, wt i ≠ 0)
    {q : MvPolynomial ι K} {c : NatOrdinal} (hq : IsWeightedHomogeneous wt q c) {ζ : ℝ}
    (hζ : ζ < 0) :
    ordinalValue (translatedTruncation ((aeval σ.lift q : Series K) : K⟦ℝ⟧) ζ) < ω^ c := by
  classical
  have hsplit : translatedTruncation ((aeval σ.lift q : Series K) : K⟦ℝ⟧) ζ =
      ∑ d ∈ q.support, (HahnSeries.Nonpositive.C : K →+* Series K) (coeff d q) *
        translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) ζ := by
    conv_lhs => rw [q.as_sum, map_sum]
    rw [AddSubmonoidClass.coe_finsetSum, ← translatedTruncationAddMonoidHom_apply, map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    have hmon : monomial d (coeff d q) = C (coeff d q) * monomial d (1 : K) := by
      rw [C_mul_monomial, mul_one]
    rw [translatedTruncationAddMonoidHom_apply, hmon, map_mul, aeval_C,
      HahnSeries.Nonpositive.algebraMap_apply, Subring.coe_mul, HahnSeries.Nonpositive.coe_C,
      translatedTruncation_C_mul]
  rw [hsplit]
  refine ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos _) fun d hd ↦ ?_
  have := hσ.ordinalValue_translatedTruncation_aeval_monomial_lt hwt d hζ
  rw [hq (mem_support_iff.mp hd)] at this
  exact ordinalValue_C_mul_lt _ this

end Lifts

end Berarducci
