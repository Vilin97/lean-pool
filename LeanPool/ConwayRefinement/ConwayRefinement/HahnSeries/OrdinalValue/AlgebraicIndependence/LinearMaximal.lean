/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Syzygy
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.UnboundedTruncations
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.LeastTermSup
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

/-!
# A maximal variable occurs linearly when the degree is a limit ordinal

Let `F` be a relation of degree `α`, let `B₀` have maximal degree `δ := deg B₀`, and let `D` be
the degree of `F` in `X_{B₀}`. If `deg H_D ⊕ (δ ⊙ D) = α`, every term of `deg H_D` is at least
`ω^β`, and the nonzero part `δ_{<β}` has last term `ω^e` with `e ≠ 0`, then `D = 1`.

Suppose `D ≥ 2`. Write `α′ := α_{≥β} ⊕ λ₀` with `λ₀ < α_{<β}`. The components of degree at least
`τ` of `pol((∂F/∂X_{B₀})(b_𝓑)^{|γ})` lie in the ideal of the `∂F/∂X_B` over the variables `B` of
`F` with `deg B > δ` (`exists_forall_componentsGE_pol_translatedTruncation_aeval_pderiv_mem`); there
are no such variables, so these components vanish, for any degree `τ` with `α′ ≤ τ ⊕ δ`. Here
`∂F/∂X_{B₀} ≠ 0` (characteristic `0`) is homogeneous of degree `h := deg H_D ⊕ (δ ⊙ (D−1))`, so
`v_J((∂F/∂X_{B₀})(b_𝓑)) = ω^h` by injectivity below `α`, and the cofinality clause of
[Ber00, Lem. 6.8] gives translated truncations of ordinal value `ω^τ` for every `τ < h` — whose
polynomials have a nonzero component of degree `τ`. It remains to find `τ < h` with `α′ ≤ τ ⊕ δ`:
the part of `h` below `β` is `(D−1) ⊙ δ_{<β}`, and some `σ < (D−1) ⊙ δ_{<β}` has
`σ ⊕ δ_{<β} > λ₀`; take `τ := h_{≥β} ⊕ σ`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace NatOrdinal

/-- A natural ordinal whose Cantor normal form has last term `ω^e` with `e ≠ 0` is a limit. -/
theorem constantCoeff_eq_zero_of_leastTerm_eq_wpow {a e : NatOrdinal} (he : e ≠ 0)
    (ha : leastTerm a = ω^ e) : a.constantCoeff = 0 := by
  by_contra h
  have := leastTerm_eq_one_of_constantCoeff_pos (pos_iff_ne_zero.mpr h)
  rw [ha, ← wpow_zero, wpow_inj] at this
  exact he this

theorem ne_zero_of_leastTerm_eq_wpow {a e : NatOrdinal} (ha : leastTerm a = ω^ e) : a ≠ 0 := by
  rintro rfl
  rw [leastTerm_zero] at ha
  exact (wpow_pos e).ne ha

end NatOrdinal

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} {wt : ι → NatOrdinal}

variable {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β) (hσ : σ.IsPrincipal)
include hx hinj hσ

/-- **A maximal variable occurs linearly.** Let `F` be a relation of degree `α` in
variables of degree `< α`, `B₀` a variable of `F` of maximal degree, `degHD ⊕ (D • wt B₀) = α` with
`D` the degree of `F` in `X_{B₀}`, every term of `degHD` at least `ω^β`, the part of `wt B₀` below
`β` with last term `ω^e`, `e ≠ 0`, and `lam₀ < α_{<β}`. If the translated truncations of `F(b_𝓑)`
have ordinal value below `ω^{α₁}` for all `γ < 0` sufficiently close to `0`, with
`α₁ ≤ α_{≥β} ⊕ lam₀` and `α₁ ≤ α`, and every term of the expansion of a monomial of `F` with at
least two translated truncations has degree below `α_{≥β} ⊕ lam₀`, then `D = 1` (characteristic
`0`). -/
theorem degreeOf_eq_one_of_forall_termDegree_lt [CharZero K] {F : MvPolynomial ι K}
    (hF : IsWeightedHomogeneous wt F α) (hvars : ∀ i ∈ F.vars, wt i < α)
    {B₀ : ι} (hB₀ : B₀ ∈ F.vars) (hmax : ∀ i ∈ F.vars, wt i ≤ wt B₀)
    {degHD : NatOrdinal} (hdegHD : degHD + degreeOf B₀ F • wt B₀ = α)
    {β : NatOrdinal} (hdegHDβ : ∀ t ∈ degHD.val.additivePrincipalTerms, (ω^ β).val ≤ t)
    {e : NatOrdinal} (he : e ≠ 0)
    (ht : NatOrdinal.leastTerm (NatOrdinal.partLT β (wt B₀)) = ω^ e)
    {lam₀ : NatOrdinal} (hlam₀ : lam₀ < NatOrdinal.partLT β α)
    {α₁ : NatOrdinal} (hα₁ : α₁ ≤ NatOrdinal.partGE β α + lam₀) (hα₁α : α₁ ≤ α)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hG : ∀ γ : ℝ, -ε₁ < γ → γ < 0 →
      ordinalValue (translatedTruncation ((aeval σ.lift F : Series K) : K⟦ℝ⟧) γ) < ω^ α₁)
    (hwin : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ →
      ρ < NatOrdinal.partGE β α + lam₀) :
    degreeOf B₀ F = 1 := by
  classical
  set D := degreeOf B₀ F with hDdef
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (mem_vars_iff_degreeOf_ne_zero.mp hB₀)
  by_contra hne
  have hD2 : 2 ≤ D := by omega
  set g := wt B₀ with hgdef
  set t := NatOrdinal.partLT β g with htdef
  have ht0 : t ≠ 0 := NatOrdinal.ne_zero_of_leastTerm_eq_wpow ht
  have hg0 : g ≠ 0 := hx.ne_zero B₀
  -- the part of `α` below `β` is `D • t`, a limit
  have hμ : NatOrdinal.partLT β α = D • t := by
    rw [← hdegHD, NatOrdinal.partLT_add, NatOrdinal.partLT_eq_zero_of_forall_le hdegHDβ,
      zero_add, NatOrdinal.partLT_nsmul]
  have hμcc : (NatOrdinal.partLT β α).constantCoeff = 0 := by
    rw [hμ, NatOrdinal.constantCoeff_nsmul,
      NatOrdinal.constantCoeff_eq_zero_of_leastTerm_eq_wpow he ht, mul_zero]
  -- the degree `h = degHD ⊕ (D-1) • g` of `∂F/∂X_{B₀}`
  set h : NatOrdinal := degHD + (D - 1) • g with hhdef
  have hhg : h + g = α := by
    rw [hhdef, add_assoc, ← succ_nsmul, Nat.sub_add_cancel hD1, hdegHD]
  have hhα : h < α := by
    rw [← hhg]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hg0)
  have hhLT : NatOrdinal.partLT β h = (D - 1) • t := by
    rw [hhdef, NatOrdinal.partLT_add, NatOrdinal.partLT_eq_zero_of_forall_le hdegHDβ,
      zero_add, NatOrdinal.partLT_nsmul]
  set Θ := pderiv B₀ F with hΘdef
  have hΘ : IsWeightedHomogeneous wt Θ h := isWeightedHomogeneous_pderiv wt hF B₀ hhg
  have hΘ0 : Θ ≠ 0 := pderiv_ne_zero_of_mem_vars hB₀
  have hvΘ : ordinalValue (aeval σ.lift Θ) = ω^ h :=
    σ.ordinalValue_aeval_eq_of_injectiveAt (hinj h hhα) hΘ hΘ0
  -- the degree `τ = h_{≥β} ⊕ σ'` with `σ' < (D-1) • t` and `λ₀ + 1 ≤ σ' ⊕ t`
  have hlam : (D - 1) • t ≠ 0 := NatOrdinal.nsmul_ne_zero_of_ne_zero ht0 (by omega)
  have hsig : t = 0 ∨ NatOrdinal.leastTerm ((D - 1) • t) ≤ NatOrdinal.leastTerm t :=
    Or.inr (le_of_eq (NatOrdinal.leastTerm_nsmul ht0 (by omega)))
  have htau : lam₀ + 1 < (D - 1) • t + t := by
    rw [← succ_nsmul, Nat.sub_add_cancel hD1, ← hμ]
    refine lt_of_le_of_ne (Order.add_one_le_of_lt hlam₀) fun heq ↦ ?_
    have := congrArg NatOrdinal.constantCoeff heq
    rw [hμcc, show lam₀ + 1 = lam₀ + ((1 : ℕ) : NatOrdinal) by rw [Nat.cast_one],
      NatOrdinal.constantCoeff_add_natCast] at this
    omega
  obtain ⟨σ', hσ'lt, hσ'⟩ := NatOrdinal.exists_lt_le_add_of_lastCantorTerm_le hlam hsig htau
  set τ : NatOrdinal := NatOrdinal.partGE β h + σ' with hτdef
  have hτh : τ < h := by
    conv_rhs => rw [← NatOrdinal.partGE_add_partLT β h]
    rw [hhLT]
    exact add_lt_add_right hσ'lt _
  have hτα'' : NatOrdinal.partGE β α + lam₀ ≤ τ + g := by
    have h1 : τ + g = NatOrdinal.partGE β α + (σ' + t) := by
      rw [← hhg, NatOrdinal.partGE_add, hτdef, htdef]
      conv_lhs => rw [show g = NatOrdinal.partGE β g + NatOrdinal.partLT β g from
        (NatOrdinal.partGE_add_partLT β g).symm]
      abel
    rw [h1]
    exact add_le_add_right ((lt_add_one lam₀).le.trans hσ') _
  -- no variable of `F` has degree above `wt B₀`: the components of degree at least `τ` vanish
  obtain ⟨ε, hε, h2⟩ := σ.exists_forall_componentsGE_pol_translatedTruncation_aeval_pderiv_mem hx
    hinj hσ hF hvars hα₁ hα₁α hε₁ hG hwin B₀ hτα''
  have hempty : IsEmpty {j : ι // j ∈ F.vars ∧ wt B₀ < wt j} :=
    ⟨fun j ↦ absurd j.2.2 (not_lt.mpr (hmax j.1 j.2.1))⟩
  have hzero : ∀ γ : ℝ, -ε < γ → γ < 0 → componentsGE wt τ (σ.pol hx α
      (translatedTruncation ((aeval σ.lift Θ : Series K) : K⟦ℝ⟧) γ)) = 0 := by
    intro γ hγε hγ0
    have := h2 γ hγε hγ0
    rwa [Set.range_eq_empty, Ideal.span_empty, Ideal.mem_bot] at this
  -- a translated truncation of ordinal value exactly `ω^τ` (cofinality clause of [Ber00, Lem. 6.8])
  obtain ⟨γ, hγε, hγ0, hγ⟩ := exists_ordinalValue_translatedTruncation_eq_wpow_of_lt hτh
    (aeval σ.lift Θ) hvΘ (neg_neg_of_pos hε)
  have hlt : ordinalValue (translatedTruncation ((aeval σ.lift Θ : Series K) : K⟦ℝ⟧) γ) < ω^ α := by
    rw [hγ]; exact NatOrdinal.wpow_lt_wpow.mpr (hτh.trans hhα)
  have hnotJ : translatedTruncation ((aeval σ.lift Θ : Series K) : K⟦ℝ⟧) γ ∉
      HahnSeries.Nonpositive.negativeMonomialIdeal K :=
    fun h ↦ NatOrdinal.wpow_ne_zero τ (hγ ▸ ordinalValue_eq_zero_iff.mpr h)
  have hdeg := σ.ordinalValue_eq_wpow_weightedTotalDegree_pol hx hinj hlt hnotJ
  rw [hγ, NatOrdinal.wpow_inj] at hdeg
  have hp0 : σ.pol hx α (translatedTruncation ((aeval σ.lift Θ : Series K) : K⟦ℝ⟧) γ) ≠ 0 := by
    intro h
    have := σ.toGerm_aeval_pol hx hlt
    rw [h, map_zero, map_zero, toGerm_apply, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hnotJ this
  have hcomp := weightedHomogeneousComponent_weightedTotalDegree_ne_zero (wt := wt) hp0
  rw [← hdeg, ← weightedHomogeneousComponent_componentsGE_of_le wt le_rfl, hzero γ hγε hγ0,
    map_zero] at hcomp
  exact hcomp rfl

end Lifts

end Berarducci
