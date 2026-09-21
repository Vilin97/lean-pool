/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.RemainderBound
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.MapWeight
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Split
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.PairBounds

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The contradiction when the degree is a limit ordinal

The limit step of the injectivity induction ends in a purely polynomial argument, and this file
isolates it from the analysis that supplies its hypotheses.

Fix ordinal degrees `wt` for the variables, a cutoff exponent `β`, and write `a_{<β}` for the part
of `a` below `ω^β` (Lean `NatOrdinal.partLT β a`). Let `F` be homogeneous of degree `α`, let `B₀`
be a variable occurring in `F` to degree at most one with `(wt B₀)_{<β} = α_{<β}`, and set
`H := ∂F/∂X_{B₀}`.

Then every variable of `H` has vanishing part below `ω^β`
(`partLT_eq_zero_of_mem_vars_pderiv`), because the parts below `ω^β` of a monomial of `F` add up
to `α_{<β}`, all of which is already used by the single occurrence of `X_{B₀}`. In characteristic
zero this makes the classification of variables by their parts below `ω^β` cut `H` off from every
variable with a nonzero part: `pderiv_eq_zero_of_partLT_ne_zero`.

The contradiction (`false_of_pderiv_eq_sum_of_partLT_ne_zero`) follows: some variable `B'` of `H`
has `∂H/∂X_{B'} ≠ 0`, and `B'` has vanishing part below `ω^β`. Hence
`0 + lam₀ = lam₀`, so the assumed derivative identity applies at `B'`. It writes
`∂F/∂X_{B'} = ∑_B (∂F/∂X_B) U_B` over variables `B` with nonzero part below `ω^β` and with
`∂U_B/∂X_{B₀} = 0`. Differentiating in `X_{B₀}` sends the left side to `∂H/∂X_{B'}` and kills
every summand on the right.
-/

universe u v

open scoped NatOrdinal

public noncomputable section

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommRing R] {wt : σ → NatOrdinal}

/-- **Variables of `∂F/∂X_{B₀}` have vanishing part below `ω^β`.** In every monomial of a
homogeneous `F` the parts below `ω^β` add up to `α_{<β}`; if `X_{B₀}` occurs to degree at most one
and already accounts for all of `α_{<β}`, no other variable of the monomial can contribute. -/
theorem partLT_eq_zero_of_mem_vars_pderiv {β α : NatOrdinal} {F : MvPolynomial σ R} {B₀ : σ}
    (hF : IsWeightedHomogeneous wt F α) (hdeg : degreeOf B₀ F ≤ 1)
    (hB₀ : NatOrdinal.partLT β (wt B₀) = NatOrdinal.partLT β α)
    {i : σ} (hi : i ∈ (pderiv B₀ F).vars) : NatOrdinal.partLT β (wt i) = 0 := by
  classical
  obtain ⟨d', hd', hid'⟩ := (mem_vars_iff_mem_support i).mp hi
  obtain ⟨d, hd, hdv, rfl⟩ := exists_mem_support_of_mem_support_pderiv hd'
  have hd1 : d B₀ = 1 :=
    le_antisymm ((monomial_le_degreeOf B₀ hd).trans hdeg) (Nat.one_le_iff_ne_zero.mpr hdv)
  -- `X_{B₀}` occurs exactly once, so it is gone from the monomial of the derivative
  have hi0 : i ≠ B₀ := by
    rintro rfl
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_same, hd1] at hid'
    exact hid' rfl
  have hid : i ∈ d.support := by
    rw [Finsupp.mem_support_iff] at hid' ⊢
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hi0.symm, Nat.sub_zero] at hid'
    exact hid'
  -- the parts below `ω^β` of the monomial add up to `α_{<β}`
  have hsum : ∑ j ∈ d.support, d j • NatOrdinal.partLT β (wt j) = NatOrdinal.partLT β α := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using
      (hF.map_weight (NatOrdinal.partLTAddMonoidHom β) (mem_support_iff.mp hd))
  -- and `X_{B₀}` alone already accounts for all of it
  have hB₀d : B₀ ∈ d.support := Finsupp.mem_support_iff.mpr hdv
  rw [← Finset.add_sum_erase _ _ hB₀d, hd1, one_smul, hB₀] at hsum
  have hrest : ∑ j ∈ d.support.erase B₀, d j • NatOrdinal.partLT β (wt j) = 0 :=
    add_eq_left.mp hsum
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ zero_le (a := _)] at hrest
  rcases smul_eq_zero.mp (hrest i (Finset.mem_erase.mpr ⟨hi0, hid⟩)) with h | h
  · exact absurd h (Finsupp.mem_support_iff.mp hid)
  · exact h

/-- **The parts below `ω^β` of a monomial's factors add up.** In a monomial of a homogeneous
polynomial that contains two named variables once each, the part below `ω^β` of the rest of the
monomial, together with the parts of those two variables, is the part below `ω^β` of the
polynomial's degree. -/
theorem partLT_weight_add_partLT_add_partLT {β α : NatOrdinal} {F : MvPolynomial σ R}
    (hF : IsWeightedHomogeneous wt F α) {d : σ →₀ ℕ} {i u : σ}
    (hd : d + Finsupp.single i 1 + Finsupp.single u 1 ∈ F.support) :
    NatOrdinal.partLT β (Finsupp.weight wt d) + NatOrdinal.partLT β (wt i) +
      NatOrdinal.partLT β (wt u) = NatOrdinal.partLT β α := by
  have hw : NatOrdinal.partLT β (Finsupp.weight wt
      (d + Finsupp.single i 1 + Finsupp.single u 1)) = NatOrdinal.partLT β α :=
    congrArg _ (hF (mem_support_iff.mp hd))
  rw [← hw, map_add, map_add, Finsupp.weight_single, Finsupp.weight_single, one_smul, one_smul,
    NatOrdinal.partLT_add, NatOrdinal.partLT_add]

/-- Both named variables of a decomposed monomial occur in it. -/
theorem mem_support_of_eq_add_single_add_single {d m : σ →₀ ℕ} {i u : σ}
    (h : m = d + Finsupp.single i 1 + Finsupp.single u 1) :
    i ∈ m.support ∧ u ∈ m.support := by
  classical
  constructor <;> rw [Finsupp.mem_support_iff, h] <;>
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply] <;> omega

/-- The rest of a decomposed monomial is determined by the monomial and the two variables. -/
theorem eq_of_eq_add_single_add_single {d d' m : σ →₀ ℕ} {i u : σ}
    (h : m = d + Finsupp.single i 1 + Finsupp.single u 1)
    (h' : m = d' + Finsupp.single i 1 + Finsupp.single u 1) : d' = d :=
  add_right_cancel (add_right_cancel (h'.symm.trans h))

/-- **The pair bound from the two-truncation remainder bound.** If every term of the expansion of a
monomial of `F` with at least two truncated factors has degree below `α_{≥β} ⊕ λ`, then lowering
the parts below `ω^β` of two variables of a monomial keeps the sum of those parts, together with
the part of the rest of the monomial, at or below `λ`.

Truncating exactly those two factors exhibits such a term, and its part at or above `ω^β` is
already `α_{≥β}`, so the bound falls entirely on the parts below. -/
theorem pair_bound_of_forall_termDegree_lt {β α lam : NatOrdinal}
    {F : MvPolynomial σ R} (hF : IsWeightedHomogeneous wt F α)
    (hlam : lam < NatOrdinal.partLT β α)
    (hrem : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ →
      ρ < NatOrdinal.partGE β α + lam)
    {d : σ →₀ ℕ} {i j : σ}
    (hd : d + Finsupp.single i 1 + Finsupp.single j 1 ∈ F.support)
    {ρᵢ ρⱼ : NatOrdinal} (hρᵢ : ρᵢ < NatOrdinal.partLT β (wt i))
    (hρⱼ : ρⱼ < NatOrdinal.partLT β (wt j)) :
    NatOrdinal.partLT β (Finsupp.weight wt d) + ρᵢ + ρⱼ ≤ lam := by
  have hlamβ : lam < ω^ β := hlam.trans (NatOrdinal.partLT_lt _ _)
  have hzeroGE : ∀ a : NatOrdinal, NatOrdinal.partLT β (NatOrdinal.partGE β a) = 0 := fun _ ↦
    NatOrdinal.partLT_eq_zero_of_forall_le
      fun _ hs ↦ NatOrdinal.wpow_le_of_mem_additivePrincipalTerms_partGE hs
  have hGE : NatOrdinal.partGE β (NatOrdinal.partGE β α + lam) = NatOrdinal.partGE β α := by
    rw [NatOrdinal.partGE_add, NatOrdinal.partGE_partGE,
      NatOrdinal.partGE_eq_zero_of_lt hlamβ, add_zero]
  have hLT : NatOrdinal.partLT β (NatOrdinal.partGE β α + lam) = lam := by
    rw [NatOrdinal.partLT_add, NatOrdinal.partLT_eq_self_of_lt hlamβ, hzeroGE, zero_add]
  -- truncating exactly the two factors exhibits a term of the expansion
  have hρᵢ' : NatOrdinal.partGE β (wt i) + ρᵢ < wt i := by
    conv_rhs => rw [← NatOrdinal.partGE_add_partLT β (wt i)]
    exact add_lt_add_of_le_of_lt le_rfl hρᵢ
  have hρⱼ' : NatOrdinal.partGE β (wt j) + ρⱼ < wt j := by
    conv_rhs => rw [← NatOrdinal.partGE_add_partLT β (wt j)]
    exact add_lt_add_of_le_of_lt le_rfl hρⱼ
  have hlt := hrem _ hd 2 _ le_rfl (termDegree_pair (wt := wt) d hρᵢ' hρⱼ')
  set ρ := Finsupp.weight wt d + (NatOrdinal.partGE β (wt i) + ρᵢ) +
    (NatOrdinal.partGE β (wt j) + ρⱼ) with hρdef
  have hρᵢβ : ρᵢ < ω^ β := hρᵢ.trans (NatOrdinal.partLT_lt β _)
  have hρⱼβ : ρⱼ < ω^ β := hρⱼ.trans (NatOrdinal.partLT_lt β _)
  -- its part at or above `ω^β` is already the whole of `α_{≥β}`
  have hhigh : NatOrdinal.partGE β ρ = NatOrdinal.partGE β (NatOrdinal.partGE β α + lam) := by
    have hα : NatOrdinal.partGE β α = NatOrdinal.partGE β
        (Finsupp.weight wt (d + Finsupp.single i 1 + Finsupp.single j 1)) :=
      congrArg _ (hF (mem_support_iff.mp hd)).symm
    rw [hGE, hα, hρdef, map_add, map_add, Finsupp.weight_single, Finsupp.weight_single,
      one_smul, one_smul]
    simp only [NatOrdinal.partGE_add, NatOrdinal.partGE_partGE,
      NatOrdinal.partGE_eq_zero_of_lt hρᵢβ, NatOrdinal.partGE_eq_zero_of_lt hρⱼβ, add_zero]
  have hlow := NatOrdinal.partLT_lt_of_lt_of_partGE_eq hlt hhigh
  rw [hLT, hρdef] at hlow
  simp only [NatOrdinal.partLT_add, NatOrdinal.partLT_eq_self_of_lt hρᵢβ,
    NatOrdinal.partLT_eq_self_of_lt hρⱼβ, hzeroGE, zero_add] at hlow
  exact hlow.le

/-- **The pair bound from a bound on the parts below the cutoff.** The same conclusion from the
form the term-degree analysis actually delivers: a bound on the part below the cutoff of every
term with at least two truncated factors that keeps the whole part above it. -/
theorem pair_bound_of_forall_partLT_le {β α lam : NatOrdinal}
    {F : MvPolynomial σ R} (hF : IsWeightedHomogeneous wt F α)
    (hrem : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ →
      NatOrdinal.partGE β ρ = NatOrdinal.partGE β α → NatOrdinal.partLT β ρ ≤ lam)
    {d : σ →₀ ℕ} {i j : σ}
    (hd : d + Finsupp.single i 1 + Finsupp.single j 1 ∈ F.support)
    {ρᵢ ρⱼ : NatOrdinal} (hρᵢ : ρᵢ < NatOrdinal.partLT β (wt i))
    (hρⱼ : ρⱼ < NatOrdinal.partLT β (wt j)) :
    NatOrdinal.partLT β (Finsupp.weight wt d) + ρᵢ + ρⱼ ≤ lam := by
  have hzeroGE : ∀ a : NatOrdinal, NatOrdinal.partLT β (NatOrdinal.partGE β a) = 0 := fun _ ↦
    NatOrdinal.partLT_eq_zero_of_forall_le
      fun _ hs ↦ NatOrdinal.wpow_le_of_mem_additivePrincipalTerms_partGE hs
  have hρᵢ' : NatOrdinal.partGE β (wt i) + ρᵢ < wt i := by
    conv_rhs => rw [← NatOrdinal.partGE_add_partLT β (wt i)]
    exact add_lt_add_of_le_of_lt le_rfl hρᵢ
  have hρⱼ' : NatOrdinal.partGE β (wt j) + ρⱼ < wt j := by
    conv_rhs => rw [← NatOrdinal.partGE_add_partLT β (wt j)]
    exact add_lt_add_of_le_of_lt le_rfl hρⱼ
  set ρ := Finsupp.weight wt d + (NatOrdinal.partGE β (wt i) + ρᵢ) +
    (NatOrdinal.partGE β (wt j) + ρⱼ) with hρdef
  have hρᵢβ : ρᵢ < ω^ β := hρᵢ.trans (NatOrdinal.partLT_lt β _)
  have hρⱼβ : ρⱼ < ω^ β := hρⱼ.trans (NatOrdinal.partLT_lt β _)
  have hhigh : NatOrdinal.partGE β ρ = NatOrdinal.partGE β α := by
    have hα : NatOrdinal.partGE β α = NatOrdinal.partGE β
        (Finsupp.weight wt (d + Finsupp.single i 1 + Finsupp.single j 1)) :=
      congrArg _ (hF (mem_support_iff.mp hd)).symm
    rw [hα, hρdef, map_add, map_add, Finsupp.weight_single, Finsupp.weight_single,
      one_smul, one_smul]
    simp only [NatOrdinal.partGE_add, NatOrdinal.partGE_partGE,
      NatOrdinal.partGE_eq_zero_of_lt hρᵢβ, NatOrdinal.partGE_eq_zero_of_lt hρⱼβ, add_zero]
  have hlow := hrem _ hd 2 _ le_rfl (termDegree_pair (wt := wt) d hρᵢ' hρⱼ') hhigh
  simp only [NatOrdinal.partLT_add, NatOrdinal.partLT_eq_self_of_lt hρᵢβ,
    NatOrdinal.partLT_eq_self_of_lt hρⱼβ, hzeroGE, zero_add] at hlow
  exact hlow

/-- **The pair bound, unconditionally.** For a homogeneous polynomial whose degree has a nonzero
part below the cutoff, and whose variables with a nonzero part below it have a last Cantor term of
nonzero exponent, there is a bound strictly below the polynomial's part at the cutoff that
dominates every sum obtained by lowering the parts of two variables of a monomial.

The term-degree analysis supplies the bound and the previous theorem consumes it, so the second
case's pair bound needs no analytic input at all -- only that its variables are of limit weight
below the cutoff. -/
theorem exists_lt_forall_pair_bound {β α : NatOrdinal} {F : MvPolynomial σ R}
    (hF : IsWeightedHomogeneous wt F α) (hμ : NatOrdinal.partLT β α ≠ 0)
    (htail : ∀ i ∈ F.vars, NatOrdinal.partLT β (wt i) ≠ 0 →
      ∃ e, e ≠ 0 ∧ NatOrdinal.leastTerm (NatOrdinal.partLT β (wt i)) = ω^ e) :
    ∃ lam : NatOrdinal, lam < NatOrdinal.partLT β α ∧
      ∀ (d : σ →₀ ℕ) (i j : σ),
        d + Finsupp.single i 1 + Finsupp.single j 1 ∈ F.support →
        ∀ ρᵢ ρⱼ : NatOrdinal, ρᵢ < NatOrdinal.partLT β (wt i) →
          ρⱼ < NatOrdinal.partLT β (wt j) →
          NatOrdinal.partLT β (Finsupp.weight wt d) + ρᵢ + ρⱼ ≤ lam := by
  obtain ⟨lam, hlam, hrem⟩ :=
    exists_forall_partLT_le_of_termDegree (K := R) F (fun _ hd ↦ hF (mem_support_iff.mp hd))
      hμ htail
  exact ⟨lam, hlam, fun d i j hd ρᵢ ρⱼ hρᵢ hρⱼ ↦
    pair_bound_of_forall_partLT_le hF hrem hd hρᵢ hρⱼ⟩

/-- **A uniform pair bound over the support.** For a homogeneous polynomial whose degree has a
nonzero part below `ω^β`, one bound strictly below that part dominates every sum obtained, at any
monomial, by lowering the parts of two of its variables.

At a single monomial the two-summand lemma supplies such a bound, the parts of the monomial's
factors adding up to the polynomial's; the monomials are finitely many and so are the pairs of
variables in each, and finitely many bounds below a common ceiling collapse to one. -/
theorem exists_lt_forall_add_add_le_of_isWeightedHomogeneous {β α : NatOrdinal}
    {F : MvPolynomial σ R} (hF : IsWeightedHomogeneous wt F α)
    (hα : 0 < NatOrdinal.partLT β α) :
    ∃ lam : NatOrdinal, lam < NatOrdinal.partLT β α ∧
      ∀ (d : σ →₀ ℕ) (i u : σ),
        d + Finsupp.single i 1 + Finsupp.single u 1 ∈ F.support →
        NatOrdinal.partLT β (wt i) ≠ 0 → NatOrdinal.partLT β (wt u) ≠ 0 →
        ∀ ρ₁ ρ₂ : NatOrdinal, ρ₁ < NatOrdinal.partLT β (wt i) →
          ρ₂ < NatOrdinal.partLT β (wt u) →
          NatOrdinal.partLT β (Finsupp.weight wt d) + ρ₁ + ρ₂ ≤ lam := by
  classical
  set P : (σ →₀ ℕ) → NatOrdinal → Prop := fun m B ↦
    ∀ (d : σ →₀ ℕ) (i u : σ), m = d + Finsupp.single i 1 + Finsupp.single u 1 →
      NatOrdinal.partLT β (wt i) ≠ 0 → NatOrdinal.partLT β (wt u) ≠ 0 →
      ∀ ρ₁ ρ₂ : NatOrdinal, ρ₁ < NatOrdinal.partLT β (wt i) →
        ρ₂ < NatOrdinal.partLT β (wt u) →
        NatOrdinal.partLT β (Finsupp.weight wt d) + ρ₁ + ρ₂ ≤ B with hPdef
  have hPmono : ∀ m, ∀ {B B' : NatOrdinal}, B ≤ B' → P m B → P m B' :=
    fun m _ _ hBB' hP d i u hd hi hu ρ₁ ρ₂ hρ₁ hρ₂ ↦
      (hP d i u hd hi hu ρ₁ ρ₂ hρ₁ hρ₂).trans hBB'
  refine (NatOrdinal.exists_lt_forall_of_forall_exists_lt F.support hα P hPmono ?_).imp
    fun lam hlam ↦ ⟨hlam.1, fun d i u hd hi hu ρ₁ ρ₂ hρ₁ hρ₂ ↦
      hlam.2 _ hd d i u rfl hi hu ρ₁ ρ₂ hρ₁ hρ₂⟩
  -- at each monomial, index by the pairs of its variables
  intro m hm
  set Q : σ × σ → NatOrdinal → Prop := fun p B ↦
    ∀ d : σ →₀ ℕ, m = d + Finsupp.single p.1 1 + Finsupp.single p.2 1 →
      NatOrdinal.partLT β (wt p.1) ≠ 0 → NatOrdinal.partLT β (wt p.2) ≠ 0 →
      ∀ ρ₁ ρ₂ : NatOrdinal, ρ₁ < NatOrdinal.partLT β (wt p.1) →
        ρ₂ < NatOrdinal.partLT β (wt p.2) →
        NatOrdinal.partLT β (Finsupp.weight wt d) + ρ₁ + ρ₂ ≤ B with hQdef
  have hQmono : ∀ p, ∀ {B B' : NatOrdinal}, B ≤ B' → Q p B → Q p B' :=
    fun p _ _ hBB' hQ d hd hi hu ρ₁ ρ₂ hρ₁ hρ₂ ↦ (hQ d hd hi hu ρ₁ ρ₂ hρ₁ hρ₂).trans hBB'
  -- at each pair, the two-summand lemma, or nothing to prove
  have hQmem : ∀ p ∈ m.support ×ˢ m.support, ∃ B, B < NatOrdinal.partLT β α ∧ Q p B := by
    rintro p -
    by_cases hdec : ∃ d : σ →₀ ℕ, m = d + Finsupp.single p.1 1 + Finsupp.single p.2 1
    · obtain ⟨d, hdm⟩ := hdec
      by_cases hi : NatOrdinal.partLT β (wt p.1) = 0
      · exact ⟨0, hα, fun _ _ hi' _ _ _ _ _ ↦ absurd hi hi'⟩
      by_cases hu : NatOrdinal.partLT β (wt p.2) = 0
      · exact ⟨0, hα, fun _ _ _ hu' _ _ _ _ ↦ absurd hu hu'⟩
      obtain ⟨e₁, he₁⟩ := NatOrdinal.exists_leastTerm_eq_wpow hi
      obtain ⟨e₂, he₂⟩ := NatOrdinal.exists_leastTerm_eq_wpow hu
      obtain ⟨B, hB, hall⟩ := NatOrdinal.exists_lt_forall_add_add_le
        (O := NatOrdinal.partLT β (Finsupp.weight wt d)) hi hu he₁ he₂
      have hsum := partLT_weight_add_partLT_add_partLT (β := β) hF (hdm ▸ hm)
      refine ⟨B, hsum ▸ hB, fun d' hd' _ _ ρ₁ ρ₂ hρ₁ hρ₂ ↦ ?_⟩
      rw [eq_of_eq_add_single_add_single hdm hd']
      exact hall ρ₁ ρ₂ hρ₁ hρ₂
    · exact ⟨0, hα, fun d hd _ _ _ _ _ _ ↦ absurd ⟨d, hd⟩ hdec⟩
  obtain ⟨B, hB, hQ⟩ :=
    NatOrdinal.exists_lt_forall_of_forall_exists_lt (m.support ×ˢ m.support) hα Q hQmono hQmem
  refine ⟨B, hB, fun d i u hd hi hu ρ₁ ρ₂ hρ₁ hρ₂ ↦ ?_⟩
  obtain ⟨him, hum⟩ := mem_support_of_eq_add_single_add_single hd
  exact hQ (i, u) (Finset.mem_product.mpr ⟨him, hum⟩) d hd hi hu ρ₁ ρ₂ hρ₁ hρ₂

/-- **The agreement one level up, from a pair bound.** Take two variables occurring once each in a
monomial of a homogeneous polynomial, both with nonzero part below `ω^β`. If a bound below the
polynomial's own part below `ω^β` dominates every sum obtained by lowering those two parts, and the
first variable's part does not precede the bound in the algebraic order, then the exponent of that
part's last Cantor term is below the second's, and the bound agrees with the polynomial's part at
or above the second exponent.

Everything here except the pair bound is forced: the parts of the monomial's factors add up, and
the ordering of the exponents is what the failed algebraic-order comparison leaves. -/
theorem partGE_eq_of_forall_add_add_le_of_not_algebraicLE {β α lam : NatOrdinal}
    {F : MvPolynomial σ R} (hF : IsWeightedHomogeneous wt F α)
    {d : σ →₀ ℕ} {i u : σ} (hd : d + Finsupp.single i 1 + Finsupp.single u 1 ∈ F.support)
    (hti : NatOrdinal.partLT β (wt i) ≠ 0) (htu : NatOrdinal.partLT β (wt u) ≠ 0)
    {ei eu : NatOrdinal} (hei : NatOrdinal.leastTerm (NatOrdinal.partLT β (wt i)) = ω^ ei)
    (heu : NatOrdinal.leastTerm (NatOrdinal.partLT β (wt u)) = ω^ eu) (hei0 : ei ≠ 0)
    (hlam : lam < NatOrdinal.partLT β α)
    (hall : ∀ ρ₁ ρ₂ : NatOrdinal, ρ₁ < NatOrdinal.partLT β (wt i) →
      ρ₂ < NatOrdinal.partLT β (wt u) →
      NatOrdinal.partLT β (Finsupp.weight wt d) + ρ₁ + ρ₂ ≤ lam)
    (hdiff : ¬ NatOrdinal.AlgebraicLE (NatOrdinal.partLT β (wt i)) lam) :
    ei < eu ∧ NatOrdinal.partGE eu lam = NatOrdinal.partGE eu (NatOrdinal.partLT β α) := by
  have hsum := partLT_weight_add_partLT_add_partLT (β := β) hF hd
  rw [← hsum]
  exact NatOrdinal.lt_and_partGE_eq_of_not_algebraicLE hti htu hei heu hei0 (hsum ▸ hlam) hall
    hdiff

/-- A variable with nonzero part below `ω^β` does not occur in `∂F/∂X_{B₀}`, so differentiating
`∂F/∂X_{B₀}` with respect to it gives zero. -/
theorem pderiv_eq_zero_of_partLT_ne_zero {β α : NatOrdinal} {F : MvPolynomial σ R} {B₀ : σ}
    (hF : IsWeightedHomogeneous wt F α) (hdeg : degreeOf B₀ F ≤ 1)
    (hB₀ : NatOrdinal.partLT β (wt B₀) = NatOrdinal.partLT β α)
    {v : σ} (hv : NatOrdinal.partLT β (wt v) ≠ 0) :
    pderiv v (pderiv B₀ F) = 0 :=
  pderiv_eq_zero_of_notMem_vars fun hmem ↦
    hv (partLT_eq_zero_of_mem_vars_pderiv hF hdeg hB₀ hmem)

variable [NoZeroDivisors R] [CharZero R]

/-- Let `F` be homogeneous of degree `α`, let `B₀` occur in `F` to
degree at most one with `(wt B₀)_{<β} = α_{<β}`, and suppose `H := ∂F/∂X_{B₀}` is nonzero of
nonzero degree `δ`. Suppose that for every variable `B'` of `F` whose part below `ω^β` is a
summand of `lam₀`, in the sense that it adds to `lam₀` under Hessenberg sum, there is a relation
expressing `∂F/∂X_{B'}` as a combination of the `∂F/∂X_B` over variables `B` with nonzero part
below `ω^β`, whose cofactors are free of `X_{B₀}`. This is impossible.

Applied at a variable `B'` of `H` with `∂H/∂X_{B'} ≠ 0` — which exists in characteristic zero,
and whose part below `ω^β` vanishes, hence adds to `lam₀` to give `lam₀` — differentiating the
relation in `X_{B₀}` turns the left side into `∂H/∂X_{B'}` and every right-hand summand into
`(∂H/∂X_B) U_B = 0`, since no `B` with nonzero part below `ω^β` is a variable of `H`. -/
@[blueprint "lem:relation-at-limit-ordinal-partial-contradiction"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Partial-derivative obstruction to a linear variable")
  (statement := /--
    For an ordinal $\xi$, let $\xi_{<\beta}$ be the Hessenberg sum of the
    terms in its Cantor normal form whose exponents are below $\beta$.

    Let $R$ be a commutative ring of characteristic zero without zero
    divisors. Give the variables $X_i$ ordinal weights $w_i$, and let
    $F\in R[X_i:i\in I]$ be weighted homogeneous of degree $\alpha$. Suppose
    that $X_{B_0}$ occurs in $F$ with degree at most one and
    $(w_{B_0})_{<\beta}=\alpha_{<\beta}$. Put
    $H=\partial_{B_0}F$, and suppose that $H\ne0$ is weighted homogeneous of
    some nonzero degree $\delta$.

    Fix an ordinal $\lambda_0$. Suppose that for every variable $X_{B'}$
    occurring in $F$ such that
    $(w_{B'})_{<\beta}\oplus\eta=\lambda_0$ for some ordinal $\eta$, there
    are a finite set $S$ and polynomials $U_B$ satisfying
    \[
      (w_B)_{<\beta}\ne0,\qquad \partial_{B_0}U_B=0\quad(B\in S),
      \qquad
      \partial_{B'}F=\sum_{B\in S}(\partial_BF)U_B.
    \]
    These hypotheses are inconsistent.
  -/)
  (proof := /--
  Choose a variable $X_{B'}$ occurring in the nonzero homogeneous polynomial
  $H$. Its degree is nonzero, so $H$ has a nonconstant monomial and $B'$ can
  be chosen with $\partial_{B'}H\ne0$. Because $X_{B_0}$ occurs at most once
  and already accounts for every Cantor term below $\omega^\beta$ in the
  degree of $F$, every variable of $H$ has
  $(w_{B'})_{<\beta}=0$. The equation
  $0\oplus\lambda_0=\lambda_0$ therefore supplies the assumed identity for
  $\partial_{B'}F$.

  Differentiate this identity with respect to $X_{B_0}$. The left side is
  $\partial_{B'}H\ne0$. On the right, every $U_B$ is independent of
  $X_{B_0}$, while $(w_B)_{<\beta}\ne0$ prevents $X_B$ from occurring in
  $H$; the Leibniz rule therefore makes every summand zero, a contradiction.
  -/)]
theorem false_of_pderiv_eq_sum_of_partLT_ne_zero {β α δ lam₀ : NatOrdinal}
    {F : MvPolynomial σ R} {B₀ : σ}
    (hF : IsWeightedHomogeneous wt F α) (hdeg : degreeOf B₀ F ≤ 1)
    (hB₀ : NatOrdinal.partLT β (wt B₀) = NatOrdinal.partLT β α)
    (hH : IsWeightedHomogeneous wt (pderiv B₀ F) δ) (hH0 : pderiv B₀ F ≠ 0) (hδ : δ ≠ 0)
    (hsyz : ∀ B' ∈ F.vars, NatOrdinal.AlgebraicLE (NatOrdinal.partLT β (wt B')) lam₀ →
      ∃ (s : Finset σ) (U : σ → MvPolynomial σ R),
        (∀ B ∈ s, NatOrdinal.partLT β (wt B) ≠ 0) ∧ (∀ B ∈ s, pderiv B₀ (U B) = 0) ∧
        pderiv B' F = ∑ B ∈ s, pderiv B F * U B) :
    False := by
  classical
  -- a variable `B'` of `H` with `∂H/∂X_{B'} ≠ 0`
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hH0
  have hdne : d ≠ 0 := by
    rintro rfl
    exact hδ (by rw [← hH hd, map_zero])
  obtain ⟨B', hB'd⟩ := Finsupp.support_nonempty_iff.mpr hdne
  have hB'H : B' ∈ (pderiv B₀ F).vars :=
    (mem_vars_iff_mem_support B').mpr ⟨d, mem_support_iff.mpr hd, hB'd⟩
  -- `B'` is a variable of `F` with vanishing part below `ω^β`
  have hB'F : B' ∈ F.vars := vars_pderiv_subset B₀ F hB'H
  have hB'LT : NatOrdinal.partLT β (wt B') = 0 :=
    partLT_eq_zero_of_mem_vars_pderiv hF hdeg hB₀ hB'H
  obtain ⟨s, U, hs, hU, heq⟩ :=
    hsyz B' hB'F (hB'LT ▸ NatOrdinal.algebraicLE_zero lam₀)
  -- differentiating the relation in `X_{B₀}` kills the right side
  exact pderiv_ne_zero_of_mem_vars hB'H
    (pderiv_pderiv_eq_zero_of_sum_of_notMem_vars heq hU fun B hB hmem ↦
      hs B hB (partLT_eq_zero_of_mem_vars_pderiv hF hdeg hB₀ hmem))

/-- **The polynomials free of a variable form a subring.** The kernel of a derivation is closed
under the ring operations, since a product is annihilated as soon as both factors are. -/
def freeOf (B₀ : σ) : Subring (MvPolynomial σ R) where
  carrier := {p | pderiv B₀ p = 0}
  zero_mem' := map_zero _
  one_mem' := pderiv_one
  add_mem' hp hq := by
    rw [Set.mem_setOf_eq, map_add, hp, hq, add_zero]
  neg_mem' hp := by
    rw [Set.mem_setOf_eq, map_neg, hp, neg_zero]
  mul_mem' hp hq := by
    rw [Set.mem_setOf_eq, pderiv_mul, hp, hq, zero_mul, mul_zero, add_zero]

omit [NoZeroDivisors R] [CharZero R] in
@[simp]
theorem mem_freeOf {B₀ : σ} {p : MvPolynomial σ R} : p ∈ freeOf B₀ ↔ pderiv B₀ p = 0 :=
  Iff.rfl

omit [NoZeroDivisors R] [CharZero R] in
/-- A polynomial all of whose monomials weigh less than a variable does not involve it. -/
theorem pderiv_eq_zero_of_forall_weight_lt {P : MvPolynomial σ R} {g : NatOrdinal}
    (hP : ∀ d ∈ P.support, Finsupp.weight wt d < g) {v : σ} (hg : g ≤ wt v) :
    pderiv v P = 0 := by
  by_contra h
  obtain ⟨d', hd'⟩ := support_nonempty.mpr h
  obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
  have h1 := hP d hd
  rw [← hw] at h1
  exact absurd (hg.trans (le_add_of_nonneg_left zero_le)) (not_le.mpr h1)

omit [NoZeroDivisors R] [CharZero R] in
/-- A homogeneous polynomial lighter than a variable is free of it. -/
theorem mem_freeOf_of_isWeightedHomogeneous {c : MvPolynomial σ R} {b : NatOrdinal}
    (hc : IsWeightedHomogeneous wt c b) {B₀ : σ} (hb : b < wt B₀) : c ∈ freeOf (R := R) B₀ :=
  mem_freeOf.mpr (pderiv_eq_zero_of_forall_weight_lt (g := wt B₀)
    (fun d hd ↦ by rw [hc (mem_support_iff.mp hd)]; exact hb) le_rfl)

omit [NoZeroDivisors R] [CharZero R] in
/-- **A combination with cofactors free of a variable lies in the span over them.** This is the
bridge from the identity the syzygy produces to the membership the propagation consumes. -/
theorem mem_span_of_eq_sum_mul {B₀ : σ} {Θ : MvPolynomial σ R} {κ' : Type*} [Fintype κ']
    {c Q : κ' → MvPolynomial σ R} (hc : ∀ j, c j ∈ freeOf (R := R) B₀)
    (heq : Θ = ∑ j, c j * Q j) :
    Θ ∈ Submodule.span (freeOf (R := R) B₀) (Set.range Q) := by
  rw [heq]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ (⟨c j, hc j⟩ : freeOf (R := R) B₀) (Submodule.subset_span ⟨j, rfl⟩)

/-- The partial derivatives of `F` at the variables heavier than a given one. -/
def higherPartials (F : MvPolynomial σ R) (wt : σ → NatOrdinal) (v : σ) :
    Set (MvPolynomial σ R) :=
  (fun j ↦ pderiv j F) '' {j | j ∈ F.vars ∧ wt v < wt j}

omit [NoZeroDivisors R] [CharZero R] in
/-- **Propagation to the variables that do not step further.** If at every variable satisfying a
predicate the partial derivative of `F` is a combination, over the polynomials free of `X_{B₀}`, of
the partial derivatives at heavier variables, then it is such a combination of the partial
derivatives at heavier variables that fail the predicate.

Each step replaces a generator that satisfies the predicate by generators strictly heavier than it,
and the variables of `F` heavier than a given one shrink strictly with every step, so the process
terminates. -/
theorem pderiv_mem_span_of_forall_mem_span_higher (B₀ : σ)
    (wt : σ → NatOrdinal) {F : MvPolynomial σ R} (Good : σ → Prop)
    (hstep : ∀ v ∈ F.vars, Good v →
      pderiv v F ∈ Submodule.span (freeOf (R := R) B₀) (higherPartials F wt v))
    {v' : σ} (hv' : v' ∈ F.vars) (hg : Good v') :
    pderiv v' F ∈ Submodule.span (freeOf (R := R) B₀)
      ((fun j ↦ pderiv j F) '' {j | j ∈ F.vars ∧ ¬ Good j ∧ wt v' < wt j}) := by
  classical
  suffices H : ∀ n : ℕ, ∀ v' ∈ F.vars, (F.vars.filter fun v ↦ wt v' < wt v).card = n → Good v' →
      pderiv v' F ∈ Submodule.span (freeOf (R := R) B₀)
        ((fun j ↦ pderiv j F) '' {j | j ∈ F.vars ∧ ¬ Good j ∧ wt v' < wt j}) from
    H _ v' hv' rfl hg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v' hv' hn hgood
  refine Submodule.span_le.mpr ?_ (hstep v' hv' hgood)
  rintro _ ⟨j, ⟨hjv, hjwt⟩, rfl⟩
  by_cases hj : Good j
  · -- a generator that steps further is replaced by strictly heavier ones
    have hsub : F.vars.filter (fun v ↦ wt j < wt v) ⊂ F.vars.filter fun v ↦ wt v' < wt v := by
      refine Finset.ssubset_iff_of_subset (fun k hk ↦ ?_) |>.mpr ⟨j, ?_, ?_⟩
      · rw [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, hjwt.trans hk.2⟩
      · exact Finset.mem_filter.mpr ⟨hjv, hjwt⟩
      · rw [Finset.mem_filter]
        exact fun h ↦ absurd h.2 (lt_irrefl _)
    have hcard := Finset.card_lt_card hsub
    rw [hn] at hcard
    refine Submodule.span_le.mpr ?_ (ih _ hcard j hjv rfl hj)
    rintro _ ⟨k, ⟨hkv, hkg, hkwt⟩, rfl⟩
    exact Submodule.subset_span ⟨k, ⟨hkv, hkg, hjwt.trans hkwt⟩, rfl⟩
  · exact Submodule.subset_span ⟨j, ⟨hjv, hj, hjwt⟩, rfl⟩

omit [NoZeroDivisors R] [CharZero R] in
/-- Differentiating at a variable is linear over the polynomials free of that variable, since a
factor it annihilates passes through the Leibniz rule. -/
theorem pderiv_smul_freeOf (B₀ : σ) (r : freeOf (R := R) B₀) (p : MvPolynomial σ R) :
    pderiv B₀ (r • p) = r • pderiv B₀ p := by
  have hsmul : ∀ q : MvPolynomial σ R, r • q = (r : MvPolynomial σ R) * q := fun _ ↦ rfl
  rw [hsmul, hsmul, pderiv_mul, mem_freeOf.mp r.2, zero_mul, zero_add]

/-- Differentiating at a variable, as a map linear over the polynomials free of it. -/
@[expose]
def pderivFreeOf (B₀ : σ) :
    MvPolynomial σ R →ₗ[freeOf (R := R) B₀] MvPolynomial σ R where
  toFun := pderiv B₀
  map_add' _ _ := map_add _ _ _
  map_smul' := pderiv_smul_freeOf B₀

omit [NoZeroDivisors R] [CharZero R] in
@[simp]
theorem pderivFreeOf_apply (B₀ : σ) (p : MvPolynomial σ R) :
    pderivFreeOf (R := R) B₀ p = pderiv B₀ p :=
  rfl

omit [NoZeroDivisors R] [CharZero R] in
/-- **The differentiated syzygy contradiction, in span form.** If a partial derivative of `F` lies
in the span, over the polynomials free of `X_{B₀}`, of the partial derivatives at a set of
variables none of which occurs in `∂F/∂X_{B₀}`, then that partial derivative of `F` is annihilated
by the distinguished variable.

Differentiating at `B₀` is linear over that subring, so it carries the span to the span of the
differentiated generators, and each of those vanishes. -/
theorem pderiv_pderiv_eq_zero_of_mem_span (B₀ : σ) {F : MvPolynomial σ R} {B' : σ} {S : Set σ}
    (hmem : pderiv B' F ∈
      Submodule.span (freeOf (R := R) B₀) ((fun j ↦ pderiv j F) '' S))
    (hvars : ∀ j ∈ S, j ∉ (pderiv B₀ F).vars) :
    pderiv B' (pderiv B₀ F) = 0 := by
  have hker : ∀ q ∈ (fun j ↦ pderiv j F) '' S, pderivFreeOf (R := R) B₀ q = 0 := by
    rintro _ ⟨j, hj, rfl⟩
    rw [pderivFreeOf_apply, pderiv_pderiv_comm, pderiv_eq_zero_of_notMem_vars (hvars j hj)]
  have hzero : pderivFreeOf (R := R) B₀ (pderiv B' F) = 0 := by
    refine Submodule.span_induction (p := fun q _ ↦ pderivFreeOf (R := R) B₀ q = 0) hker ?_ ?_ ?_
      hmem
    · exact map_zero _
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    · intro a b _ hb
      rw [map_smul, hb, smul_zero]
  rwa [pderivFreeOf_apply, pderiv_pderiv_comm] at hzero

/-- **The limit contradiction from a step at every light variable.** Suppose that at every variable
of `F` whose part below `ω^β` vanishes, the partial derivative of `F` is a combination, over the
polynomials free of `X_{B₀}`, of the partial derivatives at heavier variables. With `B₀` occurring
to degree at most one and carrying all of `α_{<β}`, and `H := ∂F/∂X_{B₀}` nonzero of nonzero
degree, this is impossible.

Every variable of `H` has vanishing part below `ω^β`, so the step applies at one of them with
`∂H/∂X_{B'} ≠ 0`; propagating leaves only variables with nonzero part below `ω^β`, and none of
those occurs in `H`, so differentiating in `X_{B₀}` annihilates `H` at `B'`. -/
theorem false_of_forall_mem_span_higher {β α δ : NatOrdinal}
    {F : MvPolynomial σ R} {B₀ : σ}
    (hF : IsWeightedHomogeneous wt F α) (hdeg : degreeOf B₀ F ≤ 1)
    (hB₀ : NatOrdinal.partLT β (wt B₀) = NatOrdinal.partLT β α)
    (hH : IsWeightedHomogeneous wt (pderiv B₀ F) δ) (hH0 : pderiv B₀ F ≠ 0) (hδ : δ ≠ 0)
    (hstep : ∀ v ∈ F.vars, NatOrdinal.partLT β (wt v) = 0 →
      pderiv v F ∈ Submodule.span (freeOf (R := R) B₀) (higherPartials F wt v)) :
    False := by
  classical
  -- a variable `B'` of `H` with `∂H/∂X_{B'} ≠ 0`
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hH0
  have hdne : d ≠ 0 := by
    rintro rfl
    exact hδ (by rw [← hH hd, map_zero])
  obtain ⟨B', hB'd⟩ := Finsupp.support_nonempty_iff.mpr hdne
  have hB'H : B' ∈ (pderiv B₀ F).vars :=
    (mem_vars_iff_mem_support B').mpr ⟨d, mem_support_iff.mpr hd, hB'd⟩
  have hB'F : B' ∈ F.vars := vars_pderiv_subset B₀ F hB'H
  have hB'LT : NatOrdinal.partLT β (wt B') = 0 :=
    partLT_eq_zero_of_mem_vars_pderiv hF hdeg hB₀ hB'H
  -- propagating leaves only variables with nonzero part below `ω^β`
  have hspan := pderiv_mem_span_of_forall_mem_span_higher B₀ wt
    (fun v ↦ NatOrdinal.partLT β (wt v) = 0) hstep hB'F hB'LT
  exact pderiv_ne_zero_of_mem_vars hB'H
    (pderiv_pderiv_eq_zero_of_mem_span B₀ hspan fun j hj hmem ↦
      hj.2.1 (partLT_eq_zero_of_mem_vars_pderiv hF hdeg hB₀ hmem))

omit [NoZeroDivisors R] [CharZero R] in
/-- **The step at a light variable, from a syzygy identity.** If the partial derivative at a
variable is a combination of the partial derivatives at heavier variables, with cofactors
homogeneous of the complementary degrees, then it lies in the span of those partial derivatives
over the polynomials free of `X_{B₀}` -- provided `B₀` is of maximal weight, which makes every
cofactor lighter than it and so free of it.

This is the join between the analysis, which delivers an identity with graded cofactors, and the
propagation, which consumes a span membership. -/
theorem mem_span_higherPartials_of_eq_sum_mul {B₀ : σ} {F : MvPolynomial σ R}
    {v : σ} {κ' : Type*} [Fintype κ'] {c : κ' → MvPolynomial σ R} {g : κ' → σ}
    (hg : ∀ j, g j ∈ F.vars ∧ wt v < wt (g j))
    (hmax : ∀ i ∈ F.vars, wt i ≤ wt B₀) (hv : 0 < wt v)
    (hchom : ∀ j, ∃ b, b + wt v = wt (g j) ∧ IsWeightedHomogeneous wt (c j) b)
    (heq : pderiv v F = ∑ j, c j * pderiv (g j) F) :
    pderiv v F ∈ Submodule.span (freeOf (R := R) B₀) (higherPartials F wt v) := by
  classical
  have hfree : ∀ j, c j ∈ freeOf (R := R) B₀ := by
    intro j
    obtain ⟨b, hb, hbhom⟩ := hchom j
    refine mem_freeOf_of_isWeightedHomogeneous hbhom ?_
    have h1 : b < wt (g j) := by
      rw [← hb]
      exact lt_add_of_pos_right _ hv
    exact h1.trans_le (hmax _ (hg j).1)
  have hspan := mem_span_of_eq_sum_mul (B₀ := B₀) (Q := fun j ↦ pderiv (g j) F) hfree heq
  refine Submodule.span_le.mpr ?_ hspan
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span ⟨g j, ⟨(hg j).1, (hg j).2⟩, rfl⟩

end MvPolynomial

end
