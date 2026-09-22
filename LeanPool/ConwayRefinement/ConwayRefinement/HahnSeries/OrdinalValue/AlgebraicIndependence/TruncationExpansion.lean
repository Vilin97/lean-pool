/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.TermDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LeadingCoefficient
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationPolynomial

/-!
# The Leibniz rule with remainder, read in polynomials

Let `𝓑` be a minimal system of homogeneous generators with lifts `b_B`, and assume evaluation
injective below `α`. For a monomial `X^d = X_{B_1} ⋯ X_{B_n}` (factors listed with multiplicity)
the convolution formula [Ber00, Lem. 7.5], iterated over the factors, expresses the polynomial of
the translated truncation `(X^d(b_𝓑))^{|γ}` as a sum over the nonempty sets `S` of truncated
factors of products `∏_{s ∈ S} pol(b_s^{|ζ_s}) ∏_{s ∉ S} X_s` with `∑_{s ∈ S} ζ_s = γ`. The terms
with exactly one truncated factor sum to `∑_B pol(b_B^{|γ}) ∂X^d/∂X_B`; the remaining terms —
at least two truncated factors — have degrees of the form `⨁_{s ∉ S} deg s ⊕ ⨁_{s ∈ S} ρ_s` with
`ρ_s < deg s`. The Leibniz rule with remainder [Ber00, Lem. 7.7]
(`exists_forall_pol_translatedTruncation_aeval`): for all `γ < 0` sufficiently close to `0`,
`pol(G(b_𝓑)^{|γ}) = ∑_B pol(b_B^{|γ}) ∂G/∂X_B + R_γ`, where every monomial of the remainder `R_γ`
has such a degree, for some monomial of `G` and some set of at least two truncated factors.

The degrees are recorded by the inductive predicate `TermDegree wt d k ρ`: `ρ` is the degree of a
term of the expansion of the monomial `d` with `k` truncated factors.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} [DecidableEq ι] {wt : ι → NatOrdinal}
  {x : ι → PrincipalSubring K}

/-- A common punctured neighborhood works for finitely many eventual properties. -/
theorem exists_forall_of_forall_exists_forall {ι' : Type*} (s : Finset ι') (p : ι' → ℝ → Prop)
    (h : ∀ i ∈ s, ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 → p i γ) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 → ∀ i ∈ s, p i γ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun _ _ _ i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨ε₁, hε₁, h₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨ε₂, hε₂, h₂⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun γ hγε hγ0 i hi ↦ ?_⟩
    have hγ₁ : -ε₁ < γ := by have := min_le_left ε₁ ε₂; linarith
    have hγ₂ : -ε₂ < γ := by have := min_le_right ε₁ ε₂; linarith
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h₁ γ hγ₁ hγ0
    · exact h₂ γ hγ₂ hγ0 i hi

/-! ### Degrees of the terms of the expansion -/

/-! ### The remainder -/

variable (wt) in
/-- `E` is a *remainder* for the monomial `d`: every monomial of `E` has the degree of a term of
the expansion of `d` with at least two truncated factors. -/
def IsRemainder (d : ι →₀ ℕ) (E : MvPolynomial ι K) : Prop :=
  ∀ d' ∈ E.support, ∃ k, 2 ≤ k ∧ TermDegree wt d k (Finsupp.weight wt d')

omit [DecidableEq ι] in
theorem isRemainder_zero (d : ι →₀ ℕ) : IsRemainder wt d (0 : MvPolynomial ι K) := fun d' hd' ↦ by
  rw [support_zero] at hd'
  exact absurd hd' (Finset.notMem_empty d')

omit [DecidableEq ι] in
theorem IsRemainder.add {d : ι →₀ ℕ} {E E' : MvPolynomial ι K} (hE : IsRemainder wt d E)
    (hE' : IsRemainder wt d E') : IsRemainder wt d (E + E') := by
  classical
  intro d' hd'
  rcases Finset.mem_union.mp (support_add hd') with h | h
  · exact hE d' h
  · exact hE' d' h

omit [DecidableEq ι] in
theorem IsRemainder.sum {ι' : Type*} {d : ι →₀ ℕ} (s : Finset ι') (E : ι' → MvPolynomial ι K)
    (hE : ∀ j ∈ s, IsRemainder wt d (E j)) : IsRemainder wt d (∑ j ∈ s, E j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isRemainder_zero d
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hE a (Finset.mem_insert_self a s)).add (ih fun j hj ↦ hE j (Finset.mem_insert_of_mem hj))

omit [DecidableEq ι] in
/-- Multiplying a remainder for `d` by `X_i` gives a remainder for `d + single i 1`. -/
theorem IsRemainder.mul_X {d : ι →₀ ℕ} {E : MvPolynomial ι K} (hE : IsRemainder wt d E) (i : ι) :
    IsRemainder wt (d + Finsupp.single i 1) (E * X i) := fun d' hd' ↦ by
  classical
  obtain ⟨d₁, hd₁, d₂, hd₂, hw⟩ := exists_add_eq_weight_of_mem_support_mul (wt := wt) hd'
  obtain ⟨k, hk, hT⟩ := hE d₁ hd₁
  rw [X, support_monomial, ite_eq_right one_ne_zero, Finset.mem_singleton] at hd₂
  subst hd₂
  rw [Finsupp.weight_single, one_smul] at hw
  exact ⟨k, hk, hw ▸ TermDegree.untrunc i hT⟩

omit [DecidableEq ι] in
/-- Multiplying a polynomial whose monomials have degrees of terms of `d` with at least one
truncated factor by a polynomial of degree `< wt i` gives a remainder for `d + single i 1`. -/
theorem isRemainder_mul_of_degreeLT {d : ι →₀ ℕ} {P Q : MvPolynomial ι K}
    (hP : ∀ d' ∈ P.support, ∃ k, 1 ≤ k ∧ TermDegree wt d k (Finsupp.weight wt d')) {i : ι}
    (hQ : DegreeLT wt Q (wt i)) : IsRemainder wt (d + Finsupp.single i 1) (P * Q) := fun d' hd' ↦ by
  classical
  obtain ⟨d₁, hd₁, d₂, hd₂, hw⟩ := exists_add_eq_weight_of_mem_support_mul (wt := wt) hd'
  obtain ⟨k, hk, hT⟩ := hP d₁ hd₁
  refine ⟨k + 1, by omega, hw ▸ TermDegree.trunc i ((degreeLT_iff).mp hQ d₂ hd₂) hT⟩

/-! ### The Leibniz rule for monomials -/

namespace Lifts

variable (σ : Lifts wt x) (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
  {α : NatOrdinal} (hinj : ∀ β < α, InjectiveAt K wt x β)
include hinj

omit [DecidableEq ι] in
/-- The polynomial of a lift is its variable. -/
theorem pol_lift {i : ι} (hi : wt i < α) : σ.pol hx α (σ.lift i) = X i := by
  have h : σ.lift i = aeval σ.lift (X i : MvPolynomial ι K) := (aeval_X _ _).symm
  rw [h]
  exact σ.pol_aeval hx hinj ((isWeightedHomogeneous_X K wt i).degreeLT hi)

omit [DecidableEq ι] in
/-- The polynomial of a monomial in the lifts is the monomial. -/
theorem pol_aeval_monomial {d : ι →₀ ℕ} (hd : Finsupp.weight wt d < α) :
    σ.pol hx α (aeval σ.lift (monomial d (1 : K))) = monomial d 1 :=
  σ.pol_aeval hx hinj ((isWeightedHomogeneous_monomial wt d (1 : K) rfl).degreeLT hd)

omit [DecidableEq ι] hinj in
/-- The first-order terms of the expansion of a monomial: every monomial of
`∑_j Tj j * ∂X^d/∂X_j` has the degree of a term of `d` with one truncated factor, provided each
`Tj j` (in the application, `pol(b_j^{|γ})`) has degree `< wt j`. -/
theorem forall_termDegree_sum_mul_pderiv_monomial (d : ι →₀ ℕ) (Tj : ι → MvPolynomial ι K)
    (hTj : ∀ j ∈ d.support, DegreeLT wt (Tj j) (wt j)) :
    ∀ d' ∈ (∑ j ∈ d.support, Tj j * pderiv j (monomial d (1 : K))).support,
      ∃ k, 1 ≤ k ∧ TermDegree wt d k (Finsupp.weight wt d') := by
  classical
  intro d' hd'
  obtain ⟨j, hj, hd'j⟩ := Finset.mem_biUnion.mp (support_sum hd')
  obtain ⟨d₁, hd₁, d₂, hd₂, hw⟩ := exists_add_eq_weight_of_mem_support_mul (wt := wt) hd'j
  rw [pderiv_monomial, support_monomial] at hd₂
  split_ifs at hd₂ with h0
  · exact absurd hd₂ (Finset.notMem_empty d₂)
  · rw [Finset.mem_singleton] at hd₂
    subst hd₂
    have hdj : d - Finsupp.single j 1 + Finsupp.single j 1 = d :=
      Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hj)
    refine ⟨1, le_rfl, ?_⟩
    have := TermDegree.trunc_left j ((degreeLT_iff).mp (hTj j hj) d₁ hd₁)
      (termDegree_weight wt (d - Finsupp.single j 1))
    rw [add_comm (Finsupp.single j 1), hdj] at this
    rwa [← hw]

omit [DecidableEq ι] hinj in
/-- Splitting off one factor: `X^{d + e_i} = X^d · X_i`. -/
theorem monomial_add_single_one (d : ι →₀ ℕ) (i : ι) :
    monomial (d + Finsupp.single i 1) (1 : K) = monomial d 1 * X i := by
  rw [X, MvPolynomial.monomial_mul_monomial, mul_one]

omit [DecidableEq ι] hinj in
/-- The first-order terms after splitting off one factor:
`∑_j T_j ∂(X^d X_i)/∂X_j = (∑_j T_j ∂X^d/∂X_j) X_i + T_i X^d`. -/
theorem sum_mul_pderiv_monomial_add_single (d : ι →₀ ℕ) (i : ι) (T : ι → MvPolynomial ι K) :
    ∑ j ∈ (d + Finsupp.single i 1).support, T j * pderiv j (monomial (d + Finsupp.single i 1) 1) =
      (∑ j ∈ d.support, T j * pderiv j (monomial d (1 : K))) * X i + T i * monomial d 1 := by
  classical
  have hmem : i ∈ (d + Finsupp.single i 1).support := by
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hsub : d.support ⊆ (d + Finsupp.single i 1).support := fun j hj ↦ by
    rw [Finsupp.mem_support_iff] at hj ⊢
    rw [Finsupp.add_apply]
    omega
  simp only [monomial_add_single_one, pderiv_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul, ← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun j _ ↦ by ring
    · intro j _ hj
      rw [pderiv_monomial, Finsupp.notMem_support_iff.mp hj, Nat.cast_zero, mul_zero, monomial_zero,
        zero_mul, mul_zero]
  · rw [Finset.sum_eq_single i]
    · rw [pderiv_X_self, mul_one]
    · intro j _ hji
      rw [pderiv_X_of_ne (Ne.symm hji), mul_zero, mul_zero]
    · intro h
      exact absurd hmem h

omit [DecidableEq ι] in
/-- **The Leibniz rule with remainder for a monomial.** For `X^d` of degree `≤ α` in variables of
degree `< α`, and all `γ < 0` sufficiently close to `0`, `v_J((X^d(b_𝓑))^{|γ}) < ω^α` and the
polynomial of `(X^d(b_𝓑))^{|γ}` is `∑_j pol(b_j^{|γ}) ∂X^d/∂X_j + R_γ` with `R_γ` a remainder
for `d`. -/
theorem exists_forall_pol_translatedTruncation_aeval_monomial (d : ι →₀ ℕ)
    (hd : Finsupp.weight wt d ≤ α) (hvars : ∀ i ∈ d.support, wt i < α) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      ordinalValue (translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ)
        < ω^ α ∧
      ∃ E : MvPolynomial ι K, IsRemainder wt d E ∧
        σ.pol hx α (translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ)
          = ∑ j ∈ d.support, σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ) *
              pderiv j (monomial d 1) + E := by
  classical
  -- strong induction on the number of factors
  suffices h : ∀ n : ℕ, ∀ d : ι →₀ ℕ, Finsupp.degree d = n → Finsupp.weight wt d ≤ α →
      (∀ i ∈ d.support, wt i < α) → ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      ordinalValue (translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ)
        < ω^ α ∧
      ∃ E : MvPolynomial ι K, IsRemainder wt d E ∧
        σ.pol hx α (translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ)
          = ∑ j ∈ d.support, σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ) *
              pderiv j (monomial d 1) + E from h _ d rfl hd hvars
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d hdn hd hvars
  rcases eq_or_ne d 0 with rfl | hd0
  · -- the constant monomial
    refine ⟨1, one_pos, fun γ _ hγ0 ↦ ?_⟩
    have h1 : aeval σ.lift (monomial (0 : ι →₀ ℕ) (1 : K)) = (1 : Series K) := by
      rw [monomial_zero', C_1, map_one]
    have htr : translatedTruncation ((1 : Series K) : K⟦ℝ⟧) γ = 0 := by
      rw [Subring.coe_one, ← HahnSeries.C_one]
      exact translatedTruncation_C_of_neg 1 hγ0
    rw [h1, htr, ordinalValue_zero]
    refine ⟨NatOrdinal.wpow_pos α, 0, isRemainder_zero 0, ?_⟩
    simp only [σ.pol_zero hx hinj, Finsupp.support_zero, Finset.sum_empty, add_zero]
  · -- split off one factor `X_i`
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
    set d' := d - Finsupp.single i 1 with hd'def
    have hdd' : d' + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)
    have hwd : Finsupp.weight wt d' + wt i = Finsupp.weight wt d := by
      rw [← hdd', map_add, Finsupp.weight_single, one_smul]
    have hdeg : Finsupp.degree d' < n := by
      rw [← hdn, ← hdd', map_add, Finsupp.degree_single]
      omega
    have hwi : wt i < α := hvars i hi
    have hwd'α : Finsupp.weight wt d' < α := by
      have : Finsupp.weight wt d' < Finsupp.weight wt d' + wt i :=
        lt_add_of_pos_right _ (pos_iff_ne_zero.mpr (hx.ne_zero i))
      exact this.trans_le (hwd ▸ hd)
    have hsub : d'.support ⊆ d.support := by
      rw [hd'def]
      exact Finsupp.support_tsub
    obtain ⟨ε', hε', ih'⟩ := ih _ hdeg d' rfl hwd'α.le fun j hj ↦ hvars j (hsub hj)
    -- the translated truncations of the lifts of the variables of `d` have value below `ω^{wt j}`
    obtain ⟨εd, hεd, hdrop⟩ := exists_forall_of_forall_exists_forall d.support
      (fun j β ↦ ordinalValue (translatedTruncation (σ.lift j : K⟦ℝ⟧) β) < ω^ (wt j))
      fun j _ ↦ exists_forall_ordinalValue_translatedTruncation_lt
        (Berarducci.Represents.ordinalValue_lt (σ.represents j))
    -- the convolution formula for `X^{d'}(b_𝓑) · b_i`
    set M' : Series K := aeval σ.lift (monomial d' (1 : K)) with hM'def
    have hM' : ordinalValue M' < ω^ (Finsupp.weight wt d' + 1) :=
      Berarducci.Represents.ordinalValue_lt
        (σ.aeval_represents (isWeightedHomogeneous_monomial wt d' (1 : K) rfl))
    have hli : ordinalValue (σ.lift i) < ω^ (wt i + 1) :=
      Berarducci.Represents.ordinalValue_lt (σ.represents i)
    obtain ⟨εL, hεL, hL2⟩ := σ.exists_forall_pol_translatedTruncation_mul hx hinj hM' hli hwd'α hwi
      (hwd ▸ hd)
    -- the translated truncations of the product have value below `ω^{deg d}`
    have hprod : aeval σ.lift (monomial d (1 : K)) = M' * σ.lift i := by
      rw [← hdd', monomial_add_single_one, map_mul, aeval_X]
    have hMprod : ordinalValue (M' * σ.lift i) < ω^ (Finsupp.weight wt d + 1) := by
      rw [← hprod]
      exact Berarducci.Represents.ordinalValue_lt
        (σ.aeval_represents (isWeightedHomogeneous_monomial wt d (1 : K) rfl))
    obtain ⟨εP, hεP, hdropP⟩ := exists_forall_ordinalValue_translatedTruncation_lt hMprod
    refine ⟨min (min ε' εd) (min εL εP), lt_min (lt_min hε' hεd) (lt_min hεL hεP),
      fun γ hγε hγ0 ↦ ?_⟩
    have hm1 := min_le_left (min ε' εd) (min εL εP)
    have hm2 := min_le_right (min ε' εd) (min εL εP)
    have hγ' : -ε' < γ := by have := min_le_left ε' εd; linarith
    have hγd : -εd < γ := by have := min_le_right ε' εd; linarith
    have hγL : -εL < γ := by have := min_le_left εL εP; linarith
    have hγP : -εP < γ := by have := min_le_right εL εP; linarith
    refine ⟨?_, ?_⟩
    · rw [hprod]
      exact (hdropP γ hγP hγ0).trans_le (NatOrdinal.wpow_le_wpow.mpr hd)
    -- the index set of the convolution formula, with `0` and `γ` added
    set S : Finset ℝ := insert 0 (insert γ (convolutionIndex (M' : K⟦ℝ⟧) (σ.lift i : K⟦ℝ⟧) γ))
      with hSdef
    have hS1 : convolutionIndex (M' : K⟦ℝ⟧) (σ.lift i : K⟦ℝ⟧) γ ⊆ S :=
      (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have hS2 : (S : Set ℝ) ⊆ Set.Icc γ 0 := by
      intro β hβ
      rw [hSdef, Finset.coe_insert, Finset.coe_insert] at hβ
      rcases hβ with rfl | rfl | hβ
      · exact ⟨hγ0.le, le_rfl⟩
      · exact ⟨le_rfl, hγ0.le⟩
      · exact mem_Icc_of_mem_convolutionIndex hβ
    have h0S : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
    have hγS : γ ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hconv := hL2 γ hγL hγ0 S hS1 hS2
    rw [sum_eq_add_add_sum_erase h0S hγS hγ0.ne] at hconv
    -- the two first-order terms of the convolution formula
    rw [translatedTruncation_zero, sub_zero, σ.pol_aeval_monomial hx hinj hwd'α, sub_self,
      translatedTruncation_zero, σ.pol_lift hx hinj hwi] at hconv
    -- the induction hypothesis at `γ`
    obtain ⟨-, E', hE', hexp'⟩ := ih' γ hγ' hγ0
    -- the remaining terms form a remainder
    set R : MvPolynomial ι K := ∑ β ∈ (S.erase 0).erase γ,
      σ.pol hx α (translatedTruncation (M' : K⟦ℝ⟧) β) *
        σ.pol hx α (translatedTruncation (σ.lift i : K⟦ℝ⟧) (γ - β)) with hRdef
    have hR : IsRemainder wt d R := by
      rw [← hdd']
      refine IsRemainder.sum _ _ fun β hβ ↦ ?_
      have hβγ : β ≠ γ := (Finset.mem_erase.mp hβ).1
      have hβ0 : β ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hβ).2).1
      have hβS : β ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hβ).2).2
      obtain ⟨hβ1, hβ2⟩ := hS2 hβS
      have hβlt : β < 0 := lt_of_le_of_ne hβ2 hβ0
      have hβgt : γ < β := lt_of_le_of_ne hβ1 (Ne.symm hβγ)
      -- the degree of the truncated lift
      have hQ : DegreeLT wt (σ.pol hx α (translatedTruncation (σ.lift i : K⟦ℝ⟧) (γ - β)))
          (wt i) :=
        σ.pol_degreeLT_of_lt hx hinj hwi.le (hdrop (γ - β) (by linarith) (by linarith) i hi)
      -- the expansion of `(X^{d'}(b_𝓑))^{|β}`
      obtain ⟨-, E'', hE'', hexp''⟩ := ih' β (by linarith) hβlt
      refine isRemainder_mul_of_degreeLT (fun d₁ hd₁ ↦ ?_) hQ
      rw [hexp''] at hd₁
      rcases Finset.mem_union.mp (support_add hd₁) with h | h
      · exact forall_termDegree_sum_mul_pderiv_monomial d' _
          (fun j hj ↦ σ.pol_degreeLT_of_lt hx hinj (hvars j (hsub hj)).le
            (hdrop β (by linarith) hβlt j (hsub hj))) d₁ h
      · obtain ⟨k, hk, hT⟩ := hE'' d₁ h
        exact ⟨k, by omega, hT⟩
    refine ⟨E' * X i + R, (hdd' ▸ hE'.mul_X i).add hR, ?_⟩
    -- combine
    rw [hprod, hconv, hexp', ← hdd', sum_mul_pderiv_monomial_add_single]
    ring

omit [DecidableEq ι] hinj in
/-- The ordinal value of a scalar multiple. -/
theorem ordinalValue_C_mul_lt (k : K) {u : Series K} {β : NatOrdinal} (hu : ordinalValue u < ω^ β) :
    ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) k * u) < ω^ β := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [map_zero, zero_mul, ordinalValue_zero]
    exact NatOrdinal.wpow_pos β
  · rwa [ordinalValue_C_mul hk]

omit [DecidableEq ι] in
/-- **The Leibniz rule with remainder [Ber00, Lem. 7.7], read in polynomials.** For `H ∈ K[X]`
with monomials of degree `≤ α` in variables of degree `< α`, and all `γ < 0` sufficiently close to
`0`, `v_J(H(b_𝓑)^{|γ}) < ω^α` and `pol(H(b_𝓑)^{|γ}) = ∑_j pol(b_j^{|γ}) ∂H/∂X_j + R_γ`, where
every monomial of the remainder `R_γ` has the degree of a term of the expansion of some monomial
of `H` with at least two truncated factors. -/
@[blueprint "lem:leibniz-remainder"
  (phase := "Translated truncations")
  (title := "Polynomial Leibniz rule for translated truncations")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$ with
    $x_i\in\mathrm P_{w_i}$, and choose series $b_i$ representing the $x_i$.
    Assume that evaluation at $(x_i)$ is injective in every weighted degree
    below $\alpha<\omega_1$. For a series $a$ of ordinal value below
    $\omega^\alpha$, write $P_a$ for its resulting polynomial representative.

    Let $G\in K[X_i:i\in I]$. Suppose every monomial $X^d$ of $G$ has weight
    at most $\alpha$, and $w_i<\alpha$ for every variable $X_i$ occurring in
    $G$. Then, for every $\gamma<0$ sufficiently close to $0$,
    \[
      v_J((G(b_i))^{|\gamma})<\omega^\alpha
    \]
    and there is a polynomial $R_\gamma$ such that
    \[
      P_{(G(b_i))^{|\gamma}}
        =\sum_{i\in\operatorname{vars}(G)}
          P_{b_i^{|\gamma}}\frac{\partial G}{\partial X_i}+R_\gamma.
    \]
    More precisely, for every monomial $X^{d'}$ of $R_\gamma$, there are a
    monomial $X^d$ of $G$, an integer $k\ge2$, a factorisation
    \[
      X^d=X^{d_0}X_{i_1}\cdots X_{i_k},
    \]
    with factors listed with multiplicity, and ordinals $\rho_r<w_{i_r}$ such
    that
    \[
      \operatorname{wt}(d')
        =\operatorname{wt}(d_0)\oplus\rho_1\oplus\cdots\oplus\rho_k.
    \]
  -/)
  (proof := /--
  First take $G=X^d$ and argue by strong induction on the number of factors;
  the constant case has zero translated truncations. The evaluation
  $X^d(b_i)$ represents a homogeneous element of weight
  $\operatorname{wt}(d)$, so its ordinal value is below
  $\omega^{\operatorname{wt}(d)+1}$. Sufficiently late translated
  truncations therefore have ordinal value below
  $\omega^{\operatorname{wt}(d)}\le\omega^\alpha$.

  In the nonconstant case, split off one factor $X_i$ and apply
  \ref{lem:polynomial-convolution-formula}. The two endpoint summands, after
  identifying the unique polynomial representatives of the untruncated
  factors, give the ordinary product rule. At every interior cutoff, the
  split-off lift is properly translated, so its representative has monomial
  weights strictly below $w_i$. The induction expansion of the other factor
  has already replaced at least one variable weight by a smaller ordinal.
  Their product therefore replaces at least two weights, and an inductive
  remainder remains of the stated form after multiplication by $X_i$.

  Finally expand $G$ over its finite monomial support, choose one common
  punctured interval, and sum the monomial identities. The ultrametric
  inequality gives the asserted ordinal-value bound.
  -/)]
theorem exists_forall_pol_translatedTruncation_aeval (H : MvPolynomial ι K)
    (hH : ∀ d ∈ H.support, Finsupp.weight wt d ≤ α) (hvars : ∀ i ∈ H.vars, wt i < α) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      ordinalValue (translatedTruncation ((aeval σ.lift H : Series K) : K⟦ℝ⟧) γ) < ω^ α ∧
      ∃ E : MvPolynomial ι K,
        (∀ d' ∈ E.support, ∃ d ∈ H.support, ∃ k, 2 ≤ k ∧
          TermDegree wt d k (Finsupp.weight wt d')) ∧
        σ.pol hx α (translatedTruncation ((aeval σ.lift H : Series K) : K⟦ℝ⟧) γ) =
          ∑ j ∈ H.vars, σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ) * pderiv j H +
            E := by
  classical
  -- the expansions of the monomials, on a common interval `(-ε, 0)`
  obtain ⟨ε, hε, hmono⟩ := exists_forall_of_forall_exists_forall H.support
    (fun d γ ↦ ordinalValue (translatedTruncation
        ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ) < ω^ α ∧
      ∃ E : MvPolynomial ι K, IsRemainder wt d E ∧
        σ.pol hx α (translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ)
          = ∑ j ∈ d.support, σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ) *
              pderiv j (monomial d 1) + E)
    fun d hd ↦ σ.exists_forall_pol_translatedTruncation_aeval_monomial hx hinj d (hH d hd)
      fun i hi ↦ hvars i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)
  refine ⟨ε, hε, fun γ hγε hγ0 ↦ ?_⟩
  -- the translated truncation of `H(b_𝓑)` as a sum over the monomials of `H`
  have hmon : ∀ d, monomial d (H.coeff d) = C (H.coeff d) * monomial d (1 : K) := fun d ↦ by
    rw [C_mul_monomial, mul_one]
  have hcoe : ∀ d, aeval σ.lift (monomial d (H.coeff d)) =
      (HahnSeries.Nonpositive.C : K →+* Series K) (H.coeff d) *
        aeval σ.lift (monomial d (1 : K)) := fun d ↦ by
    rw [hmon, map_mul, aeval_C, HahnSeries.Nonpositive.algebraMap_apply]
  have hsplit : translatedTruncation ((aeval σ.lift H : Series K) : K⟦ℝ⟧) γ =
      ∑ d ∈ H.support, (HahnSeries.Nonpositive.C : K →+* Series K) (H.coeff d) *
        translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ := by
    conv_lhs => rw [H.as_sum, map_sum]
    rw [AddSubmonoidClass.coe_finsetSum, ← translatedTruncationAddMonoidHom_apply, map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [translatedTruncationAddMonoidHom_apply, hcoe, Subring.coe_mul,
      HahnSeries.Nonpositive.coe_C, translatedTruncation_C_mul]
  have hval : ∀ d ∈ H.support,
      ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) (H.coeff d) *
        translatedTruncation ((aeval σ.lift (monomial d (1 : K)) : Series K) : K⟦ℝ⟧) γ) < ω^ α :=
    fun d hd ↦ ordinalValue_C_mul_lt _ (hmono γ hγε hγ0 d hd).1
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    exact ordinalValue_sum_lt _ _ (NatOrdinal.wpow_pos α) hval
  -- the expansions of the monomials
  choose E hE hexp using fun d (hd : d ∈ H.support) ↦ (hmono γ hγε hγ0 d hd).2
  refine ⟨∑ d ∈ H.support.attach, C (H.coeff d.1) * E d.1 d.2, fun d' hd' ↦ ?_, ?_⟩
  · obtain ⟨d, _, hd'd⟩ := Finset.mem_biUnion.mp (support_sum hd')
    have hd'E : d' ∈ (E d.1 d.2).support := by
      rw [C_mul'] at hd'd
      exact support_smul hd'd
    obtain ⟨k, hk, hT⟩ := hE d.1 d.2 d' hd'E
    exact ⟨d.1, d.2, k, hk, hT⟩
  -- abbreviations
  set T : ι → MvPolynomial ι K := fun j ↦ σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ)
    with hTdef
  have hsupp : ∀ d : ι →₀ ℕ, ∀ j, j ∉ d.support → pderiv j (monomial d (1 : K)) = 0 :=
    fun d j hj ↦ by
      rw [pderiv_monomial, Finsupp.notMem_support_iff.mp hj, Nat.cast_zero, mul_zero, monomial_zero]
  have hsub : ∀ d ∈ H.support, d.support ⊆ H.vars := fun d hd j hj ↦
    (mem_vars_iff_mem_support j).mpr ⟨d, hd, hj⟩
  -- the left-hand side
  have hlhs : σ.pol hx α (translatedTruncation ((aeval σ.lift H : Series K) : K⟦ℝ⟧) γ) =
      ∑ d ∈ H.support.attach, (C (H.coeff d.1) * ∑ j ∈ H.vars, T j * pderiv j (monomial d.1 1) +
        C (H.coeff d.1) * E d.1 d.2) := by
    rw [hsplit, σ.pol_sum hx hinj _ _ hval, ← Finset.sum_attach H.support]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [σ.pol_C_mul hx hinj _ (hmono γ hγε hγ0 _ d.2).1, hexp d.1 d.2, mul_add]
    congr 2
    exact Finset.sum_subset (hsub d.1 d.2) fun j _ hj ↦ by rw [hsupp d.1 j hj, mul_zero]
  -- the right-hand side
  have hpd : ∀ j, pderiv j H =
      ∑ d ∈ H.support.attach, C (H.coeff d.1) * pderiv j (monomial d.1 1) := fun j ↦ by
      conv_lhs => rw [H.as_sum, map_sum, ← Finset.sum_attach H.support]
      exact Finset.sum_congr rfl fun d _ ↦ by rw [hmon, pderiv_C_mul]
  rw [hlhs, Finset.sum_add_distrib]
  congr 1
  simp only [hpd, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

omit [DecidableEq ι] in
/-- **The Leibniz rule with remainder, differentiated.** Differentiating the Leibniz rule for `F`
with respect to `X_v` and comparing with the rule for `∂F/∂X_v`: for all `γ < 0` sufficiently
close to `0`,
`pol((∂F/∂X_v)(b_𝓑)^{|γ}) = ∂/∂X_v [pol(F(b_𝓑)^{|γ})] - ∑_j (∂/∂X_v pol(b_j^{|γ})) ∂F/∂X_j
- ∂R_γ/∂X_v + R'_γ`, where every monomial of `R_γ`, resp. `R'_γ`, has the degree of a term of the
expansion of a monomial of `F`, resp. of `∂F/∂X_v`, with at least two truncated factors. -/
@[blueprint "lem:differentiated-leibniz-remainder"
  (phase := "Translated truncations")
  (title := "Differentiated polynomial Leibniz rule")
  (statement := /--
    Let $K$ be a field, let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$ with
    $x_i\in\mathrm P_{w_i}$, and choose series $b_i$ representing the $x_i$.
    Assume that evaluation at $(x_i)$ is injective in every weighted degree
    below $\alpha<\omega_1$, and write $P_a$ for the polynomial representative
    of a series $a$ of ordinal value below $\omega^\alpha$.

    Let $F\in K[X_i:i\in I]$. Suppose every monomial of $F$ has weight at most
    $\alpha$, and $w_i<\alpha$ for every variable $X_i$ occurring in $F$. For
    every $v\in I$ and every $\gamma<0$ sufficiently close to $0$, there are
    polynomials $R_\gamma,R'_\gamma$ such that
    \[
      P_{((\partial_vF)(b_i))^{|\gamma}}
       =\partial_vP_{(F(b_i))^{|\gamma}}
       -\sum_{j\in\operatorname{vars}(F)}
          (\partial_vP_{b_j^{|\gamma}})\,\partial_jF
       -\partial_vR_\gamma+R'_\gamma,
    \]
    where every monomial of $R_\gamma$, respectively $R'_\gamma$, is obtained
    from a monomial of $F$, respectively $\partial_vF$, by replacing the
    weights of at least two variable factors, counted with multiplicity, by
    strictly smaller ordinals.
  -/)
  (proof := /--
  Partial differentiation weakly decreases every monomial weight and
  introduces no new variables. Hence \ref{lem:leibniz-remainder} applies to
  both $F$ and $\partial_vF$ on one
  common punctured interval. Differentiate the expansion for $F$, use the
  polynomial product rule and commutativity of partial derivatives, and
  subtract the expansion for $\partial_vF$. Variables of $F$ absent from
  $\partial_vF$ contribute zero, so both sums may be indexed by
  $\operatorname{vars}(F)$. Rearrangement gives the displayed identity while
  preserving the two remainder conditions.
  -/)]
theorem exists_forall_pol_translatedTruncation_aeval_pderiv (F : MvPolynomial ι K)
    (hF : ∀ d ∈ F.support, Finsupp.weight wt d ≤ α) (hvars : ∀ i ∈ F.vars, wt i < α) (v : ι) :
    ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 →
      ∃ E E' : MvPolynomial ι K,
        (∀ d' ∈ E.support, ∃ d ∈ F.support, ∃ k, 2 ≤ k ∧
          TermDegree wt d k (Finsupp.weight wt d')) ∧
        (∀ d' ∈ E'.support, ∃ d ∈ (pderiv v F).support, ∃ k, 2 ≤ k ∧
          TermDegree wt d k (Finsupp.weight wt d')) ∧
        σ.pol hx α (translatedTruncation ((aeval σ.lift (pderiv v F) : Series K) : K⟦ℝ⟧) γ) =
          pderiv v (σ.pol hx α (translatedTruncation ((aeval σ.lift F : Series K) : K⟦ℝ⟧) γ)) -
            ∑ j ∈ F.vars, pderiv v (σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ)) *
              pderiv j F - pderiv v E + E' := by
  classical
  have hΘ : ∀ d ∈ (pderiv v F).support, Finsupp.weight wt d ≤ α := fun d' hd' ↦ by
    obtain ⟨d, hd, hw⟩ := exists_add_eq_weight_of_mem_support_pderiv wt hd'
    exact (NatOrdinal.le_add_right.trans hw.le).trans (hF d hd)
  have hvarsΘ : ∀ i ∈ (pderiv v F).vars, wt i < α := fun i hi ↦ hvars i (vars_pderiv_subset v F hi)
  obtain ⟨ε₁, hε₁, h₁⟩ := σ.exists_forall_pol_translatedTruncation_aeval hx hinj F hF hvars
  obtain ⟨ε₂, hε₂, h₂⟩ := σ.exists_forall_pol_translatedTruncation_aeval hx hinj (pderiv v F) hΘ
    hvarsΘ
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun γ hγε hγ0 ↦ ?_⟩
  have hγ₁ : -ε₁ < γ := by have := min_le_left ε₁ ε₂; linarith
  have hγ₂ : -ε₂ < γ := by have := min_le_right ε₁ ε₂; linarith
  obtain ⟨-, E, hE, hexpF⟩ := h₁ γ hγ₁ hγ0
  obtain ⟨-, E', hE', hexpΘ⟩ := h₂ γ hγ₂ hγ0
  refine ⟨E, E', hE, hE', ?_⟩
  set T : ι → MvPolynomial ι K := fun j ↦ σ.pol hx α (translatedTruncation (σ.lift j : K⟦ℝ⟧) γ)
    with hTdef
  -- differentiate the expansion of `F`
  have hdF : pderiv v (σ.pol hx α (translatedTruncation ((aeval σ.lift F : Series K) : K⟦ℝ⟧) γ)) =
      ∑ j ∈ F.vars, pderiv v (T j) * pderiv j F + ∑ j ∈ F.vars, T j * pderiv j (pderiv v F) +
        pderiv v E := by
    rw [hexpF, map_add, map_sum, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [pderiv_mul, pderiv_pderiv_comm]
  -- the expansion of `∂F/∂X_v`, summed over the variables of `F`
  have hexpΘ' : σ.pol hx α (translatedTruncation ((aeval σ.lift (pderiv v F) : Series K) : K⟦ℝ⟧) γ)
      = ∑ j ∈ F.vars, T j * pderiv j (pderiv v F) + E' := by
    rw [hexpΘ]
    congr 1
    exact Finset.sum_subset (vars_pderiv_subset v F) fun j _ hj ↦ by
      rw [pderiv_eq_zero_of_notMem_vars hj, mul_zero]
  rw [hexpΘ', hdF]
  ring

end Lifts

end Berarducci
