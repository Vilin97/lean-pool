/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LiftFamily
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermSuccessorStep
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.LimitOrdinalContradiction
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Separation


/-!
# Relations of limit-ordinal degree split at a Cantor cutoff

When the degree is a nonzero limit ordinal, choose a variable of maximal weight in a polynomial
relation. The configuration studied here occurs when its weight has a Cantor term below the least
term of the leading coefficient's degree. `LimitOrdinalRelationAtCutoff` records the relation, the
separating cutoff, and the two bounds used by the derivative argument. The results below derive the
required ordinal identities and exclude such a relation.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter MvPolynomial HahnSeries HahnSeries.Nonpositive

public noncomputable section

namespace HahnSeries.Germ

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

variable {ι : Type w} {wt : ι → NatOrdinal.{u}}
  {xg : ι → (cantorBendixsonDegreeValuation (G := G) (R := K)).AssociatedGraded}
variable (σ : LiftFamily wt xg)

/-- A relation whose degree is a limit ordinal, a variable of maximal degree, a cutoff below every
term of the leading coefficient's degree, and uniform bounds for translated truncations and the
Leibniz remainder. -/
structure LimitOrdinalRelationAtCutoff (α : NatOrdinal.{u}) where
  /-- The relation. -/
  F : MvPolynomial ι K
  hom : IsWeightedHomogeneous wt F α
  eval_zero : aeval xg F = 0
  ne_zero : F ≠ 0
  vars_lt : ∀ i ∈ F.vars, wt i < α
  vars_limit : ∀ i ∈ F.vars, (wt i).constantCoeff = 0
  /-- A variable of maximal degree. -/
  B₀ : ι
  mem : B₀ ∈ F.vars
  max : ∀ i ∈ F.vars, wt i ≤ wt B₀
  /-- A cutoff exponent `β` such that every term of `deg H_D` is at least `ω^β`. -/
  β : NatOrdinal
  /-- The degree `α ⊖ (δ ⊙ D)` of `H_D`, the coefficient of `X_{B₀}^D` in `F`. -/
  degHD : NatOrdinal
  hdegHD : degHD + degreeOf B₀ F • wt B₀ = α
  degHD_terms : ∀ t ∈ degHD.val.additivePrincipalTerms, (ω^ β).val ≤ t
  degHD_ne_zero : degHD ≠ 0
  /-- The degree `δ = deg B₀` has a term below `ω^β`. -/
  term_lt : NatOrdinal.leastTerm (wt B₀) < ω^ β
  /-- The bound `λ₀`: the terms of the remainder of the Leibniz rule have degree below
  `α_{≥β} ⊕ λ₀`, and the translated truncations of `F(b_𝓑)` have ordinal value below `ω^{α₁}`
  with `α₁ ≤ α_{≥β} ⊕ λ₀`. -/
  lam₀ : NatOrdinal
  lam₀_lt : lam₀ < NatOrdinal.partLT β α
  /-- An upper bound for the degrees of sufficiently late translated truncations of the
  relation. -/
  α₁ : NatOrdinal
  α₁_le : α₁ ≤ NatOrdinal.partGE β α + lam₀
  α₁_le_α : α₁ ≤ α
  truncation_lt : ∀ᶠ γ in 𝓝[<] (0 : G),
    cantorBendixsonDegreeValuation (translatedTruncLE γ (aeval σ.lift F)) <
      (α₁ : WithBot NatOrdinal)
  remainder_lt : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ →
    ρ < NatOrdinal.partGE β α + lam₀

namespace LimitOrdinalRelationAtCutoff

variable {σ} {α : NatOrdinal.{u}} (S : LimitOrdinalRelationAtCutoff σ α)
variable (hx : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K
    (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)

/-- The part `α_{≥β}` of `α` at or above `β`. -/
def αGE : NatOrdinal := NatOrdinal.partGE S.β α

/-- The part `α_{<β}` of `α` below `β`. -/
def αLT : NatOrdinal := NatOrdinal.partLT S.β α

/-- The part `(deg B)_{<β}` of the degree of a variable `B` below `β`. -/
def degLT (i : ι) : NatOrdinal := NatOrdinal.partLT S.β (wt i)

/-- `H := ∂F/∂X_{B₀}`, the partial derivative of `F` at its variable of maximal degree. -/
def H : MvPolynomial ι K := pderiv S.B₀ S.F

/-- The part of `deg B` below `β` equals the part of `α` below `β`. -/
def LowDegreePartEq (i : ι) : Prop := S.degLT i = S.αLT

/-- The part of `deg B` below `β` precedes `λ₀` in the algebraic order. -/
def LowDegreePartAlgebraicLE (i : ι) : Prop := NatOrdinal.AlgebraicLE (S.degLT i) S.lam₀

theorem αGE_def : S.αGE = NatOrdinal.partGE S.β α := (rfl)
theorem αLT_def : S.αLT = NatOrdinal.partLT S.β α := (rfl)
theorem degLT_def (i : ι) : S.degLT i = NatOrdinal.partLT S.β (wt i) := (rfl)
theorem H_def : S.H = pderiv S.B₀ S.F := (rfl)
theorem lowDegreePartEq_iff (i : ι) : S.LowDegreePartEq i ↔ S.degLT i = S.αLT := (Iff.rfl)
theorem lowDegreePartAlgebraicLE_iff (i : ι) :
    S.LowDegreePartAlgebraicLE i ↔ NatOrdinal.AlgebraicLE (S.degLT i) S.lam₀ := (Iff.rfl)

theorem αGE_add_αLT : S.αGE + S.αLT = α := NatOrdinal.partGE_add_partLT _ _

theorem partGE_add_degLT (i : ι) : NatOrdinal.partGE S.β (wt i) + S.degLT i = wt i :=
  NatOrdinal.partGE_add_partLT _ _

theorem degLT_lt_wpow (i : ι) : S.degLT i < ω^ S.β := NatOrdinal.partLT_lt _ _

theorem αLT_lt_wpow : S.αLT < ω^ S.β := NatOrdinal.partLT_lt _ _

theorem lam₀_lt_wpow : S.lam₀ < ω^ S.β := S.lam₀_lt.trans S.αLT_lt_wpow

theorem partGE_αGE_add_lam₀ :
    NatOrdinal.partGE S.β (NatOrdinal.partGE S.β α + S.lam₀) =
      NatOrdinal.partGE S.β α := by
  rw [NatOrdinal.partGE_add, NatOrdinal.partGE_partGE,
    NatOrdinal.partGE_eq_zero_of_lt S.lam₀_lt_wpow, add_zero]

theorem partLT_αGE_add_lam₀ :
    NatOrdinal.partLT S.β (NatOrdinal.partGE S.β α + S.lam₀) = S.lam₀ := by
  have := NatOrdinal.partGE_add_partLT S.β (NatOrdinal.partGE S.β α + S.lam₀)
  rw [S.partGE_αGE_add_lam₀] at this
  exact add_left_cancel this

theorem partLT_degHD : NatOrdinal.partLT S.β S.degHD = 0 :=
  NatOrdinal.partLT_eq_zero_of_forall_le S.degHD_terms

theorem αLT_eq_nsmul_degLT : S.αLT = degreeOf S.B₀ S.F • S.degLT S.B₀ := by
  have h : NatOrdinal.partLT S.β α =
      NatOrdinal.partLT S.β (S.degHD + degreeOf S.B₀ S.F • wt S.B₀) :=
    congrArg _ S.hdegHD.symm
  rw [αLT, h, NatOrdinal.partLT_add, S.partLT_degHD, zero_add, NatOrdinal.partLT_nsmul]
  rfl

/-- In every monomial of `F` the parts below `β` add up to `α_{<β}`. -/
theorem sum_degLT_eq_αLT {d : ι →₀ ℕ} (hd : d ∈ S.F.support) :
    ∑ i ∈ d.support, d i • S.degLT i = S.αLT := by
  simpa [degLT, αLT, Finsupp.weight_apply, Finsupp.sum] using
    (S.hom.map_weight (NatOrdinal.partLTAddMonoidHom S.β) (mem_support_iff.mp hd))

/-- In every monomial of `F` the parts at or above `β` add up to `α_{≥β}`. -/
theorem sum_partGE_eq_αGE {d : ι →₀ ℕ} (hd : d ∈ S.F.support) :
    ∑ i ∈ d.support, d i • NatOrdinal.partGE S.β (wt i) = S.αGE := by
  simpa [αGE, Finsupp.weight_apply, Finsupp.sum] using
    (S.hom.map_weight (NatOrdinal.partGEAddMonoidHom S.β) (mem_support_iff.mp hd))

variable (hxms : OrdinalGraded.IsMinimalSystem
  (DirectSum.rangeLof K (cantorBendixsonDegreeValuation (G := G) (R := K)).Component) wt xg)
include hx

theorem β_ne_zero : S.β ≠ 0 := by
  intro h
  have hbad := S.term_lt
  rw [h, NatOrdinal.wpow_zero] at hbad
  exact absurd (NatOrdinal.one_le_leastTerm (hx.ne_zero S.B₀)) (not_le.mpr hbad)

/-- For every variable `B` of `F`, `(deg B)_{<β}` has finite part `0`. -/
theorem degLT_constantCoeff {i : ι} (hi : i ∈ S.F.vars) : (S.degLT i).constantCoeff = 0 := by
  rw [degLT, NatOrdinal.constantCoeff_partLT (S.β_ne_zero hx)]
  exact S.vars_limit i hi

/-- If `(deg B)_{<β} ≠ 0`, the last term of its Cantor normal form is `ω^e` with `e ≠ 0`. -/
theorem exists_leastTerm_degLT {i : ι} (hi : i ∈ S.F.vars) (h : S.degLT i ≠ 0) :
    ∃ e, e ≠ 0 ∧ NatOrdinal.leastTerm (S.degLT i) = ω^ e := by
  obtain ⟨e, he⟩ := NatOrdinal.exists_leastTerm_eq_wpow h
  refine ⟨e, fun he0 ↦ ?_, he⟩
  rw [he0, NatOrdinal.wpow_zero, ← NatOrdinal.removeLeastTerm_add_one_eq_self_iff] at he
  have := S.degLT_constantCoeff hx hi
  rw [← he, show (1 : NatOrdinal) = ((1 : ℕ) : NatOrdinal) by rw [Nat.cast_one],
    NatOrdinal.constantCoeff_add_natCast] at this
  omega

/-- `(deg B₀)_{<β} ≠ 0`: the variable of maximal degree has a term below `ω^β`. -/
theorem degLT_B₀_ne_zero : S.degLT S.B₀ ≠ 0 := by
  obtain ⟨e, he⟩ := NatOrdinal.exists_leastTerm_eq_wpow (hx.ne_zero S.B₀)
  have hlt : e < S.β := by
    have := S.term_lt
    rwa [he, NatOrdinal.wpow_lt_wpow] at this
  exact NatOrdinal.partLT_ne_zero_of_leastTerm_lt (hx.ne_zero S.B₀) he hlt

theorem αLT_ne_zero : S.αLT ≠ 0 := by
  rw [S.αLT_eq_nsmul_degLT]
  exact NatOrdinal.nsmul_ne_zero_of_ne_zero (S.degLT_B₀_ne_zero hx)
    (Nat.one_le_iff_ne_zero.mpr (mem_vars_iff_degreeOf_ne_zero.mp S.mem))

theorem αLT_constantCoeff : S.αLT.constantCoeff = 0 := by
  rw [S.αLT_eq_nsmul_degLT, NatOrdinal.constantCoeff_nsmul, S.degLT_constantCoeff hx S.mem,
    mul_zero]

/-! ### `X_{B₀}` occurs linearly in `F` -/

omit hx in
/-- `(deg B₀)_{<β} = α_{<β}`, given that `X_{B₀}` occurs linearly in `F`.

Linearity is the one step that ordinal arithmetic does not supply. It is the
linear-maximality argument, which each setting proves by its own truncation analysis, so it enters
here as a hypothesis. -/
theorem degLT_B₀ (hD : degreeOf S.B₀ S.F = 1) : S.degLT S.B₀ = S.αLT := by
  rw [S.αLT_eq_nsmul_degLT, hD, one_smul]

omit hx in
theorem lowDegreePartEq_B₀ (hD : degreeOf S.B₀ S.F = 1) : S.LowDegreePartEq S.B₀ := S.degLT_B₀ hD

omit hx in
theorem degHD_add (hD : degreeOf S.B₀ S.F = 1) : S.degHD + wt S.B₀ = α := by
  have := S.hdegHD
  rwa [hD, one_smul] at this

omit hx in
/-- `H = ∂F/∂X_{B₀}` is homogeneous of degree `α ⊖ δ`. -/
theorem H_hom (hD : degreeOf S.B₀ S.F = 1) : IsWeightedHomogeneous wt S.H S.degHD :=
  isWeightedHomogeneous_pderiv wt S.hom S.B₀ (S.degHD_add hD)

omit hx in
theorem H_ne_zero : S.H ≠ 0 := pderiv_ne_zero_of_mem_vars S.mem

omit hx in
/-- Every monomial of `F` contains `X_{B₀}` at most once. -/
theorem apply_B₀_le_one {d : ι →₀ ℕ} (hD : degreeOf S.B₀ S.F = 1) (hd : d ∈ S.F.support) :
    d S.B₀ ≤ 1 := by
  have := monomial_le_degreeOf S.B₀ hd
  rwa [hD] at this

omit hx in
/-- Every variable `B` of `H` has `(deg B)_{<β} = 0`. -/
theorem degLT_eq_zero_of_mem_vars_H {i : ι} (hD : degreeOf S.B₀ S.F = 1) (hi : i ∈ S.H.vars) :
    S.degLT i = 0 := by
  classical
  obtain ⟨d', hd', hid'⟩ := (mem_vars_iff_mem_support i).mp hi
  obtain ⟨d, hd, hdv, rfl⟩ := exists_mem_support_of_mem_support_pderiv hd'
  have hd1 : d S.B₀ = 1 :=
    le_antisymm (S.apply_B₀_le_one hD hd) (Nat.one_le_iff_ne_zero.mpr hdv)
  -- `i ≠ B₀`, since `B₀` occurs once
  have hi0 : i ≠ S.B₀ := by
    rintro rfl
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_same, hd1] at hid'
    exact hid' rfl
  have hid : i ∈ d.support := by
    rw [Finsupp.mem_support_iff] at hid' ⊢
    rw [Finsupp.tsub_apply, Finsupp.single_apply, ite_eq_right hi0.symm, Nat.sub_zero] at hid'
    exact hid'
  -- the parts below `β` of `d` add up to `α_{<β} = (deg B₀)_{<β}`, and `B₀` contributes all of it
  have hsum := S.sum_degLT_eq_αLT hd
  have hB₀d : S.B₀ ∈ d.support := Finsupp.mem_support_iff.mpr hdv
  rw [← Finset.add_sum_erase _ _ hB₀d, hd1, one_smul, S.degLT_B₀ hD] at hsum
  have hrest : ∑ j ∈ d.support.erase S.B₀, d j • S.degLT j = 0 := add_eq_left.mp hsum
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ zero_le)] at hrest
  have := hrest i (Finset.mem_erase.mpr ⟨hi0, hid⟩)
  rcases (smul_eq_zero.mp this) with h | h
  · exact absurd h (Finsupp.mem_support_iff.mp hid)
  · exact h

/-! ### Two factors with nonzero parts below `β` -/

omit hx in
/-- **The bound on a term of the remainder with two truncated factors.** If `d' · X_i · X_j` is a
monomial of `F`, then `(deg d')_{<β} ⊕ ρᵢ ⊕ ρⱼ ≤ λ₀` for all `ρᵢ < S.degLT i`,
`ρⱼ < S.degLT j`. -/
theorem pair_bound {d' : ι →₀ ℕ} {i j : ι}
    (hd : d' + Finsupp.single i 1 + Finsupp.single j 1 ∈ S.F.support) {ρᵢ ρⱼ : NatOrdinal}
    (hρᵢ : ρᵢ < S.degLT i) (hρⱼ : ρⱼ < S.degLT j) :
    NatOrdinal.partLT S.β (Finsupp.weight wt d') + ρᵢ + ρⱼ ≤ S.lam₀ :=
  MvPolynomial.pair_bound_of_forall_termDegree_lt S.hom S.lam₀_lt S.remainder_lt hd hρᵢ hρⱼ

/-! ### Low-degree parts and the generators considered at a variable -/

/-- A variable has a proper low-degree part outside the algebraic bound when its part below the
cutoff is nonzero, differs from the low part of `α`, and does not precede the bound in the
algebraic order. -/
def HasProperLowDegreePartNotAlgebraicLE (i : ι) : Prop :=
  i ∈ S.F.vars ∧ S.degLT i ≠ 0 ∧ ¬ S.LowDegreePartEq i ∧ ¬ S.LowDegreePartAlgebraicLE i

omit hx in
theorem hasProperLowDegreePartNotAlgebraicLE_iff (i : ι) :
    S.HasProperLowDegreePartNotAlgebraicLE i ↔
      i ∈ S.F.vars ∧ S.degLT i ≠ 0 ∧ ¬ S.LowDegreePartEq i ∧
        ¬ S.LowDegreePartAlgebraicLE i := Iff.rfl

omit hx in
/-- For every variable `B` of `F`, `(deg B)_{<β} ≼ α_{<β}` in the algebraic order. -/
theorem degLT_algebraicLE_αLT {i : ι} (hi : i ∈ S.F.vars) :
    NatOrdinal.AlgebraicLE (S.degLT i) S.αLT := by
  classical
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp hi
  have hsum := S.sum_degLT_eq_αLT hd
  rw [← Finset.add_sum_erase _ _ hid] at hsum
  have h1 : d i • S.degLT i = S.degLT i + (d i - 1) • S.degLT i := by
    conv_lhs => rw [show d i = d i - 1 + 1 from
      (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hid))).symm]
    rw [succ_nsmul']
  rw [h1, add_assoc] at hsum
  rw [← hsum]
  exact NatOrdinal.algebraicLE_add_right _ _

omit hx in
/-- A monomial containing `X_i` twice is `d' · X_i · X_i`. -/
theorem exists_eq_add_single_add_single_self {d : ι →₀ ℕ} {i : ι} (h : 2 ≤ d i) :
    ∃ d' : ι →₀ ℕ, d = d' + Finsupp.single i 1 + Finsupp.single i 1 := by
  classical
  refine ⟨d - Finsupp.single i 1 - Finsupp.single i 1, ?_⟩
  have h1 : Finsupp.single i 1 ≤ d - Finsupp.single i 1 := by
    rw [Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have h2 : Finsupp.single i 1 ≤ d := Finsupp.single_le_iff.mpr (by omega)
  rw [tsub_add_cancel_of_le h1, tsub_add_cancel_of_le h2]

omit hx in
/-- A monomial containing distinct variables `X_i` and `X_u` is `d' · X_i · X_u`. -/
theorem exists_eq_add_single_add_single {d : ι →₀ ℕ} {i u : ι} (hi : i ∈ d.support)
    (hu : u ∈ d.support) (hui : u ≠ i) :
    ∃ d' : ι →₀ ℕ, d = d' + Finsupp.single i 1 + Finsupp.single u 1 := by
  classical
  refine ⟨d - Finsupp.single i 1 - Finsupp.single u 1, ?_⟩
  have hdi : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hdu : 1 ≤ d u := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hu)
  have h1 : Finsupp.single u 1 ≤ d - Finsupp.single i 1 := by
    rw [Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hui)]
    omega
  have h2 : Finsupp.single i 1 ≤ d := Finsupp.single_le_iff.mpr hdi
  rw [add_right_comm, tsub_add_cancel_of_le h1, tsub_add_cancel_of_le h2]

omit hx in
/-- For a monomial `d' · X_i · X_u` of `F`, its three low-degree parts sum to `α_{<β}`. -/
theorem partLT_weight_add_degLT_add_degLT {d' : ι →₀ ℕ} {i u : ι}
    (hd : d' + Finsupp.single i 1 + Finsupp.single u 1 ∈ S.F.support) :
    NatOrdinal.partLT S.β (Finsupp.weight wt d') + S.degLT i + S.degLT u = S.αLT := by
  rw [S.αLT_def, S.degLT_def, S.degLT_def]
  exact MvPolynomial.partLT_weight_add_partLT_add_partLT S.hom hd

/-- A variable whose proper low-degree part does not precede `λ₀` occurs with exponent `1` in every
monomial of `F` that contains it. -/
theorem apply_eq_one_of_hasProperLowDegreePartNotAlgebraicLE {i : ι}
    (hi : S.HasProperLowDegreePartNotAlgebraicLE i) {d : ι →₀ ℕ}
    (hd : d ∈ S.F.support) (hid : i ∈ d.support) : d i = 1 := by
  obtain ⟨hiv, ht, -, hdiff⟩ := hi
  by_contra hne
  have h2 : 2 ≤ d i := by
    have := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hid)
    omega
  obtain ⟨d', rfl⟩ := exists_eq_add_single_add_single_self h2
  obtain ⟨e, he, hte⟩ := S.exists_leastTerm_degLT hx hiv ht
  have hμ := S.partLT_weight_add_degLT_add_degLT hd
  have hlμ : S.lam₀ < S.αLT := S.lam₀_lt
  exact hdiff ((S.lowDegreePartAlgebraicLE_iff i).mpr
    (NatOrdinal.algebraicLE_of_forall_add_add_le ht ht hte hte he (hμ ▸ hlμ)
      fun ρ₁ ρ₂ hρ₁ hρ₂ ↦ S.pair_bound hd hρ₁ hρ₂))

/-- If a nonzero low-degree factor occurs with a variable whose proper low-degree part does not
precede `λ₀`, its last Cantor exponent is larger and detects the same high window in `λ₀` and
`α_{<β}`. -/
theorem lt_and_partGE_eq_of_hasProperLowDegreePartNotAlgebraicLE {i : ι}
    (hi : S.HasProperLowDegreePartNotAlgebraicLE i) {d : ι →₀ ℕ}
    (hd : d ∈ S.F.support) (hid : i ∈ d.support) {u : ι} (hud : u ∈ d.support)
    (hui : u ≠ i) (htu : S.degLT u ≠ 0) {eᵢ eᵤ : NatOrdinal}
    (heᵢ : NatOrdinal.leastTerm (S.degLT i) = ω^ eᵢ)
    (heᵤ : NatOrdinal.leastTerm (S.degLT u) = ω^ eᵤ) :
    eᵢ < eᵤ ∧ NatOrdinal.partGE eᵤ S.lam₀ = NatOrdinal.partGE eᵤ S.αLT := by
  obtain ⟨hiv, hti, -, hdiff⟩ := id hi
  have hdiff' : ¬ NatOrdinal.AlgebraicLE (S.degLT i) S.lam₀ :=
    fun h ↦ hdiff ((S.lowDegreePartAlgebraicLE_iff i).mpr h)
  have hlμ : S.lam₀ < S.αLT := S.lam₀_lt
  have he0 : eᵢ ≠ 0 := by
    obtain ⟨e', he', hte'⟩ := S.exists_leastTerm_degLT hx hiv hti
    rw [heᵢ, NatOrdinal.wpow_inj] at hte'
    exact fun h ↦ he' (hte' ▸ h)
  obtain ⟨d', rfl⟩ := exists_eq_add_single_add_single hid hud hui
  have hμ := S.partLT_weight_add_degLT_add_degLT hd
  have hall : ∀ ρ₁ ρ₂ : NatOrdinal, ρ₁ < S.degLT i → ρ₂ < S.degLT u →
      NatOrdinal.partLT S.β (Finsupp.weight wt d') + ρ₁ + ρ₂ ≤ S.lam₀ :=
    fun ρ₁ ρ₂ hρ₁ hρ₂ ↦ S.pair_bound hd hρ₁ hρ₂
  rw [← hμ]
  exact NatOrdinal.lt_and_partGE_eq_of_not_algebraicLE hti htu heᵢ heᵤ he0 (hμ ▸ hlμ) hall
    hdiff'

omit hx in
/-- The last term of a finite sum of nonzero natural ordinals is the last term of a summand. -/
theorem exists_leastTerm_sum_eq {ι' : Type*} {s : Finset ι'} (hs : s.Nonempty)
    (f : ι' → NatOrdinal) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, NatOrdinal.leastTerm (∑ j ∈ s, f j) = NatOrdinal.leastTerm (f i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by rw [Finset.sum_singleton]⟩
  | cons a s ha hs ih =>
    obtain ⟨i, hi, hi'⟩ := ih fun j hj ↦ hf j (Finset.mem_cons_of_mem hj)
    have hsum : ∑ j ∈ s, f j ≠ 0 := by
      have hle : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum (fun j _ ↦ zero_le) hi
      exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr (hf i (Finset.mem_cons_of_mem hi))) hle).ne'
    rw [Finset.sum_cons, NatOrdinal.leastTerm_add (hf a (Finset.mem_cons_self a s)) hsum]
    rcases min_choice (NatOrdinal.leastTerm (f a))
        (NatOrdinal.leastTerm (∑ j ∈ s, f j)) with h | h
    · exact ⟨a, Finset.mem_cons_self a s, h⟩
    · exact ⟨i, Finset.mem_cons_of_mem hi, h.trans hi'⟩

/-- For a variable whose proper low-degree part does not precede `λ₀`, the last Cantor exponent of
its complementary low degree detects the same high window in `λ₀` and `α_{<β}`. -/
theorem partGE_lam₀_eq_of_hasProperLowDegreePartNotAlgebraicLE {i : ι}
    (hi : S.HasProperLowDegreePartNotAlgebraicLE i) {c ε : NatOrdinal}
    (hc : c + S.degLT i = S.αLT) (hε : NatOrdinal.leastTerm c = ω^ ε) :
    NatOrdinal.partGE ε S.lam₀ = NatOrdinal.partGE ε S.αLT := by
  classical
  obtain ⟨hiv, hti, htop, -⟩ := id hi
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp hiv
  have hd1 := S.apply_eq_one_of_hasProperLowDegreePartNotAlgebraicLE hx hi hd hid
  have hsum := S.sum_degLT_eq_αLT hd
  rw [← Finset.add_sum_erase _ _ hid, hd1, one_smul, add_comm] at hsum
  have hc' : ∑ j ∈ d.support.erase i, d j • S.degLT j = c :=
    add_right_cancel (hsum.trans hc.symm)
  set s := (d.support.erase i).filter fun j ↦ S.degLT j ≠ 0 with hsdef
  have hcs : ∑ j ∈ s, d j • S.degLT j = c := by
    rw [← hc', hsdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs with h
    · rfl
    · rw [not_not.mp h, smul_zero]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_add] at hc
    exact htop ((S.lowDegreePartEq_iff i).mpr hc)
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hcs
    exact hc0 hcs.symm
  have hsne : ∀ j ∈ s, d j • S.degLT j ≠ 0 := fun j hj ↦ by
    obtain ⟨hj, htj⟩ := Finset.mem_filter.mp hj
    exact NatOrdinal.nsmul_ne_zero_of_ne_zero htj
      (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (Finset.mem_erase.mp hj).2))
  obtain ⟨u, hus, hu⟩ := exists_leastTerm_sum_eq hs _ hsne
  obtain ⟨hu', htu⟩ := Finset.mem_filter.mp hus
  obtain ⟨hui, hud⟩ := Finset.mem_erase.mp hu'
  rw [hcs, hε, NatOrdinal.leastTerm_nsmul htu
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hud))] at hu
  obtain ⟨eᵢ, -, heᵢ⟩ := S.exists_leastTerm_degLT hx hiv hti
  exact
    (S.lt_and_partGE_eq_of_hasProperLowDegreePartNotAlgebraicLE
      hx hi hd hid hud hui htu heᵢ hu.symm).2

/-- A variable contributes to the derivative at `v'` when its low-degree part equals `α_{<β}`, or
when it has strictly larger degree and its proper low-degree part does not precede `λ₀`. -/
def ContributesToPartialDerivativeAt (v' v : ι) : Prop :=
  v ∈ S.F.vars ∧ (S.LowDegreePartEq v ∨ (S.HasProperLowDegreePartNotAlgebraicLE v ∧ wt v' < wt v))

omit hx in
theorem contributesToPartialDerivativeAt_iff (v' v : ι) :
    S.ContributesToPartialDerivativeAt v' v ↔
      v ∈ S.F.vars ∧
        (S.LowDegreePartEq v ∨ (S.HasProperLowDegreePartNotAlgebraicLE v ∧ wt v' < wt v)) :=
  Iff.rfl

omit hx in
theorem finite_setOf_contributesToPartialDerivativeAt (v' : ι) :
    Finite {v // S.ContributesToPartialDerivativeAt v' v} :=
  (S.F.vars.finite_toSet.subset fun v
    (hv : S.ContributesToPartialDerivativeAt v' v) ↦ hv.1).to_subtype

/-! ### The configuration does not occur -/

/-- The packaged polynomial and cutoff hypotheses imply the partial-derivative contradiction. -/
theorem false_of_lowDegreePartAlgebraicLE_decomposition (hD : degreeOf S.B₀ S.F = 1)
    (hpartials : ∀ v', v' ∈ S.F.vars → S.LowDegreePartAlgebraicLE v' →
      ∃ (s : Finset ι) (U : ι → MvPolynomial ι K),
        (∀ v ∈ s, S.ContributesToPartialDerivativeAt v' v) ∧
          (∀ v ∈ s, pderiv S.B₀ (U v) = 0) ∧
            pderiv v' S.F = ∑ v ∈ s, pderiv v S.F * U v) :
    False := by
  classical
  refine MvPolynomial.false_of_pderiv_eq_sum_of_partLT_ne_zero (lam₀ := S.lam₀) S.hom
    (le_of_eq hD) (S.degLT_B₀ hD) (S.H_hom hD) S.H_ne_zero S.degHD_ne_zero fun v' hv' hdiff ↦ ?_
  have hdiff' : S.LowDegreePartAlgebraicLE v' := hdiff
  obtain ⟨s, U, hs, hU, heq⟩ := hpartials v' hv' hdiff'
  refine ⟨s, U, fun v hv h0 ↦ ?_, hU, heq⟩
  rcases ((S.contributesToPartialDerivativeAt_iff v' v).mp (hs v hv)).2 with htop | ⟨hL, -⟩
  · exact S.αLT_ne_zero hx (by rw [← (S.lowDegreePartEq_iff v).mp htop]; exact h0)
  · exact ((S.hasProperLowDegreePartNotAlgebraicLE_iff v).mp hL).2.1 h0

end LimitOrdinalRelationAtCutoff

end HahnSeries.Germ

end
