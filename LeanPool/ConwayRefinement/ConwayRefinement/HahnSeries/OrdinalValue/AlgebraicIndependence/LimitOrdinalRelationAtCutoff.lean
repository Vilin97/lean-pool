/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LinearMaximal
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.LimitOrdinalContradiction
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AlgebraicOrder

/-!
# Relations of limit-ordinal degree split at a Cantor cutoff

Let `α` be a limit ordinal, assume evaluation is injective below `α`, and let `F ≠ 0` be
homogeneous of degree `α` with `F(𝓑) = 0`. Let `B₀` be a variable of `F` of maximal degree
`δ := deg B₀`,
`D` the degree of `F` in `X_{B₀}`, `H_D` the coefficient of `X_{B₀}^D` in `F`, homogeneous of
degree `α ⊖ (δ ⊙ D)`, and `ω^β` the last term of the Cantor normal form of `deg H_D`.
The leading-coefficient argument excludes a constant `H_D` and excludes the situation in which
every term of `δ` is at least `ω^β`. Thus `δ` has a term below `ω^β`. Write every degree as
`λ = λ_{≥β} ⊕ λ_{<β}`, its parts at or above and below `β`; for a variable `B` of `F` the
part `(deg B)_{<β}` is `S.degLT B`; `α_{≥β}`, `α_{<β}` are `S.αGE`, `S.αLT`. The bound on
remainder of the Leibniz rule (`RemainderBound`) and the ordinal values of the translated
truncations of `F(b_𝓑)` provide `λ₀ < α_{<β}` such that every term of the expansion of a
monomial of `F` by the convolution formula with at least two truncated factors has degree below
`α' := α_{≥β} ⊕ λ₀`, together with `α₁ ≤ α'` and `ε₁ > 0` such that
`v_J(F(b_𝓑)^{|γ}) < ω^{α₁}` for all `γ ∈ (-ε₁, 0)`.

`LimitOrdinalRelationAtCutoff` bundles this relation, cutoff, and the required bounds.
`LimitOrdinalRelationAtCutoff.HasCanonicalBounds` records the canonical choice obtained from the
last term of `deg H_D`. The first consequences are: `β ≠ 0`; every `(deg B)_{<β}` is a limit
ordinal or `0`;
`D = 1`; `(deg B₀)_{<β} = α_{<β}`; `H := ∂F/∂X_{B₀}` is nonzero and homogeneous of degree
`α ⊖ δ`; every variable of `H` has zero part below `β`; in every monomial of `F` the parts
below `β` add up to `α_{<β}`; and two factors with nonzero parts below `β` obey `pair_bound`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K] {ι : Type w} {wt : ι → NatOrdinal}
variable {x : ι → PrincipalSubring K}

namespace Lifts

variable (σ : Lifts wt x) {α : NatOrdinal}

/-- A homogeneous relation whose degree is a limit ordinal, a maximal variable, a Cantor cutoff,
and uniform bounds for translated truncations and the Leibniz remainder. -/
structure LimitOrdinalRelationAtCutoff (α : NatOrdinal) where
  /-- The relation. -/
  F : MvPolynomial ι K
  hom : IsWeightedHomogeneous wt F α
  eval_zero : aeval x F = 0
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
  `α_{≥β} ⊕ λ₀`, and the translated truncations of `F(b_𝓑)` have ordinal value below
  `ω^{α₁}` with `α₁ ≤ α_{≥β} ⊕ λ₀`. -/
  lam₀ : NatOrdinal
  lam₀_lt : lam₀ < NatOrdinal.partLT β α
  α₁ : NatOrdinal
  α₁_le : α₁ ≤ NatOrdinal.partGE β α + lam₀
  α₁_le_α : α₁ ≤ α
  ε₁ : ℝ
  ε₁_pos : 0 < ε₁
  truncation_lt : ∀ γ : ℝ, -ε₁ < γ → γ < 0 →
    ordinalValue (translatedTruncation ((aeval σ.lift F : Series K) : K⟦ℝ⟧) γ) < ω^ α₁
  remainder_lt : ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k →
    TermDegree wt d k ρ → ρ < NatOrdinal.partGE β α + lam₀

namespace LimitOrdinalRelationAtCutoff

variable {σ} (S : σ.LimitOrdinalRelationAtCutoff α)

/-- The part `α_{≥β}` of `α` at or above `β`. -/
def αGE : NatOrdinal := NatOrdinal.partGE S.β α

/-- The part `α_{<β}` of `α` below `β`. -/
def αLT : NatOrdinal := NatOrdinal.partLT S.β α

/-- The part `(deg B)_{<β}` of the degree of a variable `B` below `β`. -/
def degLT (i : ι) : NatOrdinal := NatOrdinal.partLT S.β (wt i)

/-- `H := ∂F/∂X_{B₀}`, the partial derivative of `F` at its variable of maximal degree. -/
def H : MvPolynomial ι K := pderiv S.B₀ S.F

/-- The part of `deg B` below `β` is zero. -/
def LowDegreePartEqZero (i : ι) : Prop := S.degLT i = 0

/-- The part of `deg B` below `β` equals the part of `α` below `β`. -/
def LowDegreePartEq (i : ι) : Prop := S.degLT i = S.αLT

/-- The part of `deg B` below `β` precedes `λ₀` in the algebraic order. -/
def LowDegreePartAlgebraicLE (i : ι) : Prop := NatOrdinal.AlgebraicLE (S.degLT i) S.lam₀

theorem αGE_def : S.αGE = NatOrdinal.partGE S.β α := (rfl)
theorem αLT_def : S.αLT = NatOrdinal.partLT S.β α := (rfl)
theorem degLT_def (i : ι) : S.degLT i = NatOrdinal.partLT S.β (wt i) := (rfl)
theorem H_def : S.H = pderiv S.B₀ S.F := (rfl)
theorem lowDegreePartEqZero_iff (i : ι) : S.LowDegreePartEqZero i ↔ S.degLT i = 0 := (Iff.rfl)
theorem lowDegreePartEq_iff (i : ι) : S.LowDegreePartEq i ↔ S.degLT i = S.αLT := (Iff.rfl)
theorem lowDegreePartAlgebraicLE_iff (i : ι) :
    S.LowDegreePartAlgebraicLE i ↔ NatOrdinal.AlgebraicLE (S.degLT i) S.lam₀ := (Iff.rfl)

/-- The canonical cutoff and bounds obtained from the last term of `deg H_D` and the truncation
and remainder estimates. -/
structure HasCanonicalBounds : Prop where
  /-- The degree `α` is nonzero. -/
  α_ne_zero : α ≠ 0
  /-- The degree `α` is a limit ordinal. -/
  α_constantCoeff : α.constantCoeff = 0
  /-- The last-term exponent `β` is nonzero. -/
  β_ne_zero : S.β ≠ 0
  /-- `ω^β` is the last term of the Cantor normal form of `deg H_D`. -/
  leastTerm_degHD : NatOrdinal.leastTerm S.degHD = ω^ S.β
  /-- The translated-truncation exponent satisfies `α₁ < α`. -/
  α₁_lt : S.α₁ < α
  /-- A remainder bound `λ` and the resulting definition of `λ₀`. -/
  lambda_choice : ∃ lam : NatOrdinal,
    lam < S.αLT ∧
      (∀ d ∈ S.F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ →
        NatOrdinal.partGE S.β ρ = S.αGE → NatOrdinal.partLT S.β ρ ≤ lam) ∧
      S.lam₀ = Max.max (lam + 1)
        (if NatOrdinal.partGE S.β S.α₁ = S.αGE then NatOrdinal.partLT S.β S.α₁ else 0)

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

variable (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
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

variable (hinj : ∀ β < α, InjectiveAt K wt x β) (hσ : σ.IsPrincipal)
include hinj hσ

/-- **`D = 1`: `X_{B₀}` occurs linearly in `F`.** -/
@[blueprint "lem:relation-at-limit-ordinal-maximal-variable-linear"
  (phase := "Limit ordinals in the degree induction")
  (title := "Maximal-variable linearity for the ordinal-value degree")
  (statement := /--
    Let $K$ be a field of characteristic zero. Let $(x_i)_{i\in I}$ be a
    minimal homogeneous generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose principal series $b_i$ of degree
    $w_i$ representing $x_i$. Assume evaluation at $(x_i)$ is injective on
    every homogeneous degree below $\alpha$.

    Let $0\ne F\in K[X_i:i\in I]$ be weighted homogeneous of degree $\alpha$
    with $F(x)=0$. Suppose every variable of $F$ has weight below $\alpha$
    and zero constant Cantor coefficient. Choose $X_{B_0}$ of maximal weight
    among the variables of $F$, and put $D=\deg_{X_{B_0}}F$. Suppose there are
    ordinals $\beta,\Delta,\lambda_0,\alpha_1$ such that
    \[
      \Delta\ne0,\qquad
      \Delta\oplus D w_{B_0}=\alpha,\qquad
      \lambda_0<\alpha_{<\beta},
    \]
    every Cantor term of $\Delta$ is at least $\omega^\beta$, and the last
    Cantor term of $w_{B_0}$ is below $\omega^\beta$. Assume also
    \[
      \alpha_1\le\alpha_{\ge\beta}\oplus\lambda_0,
      \qquad \alpha_1\le\alpha,
    \]
    that for some $\varepsilon_1>0$ every $\gamma\in(-\varepsilon_1,0)$
    satisfies
    \[
      v_J\bigl(F(b)^{\vert\gamma}\bigr)<\omega^{\alpha_1},
    \]
    and that in the convolution expansion of any monomial of $F$, every term
    $\rho$ using at least two translated truncations satisfies
    $\rho<\alpha_{\ge\beta}\oplus\lambda_0$.

    Then $D=1$.
  -/)
  (proof := /--
  Suppose $D\ge2$, put $t=(w_{B_0})_{<\beta}$, and set
  $\Theta=\partial_{B_0}F$. The hypotheses give
  $\alpha_{<\beta}=Dt$, while $t$ is a nonzero limit ordinal. The polynomial
  $\Theta$ is nonzero and homogeneous of degree
  \[
    h=\Delta\oplus(D-1)w_{B_0}<\alpha.
  \]
  Since evaluation is injective in degree $h$, the homogeneous evaluation
  $\Theta(b)$ has ordinal value $\omega^h$.

  Since $\lambda_0\oplus1<(D-1)t\oplus t$,
  \ref{lem:natural-sum-approach} gives $s<(D-1)t$ with
  $\lambda_0\oplus1\le s\oplus t$. Put
  $\tau=h_{\ge\beta}\oplus s$. Then $\tau<h$ and
  $\alpha_{\ge\beta}\oplus\lambda_0\le\tau\oplus w_{B_0}$.

  By \ref{lem:differentiated-relation}, the components of weight at least
  $\tau$ in a polynomial representing a sufficiently late translated
  truncation of $\Theta(b)$ lie in the ideal generated by
  $\partial_BF$ for variables with $w_B>w_{B_0}$. Maximality of $B_0$ makes
  this ideal zero. On the other hand, \ref{lem:truncation-values} supplies
  such a translated truncation with ordinal value exactly $\omega^\tau$.
  This ordinal value is nonzero, and $\tau<h<\alpha$, so its unique
  polynomial representative with monomial weights below $\alpha$ is defined.
  By \ref{prop:ordinal-value-of-polynomial-representative}, its largest
  monomial weight is $\tau$; hence its component of weight $\tau$ is nonzero,
  a contradiction.
  -/)]
theorem degreeOf_eq_one [CharZero K] : degreeOf S.B₀ S.F = 1 := by
  obtain ⟨e, he, ht⟩ := S.exists_leastTerm_degLT hx S.mem (S.degLT_B₀_ne_zero hx)
  exact σ.degreeOf_eq_one_of_forall_termDegree_lt hx hinj hσ S.hom S.vars_lt S.mem S.max
    S.hdegHD S.degHD_terms he ht S.lam₀_lt S.α₁_le S.α₁_le_α S.ε₁_pos S.truncation_lt
    S.remainder_lt

variable [CharZero K]

/-- `(deg B₀)_{<β} = α_{<β}`. -/
theorem degLT_B₀ : S.degLT S.B₀ = S.αLT := by
  rw [S.αLT_eq_nsmul_degLT, S.degreeOf_eq_one hx hinj hσ, one_smul]

theorem lowDegreePartEq_B₀ : S.LowDegreePartEq S.B₀ := S.degLT_B₀ hx hinj hσ

theorem degHD_add : S.degHD + wt S.B₀ = α := by
  have := S.hdegHD
  rwa [S.degreeOf_eq_one hx hinj hσ, one_smul] at this

/-- `H = ∂F/∂X_{B₀}` is homogeneous of degree `α ⊖ δ`. -/
theorem H_hom : IsWeightedHomogeneous wt S.H S.degHD :=
  isWeightedHomogeneous_pderiv wt S.hom S.B₀ (S.degHD_add hx hinj hσ)

omit hx hinj hσ in
theorem H_ne_zero : S.H ≠ 0 := pderiv_ne_zero_of_mem_vars S.mem

/-- Every monomial of `F` contains `X_{B₀}` at most once. -/
theorem apply_B₀_le_one {d : ι →₀ ℕ} (hd : d ∈ S.F.support) : d S.B₀ ≤ 1 := by
  have := monomial_le_degreeOf S.B₀ hd
  rwa [S.degreeOf_eq_one hx hinj hσ] at this

/-- Every variable `B` of `H` has `(deg B)_{<β} = 0`. -/
theorem degLT_eq_zero_of_mem_vars_H {i : ι} (hi : i ∈ S.H.vars) : S.degLT i = 0 := by
  classical
  obtain ⟨d', hd', hid'⟩ := (mem_vars_iff_mem_support i).mp hi
  obtain ⟨d, hd, hdv, rfl⟩ := exists_mem_support_of_mem_support_pderiv hd'
  have hd1 : d S.B₀ = 1 :=
    le_antisymm (S.apply_B₀_le_one hx hinj hσ hd) (Nat.one_le_iff_ne_zero.mpr hdv)
  -- `i ≠ B₀`, since `B₀` occurs once
  have hi0 : i ≠ S.B₀ := by
    rintro rfl
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, Finsupp.single_eq_same, hd1] at hid'
    exact hid' rfl
  have hid : i ∈ d.support := by
    rw [Finsupp.mem_support_iff] at hid' ⊢
    rw [Finsupp.tsub_apply, Finsupp.single_apply, ite_eq_right hi0.symm, Nat.sub_zero] at hid'
    exact hid'
  -- The parts below `β` add up to `α_{<β} = (deg B₀)_{<β}`; `B₀` contributes all of it.
  have hsum := S.sum_degLT_eq_αLT hd
  have hB₀d : S.B₀ ∈ d.support := Finsupp.mem_support_iff.mpr hdv
  rw [← Finset.add_sum_erase _ _ hB₀d, hd1, one_smul, S.degLT_B₀ hx hinj hσ] at hsum
  have hrest : ∑ j ∈ d.support.erase S.B₀, d j • S.degLT j = 0 := add_eq_left.mp hsum
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ zero_le)] at hrest
  have := hrest i (Finset.mem_erase.mpr ⟨hi0, hid⟩)
  rcases (smul_eq_zero.mp this) with h | h
  · exact absurd h (Finsupp.mem_support_iff.mp hid)
  · exact h

theorem lowDegreePartEqZero_of_mem_vars_H {i : ι} (hi : i ∈ S.H.vars) :
    S.LowDegreePartEqZero i :=
  S.degLT_eq_zero_of_mem_vars_H hx hinj hσ hi

/-! ### Two factors with nonzero parts below `β` -/

omit hx hinj hσ [CharZero K] in
/-- **The bound on a term of the remainder with two truncated factors.** If `d' · X_i · X_j` is a
monomial of `F`, then `(deg d')_{<β} ⊕ ρᵢ ⊕ ρⱼ ≤ λ₀` for all `ρᵢ < S.degLT i`,
`ρⱼ < S.degLT j`. -/
theorem pair_bound {d' : ι →₀ ℕ} {i j : ι}
    (hd : d' + Finsupp.single i 1 + Finsupp.single j 1 ∈ S.F.support) {ρᵢ ρⱼ : NatOrdinal}
    (hρᵢ : ρᵢ < S.degLT i) (hρⱼ : ρⱼ < S.degLT j) :
    NatOrdinal.partLT S.β (Finsupp.weight wt d') + ρᵢ + ρⱼ ≤ S.lam₀ :=
  MvPolynomial.pair_bound_of_forall_termDegree_lt S.hom S.lam₀_lt S.remainder_lt hd hρᵢ hρⱼ

end LimitOrdinalRelationAtCutoff

end Lifts

end Berarducci
