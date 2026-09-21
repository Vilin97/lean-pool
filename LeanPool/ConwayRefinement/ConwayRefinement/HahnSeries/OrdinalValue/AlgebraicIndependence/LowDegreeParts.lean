/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.LimitOrdinalContradiction
public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LimitOrdinalRelationAtCutoff

/-!
# Low-degree parts and algebraic order

For a relation of limit-ordinal degree `α` and a cutoff `β`, distinguish variables whose part of
the degree below `β` is zero, equals `α_{<β}`, precedes `λ₀` in the algebraic order, or is nonzero
and does not precede `λ₀` in that order. The bound `pair_bound` on a remainder term with two
truncated factors, through `PairBounds`, describes the last class: such a variable `B` occurs with
exponent `1` in every monomial of `F`;
every other variable `B'` with `(deg B')_{<β} ≠ 0` in such a monomial has the exponent `e_{B'}`
of the last term of `(deg B')_{<β}` above the exponent `e_B` of the last term of `(deg B)_{<β}`,
and `(λ₀)_{≥e_{B'}} = (α_{<β})_{≥e_{B'}}`; and with `ω^ε` the last term of the Cantor normal form
of `α_{<β} ⊖ (deg B)_{<β}`, `(λ₀)_{≥ε} = (α_{<β})_{≥ε}`.
-/

universe v w

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace NatOrdinal

/-- The last term of the Cantor normal form of a sum of nonzero natural ordinals is the last term
of one of them. -/
theorem exists_leastTerm_sum_eq {ι' : Type*} {s : Finset ι'} (hs : s.Nonempty)
    (f : ι' → NatOrdinal) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, leastTerm (∑ j ∈ s, f j) = leastTerm (f i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by rw [Finset.sum_singleton]⟩
  | cons a s ha hs ih =>
    obtain ⟨i, hi, hi'⟩ := ih fun j hj ↦ hf j (Finset.mem_cons_of_mem hj)
    have hsum : ∑ j ∈ s, f j ≠ 0 := by
      have : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum (fun j _ ↦ zero_le) hi
      exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr (hf i (Finset.mem_cons_of_mem hi))) this).ne'
    rw [Finset.sum_cons, leastTerm_add (hf a (Finset.mem_cons_self a s)) hsum]
    rcases min_choice (leastTerm (f a)) (leastTerm (∑ j ∈ s, f j)) with h | h
    · exact ⟨a, Finset.mem_cons_self a s, h⟩
    · exact ⟨i, Finset.mem_cons_of_mem hi, h.trans hi'⟩

end NatOrdinal

namespace Berarducci

/-! ### Splitting off factors of a monomial -/

variable {ι : Type w}

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

/-- A monomial containing `X_i` and `X_u`, `u ≠ i`, is `d' · X_i · X_u`. -/
theorem exists_eq_add_single_add_single {d : ι →₀ ℕ} {i u : ι} (hi : i ∈ d.support)
    (hu : u ∈ d.support) (hui : u ≠ i) :
    ∃ d' : ι →₀ ℕ, d = d' + Finsupp.single i 1 + Finsupp.single u 1 := by
  classical
  refine ⟨d - Finsupp.single i 1 - Finsupp.single u 1, ?_⟩
  have hdi : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hdu : 1 ≤ d u := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hu)
  have h1 : Finsupp.single u 1 ≤ d - Finsupp.single i 1 := by
    rw [Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hui)]
    omega
  have h2 : Finsupp.single i 1 ≤ d := Finsupp.single_le_iff.mpr hdi
  rw [add_right_comm, tsub_add_cancel_of_le h1, tsub_add_cancel_of_le h2]

variable {K : Type v} [Field K] {wt : ι → NatOrdinal} {x : ι → PrincipalSubring K}

namespace Lifts.LimitOrdinalRelationAtCutoff

variable {σ : Lifts wt x} {α : NatOrdinal} (S : σ.LimitOrdinalRelationAtCutoff α)

/-- A variable of `F` has a proper low-degree part outside the algebraic bound when its part below
`β` is nonzero, is not all of `α_{<β}`, and does not precede `λ₀` in the algebraic order. -/
def HasProperLowDegreePartNotAlgebraicLE (i : ι) : Prop :=
  i ∈ S.F.vars ∧ S.degLT i ≠ 0 ∧ ¬ S.LowDegreePartEq i ∧ ¬ S.LowDegreePartAlgebraicLE i

theorem hasProperLowDegreePartNotAlgebraicLE_iff (i : ι) :
    S.HasProperLowDegreePartNotAlgebraicLE i ↔
      i ∈ S.F.vars ∧ S.degLT i ≠ 0 ∧ ¬ S.LowDegreePartEq i ∧
        ¬ S.LowDegreePartAlgebraicLE i := (Iff.rfl)

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

/-- For a monomial `d' · X_i · X_u` of `F`: `(deg d')_{<β} ⊕ S.degLT i ⊕ S.degLT u = α_{<β}`. -/
theorem partLT_weight_add_degLT_add_degLT {d' : ι →₀ ℕ} {i u : ι}
    (hd : d' + Finsupp.single i 1 + Finsupp.single u 1 ∈ S.F.support) :
    NatOrdinal.partLT S.β (Finsupp.weight wt d') + S.degLT i + S.degLT u = S.αLT := by
  rw [S.αLT_def, S.degLT_def, S.degLT_def]
  exact MvPolynomial.partLT_weight_add_partLT_add_partLT S.hom hd

variable (hx : IsMinimalSystem (Berarducci.principalGrading K) wt x)
include hx

/-- **A variable whose proper low-degree part does not precede `λ₀` occurs once in each monomial
that contains it.** -/
@[blueprint "lem:low-degree-part-outside-algebraic-bound-occurs-linearly"
  (phase := "Limit ordinals in the degree induction")
  (title := "Linearity when $(w_B)_{<\\beta}\\oplus\\nu\\ne\\lambda_0$ for every $\\nu$")
  (statement := /--
    Let $K$ be a field. Let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose series $b_i$ representing $x_i$.

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

    Let $X_B$ occur in $F$, and suppose
    \[
      0<(w_B)_{<\beta}\ne\alpha_{<\beta},
      \qquad
      (w_B)_{<\beta}\not\preccurlyeq\lambda_0.
    \]
    Then $X_B$ has exponent $1$ in every monomial of $F$ in which it occurs.
  -/)
  (proof := /--
  Put $t=(w_B)_{<\beta}$. If some monomial contains $X_B$ at least twice,
  write it as $M'X_B^2$. The finite part of $t$ is zero, so its last Cantor
  term is $\omega^e$ for some $e\ne0$. Weighted homogeneity gives
  \[
    (\deg M')_{<\beta}\oplus t\oplus t=\alpha_{<\beta}.
  \]
  The two-truncation bound says that for all $\rho_1,\rho_2<t$,
  \[
    (\deg M')_{<\beta}\oplus\rho_1\oplus\rho_2\le\lambda_0.
  \]
  Since $\lambda_0<\alpha_{<\beta}$,
  \ref{lem:equal-last-terms-hessenberg-decomposition} gives
  $t\preccurlyeq\lambda_0$, a contradiction.
  -/)]
theorem apply_eq_one_of_hasProperLowDegreePartNotAlgebraicLE {i : ι}
    (hi : S.HasProperLowDegreePartNotAlgebraicLE i) {d : ι →₀ ℕ} (hd : d ∈ S.F.support)
    (hid : i ∈ d.support) : d i = 1 := by
  obtain ⟨hiv, ht, -, hdiff⟩ := hi
  by_contra hne
  have h2 : 2 ≤ d i := by
    have := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hid)
    omega
  obtain ⟨d', rfl⟩ := exists_eq_add_single_add_single_self h2
  obtain ⟨e, he, hte⟩ := S.exists_leastTerm_degLT hx hiv ht
  have hμ := S.partLT_weight_add_degLT_add_degLT hd
  have hlμ : S.lam₀ < S.αLT := by rw [S.αLT_def]; exact S.lam₀_lt
  exact hdiff ((S.lowDegreePartAlgebraicLE_iff i).mpr
    (NatOrdinal.algebraicLE_of_forall_add_add_le ht ht hte hte he (hμ ▸ hlμ)
      fun ρ₁ ρ₂ hρ₁ hρ₂ ↦ S.pair_bound hd hρ₁ hρ₂))

/-- **The other factors with nonzero part below `β`.** Suppose the proper low-degree part of
`X_i` does not precede `λ₀`, and `X_u`, with `S.degLT u ≠ 0`, occurs with `X_i` in a monomial of
`F`. If `ω^{eᵢ}` and `ω^{eᵤ}` are the last terms of the Cantor normal forms of `S.degLT i` and
`S.degLT u`, then `eᵢ < eᵤ` and `(λ₀)_{≥eᵤ} = (α_{<β})_{≥eᵤ}`. -/
@[blueprint "lem:later-cantor-terms-outside-algebraic-bound"
  (phase := "Limit ordinals in the degree induction")
  (title := "Separation of last Cantor terms under a two-factor bound")
  (statement := /--
    Let $K$ be a field. Let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose series $b_i$ representing $x_i$.

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

    Let distinct variables $X_B,X_C$ occur in the same monomial of $F$.
    Suppose
    \[
      0<(w_B)_{<\beta}\ne\alpha_{<\beta},\qquad
      (w_B)_{<\beta}\oplus\nu\ne\lambda_0
      \quad\text{for every ordinal }\nu,
    \]
    and $(w_C)_{<\beta}\ne0$. If the last Cantor terms of
    $(w_B)_{<\beta}$ and $(w_C)_{<\beta}$ are respectively
    $\omega^{e_B}$ and $\omega^{e_C}$, then
    \[
      e_B<e_C,\qquad
      (\lambda_0)_{\ge e_C}=(\alpha_{<\beta})_{\ge e_C}.
    \]
  -/)
  (proof := /--
  Write the chosen monomial as $M'X_BX_C$ and put
  $O=(\deg M')_{<\beta}$. Weighted homogeneity gives
  \[
    O\oplus(w_B)_{<\beta}\oplus(w_C)_{<\beta}=\alpha_{<\beta},
  \]
  while the convolution-remainder hypothesis bounds
  $O\oplus\rho_B\oplus\rho_C$ by $\lambda_0$ whenever
  $\rho_B<(w_B)_{<\beta}$ and $\rho_C<(w_C)_{<\beta}$.

  The exponent $e_B$ is nonzero because the variables of $F$ have zero
  constant Cantor coefficient. If $e_B=e_C$, then
  \ref{lem:equal-last-terms-hessenberg-decomposition} gives an ordinal $\nu$ with
  $(w_B)_{<\beta}\oplus\nu=\lambda_0$. If $e_C<e_B$, the same conclusion
  follows from \ref{lem:unequal-last-terms-hessenberg-decomposition}. Both contradict
  the hypothesis, so $e_B<e_C$. The upper-Cantor-term rigidity used in the
  proof of the unequal-last-term case, applied to the same bound, then gives
  $(\lambda_0)_{\ge e_C}=(\alpha_{<\beta})_{\ge e_C}$.
  -/)]
theorem lt_and_partGE_eq_of_hasProperLowDegreePartNotAlgebraicLE {i : ι}
    (hi : S.HasProperLowDegreePartNotAlgebraicLE i) {d : ι →₀ ℕ}
    (hd : d ∈ S.F.support) (hid : i ∈ d.support) {u : ι} (hud : u ∈ d.support) (hui : u ≠ i)
    (htu : S.degLT u ≠ 0) {eᵢ eᵤ : NatOrdinal} (heᵢ : NatOrdinal.leastTerm (S.degLT i) = ω^ eᵢ)
    (heᵤ : NatOrdinal.leastTerm (S.degLT u) = ω^ eᵤ) :
    eᵢ < eᵤ ∧ NatOrdinal.partGE eᵤ S.lam₀ = NatOrdinal.partGE eᵤ S.αLT := by
  obtain ⟨hiv, hti, -, hdiff⟩ := id hi
  have hdiff' : ¬ NatOrdinal.AlgebraicLE (S.degLT i) S.lam₀ :=
    fun h ↦ hdiff ((S.lowDegreePartAlgebraicLE_iff i).mpr h)
  have hlμ : S.lam₀ < S.αLT := by rw [S.αLT_def]; exact S.lam₀_lt
  -- the last term of `(deg X_i)_{<β}` has nonzero exponent
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

/-- Suppose the proper low-degree part of `i` does not precede `λ₀`, and
`c ⊕ S.degLT i = α_{<β}` (so `c = α_{<β} ⊖ (deg X_i)_{<β}`). If `ω^ε` is the
last term of the Cantor normal form of `c`, then `(λ₀)_{≥ε} = (α_{<β})_{≥ε}`. -/
@[blueprint "lem:complementary-cantor-tail"
  (phase := "Limit ordinals in the degree induction")
  (title := "Upper Cantor terms at the complementary low weight")
  (statement := /--
    Let $K$ be a field. Let $(x_i)_{i\in I}$ be a minimal homogeneous
    generating system of $\widehat{\mathrm P}$, with
    $x_i\in\mathrm P_{w_i}$, and choose series $b_i$ representing $x_i$.

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

    Let $X_B$ occur in $F$, and suppose
    \[
      0<(w_B)_{<\beta}\ne\alpha_{<\beta},\qquad
      (w_B)_{<\beta}\oplus\nu\ne\lambda_0
      \quad\text{for every ordinal }\nu.
    \]
    If
    \[
      c\oplus(w_B)_{<\beta}=\alpha_{<\beta}
    \]
    and the last Cantor term of $c$ is $\omega^e$, then
    \[
      (\lambda_0)_{\ge e}=(\alpha_{<\beta})_{\ge e}.
    \]
  -/)
  (proof := /--
  Choose a monomial containing $X_B$. By
  \ref{lem:low-degree-part-outside-algebraic-bound-occurs-linearly}, $X_B$ has exponent one in this
  monomial. After deleting it, the natural sum of the remaining nonzero parts
  below $\beta$ is $c$. This family is nonempty because otherwise
  $(w_B)_{<\beta}=\alpha_{<\beta}$.

  The last Cantor term of a finite natural sum of nonzero ordinals is the last
  Cantor term of one of its summands. Choose a remaining variable $X_C$ that
  supplies $\omega^e$. Then
  \ref{lem:later-cantor-terms-outside-algebraic-bound} applied to $X_B$ and
  $X_C$ gives
  $(\lambda_0)_{\ge e}=(\alpha_{<\beta})_{\ge e}$.
  -/)]
theorem partGE_lam₀_eq_of_hasProperLowDegreePartNotAlgebraicLE {i : ι}
    (hi : S.HasProperLowDegreePartNotAlgebraicLE i) {c ε : NatOrdinal}
    (hc : c + S.degLT i = S.αLT) (hε : NatOrdinal.leastTerm c = ω^ ε) :
    NatOrdinal.partGE ε S.lam₀ = NatOrdinal.partGE ε S.αLT := by
  classical
  obtain ⟨hiv, hti, htop, -⟩ := id hi
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp hiv
  have hd1 := S.apply_eq_one_of_hasProperLowDegreePartNotAlgebraicLE hx hi hd hid
  -- the parts below `β` of the other factors add up to `c`
  have hsum := S.sum_degLT_eq_αLT hd
  rw [← Finset.add_sum_erase _ _ hid, hd1, one_smul, add_comm] at hsum
  have hc' : ∑ j ∈ d.support.erase i, d j • S.degLT j = c :=
    add_right_cancel (hsum.trans hc.symm)
  -- restrict to the factors with nonzero part below `β`
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
  obtain ⟨u, hus, hu⟩ := NatOrdinal.exists_leastTerm_sum_eq hs _ hsne
  obtain ⟨hu', htu⟩ := Finset.mem_filter.mp hus
  obtain ⟨hui, hud⟩ := Finset.mem_erase.mp hu'
  rw [hcs, hε, NatOrdinal.leastTerm_nsmul htu
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hud))] at hu
  obtain ⟨eᵢ, -, heᵢ⟩ := S.exists_leastTerm_degLT hx hiv hti
  exact
    (S.lt_and_partGE_eq_of_hasProperLowDegreePartNotAlgebraicLE
      hx hi hd hid hud hui htu heᵢ hu.symm).2

end Lifts.LimitOrdinalRelationAtCutoff

end Berarducci
