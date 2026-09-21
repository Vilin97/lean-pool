/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

/-!
# Derivations of polynomial rings graded by ordinals

Polynomial rings `R[X_i]` graded by `deg X_i = wt i` for ordinal degrees `wt : σ → NatOrdinal`
(Mathlib's `IsWeightedHomogeneous wt`). This file collects the degree bookkeeping for the
derivations `∂_g = ∑_i g_i ∂/∂X_i` (Lean `mkDerivation R g`) of such a ring:

* a variable of a homogeneous polynomial has degree at most the polynomial's, and the finite part
  of the degree of a monomial is the sum of the finite parts of the degrees of its variables;
* `∂/∂X_j ∘ ∂_g = ∂_{∂_j g} + ∂_g ∘ ∂/∂X_j`, and `∂_g F = ∑_{i ∈ S} g_i ∂F/∂X_i` for every finite
  `S` containing the variables of `F`;
* the partial derivative `∂F/∂X_i` of a homogeneous `F` of degree `δ` is homogeneous of degree
  `δ ⊖ wt i` when `wt i ≼ δ` in the algebraic order (there is `β` with
  `β ⊕ wt i = δ`), and zero
  otherwise; a derivation whose value on `X_i` is homogeneous of degree `wt i ⊖ 1` for `wt i` a
  successor and zero otherwise sends homogeneous polynomials of degree `δ` to homogeneous
  polynomials of degree `δ.removeNat 1`, which is `δ ⊖ 1` for a successor `δ`;
* Euler's identity `∑_i (wt i)_{<1} X_i ∂F/∂X_i = δ_{<1} F` for `F` homogeneous of degree `δ`,
  where `α_{<1}` is the finite part of `α` (Lean `constantCoeff`, the constant term of the Cantor
  normal form).
-/

universe u v

open Finsupp

public section

namespace Finsupp

variable {ι : Type u} (wt : ι → NatOrdinal)

/-- The finite part of the degree of a monomial is the sum of the finite parts of the degrees of
its variables. -/
theorem constantCoeff_weight (d : ι →₀ ℕ) :
    (Finsupp.weight wt d).constantCoeff = ∑ i ∈ d.support, d i * (wt i).constantCoeff := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum]
  induction d.support using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, NatOrdinal.constantCoeff_add,
      NatOrdinal.constantCoeff_nsmul, ih]

/-- The degree of a monomial is at least the degree of each of its variables. -/
theorem le_weight_of_mem_support (d : ι →₀ ℕ) {i : ι} (hi : i ∈ d.support) :
    wt i ≤ Finsupp.weight wt d := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine le_trans ?_ (Finset.single_le_sum (fun j _ ↦ zero_le) hi)
  have h1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  calc wt i = 1 • wt i := (one_nsmul _).symm
    _ ≤ d i • wt i := nsmul_le_nsmul_left zero_le h1

end Finsupp

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommRing R] (wt : σ → NatOrdinal)

/-! ### Variables and degrees -/

/-- A variable of a homogeneous polynomial has degree at most the polynomial's. -/
theorem IsWeightedHomogeneous.wt_le_of_mem_vars {p : MvPolynomial σ R} {δ : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p δ) {i : σ} (hi : i ∈ p.vars) : wt i ≤ δ := by
  obtain ⟨d, hd, hdi⟩ := (mem_vars_iff_mem_support i).mp hi
  rw [← hp (mem_support_iff.mp hd)]
  exact Finsupp.le_weight_of_mem_support wt d hdi

/-! ### Derivations -/

/-- A finite sum of derivations, applied. -/
theorem _root_.Derivation.finset_sum_apply {ι : Type*} (s : Finset ι)
    (D : ι → Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (p : MvPolynomial σ R) :
    (∑ i ∈ s, D i) p = ∑ i ∈ s, D i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

/-- `∂_g F = ∑_{i ∈ S} g_i ∂F/∂X_i` for every finite set `S` of variables containing those of
`F`. -/
theorem mkDerivation_eq_sum (g : σ → MvPolynomial σ R) {p : MvPolynomial σ R} {S : Finset σ}
    (hS : ∀ i ∈ p.vars, i ∈ S) : mkDerivation R g p = ∑ i ∈ S, g i * pderiv i p := by
  classical
  have h : mkDerivation R g p = (∑ i ∈ S, g i • pderiv i) p := by
    refine derivation_eq_of_forall_mem_vars fun i hi ↦ ?_
    rw [mkDerivation_X, Derivation.finset_sum_apply, Finset.sum_eq_single i]
    · rw [Derivation.smul_apply, pderiv_X_self, smul_eq_mul, mul_one]
    · intro j _ hji
      rw [Derivation.smul_apply, pderiv_X_of_ne hji.symm, smul_zero]
    · intro hiS
      exact absurd (hS i hi) hiS
  rw [h, Derivation.finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Derivation.smul_apply, smul_eq_mul]

/-- `∂/∂X_j ∘ ∂_g = ∂_{∂_j g} + ∂_g ∘ ∂/∂X_j`. -/
theorem pderiv_mkDerivation (g : σ → MvPolynomial σ R) (j : σ) (p : MvPolynomial σ R) :
    pderiv j (mkDerivation R g p) =
      mkDerivation R (fun i ↦ pderiv j (g i)) p + mkDerivation R g (pderiv j p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]; abel
  | mul_X p i ih =>
    have hc : mkDerivation R g (pderiv j (X i)) = 0 := by
      by_cases hij : i = j
      · subst hij; rw [pderiv_X_self, ← C_1, derivation_C]
      · rw [pderiv_X_of_ne hij, map_zero]
    rw [Derivation.leibniz, Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_add, pderiv_mul, pderiv_mul, ih, mkDerivation_X, mkDerivation_X, pderiv_mul, map_add,
      Derivation.leibniz, Derivation.leibniz, hc, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, mkDerivation_X]
    ring

/-- Partial derivatives commute. -/
theorem pderiv_pderiv_comm (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  have hX : ∀ a b k : σ, pderiv a (pderiv b (X k : MvPolynomial σ R)) = 0 := fun a b k ↦ by
    rcases eq_or_ne k b with rfl | h
    · rw [pderiv_X_self, pderiv_one]
    · rw [pderiv_X_of_ne h, map_zero]
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k ih =>
    rw [pderiv_mul, pderiv_mul, map_add, map_add, pderiv_mul, pderiv_mul, pderiv_mul, pderiv_mul,
      ih, hX, hX]
    ring

/-- The variables of a partial derivative are among those of the polynomial. -/
theorem vars_pderiv_subset (i : σ) (p : MvPolynomial σ R) : (pderiv i p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨d', hd', hjd'⟩ := (mem_vars_iff_mem_support j).mp hj
  -- `d'` is `d - single i 1` for a monomial `d` of `p` with `d i ≠ 0`
  have : d' ∈ (p.support.image fun d ↦ d - Finsupp.single i 1) := by
    have hsum : pderiv i p =
        ∑ d ∈ p.support, monomial (d - Finsupp.single i 1) (AddMonoidAlgebra.coeff p d * d i) := by
      conv_lhs => rw [p.as_sum, map_sum]
      exact Finset.sum_congr rfl fun d _ ↦ pderiv_monomial
    rw [hsum] at hd'
    obtain ⟨d, hd, hd'd⟩ := Finset.mem_biUnion.mp (support_sum hd')
    rw [support_monomial] at hd'd
    split_ifs at hd'd with h0
    · exact absurd hd'd (Finset.notMem_empty d')
    · rw [Finset.mem_singleton] at hd'd
      subst hd'd
      exact Finset.mem_image_of_mem _ hd
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp this
  exact (mem_vars_iff_mem_support j).mpr ⟨d, hd, Finsupp.support_tsub hjd'⟩

/-- A monomial of `∂_i p` comes from a monomial of `p` containing `X_i`, with one occurrence of
`X_i` removed. -/
theorem exists_mem_support_of_mem_support_pderiv {i : σ}
    {p : MvPolynomial σ R} {d' : σ →₀ ℕ} (hd' : d' ∈ (pderiv i p).support) :
    ∃ d ∈ p.support, d i ≠ 0 ∧ d' = d - Finsupp.single i 1 := by
  classical
  have hsum : pderiv i p =
      ∑ d ∈ p.support, monomial (d - Finsupp.single i 1) (AddMonoidAlgebra.coeff p d * d i) := by
    conv_lhs => rw [p.as_sum, map_sum]
    exact Finset.sum_congr rfl fun d _ ↦ pderiv_monomial
  rw [hsum] at hd'
  obtain ⟨d, hd, hd'd⟩ := Finset.mem_biUnion.mp (support_sum hd')
  rw [support_monomial] at hd'd
  split_ifs at hd'd with h0
  · exact absurd hd'd (Finset.notMem_empty d')
  · rw [Finset.mem_singleton] at hd'd
    exact ⟨d, hd, fun h ↦ h0 (by rw [h, Nat.cast_zero, mul_zero]), hd'd⟩

/-- A monomial of `∂_i p` comes from a monomial of `p` containing `X_i`, with the degree of
`X_i` removed. -/
theorem exists_add_eq_weight_of_mem_support_pderiv (wt : σ → NatOrdinal) {i : σ}
    {p : MvPolynomial σ R} {d' : σ →₀ ℕ} (hd' : d' ∈ (pderiv i p).support) :
    ∃ d ∈ p.support, Finsupp.weight wt d' + wt i = Finsupp.weight wt d := by
  obtain ⟨d, hd, hdi, rfl⟩ := exists_mem_support_of_mem_support_pderiv hd'
  exact ⟨d, hd, Finsupp.weight_sub_single_add (w := wt) hdi⟩

/-! ### Nonvanishing of partial derivatives in characteristic zero -/

/-- The coefficient of `d - X_v` in `∂_v p`, for a monomial `d` containing `X_v`. -/
theorem coeff_sub_single_pderiv {v : σ} {p : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d v ≠ 0) :
    AddMonoidAlgebra.coeff (pderiv v p) (d - Finsupp.single v 1) = AddMonoidAlgebra.coeff p d * (d v : R) := by
  classical
  have hsum : pderiv v p =
      ∑ d' ∈ p.support, monomial (d' - Finsupp.single v 1) (AddMonoidAlgebra.coeff p d' * d' v) := by
    conv_lhs => rw [p.as_sum, map_sum]
    exact Finset.sum_congr rfl fun d' _ ↦ pderiv_monomial
  rw [hsum, MvPolynomial.coeff_sum]
  by_cases hdp : d ∈ p.support
  · rw [Finset.sum_eq_single d]
    · rw [coeff_monomial, ite_eq_left rfl]
    · intro d' _ hne
      rw [coeff_monomial]
      split_ifs with h
      · by_cases hd'v : d' v = 0
        · rw [hd'v, Nat.cast_zero, mul_zero]
        · exfalso
          apply hne
          have h1 := tsub_add_cancel_of_le
            (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd'v))
          have h2 := tsub_add_cancel_of_le
            (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd))
          rw [← h1, ← h2, h]
      · rfl
    · intro h; exact absurd hdp h
  · rw [Finset.sum_eq_zero, notMem_support_iff.mp hdp, zero_mul]
    intro d' hd'
    rw [coeff_monomial]
    split_ifs with h
    · by_cases hd'v : d' v = 0
      · rw [hd'v, Nat.cast_zero, mul_zero]
      · exfalso
        have h1 := tsub_add_cancel_of_le
          (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd'v))
        have h2 := tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hd))
        have : d' = d := by rw [← h1, ← h2, h]
        exact hdp (this ▸ hd')
    · rfl

/-- In characteristic zero, the partial derivative with respect to a variable that occurs is
nonzero. -/
theorem pderiv_ne_zero_of_mem_vars [NoZeroDivisors R] [CharZero R] {v : σ}
    {p : MvPolynomial σ R} (hv : v ∈ p.vars) : pderiv v p ≠ 0 := by
  obtain ⟨d, hd, hdv⟩ := (mem_vars_iff_mem_support v).mp hv
  have hdv' : d v ≠ 0 := Finsupp.mem_support_iff.mp hdv
  intro h
  have := coeff_sub_single_pderiv (p := p) hdv'
  rw [h, MvPolynomial.coeff_zero] at this
  exact mul_ne_zero (mem_support_iff.mp hd) (Nat.cast_ne_zero.mpr hdv') this.symm

/-! ### Homogeneity -/

/-- The partial derivative `∂/∂X_i` of a homogeneous polynomial of degree `δ` is homogeneous of
degree `β = δ ⊖ wt i` when `β ⊕ wt i = δ`. -/
theorem isWeightedHomogeneous_pderiv {p : MvPolynomial σ R} {δ : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p δ) (i : σ) {β : NatOrdinal} (hβ : β + wt i = δ) :
    IsWeightedHomogeneous wt (pderiv i p) β := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R wt _
  | add p q _ _ ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hd =>
    rw [pderiv_monomial]
    by_cases hdi : d i = 0
    · rw [hdi, Nat.cast_zero, mul_zero, monomial_zero]
      exact isWeightedHomogeneous_zero R wt _
    · refine isWeightedHomogeneous_monomial wt _ _ ?_
      have h := Finsupp.weight_sub_single_add (w := wt) hdi
      rw [hd] at h
      exact add_right_cancel (h.trans hβ.symm)

/-- If `p` is weighted-homogeneous of degree `δ` and `δ ≠ β + wt i` for every `β`, then the
partial derivative of `p` with respect to `X_i` vanishes. -/
@[blueprint "lem:partial-derivative-vanishes"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Vanishing criterion for partial derivatives of weighted-homogeneous polynomials")
  (statement := /--
    If $F$ is weighted-homogeneous of degree $\delta$ and
    $\delta\ne\beta\oplus w(i)$ for every $\beta$, then $\partial_iF=0$.
  -/)
  (proof := /--
  Any monomial containing $X_i$ would express $\delta$ as the natural sum of
  $w(i)$ and the weight left after removing one occurrence of $X_i$.
  -/)]
theorem pderiv_eq_zero_of_isWeightedHomogeneous {p : MvPolynomial σ R} {δ : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p δ) (i : σ) (h : ¬ ∃ β, β + wt i = δ) : pderiv i p = 0 := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]
  | add p q _ _ ihp ihq => rw [map_add, ihp, ihq, add_zero]
  | monomial d r hd =>
    rw [pderiv_monomial]
    by_cases hdi : d i = 0
    · rw [hdi, Nat.cast_zero, mul_zero, monomial_zero]
    · exact absurd ⟨_, (Finsupp.weight_sub_single_add (w := wt) hdi).trans hd⟩ h

/-- Suppose `g i` is weighted-homogeneous of the degree obtained from `wt i` by subtracting one
from its positive constant Cantor coefficient, and is zero when that coefficient vanishes. The
derivation determined by `g` sends weight `δ` to the weight obtained by truncated subtraction of
one from the constant Cantor coefficient of `δ`. -/
@[blueprint "lem:polynomial-vector-field-lowers-degree"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Weighted degree of polynomial derivations")
  (statement := /--
    Suppose $g_i$ is weighted-homogeneous of the degree obtained from $w(i)$ by
    subtracting one from its positive constant Cantor coefficient, and is zero
    when that coefficient vanishes. If $F$ is weighted-homogeneous of degree
    $\delta$, then $D_g(F)$ is weighted-homogeneous of the degree obtained by
    truncated subtraction of one from the constant Cantor coefficient of
    $\delta$ (so the degree remains $\delta$ when that coefficient is zero).
  -/)
  (proof := /--
  For a monomial, $\partial_iF$ removes $w(i)$ from the weight, while
  multiplication by $g_i$ restores it with one subtracted from its constant
  Cantor coefficient. Hessenberg addition therefore subtracts one from the
  constant Cantor coefficient of $\delta$. Linearity handles sums.
  -/)]
theorem mkDerivation_isWeightedHomogeneous_removeNat (g : σ → MvPolynomial σ R)
    (hg : ∀ i, 0 < (wt i).constantCoeff →
      IsWeightedHomogeneous wt (g i) ((wt i).removeNat 1))
    (hg0 : ∀ i, (wt i).constantCoeff = 0 → g i = 0) {p : MvPolynomial σ R} {δ : NatOrdinal}
    (hp : IsWeightedHomogeneous wt p δ) :
    IsWeightedHomogeneous wt (mkDerivation R g p) (δ.removeNat 1) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R wt _
  | add p q _ _ ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hd =>
    rw [mkDerivation_monomial, smul_eq_C_mul]
    refine IsWeightedHomogeneous.C_mul ?_ r
    unfold Finsupp.sum
    refine IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ ?_
    change IsWeightedHomogeneous wt (monomial (d - Finsupp.single i 1) (d i : R) • g i) _
    rw [smul_eq_mul]
    by_cases hci : (wt i).constantCoeff = 0
    · rw [hg0 i hci, mul_zero]
      exact isWeightedHomogeneous_zero R wt _
    · have hpos : 0 < (wt i).constantCoeff := Nat.pos_of_ne_zero hci
      have hw : δ.removeNat 1 =
          Finsupp.weight wt (d - Finsupp.single i 1) + (wt i).removeNat 1 := by
        rw [← hd, ← Finsupp.weight_sub_single_add (w := wt) (Finsupp.mem_support_iff.mp hi),
          add_comm, NatOrdinal.removeNat_add_right _ _ hpos, add_comm]
      rw [hw]
      exact (isWeightedHomogeneous_monomial wt _ _ rfl).mul (hg i hpos)

/-! ### Euler's identity -/

/-- **Euler's identity** for constant Cantor coefficients. If `p` is weighted-homogeneous of
degree `δ` and `S` contains the variables of `p`, then
`∑ i ∈ S, (wt i).constantCoeff • (X i * pderiv i p) = δ.constantCoeff • p`. -/
@[blueprint "lem:weighted-euler-identity"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Weighted Euler identity")
  (statement := /--
    If $F$ is weighted-homogeneous of degree $\delta$ and $S$ is any finite
    set containing its variables, then
    \[
      \sum_{i\in S} n_iX_i\frac{\partial F}{\partial X_i}=nF,
    \]
    where $n_i$ and $n$ are the constant Cantor coefficients of $w(i)$ and
    $\delta$.
  -/)
  (proof := /--
  On a monomial, the coefficient contributed by $X_i\partial_i$ is the
  multiplicity of $X_i$. Weighted by the constant Cantor coefficient of
  $w(i)$ and summed over $i$, this is the constant Cantor coefficient of the
  monomial's total weight, namely $n$. Extend by linearity.
  -/)]
theorem IsWeightedHomogeneous.sum_constantCoeff_X_mul_pderiv {p : MvPolynomial σ R}
    {δ : NatOrdinal} (hp : IsWeightedHomogeneous wt p δ) {S : Finset σ}
    (hS : ∀ i ∈ p.vars, i ∈ S) :
    ∑ i ∈ S, (wt i).constantCoeff • (X i * pderiv i p) = δ.constantCoeff • p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdsupp : ∀ i ∈ d.support, i ∈ S := fun i hi ↦
    hS i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)
  have hδ : δ.constantCoeff = ∑ i ∈ S, (wt i).constantCoeff * d i := by
    rw [← hp (mem_support_iff.mp hd), Finsupp.constantCoeff_weight]
    rw [← Finset.sum_subset (fun i hi ↦ hdsupp i hi) fun i _ hi ↦ by
      rw [Finsupp.notMem_support_iff.mp hi, mul_zero]]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [hδ, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [X_mul_pderiv_monomial, mul_smul, smul_comm]

/-- **The differentiated syzygy contradiction.** Suppose a partial derivative of `F` is a
combination of other partial derivatives of `F` whose cofactors are free of a distinguished
variable, and suppose none of the differentiating variables occurs in the partial derivative of
`F` at that distinguished variable. Then that partial derivative of `F` is annihilated by the
differentiating variable: applying the distinguished derivation to the combination kills every
cofactor term and every remaining factor.

This is the shape of the final contradiction of the limit step, where the annihilated partial is
known to be nonzero. -/
theorem pderiv_pderiv_eq_zero_of_sum_of_notMem_vars {σ : Type*}
    {R : Type*} [CommRing R] {F : MvPolynomial σ R} {B₀ B' : σ} {s : Finset σ}
    {U : σ → MvPolynomial σ R}
    (hsyz : pderiv B' F = ∑ B ∈ s, pderiv B F * U B)
    (hU : ∀ B ∈ s, pderiv B₀ (U B) = 0)
    (hvars : ∀ B ∈ s, B ∉ (pderiv B₀ F).vars) :
    pderiv B' (pderiv B₀ F) = 0 := by
  classical
  have hkey : pderiv B₀ (pderiv B' F) = pderiv B₀ (∑ B ∈ s, pderiv B F * U B) :=
    congrArg (fun p ↦ pderiv B₀ p) hsyz
  rw [pderiv_pderiv_comm, map_sum] at hkey
  rw [hkey]
  refine Finset.sum_eq_zero fun B hB ↦ ?_
  rw [pderiv_mul, hU B hB, mul_zero, add_zero, pderiv_pderiv_comm,
    pderiv_eq_zero_of_notMem_vars (hvars B hB), zero_mul]

end MvPolynomial

end
