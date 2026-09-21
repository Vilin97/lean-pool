/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Expansion of a multivariate polynomial in one variable

Mathlib identifies `MvPolynomial (Option σ') R` with polynomials in one variable over
`MvPolynomial σ' R` (`MvPolynomial.optionEquivLeft`). Composing with the renaming along
`Option {y // y ≠ x} ≃ σ` gives, for a variable `x : σ`, the expansion of every
`p : MvPolynomial σ R` in powers of `X x`: `expandEquiv x p` is a polynomial over the polynomials in
the remaining variables, and `xCoeff x k p` is its `k`-th coefficient read back in
`MvPolynomial σ R`, a polynomial not involving `x` (an element of `supported R {x}ᶜ`). The lemmas
here translate the `Polynomial.coeff` API through that identification: the expansion
`p = ∑_k xCoeff x k p * X x ^ k`, the coefficients of such an expansion, the nonvanishing of the
leading coefficient, and the behaviour of the coefficients under weighted homogeneity.

The file also records how weighted homogeneity interacts with derivations `mkDerivation R f` whose
values on the variables have weight `wt i - 1`: such a derivation lowers weight by one, and it
preserves "does not involve `x`" on polynomials whose variables all have weight at most `wt x`.
-/

universe u v

public noncomputable section

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommRing R]

/-! ### Weighted homogeneity and the variables -/

variable (wt : σ → ℕ)

/-- A variable of a weighted-homogeneous polynomial has weight at most the polynomial's. -/
theorem IsWeightedHomogeneous.weight_le_of_mem_vars {p : MvPolynomial σ R} {w : ℕ}
    (hp : IsWeightedHomogeneous wt p w) {i : σ} (hi : i ∈ p.vars) : wt i ≤ w := by
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  rw [← hp (mem_support_iff.mp hm)]
  exact Finsupp.le_weight_of_ne_zero' wt (Finsupp.mem_support_iff.mp hmi)

/-- A weighted-homogeneous polynomial of weight less than `wt x` does not involve `x`. -/
theorem IsWeightedHomogeneous.mem_supported_of_lt {p : MvPolynomial σ R} {w : ℕ}
    (hp : IsWeightedHomogeneous wt p w) {x : σ} (hx : w < wt x) : p ∈ supported R {x}ᶜ := by
  rw [mem_supported]
  intro y hy
  rw [Set.mem_compl_singleton_iff]
  rintro rfl
  exact absurd (hp.weight_le_of_mem_vars wt hy) (not_le.mpr hx)

/-- A derivation whose values on the variables are weighted-homogeneous of weight `wt i - 1`
lowers the weight of weighted-homogeneous polynomials by one. -/
theorem mkDerivation_isWeightedHomogeneous (f : σ → MvPolynomial σ R)
    (hf : ∀ i, IsWeightedHomogeneous wt (f i) (wt i - 1)) (hwt : ∀ i, 1 ≤ wt i)
    {p : MvPolynomial σ R} {w : ℕ} (hp : IsWeightedHomogeneous wt p w) :
    IsWeightedHomogeneous wt (mkDerivation R f p) (w - 1) := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R wt _
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hr =>
    rw [mkDerivation_monomial, smul_eq_C_mul]
    refine IsWeightedHomogeneous.C_mul ?_ r
    unfold Finsupp.sum
    refine IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ ?_
    have hd := Finsupp.weight_sub_single_add (w := wt) (Finsupp.mem_support_iff.mp hi)
    change IsWeightedHomogeneous wt (monomial (d - Finsupp.single i 1) (d i : R) • f i) (w - 1)
    rw [smul_eq_mul]
    have hw : w - 1 = Finsupp.weight wt (d - Finsupp.single i 1) + (wt i - 1) := by
      have := hwt i
      omega
    rw [hw]
    exact (isWeightedHomogeneous_monomial wt _ _ rfl).mul (hf i)

/-- Such a derivation preserves "does not involve `x`" on polynomials whose variables all have
weight at most `wt x`. -/
theorem mkDerivation_mem_supported (hwt : ∀ i, 1 ≤ wt i) (f : σ → MvPolynomial σ R)
    (hf : ∀ i, IsWeightedHomogeneous wt (f i) (wt i - 1)) {x : σ} {p : MvPolynomial σ R}
    (hp : p ∈ supported R {x}ᶜ) (hvars : ∀ i ∈ p.vars, wt i ≤ wt x) :
    mkDerivation R f p ∈ supported R {x}ᶜ := by
  have hs : {i | i ≠ x ∧ wt i ≤ wt x} ⊆ {x}ᶜ := fun i hi ↦ hi.1
  have hp' : p ∈ Algebra.adjoin R (X '' {i | i ≠ x ∧ wt i ≤ wt x}) :=
    mem_supported.mpr fun i hi ↦ ⟨(mem_supported.mp hp) hi, hvars i hi⟩
  clear hp hvars
  induction hp' using Algebra.adjoin_induction with
  | mem q hq =>
    obtain ⟨i, hi, rfl⟩ := hq
    rw [mkDerivation_X]
    exact (hf i).mem_supported_of_lt wt (by have := hwt x; have := hi.2; omega)
  | algebraMap r => rw [Derivation.map_algebraMap]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b ha' hb' ha hb =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (supported_mono hs ha') hb) (mul_mem (supported_mono hs hb') ha)

/-! ### The expansion in powers of one variable -/

variable (x : σ)

/-- Polynomials in the variables other than `x` do not involve `x`. -/
theorem rename_val_mem_supported (q : MvPolynomial {y // y ≠ x} R) :
    rename Subtype.val q ∈ supported R {x}ᶜ := by
  classical
  rw [mem_supported]
  intro y hy
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hy)
  exact z.2

theorem exists_rename_val_eq_of_mem_supported {a : MvPolynomial σ R} (ha : a ∈ supported R {x}ᶜ) :
    ∃ q : MvPolynomial {y // y ≠ x} R, rename Subtype.val q = a := by
  rw [supported_eq_range_rename] at ha
  obtain ⟨q, hq⟩ := ha
  exact ⟨q, hq⟩

variable [DecidableEq σ]

/-- `MvPolynomial σ R` as polynomials in `X x` over the polynomials in the other variables. -/
def expandEquiv : MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {y // y ≠ x} R) :=
  (renameEquiv R (Equiv.optionSubtypeNe x).symm).trans (optionEquivLeft R _)

theorem expandEquiv_rename_val (q : MvPolynomial {y // y ≠ x} R) :
    expandEquiv x (rename Subtype.val q) = Polynomial.C q := by
  rw [expandEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_rename]
  have : (Equiv.optionSubtypeNe x).symm ∘ Subtype.val = some :=
    funext fun y ↦ Equiv.optionSubtypeNe_symm_of_ne y.2
  rw [this]
  induction q using MvPolynomial.induction_on with
  | C r => rw [rename_C, optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, optionEquivLeft_X_some, Polynomial.C_mul]

theorem expandEquiv_symm_C (q : MvPolynomial {y // y ≠ x} R) :
    (expandEquiv x).symm (Polynomial.C q) = rename Subtype.val q := by
  rw [← expandEquiv_rename_val, AlgEquiv.symm_apply_apply]

theorem expandEquiv_X_self : expandEquiv x (X x : MvPolynomial σ R) = Polynomial.X := by
  rw [expandEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.optionSubtypeNe_symm_self, optionEquivLeft_X_none]

theorem expandEquiv_symm_X : (expandEquiv x).symm Polynomial.X = (X x : MvPolynomial σ R) := by
  rw [← expandEquiv_X_self, AlgEquiv.symm_apply_apply]

/-- The degree of the expansion is the degree in `x`. -/
theorem natDegree_expandEquiv (p : MvPolynomial σ R) :
    (expandEquiv x p).natDegree = p.degreeOf x := by
  rw [expandEquiv, AlgEquiv.trans_apply, natDegree_optionEquivLeft, renameEquiv_apply]
  have := degreeOf_rename_of_injective (Equiv.optionSubtypeNe x).symm.injective (p := p) x
  rwa [Equiv.optionSubtypeNe_symm_self] at this

/-- The coefficient of `X x ^ k`, read back as a polynomial in all the variables; it does not
involve `x`. -/
def xCoeff (k : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (rename (Subtype.val : {y // y ≠ x} → σ)).toLinearMap ∘ₗ
    Polynomial.lcoeff (MvPolynomial {y // y ≠ x} R) k ∘ₗ (expandEquiv x).toLinearEquiv.toLinearMap

theorem xCoeff_apply (k : ℕ) (p : MvPolynomial σ R) :
    xCoeff x k p = rename Subtype.val ((expandEquiv x p).coeff k) := (rfl)

theorem xCoeff_mem_supported (k : ℕ) (p : MvPolynomial σ R) : xCoeff x k p ∈ supported R {x}ᶜ :=
  rename_val_mem_supported x _

theorem coeff_xCoeff (k : ℕ) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (xCoeff x k p) = if m x = 0 then coeff (m + Finsupp.single x k) p else 0 := by
  rw [xCoeff_apply]
  split_ifs with hm
  · have hsub : (m.support : Set σ) ⊆ Set.range (Subtype.val : {y // y ≠ x} → σ) := fun y hy ↦
      ⟨⟨y, fun h ↦ (Finsupp.mem_support_iff.mp hy) (h ▸ hm)⟩, rfl⟩
    conv_lhs => rw [← Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective m hsub]
    rw [coeff_rename_mapDomain _ Subtype.val_injective, expandEquiv, AlgEquiv.trans_apply,
      optionEquivLeft_coeff_coeff, renameEquiv_apply,
      ← coeff_rename_mapDomain _ (Equiv.optionSubtypeNe x).symm.injective]
    congr 2
    ext (_ | y)
    · rw [Finsupp.mapDomain_equiv_apply, Finsupp.optionElim_apply_none, Equiv.symm_symm,
        Equiv.optionSubtypeNe_none, Finsupp.add_apply, Finsupp.single_eq_same, hm, zero_add]
    · rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_some,
        Finsupp.optionElim_apply_some, Finsupp.add_apply, Finsupp.single_eq_of_ne y.2,
        add_zero, Finsupp.comapDomain_apply]
  · refine coeff_rename_eq_zero _ _ _ fun u hu ↦ (hm ?_).elim
    rw [← hu, Finsupp.mapDomain_notin_range]
    rintro ⟨y, hy⟩
    exact y.2 hy

/-- The coefficient of `X x ^ k` in `a * X x ^ d`, for `a` not involving `x`. -/
theorem xCoeff_mul_X_pow {a : MvPolynomial σ R} (ha : a ∈ supported R {x}ᶜ) (k d : ℕ) :
    xCoeff x k (a * X x ^ d) = if k = d then a else 0 := by
  obtain ⟨q, rfl⟩ := exists_rename_val_eq_of_mem_supported x ha
  rw [xCoeff_apply, map_mul, map_pow, expandEquiv_rename_val, expandEquiv_X_self,
    Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp

/-- The coefficients of an expansion in powers of `X x` whose coefficients do not involve `x`. -/
theorem xCoeff_sum_mul_X_pow (s : Finset ℕ) {q : ℕ → MvPolynomial σ R}
    (hq : ∀ d ∈ s, q d ∈ supported R {x}ᶜ) (k : ℕ) :
    xCoeff x k (∑ d ∈ s, q d * X x ^ d) = if k ∈ s then q k else 0 := by
  rw [map_sum, Finset.sum_congr rfl fun d hd ↦ xCoeff_mul_X_pow x (hq d hd) k d, Finset.sum_ite_eq]

/-- Expansion of a polynomial in powers of `X x`. -/
theorem sum_xCoeff_mul_X_pow (p : MvPolynomial σ R) :
    ∑ d ∈ Finset.range (p.degreeOf x + 1), xCoeff x d p * X x ^ d = p := by
  conv_rhs => rw [← (expandEquiv x).symm_apply_apply p, (expandEquiv x p).as_sum_range_C_mul_X_pow]
  rw [map_sum, natDegree_expandEquiv]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [map_mul, map_pow, expandEquiv_symm_C, expandEquiv_symm_X, xCoeff_apply]

theorem xCoeff_eq_zero_of_degreeOf_lt {p : MvPolynomial σ R} {k : ℕ} (h : p.degreeOf x < k) :
    xCoeff x k p = 0 := by
  rw [xCoeff_apply, Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_expandEquiv]),
    map_zero]

/-- The leading coefficient in `X x` is nonzero. -/
theorem xCoeff_degreeOf_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    xCoeff x (p.degreeOf x) p ≠ 0 := by
  rw [xCoeff_apply, ← natDegree_expandEquiv, ← Polynomial.leadingCoeff,
    map_ne_zero_iff _ (rename_injective _ Subtype.val_injective), Polynomial.leadingCoeff_ne_zero]
  exact (map_ne_zero_iff _ (expandEquiv x).injective).mpr hp

theorem vars_xCoeff_subset (k : ℕ) (p : MvPolynomial σ R) : (xCoeff x k p).vars ⊆ p.vars := by
  intro i hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  have hc := mem_support_iff.mp hm
  rw [coeff_xCoeff] at hc
  split_ifs at hc with hmx
  · refine (mem_vars_iff_mem_support i).mpr ⟨m + Finsupp.single x k, mem_support_iff.mpr hc, ?_⟩
    rw [Finsupp.mem_support_iff, Finsupp.add_apply]
    have := Finsupp.mem_support_iff.mp hmi
    omega
  · exact absurd rfl hc

/-- The coefficient of `X x ^ k` in a weighted-homogeneous polynomial of weight `w` is
weighted-homogeneous of weight `w - k · wt x`. -/
theorem xCoeff_isWeightedHomogeneous {p : MvPolynomial σ R} {w : ℕ}
    (hp : IsWeightedHomogeneous wt p w) (k : ℕ) :
    IsWeightedHomogeneous wt (xCoeff x k p) (w - k * wt x) := by
  intro m hm
  rw [coeff_xCoeff] at hm
  split_ifs at hm with h
  · have := hp hm
    rw [map_add, Finsupp.weight_single, smul_eq_mul] at this
    omega
  · exact absurd rfl hm

/-- A nonzero coefficient of `X x ^ k` in a weighted-homogeneous polynomial of weight `w` forces
`k · wt x ≤ w`. -/
theorem le_of_xCoeff_ne_zero {p : MvPolynomial σ R} {w : ℕ} (hp : IsWeightedHomogeneous wt p w)
    {k : ℕ} (h : xCoeff x k p ≠ 0) : k * wt x ≤ w := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero h
  rw [coeff_xCoeff] at hm
  split_ifs at hm with hmx
  · have := hp hm
    rw [map_add, Finsupp.weight_single, smul_eq_mul] at this
    omega
  · exact absurd rfl hm

end MvPolynomial
