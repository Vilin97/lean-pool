/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPolynomialHeight
public import Mathlib.Tactic

/-!
# Exceptional-place bookkeeping for Corvaja--Zannier

This file constructs the exceptional set used in the global summation in
Corvaja--Zannier Proposition 2.  For two nonzero functions `u` and `v`, it is
the union of the supports of their exhaustive principal divisors.  Thus both
functions, every auxiliary grid monomial, and their grid product have order
zero away from the set.  Its residue-degree-weighted size is at most twice
the sum of the two heights.

The final section proves the source estimate

`-(H(u) + H(v)) <= sum_{w in S} ord_w ((1-v)/(1-u)) deg(w)`.

The same estimate is also supplied in the paper's orientation
`(1-u)/(1-v)`.  No algebraic-closedness hypothesis is needed for the weighted
statements; over an algebraically closed constant field they specialize to
ordinary cardinality and unweighted orders.

Source provenance: published pages 1936--1937; checked semantic
reconstruction `Papers/CorvajaZannier2013/CorvajaZannier2013.tex`, lines
731--779.  The earlier Proposition 2 source gives the same bookkeeping in
`Papers/arXiv-math-0512074v3/jag_rivisto2.tex`, lines 618--653.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) exceptionalSupportPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance exceptionalSupportPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

local instance exceptionalSupportFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance exceptionalSupportFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance exceptionalSupportPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance exceptionalSupportFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance exceptionalSupportInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance exceptionalSupportInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

private theorem finitePlaceOrder_one
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (w : HeightOneSpectrum R) :
    finitePlaceOrder w (1 : F) = 0 := by
  have h := finitePlaceOrderTop_one (L := F) w
  rw [finitePlaceOrderTop_eq_coe w (1 : F) one_ne_zero] at h
  exact_mod_cast h

omit [DecidableEq K] in
/-- The exhaustive principal divisor of one is zero. -/
theorem finiteExtensionPrincipalDivisor_one :
    finiteExtensionPrincipalDivisor K L (1 : L) = 0 := by
  classical
  ext w
  cases w with
  | inl q =>
      rw [finiteExtensionPrincipalDivisor_inl]
      simpa using finitePlaceOrder_one
        (w := q) (F := FractionRing (RatFuncFiniteIntegralClosure K L))
  | inr P =>
      rw [finiteExtensionPrincipalDivisor_inr]
      simpa using finitePlaceOrder_one
        (w := primeOverHeightOne (ratFuncInfinityPlace K) P)
        (F := FractionRing (RatFuncInfinityIntegralClosure K L))

omit [DecidableEq K] in
/-- Exhaustive principal divisors turn a nonzero product into a sum. -/
theorem finiteExtensionPrincipalDivisor_mul
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteExtensionPrincipalDivisor K L (x * y) =
      finiteExtensionPrincipalDivisor K L x +
        finiteExtensionPrincipalDivisor K L y := by
  classical
  ext w
  cases w with
  | inl q =>
      have hx' :
          (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x ≠ 0 :=
        by simpa using
          (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.injective.ne hx
      have hy' :
          (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm y ≠ 0 :=
        by simpa using
          (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.injective.ne hy
      have h := congrArg (fun D => D q)
        (finitePrincipalDivisor_mul
          (R := RatFuncFiniteIntegralClosure K L)
          ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)
          ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm y)
          hx' hy')
      simpa only [finiteExtensionPrincipalDivisor_inl, map_mul,
        finitePrincipalDivisor_apply, Finsupp.add_apply] using h
  | inr P =>
      let w := primeOverHeightOne (ratFuncInfinityPlace K) P
      have hx' :
          (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x ≠ 0 :=
        by simpa using
          (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm.injective.ne hx
      have hy' :
          (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm y ≠ 0 :=
        by simpa using
          (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm.injective.ne hy
      have h := congrArg (fun D => D w)
        (finitePrincipalDivisor_mul
          (R := RatFuncInfinityIntegralClosure K L)
          ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)
          ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm y)
          hx' hy')
      simpa only [finiteExtensionPrincipalDivisor_inr, map_mul,
        finitePrincipalDivisor_apply, Finsupp.add_apply] using h

omit [DecidableEq K] in
/-- Exhaustive principal divisors turn a nonzero power into a multiple. -/
theorem finiteExtensionPrincipalDivisor_pow
    (x : L) (hx : x ≠ 0) (m : ℕ) :
    finiteExtensionPrincipalDivisor K L (x ^ m) =
      m • finiteExtensionPrincipalDivisor K L x := by
  classical
  induction m with
  | zero => simp [finiteExtensionPrincipalDivisor_one K L]
  | succ m ih =>
      rw [pow_succ, finiteExtensionPrincipalDivisor_mul K L
        (x ^ m) x (pow_ne_zero _ hx) hx, ih, succ_nsmul]

omit [DecidableEq K] in
/-- Exhaustive principal divisors turn a nonzero inverse into a negative. -/
theorem finiteExtensionPrincipalDivisor_inv
    (x : L) (hx : x ≠ 0) :
    finiteExtensionPrincipalDivisor K L x⁻¹ =
      -finiteExtensionPrincipalDivisor K L x := by
  classical
  have hmul := finiteExtensionPrincipalDivisor_mul K L x⁻¹ x
    (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx, finiteExtensionPrincipalDivisor_one K L] at hmul
  exact eq_neg_of_add_eq_zero_left hmul.symm

omit [DecidableEq K] in
/-- Exhaustive principal divisors turn a quotient into a difference. -/
theorem finiteExtensionPrincipalDivisor_div
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteExtensionPrincipalDivisor K L (x / y) =
      finiteExtensionPrincipalDivisor K L x -
        finiteExtensionPrincipalDivisor K L y := by
  classical
  rw [div_eq_mul_inv, finiteExtensionPrincipalDivisor_mul K L x y⁻¹ hx
    (inv_ne_zero hy), finiteExtensionPrincipalDivisor_inv K L y hy, sub_eq_add_neg]

/-- Product of all grid monomials in the auxiliary family.  Its divisor is
the `ordGrid` term in the global Wronskian summation. -/
def finiteExtensionAuxiliaryGridProduct (u v : L) (h k : ℕ) : L :=
  ∏ rs : Fin (k + 1) × Fin h, u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)

omit [DecidableEq K] in
private theorem finiteExtensionPrincipalDivisor_finset_prod
    {ι : Type*} (s : Finset ι) (g : ι → L)
    (hg : ∀ i ∈ s, g i ≠ 0) :
    finiteExtensionPrincipalDivisor K L (∏ i ∈ s, g i) =
      ∑ i ∈ s, finiteExtensionPrincipalDivisor K L (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteExtensionPrincipalDivisor_one K L]
  | @insert a s ha ih =>
      have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, g i ≠ 0 := fun i hi =>
        hg i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        finiteExtensionPrincipalDivisor_mul K L _ _ hga
          (Finset.prod_ne_zero_iff.mpr hgs), ih hgs]

omit [DecidableEq K] in
/-- Exact principal-divisor formula for the auxiliary grid product. -/
theorem finiteExtensionPrincipalDivisor_auxiliaryGridProduct
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0) (h k : ℕ) :
    finiteExtensionPrincipalDivisor K L
        (finiteExtensionAuxiliaryGridProduct L u v h k) =
      ∑ rs : Fin (k + 1) × Fin h,
        ((rs.1 : ℕ) • finiteExtensionPrincipalDivisor K L u +
          (rs.2 : ℕ) • finiteExtensionPrincipalDivisor K L v) := by
  classical
  rw [finiteExtensionAuxiliaryGridProduct,
    finiteExtensionPrincipalDivisor_finset_prod K L Finset.univ
      (fun rs : Fin (k + 1) × Fin h =>
        u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))]
  · apply Finset.sum_congr rfl
    intro rs _
    rw [finiteExtensionPrincipalDivisor_mul K L _ _
        (pow_ne_zero _ hu) (pow_ne_zero _ hv),
      finiteExtensionPrincipalDivisor_pow K L u hu,
      finiteExtensionPrincipalDivisor_pow K L v hv]
  · intro rs _
    exact mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)

private theorem weightedSupportDegree_le_positive_add_negative
    {ι : Type*} [DecidableEq ι] (D : ι →₀ ℤ) (weight : ι → ℕ) :
    ∑ i ∈ D.support, weight i ≤
      (∑ i ∈ D.support.filter (fun i => 0 < D i),
        (D i).toNat * weight i) +
      ∑ i ∈ D.support.filter (fun i => D i < 0),
        (-D i).toNat * weight i := by
  classical
  have hfilters :
      D.support.filter (fun i => ¬ 0 < D i) =
        D.support.filter (fun i => D i < 0) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hi, hnotpos⟩
      have hine : D i ≠ 0 := Finsupp.mem_support_iff.mp hi
      exact ⟨hi, lt_of_le_of_ne (le_of_not_gt hnotpos) hine⟩
    · intro ⟨hi, hneg⟩
      exact ⟨hi, not_lt_of_ge (le_of_lt hneg)⟩
  rw [← Finset.sum_filter_add_sum_filter_not D.support
      (fun i => 0 < D i) weight, hfilters]
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    have hpos : 0 < D i := (Finset.mem_filter.mp hi).2
    have hone : 1 ≤ (D i).toNat := by omega
    simpa using Nat.mul_le_mul_right (weight i) hone
  · apply Finset.sum_le_sum
    intro i hi
    have hneg : D i < 0 := (Finset.mem_filter.mp hi).2
    have hone : 1 ≤ (-D i).toNat := by omega
    simpa using Nat.mul_le_mul_right (weight i) hone

local instance exceptionalSupportPlaceDecidableEq :
    DecidableEq (FiniteExtensionPlace K L) := Classical.decEq _

/-- The residue-degree-weighted number of places in the support of a
principal divisor is bounded by its positive degree plus its pole height. -/
theorem finiteExtensionPrincipalDivisor_supportDegree_le
    (x : L) :
    ∑ w ∈ (finiteExtensionPrincipalDivisor K L x).support,
        finiteExtensionPlaceDegree K L w ≤
      finiteExtensionPositiveDegree K L x + finiteExtensionHeight K L x := by
  simpa only [finiteExtensionPositiveDegree, finiteExtensionHeight] using
    weightedSupportDegree_le_positive_add_negative
      (finiteExtensionPrincipalDivisor K L x)
      (finiteExtensionPlaceDegree K L)

/-- For a nonzero function, the weighted support has degree at most twice
its height. -/
theorem finiteExtensionPrincipalDivisor_supportDegree_le_two_mul_height
    (x : L) (hx : x ≠ 0) :
    ∑ w ∈ (finiteExtensionPrincipalDivisor K L x).support,
        finiteExtensionPlaceDegree K L w ≤
      2 * finiteExtensionPositiveDegree K L x := by
  calc
    _ ≤ finiteExtensionPositiveDegree K L x + finiteExtensionHeight K L x :=
      finiteExtensionPrincipalDivisor_supportDegree_le K L x
    _ = finiteExtensionPositiveDegree K L x +
        finiteExtensionPositiveDegree K L x := by
      rw [← finiteExtensionPositiveDegree_eq_height K L x hx]
    _ = _ := by omega

private def finsuppWeightedNegativeDegree
    {ι : Type*} [DecidableEq ι] (D : ι →₀ ℤ) (weight : ι → ℕ) : ℕ :=
  ∑ i ∈ D.support, (-D i).toNat * weight i

private theorem finsuppWeightedNegativeDegree_eq_filter
    {ι : Type*} [DecidableEq ι] (D : ι →₀ ℤ) (weight : ι → ℕ) :
    finsuppWeightedNegativeDegree D weight =
      ∑ i ∈ D.support.filter (fun i => D i < 0),
        (-D i).toNat * weight i := by
  classical
  calc
    ∑ i ∈ D.support, (-D i).toNat * weight i =
        (∑ i ∈ D.support.filter (fun i => D i < 0),
          (-D i).toNat * weight i) +
        ∑ i ∈ D.support.filter (fun i => ¬ D i < 0),
          (-D i).toNat * weight i := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = (∑ i ∈ D.support.filter (fun i => D i < 0),
          (-D i).toNat * weight i) + 0 := by
      congr 1
      apply Finset.sum_eq_zero
      intro i hi
      have hnonneg : 0 ≤ D i := le_of_not_gt (Finset.mem_filter.mp hi).2
      rw [Int.toNat_of_nonpos (neg_nonpos.mpr hnonneg)]
      simp
    _ = _ := by simp

private theorem finsuppWeightedPositiveDegree_eq_filter
    {ι : Type*} [DecidableEq ι] (D : ι →₀ ℤ) (weight : ι → ℕ) :
    (∑ i ∈ D.support, (D i).toNat * weight i) =
      ∑ i ∈ D.support.filter (fun i => 0 < D i),
        (D i).toNat * weight i := by
  classical
  calc
    ∑ i ∈ D.support, (D i).toNat * weight i =
        (∑ i ∈ D.support.filter (fun i => 0 < D i),
          (D i).toNat * weight i) +
        ∑ i ∈ D.support.filter (fun i => ¬ 0 < D i),
          (D i).toNat * weight i := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = (∑ i ∈ D.support.filter (fun i => 0 < D i),
          (D i).toNat * weight i) + 0 := by
      congr 1
      apply Finset.sum_eq_zero
      intro i hi
      have hnonpos : D i ≤ 0 := le_of_not_gt (Finset.mem_filter.mp hi).2
      rw [Int.toNat_of_nonpos hnonpos]
      simp
    _ = _ := by simp

private theorem finsuppWeightedNegativeDegree_eq_sum_of_support_subset
    {ι : Type*} [DecidableEq ι] (D : ι →₀ ℤ) (weight : ι → ℕ)
    (s : Finset ι) (hs : D.support ⊆ s) :
    finsuppWeightedNegativeDegree D weight =
      ∑ i ∈ s, (-D i).toNat * weight i := by
  apply Finset.sum_subset hs
  intro i _ hi
  have hzero : D i = 0 := Finsupp.notMem_support_iff.mp hi
  simp [hzero]

private theorem finsuppWeightedNegativeDegree_add_le
    {ι : Type*} [DecidableEq ι] (D E : ι →₀ ℤ) (weight : ι → ℕ) :
    finsuppWeightedNegativeDegree (D + E) weight ≤
      finsuppWeightedNegativeDegree D weight +
        finsuppWeightedNegativeDegree E weight := by
  let s := D.support ∪ E.support
  rw [finsuppWeightedNegativeDegree_eq_sum_of_support_subset
      (D + E) weight s Finsupp.support_add,
    finsuppWeightedNegativeDegree_eq_sum_of_support_subset
      D weight s Finset.subset_union_left,
    finsuppWeightedNegativeDegree_eq_sum_of_support_subset
      E weight s Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hlocal : (-(D i + E i)).toNat ≤
      (-D i).toNat + (-E i).toNat := by omega
  simpa [Finsupp.add_apply, add_mul] using
    Nat.mul_le_mul_right (weight i) hlocal

private theorem finiteExtensionHeight_eq_finsuppWeightedNegativeDegree
    (x : L) :
    finiteExtensionHeight K L x =
      finsuppWeightedNegativeDegree
        (finiteExtensionPrincipalDivisor K L x)
        (finiteExtensionPlaceDegree K L) := by
  rw [finsuppWeightedNegativeDegree_eq_filter]
  rfl

/-- Pole height is subadditive under multiplication. -/
theorem finiteExtensionHeight_mul_le
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteExtensionHeight K L (x * y) ≤
      finiteExtensionHeight K L x + finiteExtensionHeight K L y := by
  rw [finiteExtensionHeight_eq_finsuppWeightedNegativeDegree,
    finiteExtensionHeight_eq_finsuppWeightedNegativeDegree,
    finiteExtensionHeight_eq_finsuppWeightedNegativeDegree,
    finiteExtensionPrincipalDivisor_mul K L x y hx hy]
  exact finsuppWeightedNegativeDegree_add_le _ _ _

/-- The pole height of an inverse is the positive degree of the original
function. -/
theorem finiteExtensionHeight_inv_eq_positiveDegree
    (x : L) (hx : x ≠ 0) :
    finiteExtensionHeight K L x⁻¹ = finiteExtensionPositiveDegree K L x := by
  rw [finiteExtensionHeight_eq_finsuppWeightedNegativeDegree,
    finiteExtensionPrincipalDivisor_inv K L x hx,
    finsuppWeightedNegativeDegree,
    finiteExtensionPositiveDegree]
  simpa using finsuppWeightedPositiveDegree_eq_filter
    (finiteExtensionPrincipalDivisor K L x) (finiteExtensionPlaceDegree K L)

/-- Pole height is invariant under inversion of a nonzero function. -/
theorem finiteExtensionHeight_inv
    (x : L) (hx : x ≠ 0) :
    finiteExtensionHeight K L x⁻¹ = finiteExtensionHeight K L x := by
  rw [finiteExtensionHeight_inv_eq_positiveDegree K L x hx,
    finiteExtensionPositiveDegree_eq_height K L x hx]

/-- Pole height is subadditive under division. -/
theorem finiteExtensionHeight_div_le
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteExtensionHeight K L (x / y) ≤
      finiteExtensionHeight K L x + finiteExtensionHeight K L y := by
  rw [div_eq_mul_inv]
  calc
    finiteExtensionHeight K L (x * y⁻¹) ≤
        finiteExtensionHeight K L x + finiteExtensionHeight K L y⁻¹ :=
      finiteExtensionHeight_mul_le K L x y⁻¹ hx (inv_ne_zero hy)
    _ = _ := by rw [finiteExtensionHeight_inv K L y hy]

private theorem finitePlaceOrder_neg
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (w : HeightOneSpectrum R) (x : F) (hx : x ≠ 0) :
    finitePlaceOrder w (-x) = finitePlaceOrder w x := by
  have hval : (w.valuation F) (-x) = (w.valuation F) x := by simp
  rw [valuation_eq_exp_neg_finitePlaceOrder w (-x) (neg_ne_zero.mpr hx),
    valuation_eq_exp_neg_finitePlaceOrder w x hx] at hval
  have horder := WithZero.exp_injective hval
  omega

private theorem finitePlaceOrder_one_sub_eq_of_neg
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (w : HeightOneSpectrum R) (x : F) (hx : x ≠ 0)
    (hxneg : finitePlaceOrder w x < 0) :
    finitePlaceOrder w (1 - x) = finitePlaceOrder w x := by
  have hxone : x ≠ 1 := by
    intro h
    subst x
    rw [finitePlaceOrder_one] at hxneg
    omega
  have honeSub : 1 - x ≠ 0 := sub_ne_zero.mpr hxone.symm
  have hlower := finitePlaceOrder_add_ge_min w (1 : F) (-x)
    one_ne_zero (neg_ne_zero.mpr hx)
    (by simpa [sub_eq_add_neg] using honeSub)
  rw [show (1 : F) + -x = 1 - x by ring,
    finitePlaceOrder_one, finitePlaceOrder_neg w x hx,
    min_eq_right (le_of_lt hxneg)] at hlower
  have hreverse := finitePlaceOrder_add_ge_min w (1 : F) (-(1 - x))
    one_ne_zero (neg_ne_zero.mpr honeSub)
    (by simpa using hx)
  rw [show (1 : F) + -(1 - x) = x by ring,
    finitePlaceOrder_one,
    finitePlaceOrder_neg w (1 - x) honeSub] at hreverse
  by_cases hnonneg : 0 ≤ finitePlaceOrder w (1 - x)
  · rw [min_eq_left hnonneg] at hreverse
    omega
  · have hnonpos : finitePlaceOrder w (1 - x) ≤ 0 := le_of_not_ge hnonneg
    rw [min_eq_right hnonpos] at hreverse
    exact le_antisymm hreverse hlower

omit [DecidableEq K] in
/-- At a pole of `x`, subtracting `x` from one does not change the exhaustive
place order. -/
theorem finiteExtensionPrincipalDivisor_one_sub_apply_of_neg
    (x : L) (hx : x ≠ 0) (w : FiniteExtensionPlace K L)
    (hxneg : finiteExtensionPrincipalDivisor K L x w < 0) :
    finiteExtensionPrincipalDivisor K L (1 - x) w =
      finiteExtensionPrincipalDivisor K L x w := by
  cases w with
  | inl q =>
      have hx' :
          (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x ≠ 0 := by
        simpa using
          (ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm.injective.ne hx
      change finitePlaceOrder q
        ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x) < 0 at hxneg
      change finitePlaceOrder q
          ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm (1 - x)) =
        finitePlaceOrder q
          ((ratFuncFiniteIntegralClosureFractionRingEquiv K L).symm x)
      rw [map_sub, map_one]
      exact finitePlaceOrder_one_sub_eq_of_neg q _ hx' hxneg
  | inr P =>
      let q := primeOverHeightOne (ratFuncInfinityPlace K) P
      have hx' :
          (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x ≠ 0 := by
        simpa using
          (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm.injective.ne hx
      change finitePlaceOrder q
        ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x) < 0 at hxneg
      change finitePlaceOrder q
          ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm (1 - x)) =
        finitePlaceOrder q
          ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm x)
      rw [map_sub, map_one]
      exact finitePlaceOrder_one_sub_eq_of_neg q _ hx' hxneg

omit [DecidableEq K] in
private theorem finiteExtensionPrincipalDivisor_one_sub_negativePart
    (x : L) (hx : x ≠ 0) (hxone : x ≠ 1)
    (w : FiniteExtensionPlace K L) :
    (-finiteExtensionPrincipalDivisor K L (1 - x) w).toNat =
      (-finiteExtensionPrincipalDivisor K L x w).toNat := by
  by_cases hxneg : finiteExtensionPrincipalDivisor K L x w < 0
  · rw [finiteExtensionPrincipalDivisor_one_sub_apply_of_neg K L x hx w hxneg]
  · by_cases hsubneg : finiteExtensionPrincipalDivisor K L (1 - x) w < 0
    · have hsubne : 1 - x ≠ 0 := sub_ne_zero.mpr hxone.symm
      have hreverse := finiteExtensionPrincipalDivisor_one_sub_apply_of_neg
        K L (1 - x) hsubne w hsubneg
      rw [show (1 : L) - (1 - x) = x by ring] at hreverse
      rw [hreverse]
    · have hxnonneg : 0 ≤ finiteExtensionPrincipalDivisor K L x w :=
        le_of_not_gt hxneg
      have hsubnonneg : 0 ≤
          finiteExtensionPrincipalDivisor K L (1 - x) w :=
        le_of_not_gt hsubneg
      rw [Int.toNat_of_nonpos (neg_nonpos.mpr hsubnonneg),
        Int.toNat_of_nonpos (neg_nonpos.mpr hxnonneg)]

/-- The functions `x` and `1-x` have the same pole height. -/
theorem finiteExtensionHeight_one_sub
    (x : L) (hx : x ≠ 0) (hxone : x ≠ 1) :
    finiteExtensionHeight K L (1 - x) = finiteExtensionHeight K L x := by
  rw [finiteExtensionHeight_eq_finsuppWeightedNegativeDegree,
    finiteExtensionHeight_eq_finsuppWeightedNegativeDegree]
  let Dsub := finiteExtensionPrincipalDivisor K L (1 - x)
  let Dx := finiteExtensionPrincipalDivisor K L x
  let s := Dsub.support ∪ Dx.support
  rw [finsuppWeightedNegativeDegree_eq_sum_of_support_subset
      Dsub (finiteExtensionPlaceDegree K L) s Finset.subset_union_left,
    finsuppWeightedNegativeDegree_eq_sum_of_support_subset
      Dx (finiteExtensionPlaceDegree K L) s Finset.subset_union_right]
  apply Finset.sum_congr rfl
  intro w _
  rw [show Dsub w = finiteExtensionPrincipalDivisor K L (1 - x) w by rfl,
    show Dx w = finiteExtensionPrincipalDivisor K L x w by rfl,
    finiteExtensionPrincipalDivisor_one_sub_negativePart K L x hx hxone w]

private theorem sum_union_le_sum_add_sum
    {ι : Type*} [DecidableEq ι] (s t : Finset ι) (g : ι → ℕ) :
    ∑ i ∈ s ∪ t, g i ≤ (∑ i ∈ s, g i) + ∑ i ∈ t, g i := by
  calc
    ∑ i ∈ s ∪ t, g i =
        (∑ i ∈ s, g i) + ∑ i ∈ t \ s, g i := by
      rw [show s ∪ t = s ∪ (t \ s) by ext i; simp,
        Finset.sum_union Finset.disjoint_sdiff]
    _ ≤ (∑ i ∈ s, g i) + ∑ i ∈ t, g i := by
      exact Nat.add_le_add_left
        (Finset.sum_le_sum_of_subset Finset.sdiff_subset) _

section ExceptionalSet

variable {A : Type*} [Fintype A]

/-- Embed the divisor support of one function into the common support of its family. -/
def finiteExtensionFamilyMemberSupportEmbedding
    (f : A → L) (a : A) :
    {w // w ∈ (finiteExtensionPrincipalDivisor K L (f a)).support} ↪
      FiniteExtensionFamilyPlace K L f where
  toFun w := ⟨w.1,
    finiteExtensionPrincipalDivisor_support_subset_familySupport K L f a w.2⟩
  inj' := by
    intro w z hwz
    apply Subtype.ext
    exact congrArg
      (fun q : FiniteExtensionFamilyPlace K L f => q.1) hwz

/-- The support of one family member, lifted to the common family place
type. -/
def finiteExtensionFamilyMemberSupport (f : A → L) (a : A) :
    Finset (FiniteExtensionFamilyPlace K L f) := by
  classical
  exact (finiteExtensionPrincipalDivisor K L (f a)).support.attach.map
    (finiteExtensionFamilyMemberSupportEmbedding K L f a)

omit [DecidableEq K] in
@[simp]
theorem mem_finiteExtensionFamilyMemberSupport_iff
    (f : A → L) (a : A) (w : FiniteExtensionFamilyPlace K L f) :
    w ∈ finiteExtensionFamilyMemberSupport K L f a ↔
      w.1 ∈ (finiteExtensionPrincipalDivisor K L (f a)).support := by
  classical
  constructor
  · intro hw
    rw [finiteExtensionFamilyMemberSupport, Finset.mem_map] at hw
    obtain ⟨z, _, hz⟩ := hw
    have hval : z.1 = w.1 := congrArg
      (fun q : FiniteExtensionFamilyPlace K L f => q.1) hz
    simpa only [hval] using z.2
  · intro hw
    rw [finiteExtensionFamilyMemberSupport, Finset.mem_map]
    refine ⟨⟨w.1, hw⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem sum_finiteExtensionFamilyMemberSupport_placeDegree
    (f : A → L) (a : A) :
    ∑ w ∈ finiteExtensionFamilyMemberSupport K L f a,
        finiteExtensionPlaceDegree K L w.1 =
      ∑ w ∈ (finiteExtensionPrincipalDivisor K L (f a)).support,
        finiteExtensionPlaceDegree K L w := by
  classical
  rw [finiteExtensionFamilyMemberSupport, Finset.sum_map]
  simpa [finiteExtensionFamilyMemberSupportEmbedding] using!
    (Finset.sum_attach
      (finiteExtensionPrincipalDivisor K L (f a)).support
      (fun w => finiteExtensionPlaceDegree K L w))

/-- The finite exceptional set consisting exactly of the zero and pole places
of the selected functions `u` and `v`, embedded into a caller's common family
place type. -/
def finiteExtensionExceptionalSet (f : A → L) (iU iV : A) :
    Finset (FiniteExtensionFamilyPlace K L f) := by
  classical
  exact finiteExtensionFamilyMemberSupport K L f iU ∪
    finiteExtensionFamilyMemberSupport K L f iV

@[simp]
theorem mem_finiteExtensionExceptionalSet_iff
    (f : A → L) (iU iV : A) (w : FiniteExtensionFamilyPlace K L f) :
    w ∈ finiteExtensionExceptionalSet K L f iU iV ↔
      w.1 ∈ (finiteExtensionPrincipalDivisor K L (f iU)).support ∨
        w.1 ∈ (finiteExtensionPrincipalDivisor K L (f iV)).support := by
  simp [finiteExtensionExceptionalSet]

/-- Residue-degree-weighted boundary bound for the exceptional set. -/
theorem finiteExtensionExceptionalSet_weightedDegree_le
    (f : A → L) (iU iV : A) (hu : f iU ≠ 0) (hv : f iV ≠ 0) :
    ∑ w ∈ finiteExtensionExceptionalSet K L f iU iV,
        finiteExtensionPlaceDegree K L w.1 ≤
      2 * (finiteExtensionPositiveDegree K L (f iU) +
        finiteExtensionPositiveDegree K L (f iV)) := by
  calc
    _ ≤
        (∑ w ∈ finiteExtensionFamilyMemberSupport K L f iU,
          finiteExtensionPlaceDegree K L w.1) +
        ∑ w ∈ finiteExtensionFamilyMemberSupport K L f iV,
          finiteExtensionPlaceDegree K L w.1 := by
      simpa only [finiteExtensionExceptionalSet] using
        sum_union_le_sum_add_sum
          (finiteExtensionFamilyMemberSupport K L f iU)
          (finiteExtensionFamilyMemberSupport K L f iV)
          (fun w => finiteExtensionPlaceDegree K L w.1)
    _ =
        (∑ w ∈ (finiteExtensionPrincipalDivisor K L (f iU)).support,
          finiteExtensionPlaceDegree K L w) +
        ∑ w ∈ (finiteExtensionPrincipalDivisor K L (f iV)).support,
          finiteExtensionPlaceDegree K L w := by
      rw [sum_finiteExtensionFamilyMemberSupport_placeDegree,
        sum_finiteExtensionFamilyMemberSupport_placeDegree]
    _ ≤ 2 * finiteExtensionPositiveDegree K L (f iU) +
        2 * finiteExtensionPositiveDegree K L (f iV) :=
      Nat.add_le_add
        (finiteExtensionPrincipalDivisor_supportDegree_le_two_mul_height
          K L (f iU) hu)
        (finiteExtensionPrincipalDivisor_supportDegree_le_two_mul_height
          K L (f iV) hv)
    _ = _ := by omega

/-- The sum of the weighted orders over an arbitrary subset of the common
family place type is bounded below by minus the full pole height. -/
theorem finiteExtensionFamilyWeightedOrder_sum_ge_neg_height
    (f : A → L) (a : A)
    (S : Finset (FiniteExtensionFamilyPlace K L f)) :
    -((finiteExtensionHeight K L (f a) : ℕ) : ℤ) ≤
      ∑ w ∈ S, finiteExtensionFamilyWeightedOrder K L f a w := by
  classical
  let N := Finset.univ.filter
    (fun w : FiniteExtensionFamilyPlace K L f =>
      finiteExtensionFamilyOrder K L f a w < 0)
  let T := S.filter
    (fun w : FiniteExtensionFamilyPlace K L f =>
      finiteExtensionFamilyOrder K L f a w < 0)
  have hTN : T ⊆ N := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
      (Finset.mem_filter.mp hw).2⟩
  have hfilterTN : N.filter (fun w => w ∈ T) = T := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · exact fun hw => hw.2
    · exact fun hw => ⟨hTN hw, hw⟩
  have hMissingNonpos :
      ∑ w ∈ N.filter (fun w => ¬ w ∈ T),
          finiteExtensionFamilyWeightedOrder K L f a w ≤ 0 := by
    apply Finset.sum_nonpos
    intro w hw
    have hneg : finiteExtensionFamilyOrder K L f a w < 0 := by
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
    rw [finiteExtensionFamilyWeightedOrder]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (by positivity)
  have hNegativeAllLeT :
      (∑ w ∈ N, finiteExtensionFamilyWeightedOrder K L f a w) ≤
        ∑ w ∈ T, finiteExtensionFamilyWeightedOrder K L f a w := by
    have hsplit := Finset.sum_filter_add_sum_filter_not N
      (fun w => w ∈ T) (fun w =>
        finiteExtensionFamilyWeightedOrder K L f a w)
    rw [hfilterTN] at hsplit
    linarith
  have hRemainingNonneg :
      0 ≤ ∑ w ∈ S.filter (fun w =>
          ¬ finiteExtensionFamilyOrder K L f a w < 0),
        finiteExtensionFamilyWeightedOrder K L f a w := by
    apply Finset.sum_nonneg
    intro w hw
    have hnonneg : 0 ≤ finiteExtensionFamilyOrder K L f a w :=
      le_of_not_gt (Finset.mem_filter.mp hw).2
    rw [finiteExtensionFamilyWeightedOrder]
    exact mul_nonneg hnonneg (by positivity)
  have hTLeS :
      (∑ w ∈ T, finiteExtensionFamilyWeightedOrder K L f a w) ≤
        ∑ w ∈ S, finiteExtensionFamilyWeightedOrder K L f a w := by
    have hsplit := Finset.sum_filter_add_sum_filter_not S
      (fun w => finiteExtensionFamilyOrder K L f a w < 0)
      (fun w => finiteExtensionFamilyWeightedOrder K L f a w)
    change (∑ w ∈ T, finiteExtensionFamilyWeightedOrder K L f a w) +
        ∑ w ∈ S.filter (fun w =>
          ¬ finiteExtensionFamilyOrder K L f a w < 0),
          finiteExtensionFamilyWeightedOrder K L f a w =
        ∑ w ∈ S, finiteExtensionFamilyWeightedOrder K L f a w at hsplit
    linarith
  have hNegativeAll := finiteExtensionFamilyWeightedNegativeSum K L f a
  change (∑ w ∈ N, finiteExtensionFamilyWeightedOrder K L f a w) =
      -((finiteExtensionHeight K L (f a) : ℕ) : ℤ) at hNegativeAll
  rw [← hNegativeAll]
  exact hNegativeAllLeT.trans hTLeS

/-- The height bound for the reciprocal one-minus ratio used in the support
estimate. -/
theorem finiteExtensionHeight_one_sub_div_one_sub_le
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1) :
    finiteExtensionHeight K L ((1 - v) / (1 - u)) ≤
      finiteExtensionHeight K L u + finiteExtensionHeight K L v := by
  have hnum : 1 - v ≠ 0 := sub_ne_zero.mpr hvone.symm
  have hden : 1 - u ≠ 0 := sub_ne_zero.mpr huone.symm
  calc
    finiteExtensionHeight K L ((1 - v) / (1 - u)) ≤
        finiteExtensionHeight K L (1 - v) +
          finiteExtensionHeight K L (1 - u) :=
      finiteExtensionHeight_div_le K L (1 - v) (1 - u) hnum hden
    _ = finiteExtensionHeight K L v + finiteExtensionHeight K L u := by
      rw [finiteExtensionHeight_one_sub K L v hv hvone,
        finiteExtensionHeight_one_sub K L u hu huone]
    _ = _ := by omega

/-- The source lower bound for the exceptional-set contribution of
`rho = (1-v)/(1-u)`. -/
theorem finiteExtensionExceptionalSet_oneSubV_div_oneSubU_weightedOrder_lower_bound
    (f : A → L) (iU iV iRho : A)
    (hu : f iU ≠ 0) (hv : f iV ≠ 0)
    (huone : f iU ≠ 1) (hvone : f iV ≠ 1)
    (hRho : f iRho = (1 - f iV) / (1 - f iU)) :
    -((finiteExtensionPositiveDegree K L (f iU) : ℕ) +
        finiteExtensionPositiveDegree K L (f iV) : ℤ) ≤
      ∑ w ∈ finiteExtensionExceptionalSet K L f iU iV,
        finiteExtensionFamilyWeightedOrder K L f iRho w := by
  have hheight :
      finiteExtensionHeight K L (f iRho) ≤
        finiteExtensionPositiveDegree K L (f iU) +
          finiteExtensionPositiveDegree K L (f iV) := by
    rw [hRho]
    calc
      finiteExtensionHeight K L ((1 - f iV) / (1 - f iU)) ≤
          finiteExtensionHeight K L (f iU) +
            finiteExtensionHeight K L (f iV) :=
        finiteExtensionHeight_one_sub_div_one_sub_le K L
          (f iU) (f iV) hu hv huone hvone
      _ = _ := by
        rw [← finiteExtensionPositiveDegree_eq_height K L (f iU) hu,
          ← finiteExtensionPositiveDegree_eq_height K L (f iV) hv]
  have hheightInt :
      (finiteExtensionHeight K L (f iRho) : ℤ) ≤
        (finiteExtensionPositiveDegree K L (f iU) : ℤ) +
          (finiteExtensionPositiveDegree K L (f iV) : ℤ) := by
    exact_mod_cast hheight
  exact (neg_le_neg hheightInt).trans
    (finiteExtensionFamilyWeightedOrder_sum_ge_neg_height K L f iRho
      (finiteExtensionExceptionalSet K L f iU iV))

/-- The same lower bound in the paper's orientation
`rho = (1-u)/(1-v)`. -/
theorem finiteExtensionExceptionalSet_oneSubU_div_oneSubV_weightedOrder_lower_bound
    (f : A → L) (iU iV iRho : A)
    (hu : f iU ≠ 0) (hv : f iV ≠ 0)
    (huone : f iU ≠ 1) (hvone : f iV ≠ 1)
    (hRho : f iRho = (1 - f iU) / (1 - f iV)) :
    -((finiteExtensionPositiveDegree K L (f iU) : ℕ) +
        finiteExtensionPositiveDegree K L (f iV) : ℤ) ≤
      ∑ w ∈ finiteExtensionExceptionalSet K L f iU iV,
        finiteExtensionFamilyWeightedOrder K L f iRho w := by
  simpa [finiteExtensionExceptionalSet, Finset.union_comm, add_comm] using
    finiteExtensionExceptionalSet_oneSubV_div_oneSubU_weightedOrder_lower_bound
      K L f iV iU iRho hv hu hvone huone hRho

/-- Away from the exceptional set, `u` has order zero. -/
theorem finiteExtensionFamilyOrder_u_eq_zero_outsideExceptionalSet
    (f : A → L) (iU iV : A) (w : FiniteExtensionFamilyPlace K L f)
    (hw : w ∉ finiteExtensionExceptionalSet K L f iU iV) :
    finiteExtensionFamilyOrder K L f iU w = 0 := by
  apply finiteExtensionFamilyOrder_eq_zero_of_not_mem_support K L f iU w
  exact (not_or.mp ((mem_finiteExtensionExceptionalSet_iff K L f iU iV w).not.mp hw)).1

/-- Away from the exceptional set, `v` has order zero. -/
theorem finiteExtensionFamilyOrder_v_eq_zero_outsideExceptionalSet
    (f : A → L) (iU iV : A) (w : FiniteExtensionFamilyPlace K L f)
    (hw : w ∉ finiteExtensionExceptionalSet K L f iU iV) :
    finiteExtensionFamilyOrder K L f iV w = 0 := by
  apply finiteExtensionFamilyOrder_eq_zero_of_not_mem_support K L f iV w
  exact (not_or.mp ((mem_finiteExtensionExceptionalSet_iff K L f iU iV w).not.mp hw)).2

/-- Every positive-order place of `v` lies in the exceptional set. -/
theorem finiteExtensionFamilyOrder_v_positive_mem_exceptionalSet
    (f : A → L) (iU iV : A) (w : FiniteExtensionFamilyPlace K L f)
    (hw : 0 < finiteExtensionFamilyOrder K L f iV w) :
    w ∈ finiteExtensionExceptionalSet K L f iU iV := by
  rw [mem_finiteExtensionExceptionalSet_iff]
  right
  rw [Finsupp.mem_support_iff]
  exact ne_of_gt hw

/-- Every individual grid monomial has order zero away from the exceptional
set. -/
theorem finiteExtensionPrincipalDivisor_gridMonomial_eq_zero_outside
    (f : A → L) (iU iV : A) (hu : f iU ≠ 0) (hv : f iV ≠ 0)
    (r s : ℕ) (w : FiniteExtensionFamilyPlace K L f)
    (hw : w ∉ finiteExtensionExceptionalSet K L f iU iV) :
    finiteExtensionPrincipalDivisor K L
        (f iU ^ r * f iV ^ s) w.1 = 0 := by
  rw [finiteExtensionPrincipalDivisor_mul K L _ _
      (pow_ne_zero _ hu) (pow_ne_zero _ hv),
    finiteExtensionPrincipalDivisor_pow K L (f iU) hu,
    finiteExtensionPrincipalDivisor_pow K L (f iV) hv]
  have hu0 := finiteExtensionFamilyOrder_u_eq_zero_outsideExceptionalSet
    K L f iU iV w hw
  have hv0 := finiteExtensionFamilyOrder_v_eq_zero_outsideExceptionalSet
    K L f iU iV w hw
  change finiteExtensionPrincipalDivisor K L (f iU) w.1 = 0 at hu0
  change finiteExtensionPrincipalDivisor K L (f iV) w.1 = 0 at hv0
  simp [hu0, hv0]

/-- The auxiliary grid product has order zero away from the zero and pole
places of `u` and `v`. -/
theorem finiteExtensionPrincipalDivisor_auxiliaryGridProduct_eq_zero_outside
    (f : A → L) (iU iV : A) (hu : f iU ≠ 0) (hv : f iV ≠ 0)
    (h k : ℕ) (w : FiniteExtensionFamilyPlace K L f)
    (hw : w ∉ finiteExtensionExceptionalSet K L f iU iV) :
    finiteExtensionPrincipalDivisor K L
        (finiteExtensionAuxiliaryGridProduct L (f iU) (f iV) h k) w.1 = 0 := by
  rw [finiteExtensionPrincipalDivisor_auxiliaryGridProduct K L
    (f iU) (f iV) hu hv h k]
  have hu0 := finiteExtensionFamilyOrder_u_eq_zero_outsideExceptionalSet
    K L f iU iV w hw
  have hv0 := finiteExtensionFamilyOrder_v_eq_zero_outsideExceptionalSet
    K L f iU iV w hw
  change finiteExtensionPrincipalDivisor K L (f iU) w.1 = 0 at hu0
  change finiteExtensionPrincipalDivisor K L (f iV) w.1 = 0 at hv0
  simp [hu0, hv0]

/-- A family entry equal to the grid product has family order zero away from
the exceptional set. -/
theorem finiteExtensionFamilyOrder_gridProduct_eq_zero_outsideExceptionalSet
    (f : A → L) (iU iV iGrid : A) (hu : f iU ≠ 0) (hv : f iV ≠ 0)
    (h k : ℕ)
    (hGrid : f iGrid = finiteExtensionAuxiliaryGridProduct L (f iU) (f iV) h k)
    (w : FiniteExtensionFamilyPlace K L f)
    (hw : w ∉ finiteExtensionExceptionalSet K L f iU iV) :
    finiteExtensionFamilyOrder K L f iGrid w = 0 := by
  rw [finiteExtensionFamilyOrder, hGrid]
  exact finiteExtensionPrincipalDivisor_auxiliaryGridProduct_eq_zero_outside
    K L f iU iV hu hv h k w hw

section AlgebraicallyClosedConstants

variable [IsAlgClosed K]

/-- Over an algebraically closed constant field, the weighted boundary bound
is the ordinary cardinality bound used in the published proof. -/
theorem finiteExtensionExceptionalSet_card_le
    (f : A → L) (iU iV : A) (hu : f iU ≠ 0) (hv : f iV ≠ 0) :
    (finiteExtensionExceptionalSet K L f iU iV).card ≤
      2 * (finiteExtensionPositiveDegree K L (f iU) +
        finiteExtensionPositiveDegree K L (f iV)) := by
  have hbound := finiteExtensionExceptionalSet_weightedDegree_le
    K L f iU iV hu hv
  simpa [finiteExtensionPlaceDegree_eq_one K L] using hbound

/-- Unweighted source estimate for `rho = (1-v)/(1-u)` over algebraically
closed constants. -/
theorem finiteExtensionExceptionalSet_oneSubV_div_oneSubU_order_lower_bound
    (f : A → L) (iU iV iRho : A)
    (hu : f iU ≠ 0) (hv : f iV ≠ 0)
    (huone : f iU ≠ 1) (hvone : f iV ≠ 1)
    (hRho : f iRho = (1 - f iV) / (1 - f iU)) :
    -((finiteExtensionPositiveDegree K L (f iU) : ℕ) +
        finiteExtensionPositiveDegree K L (f iV) : ℤ) ≤
      ∑ w ∈ finiteExtensionExceptionalSet K L f iU iV,
        finiteExtensionFamilyOrder K L f iRho w := by
  simpa only [finiteExtensionFamilyWeightedOrder_eq_order K L f iRho] using
    finiteExtensionExceptionalSet_oneSubV_div_oneSubU_weightedOrder_lower_bound
      K L f iU iV iRho hu hv huone hvone hRho

/-- Unweighted source estimate in the paper's orientation
`rho = (1-u)/(1-v)`. -/
theorem finiteExtensionExceptionalSet_oneSubU_div_oneSubV_order_lower_bound
    (f : A → L) (iU iV iRho : A)
    (hu : f iU ≠ 0) (hv : f iV ≠ 0)
    (huone : f iU ≠ 1) (hvone : f iV ≠ 1)
    (hRho : f iRho = (1 - f iU) / (1 - f iV)) :
    -((finiteExtensionPositiveDegree K L (f iU) : ℕ) +
        finiteExtensionPositiveDegree K L (f iV) : ℤ) ≤
      ∑ w ∈ finiteExtensionExceptionalSet K L f iU iV,
        finiteExtensionFamilyOrder K L f iRho w := by
  simpa only [finiteExtensionFamilyWeightedOrder_eq_order K L f iRho] using
    finiteExtensionExceptionalSet_oneSubU_div_oneSubV_weightedOrder_lower_bound
      K L f iU iV iRho hu hv huone hvone hRho

end AlgebraicallyClosedConstants

end ExceptionalSet

end

end BGS.CorvajaZannier
