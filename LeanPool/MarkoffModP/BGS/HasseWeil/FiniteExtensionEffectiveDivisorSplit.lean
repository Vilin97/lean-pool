/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionAffineIdealDivisor
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZeroCounting
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient
public import Mathlib.Data.Finsupp.Fintype

/-!
# Splitting effective exhaustive divisors at infinity

An effective divisor on the exhaustive place type of a finite extension of
`K(X)` is a finitely supported natural-number-valued function.  Since that
place type is a sum of finite and above-infinity places, such a divisor
splits canonically into its finite and infinity parts.

This file records the inverse equivalence, degree additivity, the conversion
to the repository's integer-valued effective divisors, and the resulting
fixed-degree convolution.  The finite component is also identified with a
nonzero ideal in the normalization of `K[X]`.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial BigOperators

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- Effective divisors on all exhaustive places. -/
abbrev FiniteExtensionEffectiveDivisor :=
  FiniteExtensionPlace K L →₀ ℕ

/-- Effective divisors supported above the place at infinity. -/
abbrev FiniteExtensionEffectiveInfinityDivisor :=
  FiniteExtensionInfinityPlace K L →₀ ℕ

/-- Natural-number degree of an effective exhaustive divisor. -/
def finiteExtensionEffectiveDivisorDegree
    (D : FiniteExtensionEffectiveDivisor K L) : ℕ :=
  D.sum fun P e => e * finiteExtensionPlaceDegree K L P

/-- Natural-number degree of an effective divisor supported at infinity. -/
def finiteExtensionEffectiveInfinityDivisorDegree
    (D : FiniteExtensionEffectiveInfinityDivisor K L) : ℕ :=
  D.sum fun P e => e * finiteExtensionPlaceDegree K L (.inr P)

/-- An effective exhaustive divisor is exactly a pair consisting of its
finite-place and infinity-place components. -/
def finiteExtensionEffectiveDivisorSplitEquiv :
    FiniteExtensionEffectiveDivisor K L ≃
      (FiniteExtensionFinitePlace K L →₀ ℕ) ×
        FiniteExtensionEffectiveInfinityDivisor K L :=
  Finsupp.sumFinsuppEquivProdFinsupp

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionEffectiveDivisorSplitEquiv_finite_apply
    (D : FiniteExtensionEffectiveDivisor K L)
    (P : FiniteExtensionFinitePlace K L) :
    (finiteExtensionEffectiveDivisorSplitEquiv K L D).1 P = D (.inl P) :=
  rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionEffectiveDivisorSplitEquiv_infinity_apply
    (D : FiniteExtensionEffectiveDivisor K L)
    (P : FiniteExtensionInfinityPlace K L) :
    (finiteExtensionEffectiveDivisorSplitEquiv K L D).2 P = D (.inr P) :=
  rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionEffectiveDivisorSplitEquiv_symm_inl
    (D : (FiniteExtensionFinitePlace K L →₀ ℕ) ×
      FiniteExtensionEffectiveInfinityDivisor K L)
    (P : FiniteExtensionFinitePlace K L) :
    (finiteExtensionEffectiveDivisorSplitEquiv K L).symm D (.inl P) = D.1 P :=
  rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionEffectiveDivisorSplitEquiv_symm_inr
    (D : (FiniteExtensionFinitePlace K L →₀ ℕ) ×
      FiniteExtensionEffectiveInfinityDivisor K L)
    (P : FiniteExtensionInfinityPlace K L) :
    (finiteExtensionEffectiveDivisorSplitEquiv K L).symm D (.inr P) = D.2 P :=
  rfl

omit [Fintype K] in
/-- The existing finite-divisor degree is the restriction of exhaustive
place degree to the finite branch. -/
theorem finiteExtensionEffectiveFiniteDivisorDegree_eq_placeDegree
    (D : FiniteExtensionFinitePlace K L →₀ ℕ) :
    finiteExtensionEffectiveFiniteDivisorDegree K L D =
      D.sum (fun P e => e * finiteExtensionPlaceDegree K L (.inl P)) := by
  apply Finsupp.sum_congr
  intro P _
  rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField K L P]

/-- Degree is additive across the finite/infinity split. -/
theorem finiteExtensionEffectiveDivisorDegree_split
    (D : FiniteExtensionEffectiveDivisor K L) :
    finiteExtensionEffectiveDivisorDegree K L D =
      finiteExtensionEffectiveFiniteDivisorDegree K L
          (finiteExtensionEffectiveDivisorSplitEquiv K L D).1 +
        finiteExtensionEffectiveInfinityDivisorDegree K L
          (finiteExtensionEffectiveDivisorSplitEquiv K L D).2 := by
  rw [finiteExtensionEffectiveDivisorDegree,
    finiteExtensionEffectiveFiniteDivisorDegree_eq_placeDegree,
    finiteExtensionEffectiveInfinityDivisorDegree]
  let e := finiteExtensionEffectiveDivisorSplitEquiv K L
  let g := fun P : FiniteExtensionPlace K L => fun n : ℕ =>
    n * finiteExtensionPlaceDegree K L P
  change D.sum g =
    (e D).1.sum (g ∘ Sum.inl) + (e D).2.sum (g ∘ Sum.inr)
  calc
    D.sum g = (e.symm (e D)).sum g := by
      rw [e.symm_apply_apply]
    _ = (e D).1.sum (g ∘ Sum.inl) + (e D).2.sum (g ∘ Sum.inr) := by
      change (Finsupp.sumElim (e D).1 (e D).2).sum g = _
      exact Finsupp.sum_sumElim _ _ _

/-- Cast an effective natural-number divisor to the integer-valued divisor
type used by Riemann spaces and divisor classes. -/
def finiteExtensionEffectiveDivisorToDivisor
    (D : FiniteExtensionEffectiveDivisor K L) : FiniteExtensionDivisor K L :=
  D.mapRange (fun n : ℕ => (n : ℤ)) (by simp)

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionEffectiveDivisorToDivisor_apply
    (D : FiniteExtensionEffectiveDivisor K L)
    (P : FiniteExtensionPlace K L) :
    finiteExtensionEffectiveDivisorToDivisor K L D P = D P := by
  simp [finiteExtensionEffectiveDivisorToDivisor]

/-- The cast divisor is effective. -/
theorem finiteExtensionEffectiveDivisorToDivisor_effective
    (D : FiniteExtensionEffectiveDivisor K L) (P : FiniteExtensionPlace K L) :
    0 ≤ finiteExtensionEffectiveDivisorToDivisor K L D P := by
  simp

omit [Fintype K] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- Natural degree casts to the integer degree of the associated exhaustive
divisor. -/
theorem finiteExtensionEffectiveDivisorDegree_cast
    (D : FiniteExtensionEffectiveDivisor K L) :
    (finiteExtensionEffectiveDivisorDegree K L D : ℤ) =
      finiteExtensionDivisorDegree K L
        (finiteExtensionEffectiveDivisorToDivisor K L D) := by
  rw [finiteExtensionEffectiveDivisorDegree, finiteExtensionDivisorDegree,
    finiteExtensionEffectiveDivisorToDivisor]
  rw [Finsupp.sum_mapRange_index (fun _ => by simp)]
  push_cast
  rfl

/-- Natural effective exhaustive divisors are equivalent to the subtype of
pointwise-effective integer-valued exhaustive divisors. -/
def finiteExtensionEffectiveDivisorEquivEffectiveIntegralDivisor :
    FiniteExtensionEffectiveDivisor K L ≃
      {D : FiniteExtensionDivisor K L // ∀ P, 0 ≤ D P} where
  toFun D := ⟨finiteExtensionEffectiveDivisorToDivisor K L D,
    finiteExtensionEffectiveDivisorToDivisor_effective K L D⟩
  invFun D := D.1.mapRange Int.toNat (by simp)
  left_inv D := by
    ext P
    simp [finiteExtensionEffectiveDivisorToDivisor]
  right_inv D := by
    apply Subtype.ext
    ext P
    simp [finiteExtensionEffectiveDivisorToDivisor,
      Int.toNat_of_nonneg (D.2 P)]

/-- Splitting an effective exhaustive divisor and replacing its finite part
by the corresponding nonzero affine ideal. -/
def finiteExtensionEffectiveDivisorAffineInfinityEquiv :
    FiniteExtensionEffectiveDivisor K L ≃
      FiniteExtensionAffineIdeal K L ×
        FiniteExtensionEffectiveInfinityDivisor K L :=
  (finiteExtensionEffectiveDivisorSplitEquiv K L).trans
    ((finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm.prodCongr
      (Equiv.refl _))

/-- Under the ideal/infinity equivalence, exhaustive degree is affine ideal
degree plus infinity degree. -/
theorem finiteExtensionEffectiveDivisorDegree_eq_affine_add_infinity
    (D : FiniteExtensionEffectiveDivisor K L) :
    finiteExtensionEffectiveDivisorDegree K L D =
      finiteExtensionAffineIdealDegree K L
          (finiteExtensionEffectiveDivisorAffineInfinityEquiv K L D).1 +
        finiteExtensionEffectiveInfinityDivisorDegree K L
          (finiteExtensionEffectiveDivisorAffineInfinityEquiv K L D).2 := by
  rw [finiteExtensionEffectiveDivisorDegree_split]
  rw [finiteExtensionAffineIdealDegree_eq_divisorDegree]
  simp [finiteExtensionEffectiveDivisorAffineInfinityEquiv]

private local instance effectiveDivisorInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

private local instance effectiveDivisorInfinityClosureIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

private local instance effectiveDivisorInfinityTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

private local instance effectiveDivisorInfinityClosureTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

private local instance effectiveDivisorInfinityClosureDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) L (RatFuncInfinityIntegralClosure K L)

local instance effectiveDivisorInfinityPlaceFinite :
    Finite (FiniteExtensionInfinityPlace K L) := by
  letI := Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))
  infer_instance

omit [Fintype K] in
/-- Every infinity coefficient is bounded by the weighted degree. -/
theorem finiteExtensionEffectiveInfinityDivisor_apply_le_degree
    (D : FiniteExtensionEffectiveInfinityDivisor K L)
    (P : FiniteExtensionInfinityPlace K L) :
    D P ≤ finiteExtensionEffectiveInfinityDivisorDegree K L D := by
  apply le_trans (Nat.le_mul_of_pos_right (D P)
    (finiteExtensionPlaceDegree_pos K L (.inr P)))
  simpa [finiteExtensionEffectiveInfinityDivisorDegree] using
    (Finsupp.single_le_sum D
      (g := fun Q e => e * finiteExtensionPlaceDegree K L (.inr Q))
      (fun _ _ => Nat.zero_le _) P)

/-- Effective infinity divisors of a fixed degree form a finite type. -/
noncomputable instance finiteExtensionEffectiveInfinityDivisorsOfDegree_fintype
    (n : ℕ) :
    Fintype {D : FiniteExtensionEffectiveInfinityDivisor K L //
      finiteExtensionEffectiveInfinityDivisorDegree K L D = n} := by
  let encode :
      {D : FiniteExtensionEffectiveInfinityDivisor K L //
        finiteExtensionEffectiveInfinityDivisorDegree K L D = n} →
        (FiniteExtensionInfinityPlace K L → Fin (n + 1)) :=
    fun D P => ⟨D.1 P, by
      rw [Nat.lt_succ_iff]
      exact (finiteExtensionEffectiveInfinityDivisor_apply_le_degree
        K L D.1 P).trans_eq D.2⟩
  letI : Finite
      (FiniteExtensionInfinityPlace K L → Fin (n + 1)) := inferInstance
  letI : Finite
      {D : FiniteExtensionEffectiveInfinityDivisor K L //
        finiteExtensionEffectiveInfinityDivisorDegree K L D = n} :=
    Finite.of_injective encode (by
      intro D E h
      apply Subtype.ext
      ext P
      exact congrArg Fin.val (congrFun h P))
  exact Fintype.ofFinite _

/-- The effective-infinity-divisor coefficient of degree `n`. -/
noncomputable def finiteExtensionEffectiveInfinityDivisorCount (n : ℕ) : ℕ :=
  Fintype.card {D : FiniteExtensionEffectiveInfinityDivisor K L //
    finiteExtensionEffectiveInfinityDivisorDegree K L D = n}

/-- Fixed-degree effective exhaustive divisors split according to the degree
of their finite component. -/
def finiteExtensionEffectiveDivisorsOfDegreeSplitEquiv (n : ℕ) :
    {D : FiniteExtensionEffectiveDivisor K L //
      finiteExtensionEffectiveDivisorDegree K L D = n} ≃
      Σ m : Fin (n + 1),
        {D : (FiniteExtensionFinitePlace K L →₀ ℕ) ×
            FiniteExtensionEffectiveInfinityDivisor K L //
          finiteExtensionEffectiveFiniteDivisorDegree K L D.1 = m.1 ∧
            finiteExtensionEffectiveInfinityDivisorDegree K L D.2 =
              n - m.1} where
  toFun D := by
    let parts := finiteExtensionEffectiveDivisorSplitEquiv K L D.1
    have hsum :
        finiteExtensionEffectiveFiniteDivisorDegree K L parts.1 +
          finiteExtensionEffectiveInfinityDivisorDegree K L parts.2 = n := by
      rw [← finiteExtensionEffectiveDivisorDegree_split K L D.1, D.2]
    have hle : finiteExtensionEffectiveFiniteDivisorDegree K L parts.1 ≤ n := by
      omega
    exact ⟨⟨finiteExtensionEffectiveFiniteDivisorDegree K L parts.1,
        Nat.lt_succ_iff.mpr hle⟩,
      ⟨parts, rfl, by
        change finiteExtensionEffectiveInfinityDivisorDegree K L parts.2 =
          n - finiteExtensionEffectiveFiniteDivisorDegree K L parts.1
        omega⟩⟩
  invFun D := by
    let E := (finiteExtensionEffectiveDivisorSplitEquiv K L).symm
      D.2.1
    refine ⟨E, ?_⟩
    rw [finiteExtensionEffectiveDivisorDegree_split]
    dsimp [E]
    rw [(finiteExtensionEffectiveDivisorSplitEquiv K L).apply_symm_apply]
    rw [D.2.2.1, D.2.2.2]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ D.1.2)
  left_inv D := by
    apply Subtype.ext
    exact (finiteExtensionEffectiveDivisorSplitEquiv K L).symm_apply_apply D.1
  right_inv D := by
    apply Sigma.subtype_ext
    · apply Fin.ext
      change finiteExtensionEffectiveFiniteDivisorDegree K L
        ((finiteExtensionEffectiveDivisorSplitEquiv K L)
          ((finiteExtensionEffectiveDivisorSplitEquiv K L).symm D.2.1)).1 =
            D.1.1
      rw [(finiteExtensionEffectiveDivisorSplitEquiv K L).apply_symm_apply]
      exact D.2.2.1
    · exact (finiteExtensionEffectiveDivisorSplitEquiv K L).apply_symm_apply D.2.1

/-- Each fixed split-degree fiber is the product of its finite and infinity
fixed-degree components. -/
def finiteExtensionEffectiveDivisorSplitFiberEquiv (n : ℕ) (m : Fin (n + 1)) :
    {D : (FiniteExtensionFinitePlace K L →₀ ℕ) ×
        FiniteExtensionEffectiveInfinityDivisor K L //
      finiteExtensionEffectiveFiniteDivisorDegree K L D.1 = m.1 ∧
        finiteExtensionEffectiveInfinityDivisorDegree K L D.2 = n - m.1} ≃
      {D : FiniteExtensionFinitePlace K L →₀ ℕ //
        finiteExtensionEffectiveFiniteDivisorDegree K L D = m.1} ×
      {D : FiniteExtensionEffectiveInfinityDivisor K L //
        finiteExtensionEffectiveInfinityDivisorDegree K L D = n - m.1} where
  toFun D := ⟨⟨D.1.1, D.2.1⟩, ⟨D.1.2, D.2.2⟩⟩
  invFun D := ⟨(D.1.1, D.2.1), D.1.2, D.2.2⟩
  left_inv D := by
    apply Subtype.ext
    rfl
  right_inv D := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

noncomputable instance finiteExtensionEffectiveDivisorSplitFiber_fintype
    (n : ℕ) (m : Fin (n + 1)) :
    Fintype {D : (FiniteExtensionFinitePlace K L →₀ ℕ) ×
        FiniteExtensionEffectiveInfinityDivisor K L //
      finiteExtensionEffectiveFiniteDivisorDegree K L D.1 = m.1 ∧
        finiteExtensionEffectiveInfinityDivisorDegree K L D.2 = n - m.1} :=
  Fintype.ofEquiv _
    (finiteExtensionEffectiveDivisorSplitFiberEquiv K L n m).symm

/-- Effective exhaustive divisors of fixed degree form a finite type. -/
noncomputable instance finiteExtensionEffectiveDivisorsOfDegree_fintype
    (n : ℕ) :
    Fintype {D : FiniteExtensionEffectiveDivisor K L //
      finiteExtensionEffectiveDivisorDegree K L D = n} :=
  Fintype.ofEquiv _
    (finiteExtensionEffectiveDivisorsOfDegreeSplitEquiv K L n).symm

/-- The effective-exhaustive-divisor coefficient of degree `n`. -/
noncomputable def finiteExtensionEffectiveDivisorCount (n : ℕ) : ℕ :=
  Fintype.card {D : FiniteExtensionEffectiveDivisor K L //
    finiteExtensionEffectiveDivisorDegree K L D = n}

/-- Fixed-degree exhaustive divisor counts are the convolution of the affine
ideal coefficients with the infinity-divisor coefficients. -/
theorem finiteExtensionEffectiveDivisorCount_eq_sum_mul_infinityCount
    (n : ℕ) :
    finiteExtensionEffectiveDivisorCount K L n =
      ∑ m : Fin (n + 1),
        finiteExtensionEffectiveFiniteDivisorCount K L m.1 *
          finiteExtensionEffectiveInfinityDivisorCount K L (n - m.1) := by
  rw [finiteExtensionEffectiveDivisorCount]
  rw [Fintype.card_congr
    (finiteExtensionEffectiveDivisorsOfDegreeSplitEquiv K L n)]
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro m _
  rw [Fintype.card_congr
    (finiteExtensionEffectiveDivisorSplitFiberEquiv K L n m)]
  rw [Fintype.card_prod]
  rfl

/-- The same convolution with the finite coefficient written as the affine
ideal count in the normalization of `K[X]`. -/
theorem finiteExtensionEffectiveDivisorCount_eq_sum_affineIdealCount_mul_infinityCount
    (n : ℕ) :
    finiteExtensionEffectiveDivisorCount K L n =
      ∑ m : Fin (n + 1),
        finiteExtensionAffineIdealCount K L m.1 *
          finiteExtensionEffectiveInfinityDivisorCount K L (n - m.1) := by
  rw [finiteExtensionEffectiveDivisorCount_eq_sum_mul_infinityCount]
  apply Finset.sum_congr rfl
  intro m _
  rw [← finiteExtensionAffineIdealCount_eq_effectiveFiniteDivisorCount]

end

end BGS.HasseWeil
