/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor
public import Mathlib.Tactic

/-!
# Zero counting from principal-divisor height

This file isolates the divisor-theoretic counting step used after a
Hasse--Weil estimate.  Every place has positive degree, so each distinct zero
of a function contributes at least one to the degree of its positive divisor.
The product formula then identifies that degree with the pole height.

No point-count estimate is used here.  In particular, the genuinely
Hasse--Weil input can remain a separate upstream theorem.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial BigOperators
open IsDedekindDomain

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) zeroCountingPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance zeroCountingPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance zeroCountingFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance zeroCountingInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

/-- Every finite or above-infinity place of a finite separable function-field
extension has positive degree. -/
theorem finiteExtensionPlaceDegree_pos
    (v : FiniteExtensionPlace K L) :
    0 < finiteExtensionPlaceDegree K L v := by
  cases v with
  | inl q =>
      rw [finiteExtensionPlaceDegree]
      exact Nat.mul_pos
        (Ideal.inertiaDeg_pos q.asIdeal K[X])
        ((finitePlaceNormalizedPrime
          (HeightOneSpectrum.under K[X] q)).property.1.irreducible.natDegree_pos)
  | inr P =>
      simpa [finiteExtensionPlaceDegree] using
        Ideal.inertiaDeg_pos P.1 (RatFuncInfinityIntegers K)

/-- The finite set of places where `x` has positive order. -/
def finiteExtensionZeroPlaces (x : L) :
    Finset (FiniteExtensionPlace K L) :=
  (finiteExtensionPrincipalDivisor K L x).support.filter
    (fun v => 0 < finiteExtensionPrincipalDivisor K L x v)

omit [DecidableEq K] in
@[simp] theorem mem_finiteExtensionZeroPlaces_iff
    (x : L) (v : FiniteExtensionPlace K L) :
    v ∈ finiteExtensionZeroPlaces K L x ↔
      0 < finiteExtensionPrincipalDivisor K L x v := by
  simp only [finiteExtensionZeroPlaces, Finset.mem_filter,
    Finsupp.mem_support_iff]
  omega

/-- The degree of the positive divisor is the weighted sum over the zero
places. -/
theorem finiteExtensionPositiveDegree_eq_sum_zeroPlaces
    (x : L) :
    finiteExtensionPositiveDegree K L x =
      ∑ v ∈ finiteExtensionZeroPlaces K L x,
        (finiteExtensionPrincipalDivisor K L x v).toNat *
          finiteExtensionPlaceDegree K L v := by
  rfl

/-- Any finite set of positive-order places has cardinality at most the degree
of the positive divisor. -/
theorem card_le_finiteExtensionPositiveDegree_of_orders_positive
    (x : L) (S : Finset (FiniteExtensionPlace K L))
    (hpositive : ∀ v ∈ S, 0 < finiteExtensionPrincipalDivisor K L x v) :
    S.card ≤ finiteExtensionPositiveDegree K L x := by
  let weight : FiniteExtensionPlace K L → ℕ := fun v =>
    (finiteExtensionPrincipalDivisor K L x v).toNat *
      finiteExtensionPlaceDegree K L v
  have hsubset : S ⊆ finiteExtensionZeroPlaces K L x := by
    intro v hv
    exact (mem_finiteExtensionZeroPlaces_iff K L x v).2 (hpositive v hv)
  calc
    S.card = ∑ _v ∈ S, 1 := by simp
    _ ≤ ∑ v ∈ S, weight v := by
      apply Finset.sum_le_sum
      intro v hv
      have horder : 0 < (finiteExtensionPrincipalDivisor K L x v).toNat :=
        Int.pos_iff_toNat_pos.mp (hpositive v hv)
      have hdegree : 0 < finiteExtensionPlaceDegree K L v :=
        finiteExtensionPlaceDegree_pos K L v
      simpa [weight] using Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.ne_of_gt horder) (Nat.ne_of_gt hdegree))
    _ ≤ ∑ v ∈ finiteExtensionZeroPlaces K L x, weight v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
    _ = finiteExtensionPositiveDegree K L x := by
      rw [finiteExtensionPositiveDegree_eq_sum_zeroPlaces K L x]

/-- Any finite family of positive-order places contributes its full
residue-degree weight to the positive divisor.  This is the form needed when
degree-one and degree-two closed points are counted simultaneously over a
quadratic constant-field extension. -/
theorem sum_placeDegree_le_finiteExtensionPositiveDegree_of_orders_positive
    (x : L) (S : Finset (FiniteExtensionPlace K L))
    (hpositive : ∀ v ∈ S, 0 < finiteExtensionPrincipalDivisor K L x v) :
    ∑ v ∈ S, finiteExtensionPlaceDegree K L v ≤
      finiteExtensionPositiveDegree K L x := by
  let weight : FiniteExtensionPlace K L → ℕ := fun v =>
    (finiteExtensionPrincipalDivisor K L x v).toNat *
      finiteExtensionPlaceDegree K L v
  have hsubset : S ⊆ finiteExtensionZeroPlaces K L x := by
    intro v hv
    exact (mem_finiteExtensionZeroPlaces_iff K L x v).2 (hpositive v hv)
  calc
    ∑ v ∈ S, finiteExtensionPlaceDegree K L v ≤
        ∑ v ∈ S, weight v := by
      apply Finset.sum_le_sum
      intro v hv
      have horder : 1 ≤ (finiteExtensionPrincipalDivisor K L x v).toNat := by
        have horderPositive :
            0 < (finiteExtensionPrincipalDivisor K L x v).toNat :=
          Int.pos_iff_toNat_pos.mp (hpositive v hv)
        omega
      exact Nat.le_mul_of_pos_left
        (finiteExtensionPlaceDegree K L v) horder
    _ ≤ ∑ v ∈ finiteExtensionZeroPlaces K L x, weight v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
    _ = finiteExtensionPositiveDegree K L x := by
      rw [finiteExtensionPositiveDegree_eq_sum_zeroPlaces K L x]

/-- Weighted positive-order place counting in terms of pole height. -/
theorem sum_placeDegree_le_finiteExtensionHeight_of_orders_positive
    (x : L) (hx : x ≠ 0)
    (S : Finset (FiniteExtensionPlace K L))
    (hpositive : ∀ v ∈ S, 0 < finiteExtensionPrincipalDivisor K L x v) :
    ∑ v ∈ S, finiteExtensionPlaceDegree K L v ≤
      finiteExtensionHeight K L x := by
  rw [← finiteExtensionPositiveDegree_eq_height K L x hx]
  exact sum_placeDegree_le_finiteExtensionPositiveDegree_of_orders_positive
    K L x S hpositive

/-- If a finite type injects into positive-order places of a nonzero function,
then its cardinality is bounded by the pole height of that function. -/
theorem Fintype.card_le_finiteExtensionHeight_of_injective_orders_positive
    {ι : Type*} [Fintype ι]
    (x : L) (hx : x ≠ 0)
    (place : ι → FiniteExtensionPlace K L)
    (hinjective : Function.Injective place)
    (hpositive : ∀ i, 0 < finiteExtensionPrincipalDivisor K L x (place i)) :
    Fintype.card ι ≤ finiteExtensionHeight K L x := by
  classical
  let S : Finset (FiniteExtensionPlace K L) := Finset.univ.image place
  have hcard : S.card = Fintype.card ι := by
    simpa [S] using Finset.card_image_of_injective Finset.univ hinjective
  have hSpositive :
      ∀ v ∈ S, 0 < finiteExtensionPrincipalDivisor K L x v := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact hpositive i
  calc
    Fintype.card ι = S.card := hcard.symm
    _ ≤ finiteExtensionPositiveDegree K L x :=
      card_le_finiteExtensionPositiveDegree_of_orders_positive K L x S hSpositive
    _ = finiteExtensionHeight K L x :=
      finiteExtensionPositiveDegree_eq_height K L x hx

end

end BGS.HasseWeil
