/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import Mathlib.RingTheory.PowerSeries.Evaluation
/-!
# The equal-characteristic completed-unramified construction: the completed maximal-unramified
  field in equal characteristic

For a finite field `k`, the equal-characteristic model of the completion of
the maximal unramified extension of `k((T))` is
`(AlgebraicClosure k)((T))`.  This file equips that field with the genuine
coefficientwise arithmetic Frobenius over `k((T))`.

This is the equal-characteristic specialization of the completed-unramified
source in the equal-characteristic completed-unramified construction.  In particular, the
  Frobenius below is an actual algebra
equivalence; it is not a theorem-shaped replacement for later theta
evaluation or norm-subgroup arguments.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries Polynomial PowerSeries PowerSeries.WithPiTopology
  Topology Valued WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

variable (k : Type u) [Field k] [Finite k]

/-- The valuation balls in a valued integer ring, expressed as genuine
ideals, form its neighbourhood basis at zero. -/
theorem valuedInteger_hasBasis_ltIdeal
    {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    (𝓝 (0 : Valued.integer K)).HasBasis
      (fun _ : (MonoidWithZeroHom.ValueGroup₀
        (.ofClass (Valued.v : Valuation K Γ)))ˣ ↦ True)
      (fun γ ↦ (Valuation.ltIdeal (Valued.v : Valuation K Γ)
        (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
          (f := (.ofClass (Valued.v : Valuation K Γ)))) γ) :
        Set (Valued.integer K))) := by
  rw [nhds_subtype]
  refine ((Valued.hasBasis_nhds_zero K Γ).comap
    ((↑) : Valued.integer K → K)).congr (fun _ ↦ Iff.rfl) ?_
  intro γ _
  ext x
  change (Valued.v : Valuation K Γ).restrict x < (γ :
      MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation K Γ))) ↔
    (Valued.v : Valuation K Γ) (x : K) <
      ((Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := (.ofClass (Valued.v : Valuation K Γ)))) γ : Γˣ) : Γ)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simp

/-- The native topology on a valued integer ring is linear: its valuation
balls are ideals. -/
theorem valuedIntegerLinearTopology
    {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    IsLinearTopology (Valued.integer K) (Valued.integer K) :=
  IsLinearTopology.mk_of_hasBasis (Valued.integer K)
    (valuedInteger_hasBasis_ltIdeal (K := K))

/-- A closed valued integer ring inherits completeness from its fraction
field. -/
theorem valuedIntegerCompleteSpace
    {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] [CompleteSpace K] :
    CompleteSpace (Valued.integer K) :=
  (Valued.isClosed_integer K).completeSpace_coe

/-- The induced uniformity on a valued integer ring is compatible with its
additive group. -/
theorem valuedIntegerIsUniformAddGroup
    {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    IsUniformAddGroup (Valued.integer K) :=
  (Valued.integer K).toAddSubgroup.isUniformAddGroup

noncomputable local instance valuedIntegerLinearTopologyInstance
    {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    IsLinearTopology (Valued.integer K) (Valued.integer K) :=
  valuedIntegerLinearTopology

noncomputable local instance valuedIntegerCompleteSpaceInstance
    {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] [CompleteSpace K] :
    CompleteSpace (Valued.integer K) :=
  valuedIntegerCompleteSpace

noncomputable local instance valuedIntegerIsUniformAddGroupInstance
    {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    IsUniformAddGroup (Valued.integer K) :=
  valuedIntegerIsUniformAddGroup

omit [Finite k] in
/-- The algebraic closure of the coefficient field carries the discrete uniformity. -/
noncomputable local instance equalCharacteristicCoefficientUniformSpace :
    UniformSpace (AlgebraicClosure k) := ⊥

/-- The fixed elements of arithmetic Frobenius in the algebraic closure are
exactly the embedded elements of the finite coefficient field. -/
theorem equalCharacteristicCoefficientFrobenius_fixed_iff
    (x : AlgebraicClosure k) :
    equalCharacteristicCoefficientFrobenius k x = x ↔
      x ∈ (algebraMap k (AlgebraicClosure k)).range := by
  constructor
  · intro hx
    have hxpow : x ^ Nat.card k = x := by
      simpa [equalCharacteristicCoefficientFrobenius_apply] using hx
    let : Fintype k := Fintype.ofFinite k
    have hxint : IsIntegral k x :=
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hroot : Polynomial.aeval x
        (Polynomial.X ^ Nat.card k - Polynomial.X : k[X]) = 0 := by
      simpa using sub_eq_zero.mpr hxpow
    have hdiv : minpoly k x ∣
        (Polynomial.X ^ Nat.card k - Polynomial.X : k[X]) :=
      minpoly.dvd k x hroot
    have hsplit :
        (Polynomial.X ^ Nat.card k - Polynomial.X : k[X]).Splits := by
      rw [Nat.card_eq_fintype_card]
      simpa using (FiniteField.isSplittingField_sub k k).splits
    have hpolyne :
        (Polynomial.X ^ Nat.card k - Polynomial.X : k[X]) ≠ 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hminsplit : (minpoly k x).Splits :=
      hsplit.of_dvd hpolyne hdiv
    exact hxint.mem_range_algebraMap_of_minpoly_splits (K := k) (by
      simpa using hminsplit)
  · rintro ⟨a, rfl⟩
    exact (equalCharacteristicCoefficientFrobenius k).commutes a

/-- The equal-characteristic model of the completed maximal unramified
extension of `k((T))`. -/
def equalCharacteristicCompletedUnramifiedField :=
  (AlgebraicClosure k)⸨X⸩

/-- The completed unramified Laurent-series model is a field. -/
instance equalCharacteristicCompletedUnramifiedFieldField :
    Field (equalCharacteristicCompletedUnramifiedField k) := by
  change Field ((AlgebraicClosure k)⸨X⸩)
  infer_instance

/-- The completed unramified field carries its Laurent-series valuation. -/
noncomputable instance equalCharacteristicCompletedUnramifiedFieldValued :
    Valued (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰ := by
  change Valued ((AlgebraicClosure k)⸨X⸩) ℤᵐ⁰
  infer_instance

/-- The completed unramified Laurent-series field is complete. -/
instance equalCharacteristicCompletedUnramifiedField_completeSpace :
    CompleteSpace (equalCharacteristicCompletedUnramifiedField k) := by
  change CompleteSpace ((AlgebraicClosure k)⸨X⸩)
  infer_instance

/-- Comparison with the Laurent-series model underlying the completed
unramified field. -/
def equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries :
    equalCharacteristicCompletedUnramifiedField k ≃+*
      (AlgebraicClosure k)⸨X⸩ :=
  RingEquiv.refl _

/-- Embed a Laurent series into the named completed-unramified field. -/
def equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries :
    (AlgebraicClosure k)⸨X⸩ →+*
      equalCharacteristicCompletedUnramifiedField k :=
  (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries k).symm.toRingHom

/-- Read a named completed-unramified element in its Laurent-series model. -/
def equalCharacteristicCompletedUnramifiedFieldToLaurentSeries :
    equalCharacteristicCompletedUnramifiedField k →+*
      (AlgebraicClosure k)⸨X⸩ :=
  (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries k).toRingHom

omit [Finite k] in
/-- Converting a Laurent series into the named field and back returns the series. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldToLaurentSeries_ofLaurentSeries
    (x : (AlgebraicClosure k)⸨X⸩) :
    equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k
        (equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries k x) = x :=
  rfl

/-- A single Laurent monomial in the named completed-unramified field. -/
def equalCharacteristicCompletedUnramifiedFieldSingle
    (m : ℤ) (a : AlgebraicClosure k) :
    equalCharacteristicCompletedUnramifiedField k :=
  equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries k
    (HahnSeries.single m a)

/-- The coefficient of a named completed-unramified Laurent element. -/
def equalCharacteristicCompletedUnramifiedFieldCoeff
    (x : equalCharacteristicCompletedUnramifiedField k) (m : ℤ) :
    AlgebraicClosure k :=
  (equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k x).coeff m

omit [Finite k] in
/-- Coefficients of an imported Laurent series agree with its original coefficients. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldCoeff_ofLaurentSeries
    (x : (AlgebraicClosure k)⸨X⸩) (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries k x) m =
      x.coeff m :=
  rfl

omit [Finite k] in
/-- Two named completed-unramified elements are equal when all Laurent
coefficients agree. -/
@[ext]
theorem equalCharacteristicCompletedUnramifiedField_ext
    {x y : equalCharacteristicCompletedUnramifiedField k}
    (h : ∀ m, equalCharacteristicCompletedUnramifiedFieldCoeff k x m =
      equalCharacteristicCompletedUnramifiedFieldCoeff k y m) :
    x = y := by
  apply (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries k).injective
  ext m
  exact h m

/-- The completed unramified field is an algebra over algebraic-closure power series. -/
noncomputable instance equalCharacteristicCompletedUnramifiedPowerSeriesAlgebra :
    Algebra (AlgebraicClosure k)⟦X⟧
      (equalCharacteristicCompletedUnramifiedField k) := by
  change Algebra (AlgebraicClosure k)⟦X⟧ (AlgebraicClosure k)⸨X⸩
  infer_instance

/-- The completed unramified field is an algebra over the residue base field. -/
noncomputable instance equalCharacteristicCompletedUnramifiedCoefficientAlgebra :
    Algebra k (equalCharacteristicCompletedUnramifiedField k) := by
  change Algebra k (AlgebraicClosure k)⸨X⸩
  infer_instance

/-- The completed unramified field is an algebra over the Laurent-series base. -/
noncomputable instance equalCharacteristicCompletedUnramifiedAlgebra :
    Algebra k⸨X⸩ (equalCharacteristicCompletedUnramifiedField k) :=
  laurentSeriesCoefficientAlgebra

/-- The named completed-unramified Laurent field is the fraction field of its
power-series integer ring. -/
instance equalCharacteristicCompletedUnramifiedIsFractionRing :
    IsFractionRing (AlgebraicClosure k)⟦X⟧
      (equalCharacteristicCompletedUnramifiedField k) := by
  change IsFractionRing (AlgebraicClosure k)⟦X⟧
    (AlgebraicClosure k)⸨X⸩
  infer_instance

omit [Finite k] in
/-- A mapped power series has its original nonnegative coefficients. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldCoeff_algebraMap_powerSeries
    (f : (AlgebraicClosure k)⟦X⟧) (n : ℕ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (algebraMap (AlgebraicClosure k)⟦X⟧
          (equalCharacteristicCompletedUnramifiedField k) f) n =
      PowerSeries.coeff n f := by
  change ((f : (AlgebraicClosure k)⸨X⸩).coeff (Int.ofNat n)) =
    PowerSeries.coeff n f
  simp

omit [Finite k] in
/-- A mapped base Laurent series has coefficients embedded into the algebraic closure. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldCoeff_algebraMap_laurentSeries
    (f : k⸨X⸩) (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (algebraMap k⸨X⸩
          (equalCharacteristicCompletedUnramifiedField k) f) m =
      algebraMap k (AlgebraicClosure k) (f.coeff m) := by
  change
    (laurentSeriesCoefficientMap
      (algebraMap k (AlgebraicClosure k)) f).coeff m =
      algebraMap k (AlgebraicClosure k) (f.coeff m)
  rw [laurentSeriesCoefficientMap_coeff]

/-- Arithmetic Frobenius on the completed maximal-unramified Laurent field,
acting coefficientwise and fixing the Laurent-series base `k((T))`. -/
noncomputable def equalCharacteristicCompletedUnramifiedFrobenius :
    equalCharacteristicCompletedUnramifiedField k ≃ₐ[k⸨X⸩]
      equalCharacteristicCompletedUnramifiedField k :=
  laurentSeriesCoefficientAlgEquiv
    (equalCharacteristicCoefficientFrobenius k)

/-- Completed Frobenius applies coefficient Frobenius at every Laurent exponent. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFrobenius_coeff
    (x : equalCharacteristicCompletedUnramifiedField k) (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (equalCharacteristicCompletedUnramifiedFrobenius k x) m =
  equalCharacteristicCompletedUnramifiedFieldCoeff k x m ^
        Nat.card k := by
  change
    (laurentSeriesCoefficientAlgEquiv
        (equalCharacteristicCoefficientFrobenius k)
        (equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k x)).coeff m =
      (equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k x).coeff m ^
        Nat.card k
  rw [laurentSeriesCoefficientAlgEquiv_coeff,
    equalCharacteristicCoefficientFrobenius_apply]

/-- Coefficient Frobenius preserves the native Laurent valuation. -/
theorem equalCharacteristicCompletedUnramifiedFrobenius_valuation
    (x : equalCharacteristicCompletedUnramifiedField k) :
    Valued.v (equalCharacteristicCompletedUnramifiedFrobenius k x) =
      Valued.v x := by
  apply le_antisymm
  · by_cases hx : x = 0
    · simp [hx]
    have hxval : Valued.v x ≠ (0 : ℤᵐ⁰) :=
      (Valuation.ne_zero_iff (Valued.v :
        Valuation (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰)).2 hx
    apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
      (AlgebraicClosure k) hxval).2
    intro n hn
    have hcoeff :=
      (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
        (AlgebraicClosure k) hxval).1 (le_refl (Valued.v x)) n hn
    change equalCharacteristicCompletedUnramifiedFieldCoeff k x n = 0 at hcoeff
    change equalCharacteristicCompletedUnramifiedFieldCoeff k
      (equalCharacteristicCompletedUnramifiedFrobenius k x) n = 0
    rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff, hcoeff]
    exact zero_pow Nat.card_pos.ne'
  · by_cases hx : x = 0
    · simp [hx]
    have hfxne : equalCharacteristicCompletedUnramifiedFrobenius k x ≠ 0 :=
      (map_ne_zero (equalCharacteristicCompletedUnramifiedFrobenius k)).2 hx
    have hfxval :
        Valued.v (equalCharacteristicCompletedUnramifiedFrobenius k x) ≠
          (0 : ℤᵐ⁰) :=
      (Valuation.ne_zero_iff (Valued.v :
        Valuation (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰)).2 hfxne
    apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
      (AlgebraicClosure k) hfxval).2
    intro n hn
    have hcoeff :=
      (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
        (AlgebraicClosure k) hfxval).1
          (le_refl (Valued.v
            (equalCharacteristicCompletedUnramifiedFrobenius k x))) n hn
    change equalCharacteristicCompletedUnramifiedFieldCoeff k
      (equalCharacteristicCompletedUnramifiedFrobenius k x) n = 0 at hcoeff
    rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff] at hcoeff
    exact eq_zero_of_pow_eq_zero hcoeff

/-- Coefficient Frobenius is continuous for the Laurent valuation topology.
-/
theorem equalCharacteristicCompletedUnramifiedFrobenius_continuous :
    Continuous (equalCharacteristicCompletedUnramifiedFrobenius k) := by
  apply continuous_of_continuousAt_zero
    (equalCharacteristicCompletedUnramifiedFrobenius k).toAddMonoidHom
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).tendsto_iff
      (Valued.hasBasis_nhds_zero
        (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰),
    true_and, forall_const]
  intro γ
  refine ⟨γ, fun x hx ↦ ?_⟩
  change (Valued.v :
      Valuation (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).restrict
        (equalCharacteristicCompletedUnramifiedFrobenius k x) < γ.1
  change (Valued.v :
      Valuation (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).restrict
        x < γ.1 at hx
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rw [equalCharacteristicCompletedUnramifiedFrobenius_valuation]
  exact hx

/-- On the integer ring `(AlgebraicClosure k)[[T]]`, Laurent Frobenius is
the coefficientwise power-series Frobenius constructed for theta. -/
theorem equalCharacteristicCompletedUnramifiedFrobenius_algebraMap_powerSeries
    (f : (AlgebraicClosure k)⟦X⟧) :
    equalCharacteristicCompletedUnramifiedFrobenius k
        (algebraMap ((AlgebraicClosure k)⟦X⟧)
          (equalCharacteristicCompletedUnramifiedField k) f) =
      algebraMap ((AlgebraicClosure k)⟦X⟧)
        (equalCharacteristicCompletedUnramifiedField k)
        (equalCharacteristicPowerSeriesFrobenius k f) := by
  have hcard : Nat.card k ≠ 0 := Nat.card_pos.ne'
  ext m
  cases m with
  | ofNat n =>
      rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff]
      change
        ((f : (AlgebraicClosure k)⸨X⸩).coeff (Int.ofNat n)) ^
            Nat.card k =
          ((equalCharacteristicPowerSeriesFrobenius k f :
            (AlgebraicClosure k)⟦X⟧) :
              (AlgebraicClosure k)⸨X⸩).coeff (Int.ofNat n)
      rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe,
        equalCharacteristicPowerSeriesFrobenius_coeff]
      simp [hcard]
  | negSucc n =>
      rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff]
      change
        ((f : (AlgebraicClosure k)⸨X⸩).coeff (Int.negSucc n)) ^
            Nat.card k =
          ((equalCharacteristicPowerSeriesFrobenius k f :
            (AlgebraicClosure k)⟦X⟧) :
              (AlgebraicClosure k)⸨X⸩).coeff (Int.negSucc n)
      rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
      simp [hcard]

/-- Every coefficient of a Frobenius-fixed completed Laurent series comes
from the original finite coefficient field. -/
theorem equalCharacteristicCompletedUnramified_fixed_coeff_mem_range
    (x : equalCharacteristicCompletedUnramifiedField k)
    (hx : equalCharacteristicCompletedUnramifiedFrobenius k x = x)
    (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k x m ∈
      (algebraMap k (AlgebraicClosure k)).range := by
  apply (equalCharacteristicCoefficientFrobenius_fixed_iff k
    (equalCharacteristicCompletedUnramifiedFieldCoeff k x m)).1
  rw [equalCharacteristicCoefficientFrobenius_apply]
  have hcoeff := congrArg
    (fun y : equalCharacteristicCompletedUnramifiedField k ↦
      equalCharacteristicCompletedUnramifiedFieldCoeff k y m) hx
  change equalCharacteristicCompletedUnramifiedFieldCoeff k
      (equalCharacteristicCompletedUnramifiedFrobenius k x) m =
    equalCharacteristicCompletedUnramifiedFieldCoeff k x m at hcoeff
  rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff] at hcoeff
  exact hcoeff

/-- A chosen coefficient in `k` lifting one coefficient of a
Frobenius-fixed completed Laurent series. -/
noncomputable def equalCharacteristicCompletedUnramifiedFixedCoeff
    (x : equalCharacteristicCompletedUnramifiedField k)
    (hx : equalCharacteristicCompletedUnramifiedFrobenius k x = x)
    (m : ℤ) : k :=
  Classical.choose
    (equalCharacteristicCompletedUnramified_fixed_coeff_mem_range k x hx m)

/-- The chosen base coefficient embeds to the coefficient of the fixed series. -/
@[simp]
theorem algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff
    (x : equalCharacteristicCompletedUnramifiedField k)
    (hx : equalCharacteristicCompletedUnramifiedFrobenius k x = x)
    (m : ℤ) :
    algebraMap k (AlgebraicClosure k)
        (equalCharacteristicCompletedUnramifiedFixedCoeff k x hx m) =
      equalCharacteristicCompletedUnramifiedFieldCoeff k x m :=
  Classical.choose_spec
    (equalCharacteristicCompletedUnramified_fixed_coeff_mem_range k x hx m)

/-- A Frobenius-fixed series, descended coefficientwise to `k((T))`. -/
noncomputable def equalCharacteristicCompletedUnramifiedFixedPreimage
    (x : equalCharacteristicCompletedUnramifiedField k)
    (hx : equalCharacteristicCompletedUnramifiedFrobenius k x = x) :
    k⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun m : ℤ ↦
      equalCharacteristicCompletedUnramifiedFixedCoeff k x hx m)
    (by
      refine ⟨x.order, ?_⟩
      intro m hm
      by_contra hnot
      have hxzero :
          equalCharacteristicCompletedUnramifiedFieldCoeff k x m = 0 := by
        exact HahnSeries.coeff_eq_zero_of_lt_order (not_le.mp hnot)
      apply hm
      apply (algebraMap k (AlgebraicClosure k)).injective
      rw [map_zero,
        algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff,
        hxzero])

/-- The descended Laurent series has the chosen fixed coefficients. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFixedPreimage_coeff
    (x : equalCharacteristicCompletedUnramifiedField k)
    (hx : equalCharacteristicCompletedUnramifiedFrobenius k x = x)
    (m : ℤ) :
    (equalCharacteristicCompletedUnramifiedFixedPreimage k x hx).coeff m =
      equalCharacteristicCompletedUnramifiedFixedCoeff k x hx m := by
  rw [equalCharacteristicCompletedUnramifiedFixedPreimage]
  exact congrFun HahnSeries.coeff_ofSuppBddBelow m

/-- The fixed field of coefficientwise Frobenius is exactly the embedded
Laurent-series base `k((T))`. -/
theorem equalCharacteristicCompletedUnramifiedFrobenius_fixed_iff
    (x : equalCharacteristicCompletedUnramifiedField k) :
    equalCharacteristicCompletedUnramifiedFrobenius k x = x ↔
      x ∈ (algebraMap k⸨X⸩
        (equalCharacteristicCompletedUnramifiedField k)).range := by
  constructor
  · intro hx
    refine ⟨equalCharacteristicCompletedUnramifiedFixedPreimage k x hx, ?_⟩
    ext m
    exact algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff k x hx m
  · rintro ⟨y, rfl⟩
    exact (equalCharacteristicCompletedUnramifiedFrobenius k).commutes y

/-- The Frobenius fixes the Laurent uniformizer `T`. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFrobenius_uniformizer :
    equalCharacteristicCompletedUnramifiedFrobenius k
        (equalCharacteristicCompletedUnramifiedFieldSingle k 1 1) =
      equalCharacteristicCompletedUnramifiedFieldSingle k 1 1 := by
  have hcard : Nat.card k ≠ 0 := Nat.card_pos.ne'
  ext m
  by_cases h : m = 1
  · subst m
    simp [equalCharacteristicCompletedUnramifiedFieldSingle]
  · simp [equalCharacteristicCompletedUnramifiedFieldSingle, h, hcard]

/-- Evaluation of an outer power series with coefficients in
`(AlgebraicClosure k)[[T]]` at a topologically nilpotent point of the
completed-unramified integer ring.  This is the analytic evaluation map
needed for the theta series in the completed theta-intertwining theorem. -/
noncomputable def equalCharacteristicPowerSeriesToCompletedInteger :
    (AlgebraicClosure k)⟦X⟧ →+*
      Valued.integer (equalCharacteristicCompletedUnramifiedField k) := by
  change (AlgebraicClosure k)⟦X⟧ →+*
    Valued.integer ((AlgebraicClosure k)⸨X⸩)
  exact
    (powerSeriesEquivLaurentInteger (AlgebraicClosure k)).toRingHom

omit [Finite k] in
/-- The embedding of power series into the completed valuation ring is continuous. -/
theorem equalCharacteristicPowerSeriesToCompletedInteger_continuous :
    Continuous (equalCharacteristicPowerSeriesToCompletedInteger k) := by
  change Continuous
    (powerSeriesEquivLaurentInteger (AlgebraicClosure k)).toRingHom
  exact continuous_powerSeriesToLaurentInteger

/-- Defines `equalCharacteristicCompletedIntegerEvaluation`. -/
noncomputable def equalCharacteristicCompletedIntegerEvaluation
    (a : Valued.integer (equalCharacteristicCompletedUnramifiedField k))
    (ha : PowerSeries.HasEval a) :
    ((AlgebraicClosure k)⟦X⟧)⟦X⟧ →+*
      Valued.integer (equalCharacteristicCompletedUnramifiedField k) := by
  letI : IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k))
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
    valuedIntegerLinearTopology
  letI : CompleteSpace
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
    valuedIntegerCompleteSpace
  letI : IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
    valuedIntegerIsUniformAddGroup
  exact PowerSeries.eval₂Hom
    (equalCharacteristicPowerSeriesToCompletedInteger_continuous k) ha

/-- The Laurent uniformizer, viewed in the completed-unramified integer
ring. -/
noncomputable def equalCharacteristicCompletedIntegerUniformizer :
    Valued.integer (equalCharacteristicCompletedUnramifiedField k) :=
  equalCharacteristicPowerSeriesToCompletedInteger k PowerSeries.X

omit [Finite k] in
/-- The completed-unramified uniformizer is topologically nilpotent. -/
theorem equalCharacteristicCompletedIntegerUniformizer_hasEval :
    PowerSeries.HasEval
      (equalCharacteristicCompletedIntegerUniformizer k) := by
  have hX : PowerSeries.HasEval
      (PowerSeries.X : (AlgebraicClosure k)⟦X⟧) :=
    PowerSeries.HasEval.X
  exact hX.map
    (equalCharacteristicPowerSeriesToCompletedInteger_continuous k)

omit [Finite k] in
/-- Completed power-series evaluation sends `X` to the chosen integral element. -/
@[simp]
theorem equalCharacteristicCompletedIntegerEvaluation_X
    (a : Valued.integer (equalCharacteristicCompletedUnramifiedField k))
    (ha : PowerSeries.HasEval a) :
    equalCharacteristicCompletedIntegerEvaluation k a ha PowerSeries.X = a := by
  rw [equalCharacteristicCompletedIntegerEvaluation,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

omit [Finite k] in
/-- Completed evaluation sends a constant series to its canonical embedded value. -/
@[simp]
theorem equalCharacteristicCompletedIntegerEvaluation_C
    (a : Valued.integer (equalCharacteristicCompletedUnramifiedField k))
    (ha : PowerSeries.HasEval a)
    (f : (AlgebraicClosure k)⟦X⟧) :
    equalCharacteristicCompletedIntegerEvaluation k a ha (PowerSeries.C f) =
      equalCharacteristicPowerSeriesToCompletedInteger k f := by
  rw [equalCharacteristicCompletedIntegerEvaluation,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

end EqualCharacteristic
end LubinTate
