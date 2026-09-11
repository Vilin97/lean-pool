/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Genus.Polar
public import LeanPool.RiemannRochFunctionFields.FundamentalIdentity
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Ramification half of Stichtenoth 1.4.11
This file proves `deg (X_K)_∞ ≤ [K : k(X)]` via the fundamental identity of ramification
index and inertia degree.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero Additive

open Polynomial BigOperators Submodule IntermediateField Ideal FunctionField

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

variable [IsFullConstantField k K]

/-- Decidable equality on coordinate places for ramification proofs. -/
local instance instDecidableEqPlaceARam : DecidableEq (PlaceA k K) := Classical.decEq _
/-- The classical decidable equality on `k(X)` used by the coordinate places. -/
local instance instDecidableEqRatFuncRam : DecidableEq k⟮X⟯ := Classical.decEq _

/-- The uniformizer `t = X⁻¹` in `k(X)`. -/
noncomputable def tRatFunc : k⟮X⟯ := 1 / RatFunc.X

/-- `t` as an element of the valuation subring at infinity. -/
noncomputable def tA : inftyValuationSubring k :=
  ⟨tRatFunc k, by
    rw [Valuation.mem_valuationSubring_iff]
    dsimp [tRatFunc]
    rw [RatFunc.inftyValuation.X_inv k]
    exact WithZero.exp_le_exp.mpr (show (-1 : ℤ) ≤ 0 by omega)⟩

@[simp]
theorem tRatFunc_coe : (tA k : k⟮X⟯) = tRatFunc k := rfl

omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem maximalIdeal_infty_eq_span_t :
    IsLocalRing.maximalIdeal (inftyValuationSubring k) =
      Ideal.span {(tA k : inftyValuationSubring k)} := by
  let v := RatFunc.inftyValuation k
  have hπval : v (tRatFunc k) = WithZero.exp (-1 : ℤ) := RatFunc.inftyValuation.X_inv k
  have hgen : (↑(Valuation.IsRankOneDiscrete.generator v) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
    have h := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      (v := v) (show WithZero.exp (-1 : ℤ) ∈ Set.range v from ⟨tRatFunc k, hπval⟩)
    exact congrArg Units.val h
  have hπ : v.IsUniformizer (tA k : k⟮X⟯) := by
    rw [Valuation.IsUniformizer.iff, tRatFunc_coe k, hgen]
    exact hπval
  exact Valuation.IsUniformizer.is_generator hπ

local notation "inftyRing" => inftyValuationSubring k
local notation "inftyInts" => infiniteIntegers k K
local notation "maxIdealInfty" => IsLocalRing.maximalIdeal (inftyValuationSubring k)

/-- Ramification index of the infinite place above `k(X)`. -/
noncomputable def ramIdxInfty (P : Ideal (infiniteIntegers k K)) : ℕ :=
  (IsLocalRing.maximalIdeal (inftyValuationSubring k)).ramificationIdx' P

/-- Its image `t_K` in the function field. -/
noncomputable def tK : K := algebraMap k⟮X⟯ K (tRatFunc k)

omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem map_maximalIdeal_infty :
    Ideal.map (algebraMap inftyRing inftyInts) maxIdealInfty =
      Ideal.span {algebraMap inftyRing inftyInts (tA k)} := by
  rw [maximalIdeal_infty_eq_span_t k, Ideal.map_span, Set.image_singleton]

omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem XK_mul_tK : XK k K * tK k K = 1 := by
  dsimp only [XK, tK, tRatFunc]
  rw [← map_mul (algebraMap k⟮X⟯ K), div_eq_mul_inv, one_mul,
    mul_inv_cancel₀ RatFunc.X_ne_zero, map_one]

omit [Algebra k K] [IsScalarTower k k[X] K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem XK_mem_ringOfIntegers :
    ∃ a : ringOfIntegers k K, (a : K) = XK k K := by
  have hx : (algebraMap k[X] K (Polynomial.X : k[X])) ∈ ringOfIntegers k K :=
    (mem_integralClosure_iff (R := k[X]) (A := K)).2
      (isIntegral_algebraMap (x := (Polynomial.X : k[X])))
  refine ⟨⟨algebraMap k[X] K (Polynomial.X : k[X]), hx⟩, ?_⟩
  dsimp [XK]
  rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, RatFunc.algebraMap_X]

omit [Algebra k K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem ringOfIntegers_coe_ne_zero {a : ringOfIntegers k K} (ha : a ≠ 0) : (a : K) ≠ 0 :=
  fun h => ha ((Subtype.ext_iff).mpr h)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem principalDivisorA_nonneg_at_finite_of_mem_ringOfIntegers {a : ringOfIntegers k K}
    (ha : a ≠ 0) (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    0 ≤ principalDivisorA k K
      (Additive.ofMul (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) (Sum.inl w) := by
  rw [principalDivisorA_apply_finite, FractionalIdeal.principalDivisor_apply]
  have hle := w.valuation_le_one (K := K) a
  have hval := FractionalIdeal.valuation_eq_exp_neg_count (R := ringOfIntegers k K) (K := K) w
    (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))
  have hcount :
      FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K)
        (Additive.ofMul (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) w =
      FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton (ringOfIntegers k K)⁰
          (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) := by
    rfl
  have hnonneg :
      0 ≤ FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton (ringOfIntegers k K)⁰
          (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) := by
    let count :=
      FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton (ringOfIntegers k K)⁰
          (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha)))
    have hle' : -count ≤ 0 :=
      WithZero.exp_le_exp.mp (by rw [← hval, WithZero.exp_zero]; exact hle)
    exact neg_nonpos.mp hle'
  simpa [hcount] using hnonneg

omit [IsFullConstantField k K] in
theorem polarDivisor_XK_zero_at_finite
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    polarDivisor k K (XK k K) (Sum.inl w) = 0 := by
  have hx0 : XK k K ≠ 0 := XK_ne_zero k K
  obtain ⟨a, ha⟩ := XK_mem_ringOfIntegers k K
  have ha0 : a ≠ 0 := fun ha0 => hx0 (by simpa [ha] using congrArg Subtype.val ha0)
  have hprincipal :
      0 ≤ principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0)) (Sum.inl w) := by
    simpa [ha] using
      principalDivisorA_nonneg_at_finite_of_mem_ringOfIntegers (k := k) (K := K) ha0 w
  unfold polarDivisor
  simp only [dite_eq_right hx0, Finsupp.sup_apply]
  exact max_eq_right (neg_nonpos.mpr hprincipal)

omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem tK_ne_zero : tK k K ≠ 0 := by
  dsimp [tK, tRatFunc]
  intro h
  rw [← map_zero (algebraMap k⟮X⟯ K)] at h
  exact one_div_ne_zero RatFunc.X_ne_zero <|
    (RingHom.injective (algebraMap k⟮X⟯ K)).eq_iff.mp h

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem principalDivisorA_tK_at_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    principalDivisorA k K (Additive.ofMul (Units.mk0 (tK k K) (tK_ne_zero k K))) (Sum.inr v) =
      (ramIdxInfty k K v.asIdeal : ℤ) := by
  rw [principalDivisorA_apply_infinite]
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let tS : S := algebraMap A S (tA k)
  have htK : tK k K = algebraMap A K (tA k) := by
    dsimp [tK, tA, tRatFunc]
    rfl
  have hspan :
      FractionalIdeal.spanSingleton S⁰ (tK k K) =
        (Ideal.span {tS} : FractionalIdeal S⁰ K) := by
    rw [htK, IsScalarTower.algebraMap_apply A S K, ← FractionalIdeal.coeIdeal_span_singleton]
  have htS : tS ≠ 0 := by
    intro h
    have hz : tK k K = 0 := by
      dsimp [tS] at h
      rw [htK, IsScalarTower.algebraMap_apply A S K, h, map_zero]
    exact tK_ne_zero k K hz
  let p := IsLocalRing.maximalIdeal A
  have hinj := ValuationSubring.integralClosure_algebraMap_injective
    (v := RatFunc.inftyValuation k) (L := K)
  have hpne : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  have hmap : Ideal.map (algebraMap A S) p ≠ ⊥ := by
    rintro hbot
    exact hpne ((Ideal.map_eq_bot_iff_of_injective hinj).mp hbot)
  have hcount :
      FractionalIdeal.principalDivisor (R := S) (K := K)
          (Additive.ofMul (Units.mk0 (tK k K) (tK_ne_zero k K))) v =
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.map (algebraMap A S) p)).count
          v.asIdeal := by
    rw [FractionalIdeal.principalDivisor_apply, toMul_ofMul, Units.val_mk0, hspan,
      FractionalIdeal.count_coe (K := K) v (Ideal.span_singleton_eq_bot.not.mpr htS),
      ← map_maximalIdeal_infty k]
    rw [Ideal.count_associates_factors_eq hmap v.isPrime v.ne_bot]
  rw [hcount, ← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime
      v.ne_bot, ramIdxInfty]

omit [IsFullConstantField k K] in
theorem principalDivisorA_XK_at_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) (XK_ne_zero k K))) (Sum.inr v) =
      -(ramIdxInfty k K v.asIdeal : ℤ) := by
  have hx0 : XK k K ≠ 0 := XK_ne_zero k K
  have ht0 : tK k K ≠ 0 := tK_ne_zero k K
  let hunit : Kˣ := Units.mk0 (XK k K * tK k K) (by rw [XK_mul_tK k K]; exact one_ne_zero)
  have hmul : hunit = Units.mk0 (XK k K) hx0 * Units.mk0 (tK k K) ht0 := by
    apply Units.ext
    simp [hunit, Units.val_mul, Units.val_mk0, XK_mul_tK k K]
  have hprod :
      principalDivisorA k K (Additive.ofMul hunit) =
        principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0)) +
          principalDivisorA k K (Additive.ofMul (Units.mk0 (tK k K) ht0)) := by
    rw [show Additive.ofMul hunit =
        Additive.ofMul (Units.mk0 (XK k K) hx0 * Units.mk0 (tK k K) ht0) from congr_arg _ hmul,
      ofMul_mul, (principalDivisorA k K).map_add]
  have hone : principalDivisorA k K (Additive.ofMul hunit) = 0 := by
    ext w
    simp only [Finsupp.zero_apply]
    have hv := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul hunit) w
    have hval' : placeValuation k K w ↑(Additive.toMul (Additive.ofMul hunit)) = 1 := by
      rw [toMul_ofMul, show (↑hunit : K) = 1 by simp [hunit, XK_mul_tK k K]]
      rcases w with w | w <;> simp [placeValuation]
    have hexp :
        WithZero.exp (-((principalDivisorA k K) (Additive.ofMul hunit)) w) = WithZero.exp 0 :=
      (hv.symm.trans hval').trans WithZero.exp_zero.symm
    exact neg_eq_zero.mp (WithZero.exp_injective hexp)
  have hzero :
      principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0)) (Sum.inr v) +
          principalDivisorA k K (Additive.ofMul (Units.mk0 (tK k K) ht0)) (Sum.inr v) = 0 := by
    have := congrArg (fun D => D (Sum.inr v)) hone
    rwa [hprod] at this
  rw [principalDivisorA_tK_at_infinite k K v] at hzero
  linarith

omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [IsFullConstantField k K] in
theorem ramificationIdx_pos_over_infty
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    0 < ramIdxInfty k K v.asIdeal := by
  let A := inftyValuationSubring k
  let p := IsLocalRing.maximalIdeal A
  have hpne : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  have hPp : v.asIdeal.LiesOver p := ⟨(IsLocalRing.eq_maximalIdeal inferInstance).symm⟩
  exact Nat.cast_pos.mpr <|
    Nat.pos_iff_ne_zero.mpr <|
      IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (S := infiniteIntegers k K)
        v.asIdeal hpne

omit [IsFullConstantField k K] in
theorem polarDivisor_XK_at_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    polarDivisor k K (XK k K) (Sum.inr v) = ramIdxInfty k K v.asIdeal := by
  have hx0 : XK k K ≠ 0 := XK_ne_zero k K
  have hprincipal := principalDivisorA_XK_at_infinite (k := k) (K := K) v
  have hpos : 0 < (ramIdxInfty k K v.asIdeal : ℤ) :=
    Nat.cast_pos.mpr (ramificationIdx_pos_over_infty (k := k) (K := K) v)
  have hneg :
      (-principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0))) (Sum.inr v) =
        (ramIdxInfty k K v.asIdeal : ℤ) := by
    simpa using congrArg Neg.neg hprincipal
  unfold polarDivisor
  simp only [dite_eq_right hx0, Finsupp.sup_apply, hneg]
  exact max_eq_left (le_of_lt hpos)

/-- The height-one ideal above `∞` corresponding to an infinite place. -/
noncomputable def inftyIdealOfPlace (v : PlaceA k K) : Ideal (infiniteIntegers k K) :=
  match v with
  | Sum.inr w => w.asIdeal
  | Sum.inl _ => ⊥

omit [IsFullConstantField k K] in
theorem deg_polarDivisor_XK_eq_primesOverFinset_sum :
    deg k K (polarDivisor k K (XK k K)) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset
          (IsLocalRing.maximalIdeal (inftyValuationSubring k)) (infiniteIntegers k K),
        (ramIdxInfty k K P : ℤ) *
          ((IsLocalRing.maximalIdeal (inftyValuationSubring k)).inertiaDeg' P : ℤ) := by
  classical
  rw [deg, Finsupp.sum]
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p := IsLocalRing.maximalIdeal A
  let D := polarDivisor k K (XK k K)
  have hp : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  let pred : PlaceA k K → Prop := fun v => match v with | Sum.inr _ => true | _ => false
  let g : PlaceA k K → ℤ := fun v => (D v : ℤ) * (placeDegree k K v : ℤ)
  have hsum_filter :
      D.support.sum g =
        (D.support.filter pred).sum g :=
    Eq.symm <|
      Finset.sum_subset (Finset.filter_subset pred D.support) fun v hv hv' => by
        rcases v with v | v
        · rw [polarDivisor_XK_zero_at_finite, zero_mul]
        · exfalso
          simp only [Finset.mem_filter, pred] at hv'
          exact hv' ⟨hv, by simp⟩
  rw [hsum_filter]
  apply Finset.sum_bij (fun v _ => inftyIdealOfPlace (k := k) (K := K) v)
  · intro v hv
    simp only [Finset.mem_filter, pred] at hv
    obtain ⟨_, hright⟩ := hv
    rcases v with v | w
    · cases hright
    · rw [IsDedekindDomain.mem_primesOverFinset_iff hp]
      have hpw : p = w.asIdeal.under A :=
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A w.asIdeal)).symm
      exact ⟨w.isPrime, ⟨hpw⟩⟩
  · intro v₁ hv₁ v₂ hv₂ h
    simp only [Finset.mem_filter, pred] at hv₁ hv₂ ⊢
    match v₁ with
    | Sum.inl _ => simp at hv₁
    | Sum.inr w₁ =>
      match v₂ with
      | Sum.inl _ => simp at hv₂
      | Sum.inr w₂ =>
        simp only [inftyIdealOfPlace] at h
        exact congrArg Sum.inr (IsDedekindDomain.HeightOneSpectrum.ext h)
  · intro P hP
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff hp (P := P)).mp hP
    have hprime : P.IsPrime := hmem.1
    have hbot : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hmem
    let w : IsDedekindDomain.HeightOneSpectrum S := ⟨P, hprime, hbot⟩
    refine ⟨Sum.inr w, ?_, rfl⟩
    · simp only [Finset.mem_filter, pred, Finsupp.mem_support_iff]
      refine And.intro ?_ (by simp)
      rw [polarDivisor_XK_at_infinite]
      norm_cast
      exact (ramificationIdx_pos_over_infty k K w).ne'
  · intro v hv
    simp only [Finset.mem_filter, pred, inftyIdealOfPlace] at hv ⊢
    rcases v with v | v
    · simp at hv
    · have hpw : v.asIdeal.under A = p :=
        IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A v.asIdeal)
      rw [polarDivisor_XK_at_infinite k K v, ramIdxInfty, placeDegree_infinite_eq_inertiaDeg, hpw]

omit [IsFullConstantField k K] in
/-- Stichtenoth 1.4.11 ramification half for the chart variable: `deg (X_K)_∞ ≤ [K : k(X)]`. -/
theorem deg_polarX_le_finrank :
    deg k K (polarDivisor k K (XK k K)) ≤ Module.finrank k⟮X⟯ K := by
  rw [deg_polarDivisor_XK_eq_primesOverFinset_sum k K]
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p := IsLocalRing.maximalIdeal A
  have hp : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  let : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  have hsum := Ideal.sum_ramificationIdx'_mul_inertiaDeg' (R := A) (S := S) k⟮X⟯ K hp
  have heq :
      (∑ P ∈ IsDedekindDomain.primesOverFinset p S,
          (ramIdxInfty k K P : ℤ) * (p.inertiaDeg' P : ℤ)) =
        Module.finrank k⟮X⟯ K := by
    dsimp [ramIdxInfty]
    norm_cast
  exact le_of_eq heq

end FunctionField.Chart

end
