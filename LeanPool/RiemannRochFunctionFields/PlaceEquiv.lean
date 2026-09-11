/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Place
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Coordinate-free places and the two-chart presentation

This file proves that the intrinsic valuation-subring places of a one-dimensional function field
are equivalent to the finite/infinite two-chart presentation.  The proof restricts a place to
`k(X)`, applies Ostrowski's theorem, and recovers the unique height-one centre in the appropriate
integral closure.

## Main definitions

* `FunctionField.Place.ofChart`: regard a coordinate place as an intrinsic place.
* `FunctionField.Place.toChart`: recover a coordinate chart from an intrinsic place.
* `FunctionField.chartToPlace`: the equivalence between the two presentations.
* `FunctionField.placeValuation_isEquiv`: compatibility of normalized valuations.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField

open MonoidWithZeroHom
open Chart

variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

/-- Classical decidable equality for the rational function field used by Ostrowski. -/
local instance instDecidableEqRatFuncPlaceEquiv : DecidableEq k⟮X⟯ := Classical.decEq _

/-- A coordinate place, regarded as an intrinsic valuation subring. -/
noncomputable def Place.ofChart (w : PlaceA k K) : Place k K := by
  let q := placeValuation k K w
  let V := q.valuationSubring
  have hqdisc : q.IsRankOneDiscrete := by
    rcases w with w | w <;> dsimp [q, placeValuation] <;> infer_instance
  have hqnontrivial : q.IsNontrivial := by
    rcases w with w | w <;> dsimp [q, placeValuation] <;> infer_instance
  refine
    { toValuationSubring := V
      ne_top := by
        change q.valuationSubring ≠ ⊤
        intro htop
        exact (Valuation.valuationSubring_eq_top_iff q).mp htop hqnontrivial
      triv_on_k := fun c => by
        rw [Valuation.mem_valuationSubring_iff]
        exact placeValuation_algebraMap_le_one k K w c
      isDiscrete := ?_ }
  let : q.IsRankOneDiscrete := hqdisc
  let h := Valuation.isEquiv_valuation_valuationSubring q
  exact ⟨h.orderMonoidIso.symm.trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)⟩

@[simp]
theorem Place.ofChart_toValuationSubring (w : PlaceA k K) :
    (Place.ofChart k K w).toValuationSubring =
      (placeValuation k K w).valuationSubring := rfl

theorem Place.ofChart_valuation_isEquiv (w : PlaceA k K) :
    (placeValuation k K w).IsEquiv (Place.ofChart k K w).valuation := by
  rw [Valuation.isEquiv_iff_valuationSubring,
    Place.valuationSubring_valuation, Place.ofChart_toValuationSubring]

/-- The normalized intrinsic valuation attached to a coordinate place is exactly its coordinate
valuation. This strengthens equivalence by using uniqueness of the ordered `ℤᵐ⁰`
normalization. -/
theorem Place.ofChart_valuation_eq (w : PlaceA k K) :
    (Place.ofChart k K w).valuation = placeValuation k K w := by
  let q := placeValuation k K w
  let V := q.valuationSubring
  have hqdisc : q.IsRankOneDiscrete := by
    rcases w with w | w <;> dsimp [q, placeValuation] <;> infer_instance
  let : q.IsRankOneDiscrete := hqdisc
  let h := Valuation.isEquiv_valuation_valuationSubring q
  let e : ValueGroup₀ (.ofClass V.valuation) ≃*o ℤᵐ⁰ :=
    h.orderMonoidIso.symm.trans
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
  have hnorm : (Place.ofChart k K w).normalization = e :=
    orderMonoidIso_withZeroMulInt_unique _ _
  ext x
  change (Place.ofChart k K w).normalization
      (V.valuation.restrict x) = q x
  rw [hnorm]
  change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
      (h.orderMonoidIso.symm (V.valuation.restrict x)) = q x
  rw [show h.orderMonoidIso.symm (V.valuation.restrict x) = q.restrict x by
    change h.orderMonoidIso.symm
      (q.valuationSubring.valuation.restrict x) = q.restrict x
    exact h.orderMonoidIso.symm_apply_eq.mpr (h.orderMonoidIso_spec x).symm]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (by
        rcases w with w | w
        · exact w.valuation_surjective K
        · exact w.valuation_surjective K) x

omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem Place.finite_X_le_one
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    w.valuation K (algebraMap k⟮X⟯ K RatFunc.X) ≤ 1 := by
  let r : ringOfIntegers k K := algebraMap k[X] (ringOfIntegers k K) Polynomial.X
  have hr := w.valuation_le_one (K := K) r
  have hr_eq : (r : K) = algebraMap k⟮X⟯ K RatFunc.X := by
    calc
      (r : K) = algebraMap (ringOfIntegers k K) K r := rfl
      _ = algebraMap k[X] K Polynomial.X := by
        simpa only [r] using
          (IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K Polynomial.X).symm
      _ = algebraMap k⟮X⟯ K RatFunc.X := by
        rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, RatFunc.algebraMap_X]
  rw [← hr_eq]
  exact hr

namespace Place

variable {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
  [Algebra R L] [IsFractionRing R L]

/-- The centre in a Dedekind model of a valuation subring containing that model. -/
noncomputable def centerIdeal (V : ValuationSubring L)
    (hR : ∀ r : R, algebraMap R L r ∈ V) : Ideal R :=
  (IsLocalRing.maximalIdeal V).comap
    ((algebraMap R L).codRestrict V hR)

instance centerIdeal_isPrime (V : ValuationSubring L)
    (hR : ∀ r : R, algebraMap R L r ∈ V) : (centerIdeal V hR).IsPrime :=
  (IsLocalRing.maximalIdeal V).comap_isPrime _

/-- A nonzero centre is a height-one prime of a Dedekind model. -/
noncomputable def center (V : ValuationSubring L)
    (hR : ∀ r : R, algebraMap R L r ∈ V) (hne : centerIdeal V hR ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum R where
  asIdeal := centerIdeal V hR
  isPrime := inferInstance
  ne_bot := hne

theorem valuationSubringAtPrime_center (V : ValuationSubring L) (hV : V ≠ ⊤)
    (hR : ∀ r : R, algebraMap R L r ∈ V) (hne : centerIdeal V hR ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L (center V hR hne) = V := by
  let w := center V hR hne
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w
  have hle : A ≤ V := by
    rintro x hx
    have hvx : w.valuation L x ≤ 1 := by
      rw [← Valuation.mem_valuationSubring_iff,
        ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hx
    obtain ⟨a, s, hxs⟩ := w.exists_primeCompl_mul_eq_of_integer x hvx
    have hs_not_center : (s : R) ∉ centerIdeal V hR := by
      change (s : R) ∉ w.asIdeal
      exact s.property
    have hs_inv_mem : (algebraMap R L s)⁻¹ ∈ V := by
      have hs_not_max :
          ((⟨algebraMap R L s, hR s⟩ : V) ∉ IsLocalRing.maximalIdeal V) := by
        exact hs_not_center
      have hs_unit : IsUnit (⟨algebraMap R L s, hR s⟩ : V) := by
        simpa [IsLocalRing.mem_maximalIdeal] using hs_not_max
      obtain ⟨u, hu⟩ := hs_unit
      have hinv_mem : (algebraMap R L s)⁻¹ ∈ V := by
        have huval : ((u : V) : L) = algebraMap R L s := by
          exact congrArg Subtype.val hu
        have huinv : (((u⁻¹ : Vˣ) : V) : L) = (algebraMap R L s)⁻¹ := by
          have hmV : ((u⁻¹ : Vˣ) : V) * (u : V) = 1 := by simp
          have hmL := congrArg (fun z : V => (z : L)) hmV
          change (((u⁻¹ : Vˣ) : V) : L) * ((u : V) : L) = 1 at hmL
          rw [huval] at hmL
          exact eq_inv_of_mul_eq_one_left hmL
        rw [← huinv]
        exact (u⁻¹ : Vˣ).val.property
      exact hinv_mem
    have hs_ne : algebraMap R L s ≠ 0 := by
      have hsR : (s : R) ≠ 0 := by
        intro hs0
        exact s.property (hs0 ▸ w.asIdeal.zero_mem)
      intro hs0
      apply hsR
      apply FaithfulSMul.algebraMap_injective R L
      simpa using hs0
    have hx_eq : x = algebraMap R L a * (algebraMap R L s)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq₀ hs_ne).2
      exact hxs
    rw [hx_eq]
    exact V.mul_mem _ _ (hR a) hs_inv_mem
  exact ValuationSubring.eq_of_le_of_ne_top A hle hV

end Place

namespace Place

local instance instTowerConstantsRatFunc : IsScalarTower k k⟮X⟯ K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    exact (IsScalarTower.algebraMap_apply k k[X] K c).trans
      (IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K (algebraMap k k[X] c))

/-- The restriction of an intrinsic place to the rational function subfield. -/
noncomputable def restrict (v : Place k K) : Valuation k⟮X⟯ ℤᵐ⁰ :=
  v.valuation.comap (algebraMap k⟮X⟯ K)

instance restrict_isTrivialOn (v : Place k K) : (restrict k K v).IsTrivialOn k where
  eq_one c hc := by
    change v.valuation
      (algebraMap k⟮X⟯ K (algebraMap k k⟮X⟯ c)) = 1
    rw [← IsScalarTower.algebraMap_apply k k⟮X⟯ K]
    exact Valuation.IsTrivialOn.eq_one c hc

omit [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
    [FunctionField k K] in
theorem restrict_isNontrivial (v : Place k K) :
    (restrict k K v).IsNontrivial := by
  let q := restrict k K v
  by_contra hq
  let : v.valuation.IsTrivialOn k⟮X⟯ :=
    { eq_one := fun a ha => by
        change q a = 1
        by_contra hne
        apply hq
        refine ⟨a, ?_, hne⟩
        simp [restrict, ha] }
  obtain ⟨y, hy0, hy1⟩ :=
    (inferInstance : v.valuation.IsNontrivial).exists_val_nontrivial
  have hy : y ≠ 0 := v.valuation.ne_zero_iff.mp hy0
  exact (Valuation.transcendental_of_ne_one k⟮X⟯ y hy hy1)
    (Algebra.IsAlgebraic.isAlgebraic y)

omit [FunctionField k K] in
theorem restrict_classification (v : Place k K) :
    Xor ((restrict k K v).IsEquiv (RatFunc.inftyValuation k))
      (∃! u : IsDedekindDomain.HeightOneSpectrum k[X],
        (restrict k K v).IsEquiv (u.valuation k⟮X⟯)) := by
  let q := restrict k K v
  let : q.IsNontrivial := restrict_isNontrivial k K v
  let : q.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' q
  exact RatFunc.valuation_isEquiv_infty_or_adic (v := q)

omit [IsScalarTower k k[X] K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem finiteRing_le (v : Place k K)
    (u : IsDedekindDomain.HeightOneSpectrum k[X])
    (h : (restrict k K v).IsEquiv (u.valuation k⟮X⟯)) :
    ∀ r : ringOfIntegers k K, algebraMap (ringOfIntegers k K) K r ∈
      v.toValuationSubring := by
  have hpoly : ∀ p : k[X], algebraMap k[X] K p ∈ v.toValuationSubring := by
    intro p
    rw [← v.valuationSubring_valuation, Valuation.mem_valuationSubring_iff]
    rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
    exact h.le_one_iff_le_one.mpr (u.valuation_le_one p)
  let : IsIntegrallyClosedIn v.toValuationSubring.toSubring K :=
    Subring.isIntegrallyClosedIn_iff.mpr fun {_x} hx =>
      LocalSubring.mem_of_isMax_of_isIntegral
        v.toValuationSubring.isMax_toLocalSubring hx
  have hle : (ringOfIntegers k K).toSubring ≤ v.toValuationSubring.toSubring :=
    (Subring.integralClosure_le_iff).mpr hpoly
  exact fun r => hle r.property

omit [IsScalarTower k k[X] K] in
theorem finiteCenter_ne (v : Place k K)
    (u : IsDedekindDomain.HeightOneSpectrum k[X])
    (h : (restrict k K v).IsEquiv (u.valuation k⟮X⟯)) :
    centerIdeal v.toValuationSubring (finiteRing_le k K v u h) ≠ ⊥ := by
  obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot u.ne_bot
  let r : ringOfIntegers k K := algebraMap k[X] (ringOfIntegers k K) a
  have hr_ne : r ≠ 0 := by
    intro hr
    apply ha_ne
    apply FaithfulSMul.algebraMap_injective k[X] (ringOfIntegers k K)
    simpa [r] using hr
  intro hbot
  have hr_center : r ∈
      centerIdeal v.toValuationSubring (finiteRing_le k K v u h) := by
    change (⟨algebraMap (ringOfIntegers k K) K r,
      finiteRing_le k K v u h r⟩ : v.toValuationSubring) ∈
        IsLocalRing.maximalIdeal v.toValuationSubring
    rw [v.toValuationSubring.valuation_lt_one_iff]
    have hnorm : v.valuation (algebraMap (ringOfIntegers k K) K r) < 1 := by
      rw [show algebraMap (ringOfIntegers k K) K r = algebraMap k[X] K a by
        simpa only [r] using
          (IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K a).symm,
        IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
      exact h.lt_one_iff_lt_one.mpr
        ((u.valuation_lt_one_iff_mem a).mpr ha_mem)
    simpa only [map_one] using
      v.valuation_isEquiv_canonical.lt_one_iff_lt_one.mp hnorm
  rw [hbot] at hr_center
  exact hr_ne (Ideal.mem_bot.mp hr_center)

omit [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
    [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem infiniteRing_le (v : Place k K)
    (h : (restrict k K v).IsEquiv (RatFunc.inftyValuation k)) :
    ∀ r : infiniteIntegers k K, algebraMap (infiniteIntegers k K) K r ∈
      v.toValuationSubring := by
  have hbase : ∀ a : inftyValuationSubring k,
      algebraMap (inftyValuationSubring k) K a ∈ v.toValuationSubring := by
    intro a
    rw [← v.valuationSubring_valuation, Valuation.mem_valuationSubring_iff]
    rw [IsScalarTower.algebraMap_apply (inftyValuationSubring k) k⟮X⟯ K]
    exact h.le_one_iff_le_one.mpr a.property
  let : IsIntegrallyClosedIn v.toValuationSubring.toSubring K :=
    Subring.isIntegrallyClosedIn_iff.mpr fun {_x} hx =>
      LocalSubring.mem_of_isMax_of_isIntegral
        v.toValuationSubring.isMax_toLocalSubring hx
  have hle : (infiniteIntegers k K).toSubring ≤ v.toValuationSubring.toSubring :=
    (Subring.integralClosure_le_iff).mpr hbase
  exact fun r => hle r.property

omit [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] in
theorem infiniteCenter_ne (v : Place k K)
    (h : (restrict k K v).IsEquiv (RatFunc.inftyValuation k)) :
    centerIdeal v.toValuationSubring (infiniteRing_le k K v h) ≠ ⊥ := by
  let A := inftyValuationSubring k
  let u := IsDiscreteValuationRing.maximalIdeal A
  obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot u.ne_bot
  let r : infiniteIntegers k K := algebraMap A (infiniteIntegers k K) a
  have hr_ne : r ≠ 0 := by
    intro hr
    apply ha_ne
    apply FaithfulSMul.algebraMap_injective A (infiniteIntegers k K)
    simpa [r] using hr
  intro hbot
  have hr_center : r ∈
      centerIdeal v.toValuationSubring (infiniteRing_le k K v h) := by
    change (⟨algebraMap (infiniteIntegers k K) K r,
      infiniteRing_le k K v h r⟩ : v.toValuationSubring) ∈
        IsLocalRing.maximalIdeal v.toValuationSubring
    rw [v.toValuationSubring.valuation_lt_one_iff]
    have hnorm : v.valuation (algebraMap (infiniteIntegers k K) K r) < 1 := by
      rw [show algebraMap (infiniteIntegers k K) K r = algebraMap A K a by
        simpa only [r] using
          (IsScalarTower.algebraMap_apply A (infiniteIntegers k K) K a).symm,
        IsScalarTower.algebraMap_apply A k⟮X⟯ K]
      exact h.lt_one_iff_lt_one.mpr
        ((Valuation.mem_maximalIdeal_iff (v := RatFunc.inftyValuation k)).mp ha_mem)
    simpa only [map_one] using
      v.valuation_isEquiv_canonical.lt_one_iff_lt_one.mp hnorm
  rw [hbot] at hr_center
  exact hr_ne (Ideal.mem_bot.mp hr_center)

omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] in
theorem infinite_X_gt_one
    (w : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    1 < w.valuation K (algebraMap k⟮X⟯ K RatFunc.X) := by
  let A := inftyValuationSubring k
  let u := IsDiscreteValuationRing.maximalIdeal A
  have hund : w.asIdeal.under A = u.asIdeal := by
    exact IsLocalRing.eq_maximalIdeal inferInstance
  let : w.asIdeal.LiesOver u.asIdeal := ⟨hund.symm⟩
  have hbase : (u.valuation k⟮X⟯).IsEquiv (RatFunc.inftyValuation k) := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    apply ValuationSubring.toSubring_injective
    have hmap : Subring.map (algebraMap A k⟮X⟯) ⊤ = A.toSubring := by
      ext x
      constructor
      · rintro ⟨a, _, rfl⟩
        exact a.property
      · intro hx
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    exact (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := A) (K := k⟮X⟯)).symm.trans hmap
  have hbaseX : 1 < u.valuation k⟮X⟯ RatFunc.X :=
    hbase.one_lt_iff_one_lt.mpr (by simp [← WithZero.exp_zero])
  have he : u.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal u.ne_bot
  have hpow : 1 < (u.valuation k⟮X⟯ RatFunc.X) ^
      u.asIdeal.ramificationIdx' w.asIdeal := by
    exact one_lt_pow₀ hbaseX he
  rw [u.valuation_liesOver K w RatFunc.X] at hpow
  exact hpow

theorem ofChart_injective : Function.Injective (Place.ofChart k K) := by
  intro w₁ w₂ hw
  have hsub := congrArg Place.toValuationSubring hw
  simp only [Place.ofChart_toValuationSubring] at hsub
  rcases w₁ with w₁ | w₁ <;> rcases w₂ with w₂ | w₂
  · congr 1
    exact IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      ((Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub)
  · have hequiv : (w₁.valuation K).IsEquiv (w₂.valuation K) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
    have hle := hequiv.le_one_iff_le_one.mp (finite_X_le_one k K w₁)
    exact (not_le_of_gt (infinite_X_gt_one k K w₂) hle).elim
  · have hequiv : (w₂.valuation K).IsEquiv (w₁.valuation K) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub.symm
    have hle := hequiv.le_one_iff_le_one.mp (finite_X_le_one k K w₂)
    exact (not_le_of_gt (infinite_X_gt_one k K w₁) hle).elim
  · congr 1
    exact IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      ((Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub)

/-- Every intrinsic place occurs on one of the two coordinate charts. -/
theorem exists_chart (v : Place k K) :
    ∃ w : PlaceA k K, Place.ofChart k K w = v := by
  rcases restrict_classification k K v with h | h
  · let w := center v.toValuationSubring
      (infiniteRing_le k K v h.1) (infiniteCenter_ne k K v h.1)
    refine ⟨Sum.inr w, Place.ext ?_⟩
    rw [Place.ofChart_toValuationSubring]
    change (w.valuation K).valuationSubring = _
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact valuationSubringAtPrime_center v.toValuationSubring v.ne_top
      (infiniteRing_le k K v h.1) (infiniteCenter_ne k K v h.1)
  · let u := h.1.choose
    have hu := h.1.choose_spec.1
    let w := center v.toValuationSubring
      (finiteRing_le k K v u hu) (finiteCenter_ne k K v u hu)
    refine ⟨Sum.inl w, Place.ext ?_⟩
    rw [Place.ofChart_toValuationSubring]
    change (w.valuation K).valuationSubring = _
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact valuationSubringAtPrime_center v.toValuationSubring v.ne_top
      (finiteRing_le k K v u hu) (finiteCenter_ne k K v u hu)

/-- Recover a coordinate chart containing an intrinsic place. -/
noncomputable def toChart (v : Place k K) : PlaceA k K :=
  Classical.choose (exists_chart k K v)

theorem ofChart_toChart (v : Place k K) :
    Place.ofChart k K (toChart k K v) = v :=
  Classical.choose_spec (exists_chart k K v)

/-- Coordinate places and intrinsic places are equivalent. -/
noncomputable def chartToPlaceCore : PlaceA k K ≃ Place k K where
  toFun := Place.ofChart k K
  invFun := toChart k K
  left_inv w := ofChart_injective k K (ofChart_toChart k K (Place.ofChart k K w))
  right_inv := ofChart_toChart k K

end Place

/-- The equivalence from the two-chart construction to coordinate-free places. -/
noncomputable abbrev chartToPlace : PlaceA k K ≃ Place k K :=
  Place.chartToPlaceCore k K

@[simp]
theorem chartToPlace_apply (w : PlaceA k K) :
    chartToPlace k K w = Place.ofChart k K w := rfl

/-- The coordinate valuation and the normalized intrinsic valuation define the same place. -/
theorem placeValuation_isEquiv (w : PlaceA k K) :
    (placeValuation k K w).IsEquiv (chartToPlace k K w).valuation :=
  Place.ofChart_valuation_isEquiv k K w

/-- Compatibility of the chart and intrinsic normalized valuations. -/
theorem placeValuation_eq (w : PlaceA k K) :
    (chartToPlace k K w).valuation = placeValuation k K w :=
  Place.ofChart_valuation_eq k K w

end FunctionField
