/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.RingTheory.DedekindDomain.Factorization
/-!
# Torsion and rank sources for `S`-units

This file supplies the algebraic rank and torsion input for `S`-units.
The finite set `S` contains the finite places; all infinite places are
understood to be present.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain
open scoped NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

/-- The group of ordinary units, expressed as `S`-units for the empty set. -/
noncomputable def emptyEquivNumberFieldUnits :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) ≃* (𝓞 K)ˣ :=
  let eInteger :
      ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)ˣ ≃*
        (⊥ : Subalgebra (𝓞 K) K)ˣ :=
    Units.mapEquiv
      ((Subalgebra.equivOfEq
        ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)
        (⊥ : Subalgebra (𝓞 K) K)
        (IsDedekindDomain.integer_empty (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  let eBot :
      (⊥ : Subalgebra (𝓞 K) K)ˣ ≃* (𝓞 K)ˣ :=
    Units.mapEquiv
      ((Algebra.botEquivOfInjective
        (IsFractionRing.injective (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  (Set.unitEquivUnitsInteger
    (∅ : Set (HeightOneSpectrum (𝓞 K))) K).trans
      (eInteger.trans eBot)

/-- The canonical embedding of ordinary units into the `S`-unit group. -/
noncomputable def fromNumberFieldUnits
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (𝓞 K)ˣ →* SUnitGroup (K := K) S where
  toFun u :=
    ⟨((emptyEquivNumberFieldUnits (K := K)).symm u : Kˣ),
      fun v _ =>
        Set.unit_valuation_eq_one
          (∅ : Set (HeightOneSpectrum (𝓞 K))) K
          ((emptyEquivNumberFieldUnits (K := K)).symm u) (by simp)⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

theorem fromNumberFieldUnits_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (fromNumberFieldUnits (K := K) S) := by
  intro u v huv
  apply (emptyEquivNumberFieldUnits (K := K)).symm.injective
  ext
  exact congrArg (fun x : SUnitGroup (K := K) S => ((x : Kˣ) : K)) huv

/-- Torsion in an `S`-unit group consists exactly of the ordinary roots of
unity. -/
theorem torsion_eq_rootsOfUnity_range
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    CommGroup.torsion (SUnitGroup (K := K) S) =
      Subgroup.map (fromNumberFieldUnits (K := K) S)
        (NumberField.Units.torsion K) := by
  ext x
  constructor
  · intro hx
    have hxfin : IsOfFinOrder x :=
      (CommGroup.mem_torsion (G := SUnitGroup (K := K) S) x).mp hx
    obtain ⟨n, hnpos, hxpow⟩ := hxfin.exists_pow_eq_one
    have hxK : (((x : Kˣ) : K) ^ n) = 1 := by
      simpa using congrArg
        (fun y : SUnitGroup (K := K) S => ((y : Kˣ) : K)) hxpow
    let y : ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
      ⟨(x : Kˣ), fun v _ => by
        have hvpow :
            (v.valuation K ((x : Kˣ) : K)) ^ n = 1 := by
          rw [← map_pow, hxK, map_one]
        exact (pow_eq_one_iff_left
          (a := v.valuation K ((x : Kˣ) : K))
          (Nat.ne_of_gt hnpos)).mp hvpow⟩
    let u : (𝓞 K)ˣ := emptyEquivNumberFieldUnits y
    have hufin : IsOfFinOrder u := by
      exact (emptyEquivNumberFieldUnits (K := K)).toMonoidHom.isOfFinOrder
        ((show IsOfFinOrder y from by
          refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, ?_⟩
          ext
          exact hxK))
    refine ⟨u, ?_, ?_⟩
    · exact (CommGroup.mem_torsion (G := (𝓞 K)ˣ) u).2 hufin
    · ext
      change
        (((emptyEquivNumberFieldUnits (K := K)).symm
          (emptyEquivNumberFieldUnits (K := K) y) : Kˣ) : K) =
            ((x : Kˣ) : K)
      rw [MulEquiv.symm_apply_apply]
  · rintro ⟨u, hu, rfl⟩
    exact (CommGroup.mem_torsion
      (G := SUnitGroup (K := K) S)
      (fromNumberFieldUnits (K := K) S u)).2
        ((fromNumberFieldUnits (K := K) S).isOfFinOrder
          ((CommGroup.mem_torsion (G := (𝓞 K)ˣ) u).1 hu))

section DivisorMap

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The exponent of the principal fractional ideal of an `S`-unit at a
finite place in `S`. -/
noncomputable def divisorCoordinate
    (x : SUnitGroup (K := K) S) (v : S) : ℤ :=
  FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K))

/-- The valuation of a localization fraction is the exponential of the
negative exponent of its principal fractional ideal. -/
theorem valuation_mk'_eq_exp_neg_count
    (v : HeightOneSpectrum (𝓞 K)) {n : 𝓞 K} (hn : n ≠ 0)
    (d : (𝓞 K)⁰) :
    v.valuation K (IsLocalization.mk' K n d) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (IsLocalization.mk' K n d))) := by
  classical
  have hI :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K n d) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            ((algebraMap (𝓞 K) K) (d : 𝓞 K))⁻¹ *
          ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hx :
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (IsLocalization.mk' K n d) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff,
      IsFractionRing.mk'_eq_div, ne_eq, div_eq_zero_iff, not_or]
    exact
      ⟨(map_ne_zero_iff (algebraMap (𝓞 K) K)
          (IsFractionRing.injective (𝓞 K) K)).mpr hn,
        map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (𝓞 K) K) d.property⟩
  have hcount :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (IsLocalization.mk' K n d)) =
        ((Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {n} : Ideal (𝓞 K))).factors -
          (Associates.mk v.asIdeal).count
            (Associates.mk
              (Ideal.span {(d : 𝓞 K)} : Ideal (𝓞 K))).factors : ℤ) := by
    exact FractionalIdeal.count_well_defined (K := K) v hx hI
  rw [v.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), hcount]
  rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr
  simp [sub_eq_add_neg, add_comm]

/-- The adic valuation of a field unit is the exponential of the
negative exponent of its principal fractional ideal. -/
theorem valuation_eq_exp_neg_count
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (x : K) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) := by
  obtain ⟨n, d, hnd⟩ :=
    IsLocalization.exists_mk'_eq (𝓞 K)⁰ (x : K)
  have hn : n ≠ 0 := by
    intro hn0
    apply Units.ne_zero x
    rw [← hnd, hn0, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  rw [← hnd]
  exact valuation_mk'_eq_exp_neg_count (K := K) v hn d

/-- A field unit has valuation one exactly when its principal fractional
ideal has exponent zero at the place. -/
theorem valuation_eq_one_iff_count_eq_zero
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (x : K) = 1 ↔
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
  rw [valuation_eq_exp_neg_count (K := K) x v]
  constructor
  · intro h
    exact neg_eq_zero.mp (WithZero.exp_eq_one.mp h)
  · intro h
    simp [h]

theorem divisorCoordinate_eq_zero_iff
    (x : SUnitGroup (K := K) S) (v : S) :
    divisorCoordinate (K := K) S x v = 0 ↔
      (v : HeightOneSpectrum (𝓞 K)).valuation K ((x : Kˣ) : K) = 1 := by
  exact (valuation_eq_one_iff_count_eq_zero
    (K := K) (x : Kˣ) (v : HeightOneSpectrum (𝓞 K))).symm

theorem divisorCoordinate_mul
    (x y : SUnitGroup (K := K) S) (v : S) :
    divisorCoordinate (K := K) S (x * y) v =
      divisorCoordinate (K := K) S x v +
        divisorCoordinate (K := K) S y v := by
  change
    FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((((x : Kˣ) : K) * ((y : Kˣ) : K)))) =
      FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K)) +
        FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : Kˣ) : K))
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul]
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (x : Kˣ))
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (y : Kˣ))

theorem divisorCoordinate_one (v : S) :
    divisorCoordinate (K := K) S 1 v = 0 := by
  simp [divisorCoordinate, FractionalIdeal.count_one]

/-- The additive principal-divisor map on `S`-units. -/
noncomputable def divisor :
    Additive (SUnitGroup (K := K) S) →+
      (S → ℤ) where
  toFun x v := divisorCoordinate (K := K) S (Additive.toMul x) v
  map_zero' := by
    ext v
    exact divisorCoordinate_one (K := K) S v
  map_add' x y := by
    ext v
    exact divisorCoordinate_mul (K := K) S
      (Additive.toMul x) (Additive.toMul y) v

/-- The `ℤ`-linear principal-divisor map on `S`-units. -/
noncomputable def divisorLinearMap :
    Additive (SUnitGroup (K := K) S) →ₗ[ℤ] (S → ℤ) :=
  (divisor (K := K) S).toIntLinearMap

/-- The additive linearization of the ordinary-unit embedding. -/
noncomputable def fromNumberFieldUnitsLinearMap :
    Additive (𝓞 K)ˣ →ₗ[ℤ]
      Additive (SUnitGroup (K := K) S) :=
  (MonoidHom.toAdditive
    (fromNumberFieldUnits (K := K) S)).toIntLinearMap

theorem fromNumberFieldUnitsLinearMap_injective :
    Function.Injective (fromNumberFieldUnitsLinearMap (K := K) S) := by
  intro x y hxy
  apply Additive.toMul.injective
  exact fromNumberFieldUnits_injective (K := K) S
    (congrArg Additive.toMul hxy)

/-- An `S`-unit in the kernel of the divisor map has valuation one at every
finite place. -/
theorem valuation_eq_one_of_mem_ker_divisorLinearMap
    {x : Additive (SUnitGroup (K := K) S)}
    (hx : x ∈ LinearMap.ker (divisorLinearMap (K := K) S))
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K
      ((((Additive.toMul x :
        SUnitGroup (K := K) S) : Kˣ) : K)) = 1 := by
  by_cases hv : v ∈ S
  · let vv : S := ⟨v, hv⟩
    apply (divisorCoordinate_eq_zero_iff (K := K) S
      (Additive.toMul x) vv).1
    have hxzero :
        divisorLinearMap (K := K) S x = 0 :=
      LinearMap.mem_ker.mp hx
    simpa [divisorLinearMap, divisor] using congrFun hxzero vv
  · exact (Additive.toMul x :
      SUnitGroup (K := K) S).property v hv

/-- An `S`-unit in the divisor kernel, regarded as an `S`-unit for the
empty set. -/
noncomputable def kerDivisorToEmptySUnits
    (x : LinearMap.ker (divisorLinearMap (K := K) S)) :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
  ⟨((Additive.toMul (x : Additive (SUnitGroup (K := K) S)) :
      SUnitGroup (K := K) S) : Kˣ),
    fun v _ =>
      valuation_eq_one_of_mem_ker_divisorLinearMap
        (K := K) S x.property v⟩

/-- Ordinary units are exactly the kernel of the `S`-unit divisor map. -/
theorem range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap :
    LinearMap.range (fromNumberFieldUnitsLinearMap (K := K) S) =
      LinearMap.ker (divisorLinearMap (K := K) S) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    apply LinearMap.mem_ker.mpr
    ext v
    apply (divisorCoordinate_eq_zero_iff (K := K) S
      (fromNumberFieldUnits (K := K) S (Additive.toMul u)) v).2
    exact Set.unit_valuation_eq_one
      (∅ : Set (HeightOneSpectrum (𝓞 K))) K
      ((emptyEquivNumberFieldUnits (K := K)).symm (Additive.toMul u))
      (by simp)
  · intro hx
    let y := kerDivisorToEmptySUnits (K := K) S ⟨x, hx⟩
    let u : (𝓞 K)ˣ := emptyEquivNumberFieldUnits y
    refine ⟨Additive.ofMul u, ?_⟩
    apply Additive.toMul.injective
    change
      fromNumberFieldUnits (K := K) S u = Additive.toMul x
    apply Subtype.ext
    change
      ((emptyEquivNumberFieldUnits (K := K)).symm u : Kˣ) =
        ((Additive.toMul x : SUnitGroup (K := K) S) : Kˣ)
    dsimp [u]
    rw [MulEquiv.symm_apply_apply]
    rfl

end DivisorMap

section PrimePowerSources

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The class-number power of a prime ideal is principal. -/
theorem primeIdealPower_classNumber_isPrincipal (v : S) :
    ((v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K).IsPrincipal := by
  have hv0 :
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : HeightOneSpectrum (𝓞 K)).ne_bot
  apply (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hv0)).mp
  have hpow :
      (ClassGroup.mk0
        ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩) ^
          Fintype.card (ClassGroup (𝓞 K)) = 1 :=
    pow_card_eq_one
      (x := ClassGroup.mk0
        ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩)
  let I : (Ideal (𝓞 K))⁰ :=
    ⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (v : HeightOneSpectrum (𝓞 K)).ne_bot⟩
  have hsub :
      (⟨(v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K,
        mem_nonZeroDivisors_iff_ne_zero.mpr hv0⟩ :
          (Ideal (𝓞 K))⁰) =
        I ^ NumberField.classNumber K := by
    rfl
  rw [hsub, map_pow]
  exact hpow

/-- A generator of the principal `classNumber K`-th power of a prime ideal. -/
private noncomputable def primePowerGenerator (v : S) : 𝓞 K :=
  let I :=
    (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K
  letI : I.IsPrincipal :=
    primeIdealPower_classNumber_isPrincipal (K := K) S v
  Submodule.IsPrincipal.generator I

private theorem span_primePowerGenerator (v : S) :
    Ideal.span {primePowerGenerator (K := K) S v} =
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
        NumberField.classNumber K := by
  let I :=
    (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
      NumberField.classNumber K
  let : I.IsPrincipal :=
    primeIdealPower_classNumber_isPrincipal (K := K) S v
  simp [primePowerGenerator]

private theorem primePowerGenerator_ne_zero (v : S) :
    primePowerGenerator (K := K) S v ≠ 0 := by
  intro hzero
  have hv0 :
      (v : HeightOneSpectrum (𝓞 K)).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : HeightOneSpectrum (𝓞 K)).ne_bot
  apply hv0
  rw [← span_primePowerGenerator (K := K) S v, hzero]
  simp

private theorem spanSingleton_primePowerGenerator (v : S) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v)) =
      ((v : HeightOneSpectrum (𝓞 K)).asIdeal :
        FractionalIdeal (𝓞 K)⁰ K) ^ NumberField.classNumber K := by
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    span_primePowerGenerator (K := K) S v,
    FractionalIdeal.coeIdeal_pow]

/-- An `S`-unit whose divisor is `classNumber K` times the basis divisor at
`v`. -/
private noncomputable def primePowerSUnit (v : S) :
    SUnitGroup (K := K) S :=
  ⟨Units.mk0
      (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v))
      ((map_ne_zero_iff (algebraMap (𝓞 K) K)
        (IsFractionRing.injective (𝓞 K) K)).mpr
          (primePowerGenerator_ne_zero (K := K) S v)),
    fun w hw => by
      apply (valuation_eq_one_iff_count_eq_zero (K := K)
        (Units.mk0
          (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v))
          ((map_ne_zero_iff (algebraMap (𝓞 K) K)
            (IsFractionRing.injective (𝓞 K) K)).mpr
              (primePowerGenerator_ne_zero (K := K) S v))) w).2
      change
        FractionalIdeal.count K w
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (primePowerGenerator (K := K) S v))) = 0
      rw [spanSingleton_primePowerGenerator (K := K) S v,
        FractionalIdeal.count_pow]
      have hwv :
          (v : HeightOneSpectrum (𝓞 K)) ≠ w := by
        intro hvw
        exact hw (hvw ▸ v.property)
      rw [FractionalIdeal.count_maximal_coprime K w hwv]
      simp⟩

private noncomputable def classNumberBasisVector (v : S) : S → ℤ := by
  classical
  exact fun w =>
    if w = v then (NumberField.classNumber K : ℤ) else 0

private theorem divisorCoordinate_primePowerSUnit
    (v w : S) :
    divisorCoordinate (K := K) S (primePowerSUnit (K := K) S v) w =
      classNumberBasisVector (K := K) S v w := by
  classical
  change
    FractionalIdeal.count K (w : HeightOneSpectrum (𝓞 K))
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (primePowerGenerator (K := K) S v))) =
      classNumberBasisVector (K := K) S v w
  simp only [classNumberBasisVector]
  rw [spanSingleton_primePowerGenerator (K := K) S v]
  split_ifs with hwv
  · subst w
    simpa using
      FractionalIdeal.count_pow_self K
        (v : HeightOneSpectrum (𝓞 K))
        (NumberField.classNumber K)
  · rw [FractionalIdeal.count_pow]
    have hvw :
        (v : HeightOneSpectrum (𝓞 K)) ≠
          (w : HeightOneSpectrum (𝓞 K)) := by
      intro h
      exact hwv (Subtype.ext h.symm)
    rw [FractionalIdeal.count_maximal_coprime K
      (w : HeightOneSpectrum (𝓞 K)) hvw]
    simp

end PrimePowerSources

section Rank

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

private noncomputable def divisorRangeVector (v : S) :
    LinearMap.range (divisorLinearMap (K := K) S) :=
  ⟨classNumberBasisVector (K := K) S v,
    ⟨Additive.ofMul (primePowerSUnit (K := K) S v), by
      ext w
      exact divisorCoordinate_primePowerSUnit (K := K) S v w⟩⟩

private theorem divisorRangeVector_linearIndependent :
    LinearIndependent ℤ (divisorRangeVector (K := K) S) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have hv := congrArg
    (fun z : LinearMap.range (divisorLinearMap (K := K) S) =>
      ((z : S → ℤ) v)) hg
  simp [divisorRangeVector, classNumberBasisVector] at hv
  exact hv.resolve_right (NumberField.classNumber_ne_zero K)

/-- The divisor-map range on `S`-units has rank equal to the number of
places in `S`. -/
theorem finrank_divisor_range :
    Module.finrank ℤ
        (LinearMap.range (divisorLinearMap (K := K) S)) =
      S.card := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  apply le_antisymm
  · calc
      Module.finrank ℤ
          (LinearMap.range (divisorLinearMap (K := K) S)) ≤
          Module.finrank ℤ (S → ℤ) :=
        Submodule.finrank_le
          (LinearMap.range (divisorLinearMap (K := K) S))
      _ = S.card := by simp
  · simpa using
      (divisorRangeVector_linearIndependent (K := K) S).fintype_card_le_finrank

/-- The additive group of `S`-units is finitely generated over `ℤ`. -/
theorem moduleFinite :
    Module.Finite ℤ (Additive (SUnitGroup (K := K) S)) := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  have : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (divisorLinearMap (K := K) S) ?_ ?_
  · rw [Submodule.map_top]
    exact IsNoetherian.noetherian
      (LinearMap.range (divisorLinearMap (K := K) S))
  · rw [inf_of_le_right le_top,
      ← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
        (K := K) S]
    exact Submodule.fg_range
      (fromNumberFieldUnitsLinearMap (K := K) S)

/-- The kernel of the `S`-unit divisor map has the ordinary unit rank. -/
theorem finrank_divisor_ker :
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap (K := K) S)) =
      NumberField.Units.rank K := by
  calc
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap (K := K) S)) =
        Module.finrank ℤ
          (LinearMap.range
            (fromNumberFieldUnitsLinearMap (K := K) S)) :=
      (LinearEquiv.ofEq _ _
        (range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
          (K := K) S).symm).finrank_eq
    _ = Module.finrank ℤ (Additive (𝓞 K)ˣ) :=
      (LinearEquiv.ofInjective
        (fromNumberFieldUnitsLinearMap (K := K) S)
        (fromNumberFieldUnitsLinearMap_injective (K := K) S)).symm.finrank_eq
    _ = NumberField.Units.rank K :=
      NumberField.Units.finrank_eq K

/-- The free rank of the `S`-unit group is the ordinary Dirichlet rank plus
the number of finite places in `S`. -/
theorem finrank :
    Module.finrank ℤ (Additive (SUnitGroup (K := K) S)) =
      NumberField.Units.rank K + S.card := by
  let : Module.Finite ℤ
      (Additive (SUnitGroup (K := K) S)) :=
    moduleFinite (K := K) S
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let : Module.Finite ℤ
      (LinearMap.range (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap (K := K) S)))
  let : Module.Finite ℤ
      (LinearMap.ker (divisorLinearMap (K := K) S)) :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.ker (divisorLinearMap (K := K) S)))
  have hrank :
      Module.rank ℤ (Additive (SUnitGroup (K := K) S)) =
        Module.rank ℤ
            (LinearMap.range (divisorLinearMap (K := K) S)) +
          Module.rank ℤ
            (LinearMap.ker (divisorLinearMap (K := K) S)) := by
    have h :=
      LinearMap.rank_eq_of_surjective
        (f := (divisorLinearMap (K := K) S).rangeRestrict)
        (divisorLinearMap (K := K) S).surjective_rangeRestrict
    rw [LinearMap.ker_rangeRestrict] at h
    exact h
  have hcard :
      (Module.finrank ℤ
          (Additive (SUnitGroup (K := K) S)) : Cardinal) =
        (Module.finrank ℤ
            (LinearMap.range (divisorLinearMap (K := K) S)) : Cardinal) +
          (Module.finrank ℤ
            (LinearMap.ker (divisorLinearMap (K := K) S)) : Cardinal) := by
    rw [Module.finrank_eq_rank, Module.finrank_eq_rank,
      (LinearMap.ker (divisorLinearMap (K := K) S)).finrank_eq_rank]
    exact hrank
  rw [← Nat.cast_inj (R := Cardinal), Nat.cast_add]
  calc
    (Module.finrank ℤ
        (Additive (SUnitGroup (K := K) S)) : Cardinal) =
      (Module.finrank ℤ
          (LinearMap.range (divisorLinearMap (K := K) S)) : Cardinal) +
        (Module.finrank ℤ
          (LinearMap.ker (divisorLinearMap (K := K) S)) : Cardinal) :=
      hcard
    _ = (S.card : Cardinal) +
        (NumberField.Units.rank K : Cardinal) := by
      rw [finrank_divisor_range (K := K) S,
        finrank_divisor_ker (K := K) S]
    _ = (NumberField.Units.rank K : Cardinal) +
        (S.card : Cardinal) := by rw [add_comm]

/-- The `S`-unit rank in quotient-by-torsion form. -/
theorem finrank_modTorsion :
    Module.finrank ℤ
        (Additive
          (SUnitGroup (K := K) S ⧸
            CommGroup.torsion (SUnitGroup (K := K) S))) =
      NumberField.Units.rank K + S.card := by
  calc
    Module.finrank ℤ
        (Additive
          (SUnitGroup (K := K) S ⧸
            CommGroup.torsion (SUnitGroup (K := K) S))) =
        Module.finrank ℤ (Additive (SUnitGroup (K := K) S)) := by
      simpa using!
        (finrank_quotient_torsion_eq
          (M := Additive (SUnitGroup (K := K) S)))
    _ = NumberField.Units.rank K + S.card :=
      finrank (K := K) S

/-- Cardinality form of the `S`-unit rank:
`#S_infinite + #S_finite - 1`. -/
theorem finrank_modTorsion_eq_card_infinitePlaces_add_card_sub_one :
    Module.finrank ℤ
        (Additive
          (SUnitGroup (K := K) S ⧸
            CommGroup.torsion (SUnitGroup (K := K) S))) =
      Fintype.card (NumberField.InfinitePlace K) + S.card - 1 := by
  rw [finrank_modTorsion (K := K) S, NumberField.Units.rank]
  have hpos :
      0 < Fintype.card (NumberField.InfinitePlace K) :=
    Fintype.card_pos
  omega

end Rank

end SUnitGroup
