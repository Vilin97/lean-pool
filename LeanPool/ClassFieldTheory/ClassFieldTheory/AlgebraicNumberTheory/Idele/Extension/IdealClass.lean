/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
/-!
# Extension of ideles and ideal classes

For a finite Galois extension of number fields, scalar extension of the
relative adele algebra followed by the relative-to-ordinary comparison
gives the usual extension map on ideles.  This file descends that map to
idele classes and compares it with extension of fractional ideals and
ideal classes.
-/

@[expose] public section

open scoped NumberField TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable
section

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- On a base-field local unit, the finite relative-to-ordinary
comparison is the canonical map to the chosen place above it. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_localIdeleInclusion
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : (w.adicCompletion K)ˣ) :
    finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w
        (localIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (finitePlaceAdicCompletionMap K L w W).toMonoidHom
        x := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension]
  apply Units.ext
  simp only [Units.coe_map, Units.coe_mapEquiv,
    finitePlaceLocalTensorDecompositionUnitsComponent_coe,
    localIdeleInclusion]
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w a
          ((x : w.adicCompletion K) ⊗ₜ[K] 1)) =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)
        (x : w.adicCompletion K)
  rw [finitePlaceLocalTensorDecompositionComponent_tmul]
  simp only [map_one, mul_one]
  exact
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
      K L w a (x : w.adicCompletion K)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Local orders under the canonical completion map are multiplied by
the ramification index. -/
theorem localOrder_finitePlaceAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : (w.adicCompletion K)ˣ) :
    (FiniteIdeleGroup.localOrder W.1
      (Units.map
        (finitePlaceAdicCompletionMap K L w W).toMonoidHom
        x)).toAdd =
      (w.asIdeal.ramificationIdx' W.1.asIdeal : ℤ) *
        (FiniteIdeleGroup.localOrder w x).toAdd := by
  rw [FiniteIdeleGroup.localOrder_apply,
    FiniteIdeleGroup.localOrder_apply]
  simp only [Units.coe_map]
  change
    -WithZero.log
        (Valued.v
          (finitePlaceAdicCompletionMap K L w W
            (x : w.adicCompletion K))) =
      (w.asIdeal.ramificationIdx' W.1.asIdeal : ℤ) *
        -WithZero.log (Valued.v (x : w.adicCompletion K))
  rw [finitePlaceAdicCompletionMap_valued, WithZero.log_pow]
  simp

namespace FractionalIdealGroup

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension of nonzero fractional ideals along the inclusion of number
fields. -/
noncomputable def extension :
    FractionalIdealGroup K →* FractionalIdealGroup L :=
  Units.map
    (FractionalIdeal.extendedHom L (𝓞 L)).toMonoidHom

omit [FiniteDimensional K L] [IsGalois K L] in
/-- On a prime fractional ideal, extension is the fractional ideal
associated with the mapped integral ideal. -/
theorem extension_prime_val
    (w : HeightOneSpectrum (𝓞 K)) :
    ((extension K L (prime w) : FractionalIdealGroup L) :
      FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      (w.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
  change FractionalIdeal.extendedHom L (𝓞 L)
      (w.asIdeal :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  exact
    FractionalIdeal.extendedHom_coeIdeal_eq_map
      L (𝓞 L) w.asIdeal

omit [FiniteDimensional K L] [IsGalois K L] in
/-- At a place above `w`, the exponent of the extended prime is the
ramification index. -/
theorem count_extension_prime
    (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : _root_.finitePlaceBelow (K := K) W = w) :
    FractionalIdeal.count L W
      ((extension K L (prime w) : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      (w.asIdeal.ramificationIdx' W.asIdeal : ℤ) := by
  let : W.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal hW.symm
  have hmap :
      w.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot w.ne_bot
  rw [extension_prime_val,
    FractionalIdeal.count_coe L W hmap,
    Ideal.count_associates_factors_eq
      hmap W.isPrime W.ne_bot]
  norm_cast
  rw [←
    Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      w.asIdeal W.asIdeal hmap]
  exact
    (Ideal.ramificationIdx'_eq_ramificationIdx
      w.asIdeal W.asIdeal w.ne_bot).symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A prime below a different place has zero exponent after extension. -/
theorem count_extension_prime_ne
    (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L))
    (hW : _root_.finitePlaceBelow (K := K) W ≠ w) :
    FractionalIdeal.count L W
      ((extension K L (prime w) : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0 := by
  have hmap :
      w.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot w.ne_bot
  rw [extension_prime_val,
    FractionalIdeal.count_coe L W hmap,
    Ideal.count_associates_factors_eq
      hmap W.isPrime W.ne_bot]
  norm_cast
  rw [Multiset.count_eq_zero]
  intro hmem
  have hprimes :
      W.asIdeal ∈ w.asIdeal.primesOver (𝓞 L) :=
    (Ideal.mem_primesOver_iff_mem_normalizedFactors
      (𝓞 L) w.ne_bot).2 hmem
  apply hW
  apply HeightOneSpectrum.ext
  rw [_root_.finitePlaceBelow_asIdeal]
  exact hprimes.2.over.symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The exponent formula for extension of a fractional ideal presented
by its prime factorization. -/
theorem count_extension_factorization
    (exps : Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (W : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L W
      ((extension K L
          (factorization exps) : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        exps.toAdd
          (_root_.finitePlaceBelow (K := K) W) := by
  classical
  change FractionalIdeal.count L W
      (((extension K L)
        (exps.toAdd.prod fun v n =>
          primePowerHom v (Multiplicative.ofAdd n)) :
          FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = _
  rw [Finsupp.prod, map_prod]
  simp only [primePowerHom, MonoidHom.mk'_apply,
    toAdd_ofAdd, map_zpow]
  have hcoe :
      (((∏ v ∈ exps.toAdd.support,
          extension K L (prime v) ^ exps.toAdd v) :
            FractionalIdealGroup L) :
          FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
        ∏ v ∈ exps.toAdd.support,
          (((extension K L (prime v) :
            FractionalIdealGroup L) :
              FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^
            exps.toAdd v) := by
    simp
  rw [hcoe, FractionalIdeal.count_prod]
  · simp only [FractionalIdeal.count_zpow]
    by_cases hbelow :
        _root_.finitePlaceBelow
          (K := K) W ∈ exps.toAdd.support
    · rw [Finset.sum_eq_single
          (_root_.finitePlaceBelow (K := K) W)]
      · rw [count_extension_prime K L
          (_root_.finitePlaceBelow (K := K) W) W rfl]
        ring
      · intro v hv hne
        rw [count_extension_prime_ne K L v W]
        · simp
        · exact Ne.symm hne
      · exact fun h => (h hbelow).elim
    · have hzero :
          exps.toAdd
            (_root_.finitePlaceBelow (K := K) W) = 0 :=
        Finsupp.notMem_support_iff.mp hbelow
      rw [hzero, mul_zero]
      apply Finset.sum_eq_zero
      intro v hv
      rw [count_extension_prime_ne K L v W]
      · simp
      · intro h
        apply hbelow
        simpa [h] using hv
  · intro v hv
    exact zpow_ne_zero _ (Units.ne_zero
      (extension K L (prime v)))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension multiplies the exponent at `W` by the ramification index
over the place below `W`. -/
theorem count_extension
    (I : FractionalIdealGroup K)
    (W : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L W
      ((extension K L I : FractionalIdealGroup L) :
        FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        FractionalIdeal.count K
          (_root_.finitePlaceBelow (K := K) W)
          (I : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) := by
  obtain ⟨exps, rfl⟩ :=
    factorization_surjective (K := K) I
  rw [count_extension_factorization,
    count_factorization]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension of a prime fractional ideal commutes with passage to the
ideal class group. -/
theorem classGroup_mk_extension_prime
    (w : HeightOneSpectrum (𝓞 K)) :
    ClassGroup.mk L (extension K L (prime w)) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mk K (prime w)) := by
  let w₀ : (Ideal (𝓞 K))⁰ :=
    ⟨w.asIdeal,
      mem_nonZeroDivisors_iff_ne_zero.mpr w.ne_bot⟩
  have hw :
      prime w = FractionalIdeal.mk0 K w₀ := by
    apply Units.ext
    rfl
  rw [hw, ClassGroup.mk_mk0,
    ClassGroup.extendedHom_mk0]
  rw [← ClassGroup.mk_mk0 L
    (ClassGroup.extendedIdeal (𝓞 K) (𝓞 L) w₀)]
  apply congrArg (ClassGroup.mk L)
  apply Units.ext
  exact extension_prime_val K L w

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension of arbitrary fractional ideals commutes with passage to
the ideal class group. -/
@[simp]
theorem classGroup_mk_extension
    (I : FractionalIdealGroup K) :
    ClassGroup.mk L (extension K L I) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mk K I) := by
  obtain ⟨exps, rfl⟩ :=
    factorization_surjective (K := K) I
  change
    ((ClassGroup.mk L).comp (extension K L))
        (factorization exps) =
      ((ClassGroup.extendedHom (𝓞 K) (𝓞 L)).comp
        (ClassGroup.mk K)) (factorization exps)
  rw [factorization, MonoidHom.mk'_apply, Finsupp.prod]
  simp only [map_prod, primePowerHom, MonoidHom.mk'_apply,
    toAdd_ofAdd, MonoidHom.comp_apply, map_zpow,
    classGroup_mk_extension_prime]

end FractionalIdealGroup

namespace ClassGroup

section ExtensionPrincipality

variable
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    [IsDedekindDomain A] [IsDedekindDomain B]

/-- If extension of ideal classes is trivial, then the extension of
each integral ideal is principal. -/
theorem ideal_map_isPrincipal_of_extendedHom_eq_one
    (h : extendedHom A B = 1)
    (I : Ideal A) :
    (I.map (algebraMap A B)).IsPrincipal := by
  by_cases hI : I = ⊥
  · subst I
    refine ⟨0, ?_⟩
    simp
  · let I₀ : (Ideal A)⁰ :=
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
    have hclass :=
      DFunLike.congr_fun h (mk0 I₀)
    rw [extendedHom_mk0] at hclass
    simp only [MonoidHom.one_apply] at hclass
    have hprincipal :=
      (mk0_eq_one_iff
        (extendedIdeal A B I₀).2).mp hclass
    simpa [extendedIdeal, I₀] using hprincipal

/-- Triviality of the class-group extension map is exactly the
principalization of every integral ideal. -/
theorem extendedHom_eq_one_iff_forall_ideal_map_isPrincipal :
    extendedHom A B = 1 ↔
      ∀ I : Ideal A,
        (I.map (algebraMap A B)).IsPrincipal := by
  constructor
  · intro h I
    exact ideal_map_isPrincipal_of_extendedHom_eq_one A B h I
  · exact extendedHom_eq_one_of_forall_isPrincipal A B

end ExtensionPrincipality

end ClassGroup

namespace IdeleGroup

/-- The usual extension map on ideles, constructed through the relative
tensor-product presentation. -/
noncomputable def extension :
    IdeleGroup K →* IdeleGroup L :=
  relativeIdeleBaseChangeMulEquiv.toMonoidHom.comp
    (RelativeIdeleGroup.inclusion K L)

omit [IsGalois K L] in
theorem extension_infiniteComponent
    (a : IdeleGroup K)
    (W : InfinitePlace L) :
    infiniteComponent W (extension K L a) =
      letI : Algebra.IsIntegral K L :=
        Algebra.IsIntegral.of_finite K L
      let v :=
        _root_.infinitePlaceBelow (K := K) W
      letI : W.1.LiesOver v.1 := ⟨rfl⟩
      Units.map
        (NumberField.LiesOver.completionMap
          (v := v) (w := W))
        (infiniteComponent v a) := by
  let : Algebra.IsIntegral K L :=
    Algebra.IsIntegral.of_finite K L
  let : Algebra.IsSeparable K L :=
    Algebra.IsSeparable.of_integral K L
  let v :=
    _root_.infinitePlaceBelow (K := K) W
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  apply Units.ext
  change
    (ContinuousMulEquiv.piUnits (extension K L a).1 W :
      W.Completion) = _
  change
    (ContinuousMulEquiv.piUnits
      (_root_.relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.inclusion K L a)).1 W :
      W.Completion) = _
  rw [_root_.relativeIdeleBaseChangeMulEquiv_infinite]
  let f :=
    _root_.relativeInfiniteTensorPiMulEquiv
      (K := K) (L := L)
      ((_root_.relativeIdeleToLocalData
        (K := K) (L := L)
        (RelativeIdeleGroup.inclusion K L a)).infinite)
  change
    (ContinuousMulEquiv.piUnits
      (ContinuousMulEquiv.piUnits.symm f) W :
      W.Completion) = _
  rw [ContinuousMulEquiv.piUnits.apply_symm_apply]
  dsimp only [f]
  rw [_root_.relativeInfiniteTensorPiMulEquiv_apply]
  simp only [_root_.relativeIdeleToLocalData]
  rw [RelativeIdeleGroup.infiniteComponent_inclusion]
  rw [_root_.infinitePlaceTensorUnitsEquivAbove_apply]
  simp only [Units.coe_map]
  change
    _root_.infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) v
        ((infiniteComponent v a : v.Completion) ⊗ₜ[K] (1 : L))
        ⟨W, rfl⟩ =
      NumberField.LiesOver.completionMap
        (v := v) (w := W)
        (infiniteComponent v a : v.Completion)
  simpa only [map_one, mul_one] using
    (_root_.infinitePlaceTensorRingEquivAbove_tmul
      (K := K) (L := L) v ⟨W, rfl⟩
      (infiniteComponent v a : v.Completion) (1 : L))

omit [IsGalois K L] in
/-- The finite component of an extended idele is the canonical local
completion map applied to the component below it. -/
theorem extension_finiteComponent
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 L)) :
    finiteComponent W (extension K L a) =
      Units.map
        (finitePlaceAdicCompletionMap K L
          (_root_.finitePlaceBelow (K := K) W)
          ⟨W, rfl⟩).toMonoidHom
        (finiteComponent
          (_root_.finitePlaceBelow (K := K) W) a) := by
  change (extension K L a).2 W = _
  rw [extension, MonoidHom.comp_apply]
  change
    (relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
      (RelativeIdeleGroup.inclusion K L a)).2 W = _
  rw [
    relativeIdeleBaseChangeMulEquiv_finite,
    _root_.relativeFiniteIdeleToFiniteIdele_apply,
    _root_.relativeFiniteTensorPiMulEquiv_apply]
  change
    _root_.finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L)
        (_root_.finitePlaceBelow (K := K) W)
        ((_root_.relativeIdeleToLocalData
          (K := K) (L := L)
          (RelativeIdeleGroup.inclusion K L a)).finite
            (_root_.finitePlaceBelow (K := K) W))
        ⟨W, rfl⟩ =
      _
  simp only [_root_.relativeIdeleToLocalData]
  rw [RelativeIdeleGroup.finiteComponent_inclusion,
    _root_.finitePlaceTensorUnitsEquivAboveAdic_localIdeleInclusion]

omit [IsGalois K L] in
/-- The local order of an extended idele is multiplied by the
ramification index at the chosen place above. -/
theorem extension_localOrder
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 L)) :
    (FiniteIdeleGroup.localOrder W
      (finiteComponent W (extension K L a))).toAdd =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        (FiniteIdeleGroup.localOrder
          (_root_.finitePlaceBelow (K := K) W)
          (finiteComponent
            (_root_.finitePlaceBelow (K := K) W) a)).toAdd := by
  rw [extension_finiteComponent]
  exact
    _root_.localOrder_finitePlaceAdicCompletionMap K L
      (_root_.finitePlaceBelow (K := K) W) ⟨W, rfl⟩
      (finiteComponent
        (_root_.finitePlaceBelow (K := K) W) a)

omit [IsGalois K L] in
/-- The fractional ideal attached to an extended idele is the extension
of the fractional ideal attached to the original idele. -/
theorem fractionalIdeal_extension
    (a : IdeleGroup K) :
    fractionalIdeal (extension K L a) =
      FractionalIdealGroup.extension K L
        (fractionalIdeal a) := by
  apply FractionalIdealGroup.ext_count
  intro W
  rw [FractionalIdealGroup.count_extension]
  change
    FractionalIdeal.count L W
        (((FractionalIdealGroup.factorization (K := L))
          (FiniteIdeleGroup.valuationVector
            (extension K L a).2) : FractionalIdealGroup L) :
          FractionalIdeal
            (nonZeroDivisors (𝓞 L)) L) =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        FractionalIdeal.count K
          (_root_.finitePlaceBelow (K := K) W)
          (((FractionalIdealGroup.factorization (K := K))
            (FiniteIdeleGroup.valuationVector a.2) :
              FractionalIdealGroup K) :
            FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K)
  rw [FractionalIdealGroup.count_factorization,
    FractionalIdealGroup.count_factorization]
  exact extension_localOrder K L a W

omit [IsGalois K L] in
/-- The ideal class attached to an extended idele is the extension of
the ideal class attached to the original idele. -/
theorem idealClass_extension
    (a : IdeleGroup K) :
    idealClass (extension K L a) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (idealClass a) := by
  change
    ClassGroup.mk L
        (fractionalIdeal (extension K L a)) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mk K (fractionalIdeal a))
  rw [fractionalIdeal_extension,
    FractionalIdealGroup.classGroup_mk_extension]

omit [IsGalois K L] in
/-- Extension sends the subgroup defining the ordinary ideal class
quotient into the corresponding subgroup over the extension field. -/
theorem extension_mem_ordinaryIdealClassSubgroup
    {a : IdeleGroup K}
    (ha : a ∈
      integralAtFinitePlaces (K := K) ⊔
        principalSubgroup K) :
    extension K L a ∈
      integralAtFinitePlaces (K := L) ⊔
        principalSubgroup L := by
  change a ∈ ordinaryIdealClassSubgroup at ha
  change extension K L a ∈ ordinaryIdealClassSubgroup
  rw [ordinaryIdealClassSubgroup_eq_ker,
    MonoidHom.mem_ker] at ha ⊢
  rw [idealClass_extension, ha, map_one]

omit [IsGalois K L] in
/-- Extension of a principal idele is the corresponding principal idele
of the extension field. -/
@[simp]
theorem extension_principalIdele (x : Kˣ) :
    extension K L (principalIdele K x) =
      principalIdele L
        (Units.map (algebraMap K L).toMonoidHom x) := by
  rw [extension, MonoidHom.comp_apply,
    RelativeIdeleGroup.inclusion_principalIdele]
  apply Prod.ext
  · apply Units.ext
    funext W
    change
      _root_.infinitePlaceTensorUnitsEquivAbove
          (K := K) (L := L)
          (_root_.infinitePlaceBelow (K := K) W)
          ((_root_.relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L
              (Units.map (algebraMap K L).toMonoidHom x))).infinite
              (_root_.infinitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        algebraMap L W.Completion
          (algebraMap K L (x : K))
    simp only [_root_.relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.infiniteComponent_principalIdele]
    rw [
      _root_.infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion]
    simp
  · change
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.principalIdele K L
          (Units.map (algebraMap K L).toMonoidHom x))).2 =
        (principalIdele L
          (Units.map (algebraMap K L).toMonoidHom x)).2
    rw [relativeIdeleBaseChangeMulEquiv_finite]
    apply RestrictedProduct.ext
    intro W
    rw [_root_.relativeFiniteIdeleToFiniteIdele_apply,
      _root_.relativeFiniteTensorPiMulEquiv_apply]
    change
      _root_.finitePlaceTensorUnitsEquivAboveAdic
          (K := K) (L := L)
          (_root_.finitePlaceBelow (K := K) W)
          ((_root_.relativeIdeleToLocalData
            (K := K) (L := L)
            (RelativeIdeleGroup.principalIdele K L
              (Units.map (algebraMap K L).toMonoidHom x))).finite
              (_root_.finitePlaceBelow (K := K) W))
          ⟨W, rfl⟩ =
        Units.map (FinitePlace.embedding (K := L) W)
          (Units.map (algebraMap K L).toMonoidHom x)
    simp only [_root_.relativeIdeleToLocalData]
    rw [RelativeIdeleGroup.finiteComponent_principalIdele]
    rw [
      _root_.finitePlaceTensorUnitsEquivAboveAdic_localFieldIdeleInclusion]

/-- Extension of ideles along the identity field extension is the
identity homomorphism. -/
@[simp]
theorem extension_self :
    extension K K = MonoidHom.id (IdeleGroup K) := by
  apply MonoidHom.ext
  intro a
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext W
    change
      infiniteComponent W (extension K K a) =
        infiniteComponent W a
    rw [extension_infiniteComponent]
    dsimp only
    have hmap
        (v : InfinitePlace K)
        (hv : v = W)
        [hov : W.1.LiesOver v.1] :
        Units.map
            (NumberField.LiesOver.completionMap
              (v := v) (w := W)).toMonoidHom
            (infiniteComponent v a) =
          infiniteComponent W a := by
      subst v
      apply Units.ext
      change
        NumberField.LiesOver.completionMap
            (v := W) (w := W)
            (infiniteComponent W a : W.Completion) =
          (infiniteComponent W a : W.Completion)
      exact
        _root_.infinitePlaceCompletionMap_self_apply
          (K := K) W
          (infiniteComponent W a : W.Completion)
    exact
      hmap
        (_root_.infinitePlaceBelow (K := K) W)
        (_root_.infinitePlaceBelow_self (K := K) W)
        (hov := ⟨rfl⟩)
  · apply RestrictedProduct.ext
    intro W
    change
      finiteComponent W (extension K K a) =
        finiteComponent W a
    rw [extension_finiteComponent]
    dsimp only
    have hmap
        (v : HeightOneSpectrum (𝓞 K))
        (hbelow :
          _root_.finitePlaceBelow (K := K) W = v)
        (hv : v = W) :
        Units.map
            (finitePlaceAdicCompletionMap K K v
              ⟨W, hbelow⟩).toMonoidHom
            (finiteComponent v a) =
          finiteComponent W a := by
      subst v
      apply Units.ext
      change
        finitePlaceAdicCompletionMap K K W
            ⟨W,
              _root_.finitePlaceBelow_self
                (K := K) W⟩
            (finiteComponent W a : W.adicCompletion K) =
          (finiteComponent W a : W.adicCompletion K)
      exact
        _root_.finitePlaceAdicCompletionMap_self_apply K W
          (finiteComponent W a : W.adicCompletion K)
    exact
      hmap
        (_root_.finitePlaceBelow (K := K) W)
        rfl
        (_root_.finitePlaceBelow_self (K := K) W)

/-- Extension of ideles is functorial in a tower of finite Galois
extensions. -/
theorem extension_comp
    (M : Type w)
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M] [IsGalois M L] :
    (extension M L).comp (extension K M) =
      extension K L := by
  apply MonoidHom.ext
  intro a
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext W
    change
      infiniteComponent W
          (extension M L (extension K M a)) =
        infiniteComponent W (extension K L a)
    rw [extension_infiniteComponent,
      extension_infiniteComponent]
    dsimp only
    rw [extension_infiniteComponent]
    dsimp only
    let V := _root_.infinitePlaceBelow (K := M) W
    let v := _root_.infinitePlaceBelow (K := K) W
    have hmap
        (v' : InfinitePlace K)
        (hv' : v' = v)
        [hVv : V.1.LiesOver v'.1]
        [hWV : W.1.LiesOver V.1]
        [hWv : W.1.LiesOver v.1] :
        Units.map
            (NumberField.LiesOver.completionMap
              (v := V) (w := W)).toMonoidHom
            (Units.map
              (NumberField.LiesOver.completionMap
                (v := v') (w := V)).toMonoidHom
              (infiniteComponent v' a)) =
          Units.map
            (NumberField.LiesOver.completionMap
              (v := v) (w := W)).toMonoidHom
            (infiniteComponent v a) := by
      subst v'
      apply Units.ext
      change
        NumberField.LiesOver.completionMap
            (v := V) (w := W)
            (NumberField.LiesOver.completionMap
              (v := v) (w := V)
              (infiniteComponent v a : v.Completion)) =
          NumberField.LiesOver.completionMap
            (v := v) (w := W)
            (infiniteComponent v a : v.Completion)
      exact
        _root_.infinitePlaceCompletionMap_comp_apply
          (K := K) (L := L) (M := M) W
          (infiniteComponent v a : v.Completion)
    exact
      hmap
        (_root_.infinitePlaceBelow (K := K) V)
        (_root_.infinitePlaceBelow_infinitePlaceBelow
          (K := K) (M := M) (L := L) W)
        (hVv := ⟨rfl⟩)
        (hWV := ⟨rfl⟩)
        (hWv := ⟨rfl⟩)
  · apply RestrictedProduct.ext
    intro W
    change
      finiteComponent W
          (extension M L (extension K M a)) =
        finiteComponent W (extension K L a)
    rw [extension_finiteComponent,
      extension_finiteComponent]
    dsimp only
    rw [extension_finiteComponent]
    dsimp only
    let V := _root_.finitePlaceBelow (K := M) W
    let v := _root_.finitePlaceBelow (K := K) W
    have hmap
        (v' : HeightOneSpectrum (𝓞 K))
        (hv' : v' = v)
        (hV : _root_.finitePlaceBelow (K := K) V = v')
        (hWV : _root_.finitePlaceBelow (K := M) W = V)
        (hWv : _root_.finitePlaceBelow (K := K) W = v) :
        Units.map
            (finitePlaceAdicCompletionMap M L V
              ⟨W, hWV⟩).toMonoidHom
            (Units.map
              (finitePlaceAdicCompletionMap K M v'
                ⟨V, hV⟩).toMonoidHom
              (finiteComponent v' a)) =
          Units.map
            (finitePlaceAdicCompletionMap K L v
              ⟨W, hWv⟩).toMonoidHom
            (finiteComponent v a) := by
      subst v'
      apply Units.ext
      change
        finitePlaceAdicCompletionMap M L V ⟨W, hWV⟩
            (finitePlaceAdicCompletionMap K M v ⟨V, hV⟩
              (finiteComponent v a : v.adicCompletion K)) =
          finitePlaceAdicCompletionMap K L v ⟨W, hWv⟩
            (finiteComponent v a : v.adicCompletion K)
      exact
        finitePlaceAdicCompletionMap_comp
          K L (M := M) v V W
          hV hWV hWv
          (finiteComponent v a : v.adicCompletion K)
    exact
      hmap
        (_root_.finitePlaceBelow (K := K) V)
        (_root_.finitePlaceBelow_finitePlaceBelow
          (K := K) (M := M) (L := L) W)
        rfl rfl rfl

end IdeleGroup

/-- The usual extension map on idele classes. -/
noncomputable def ideleClassExtension :
    IdeleClassGroup K →* IdeleClassGroup L :=
  QuotientGroup.map
    (IdeleGroup.principalSubgroup K)
    (IdeleGroup.principalSubgroup L)
    (IdeleGroup.extension K L)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (algebraMap K L).toMonoidHom x,
          (IdeleGroup.extension_principalIdele K L x).symm⟩)

omit [IsGalois K L] in
theorem ideleClassExtension_mk (a : IdeleGroup K) :
    ideleClassExtension K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (IdeleGroup.extension K L a) :=
  rfl

/-- Extension of idele classes along the identity field extension is
the identity homomorphism. -/
@[simp]
theorem ideleClassExtension_self :
    ideleClassExtension K K =
      MonoidHom.id (IdeleClassGroup K) := by
  apply MonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    ideleClassExtension K K
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [ideleClassExtension_mk,
    IdeleGroup.extension_self]
  rfl

/-- Extension of idele classes is functorial in a tower of finite
Galois extensions. -/
theorem ideleClassExtension_comp
    (M : Type w)
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M] [IsGalois M L] :
    (ideleClassExtension M L).comp
        (ideleClassExtension K M) =
      ideleClassExtension K L := by
  apply MonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    ideleClassExtension M L
        (ideleClassExtension K M
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      ideleClassExtension K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a)
  rw [ideleClassExtension_mk,
    ideleClassExtension_mk,
    ideleClassExtension_mk]
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (((IdeleGroup.extension M L).comp
          (IdeleGroup.extension K M)) a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (IdeleGroup.extension K L a)
  rw [IdeleGroup.extension_comp]
