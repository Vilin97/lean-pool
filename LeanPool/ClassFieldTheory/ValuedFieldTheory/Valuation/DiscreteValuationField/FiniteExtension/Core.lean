/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
/-! Provides the public declarations in the
  `ValuationTheory.DiscreteValuationField.FiniteExtension` Lean module. -/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv →
    integralClosureValuationSubringOfMemOrInv

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_hasExtension →
    integralClosureValuationSubringOfMemOrInv_hasExtension

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_isIntegralClosure →
    integralClosureValuationSubringOfMemOrInv_isIntegralClosure

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_pullback →
    integralClosureValuationSubringOfMemOrInv_pullback

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosure_mem_valuationSubring_of_hasExtension →
    integralClosure_mem_valuationSubring_of_hasExtension

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal →
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_mem_integralClosure_of_isIntegral →
    valuationSubring_mem_integralClosure_of_isIntegral

open _root_.ValuationTheory.DiscreteValuationField renaming
  henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete →
    henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete


namespace ValuationTheory

noncomputable
section

universe u v w x y

namespace DiscreteValuationField

namespace ValuedExtension.Henselian

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
variable [base.toDVF.valuation.HasExtension target.toDVF.valuation]

/-- The canonical integer map from a Henselian base valuation ring to the
valuation subring constructed from the actual integral closure. -/
def integralClosureValuationSubringIntegerMapOfMemOrInv
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    base.valuationSubring →+*
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.toDVF.valuation hval where
  toFun a :=
    ⟨algebraMap K L (a : K),
      (integralClosureValuationSubringOfMemOrInv_pullback
        (L := L) base.toDVF.valuation hval (a : K)).2 a.2⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intro a b; ext; simp
  map_mul' := by intro a b; ext; simp

omit [FiniteDimensional K L] in
/-- The integer map into the integral-closure valuation ring is the ambient algebra map. -/
@[simp] theorem integralClosureValuationSubringIntegerMapOfMemOrInv_apply
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (a : base.valuationSubring) :
    ((integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval a :
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval) : L) =
      algebraMap K L (a : K) :=
  rfl

omit [FiniteDimensional K L] in
/-- The canonical integer map into the valuation subring built from the actual
integral closure is injective. -/
theorem integralClosureValuationSubringIntegerMapOfMemOrInv_injective
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    Function.Injective
      (integralClosureValuationSubringIntegerMapOfMemOrInv
        (K := K) (L := L) base hval) := by
  intro a b hab
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  simpa using
    congrArg
      (fun x :
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval => (x : L)) hab

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- The center of an extension valuation ring on the constructed actual
integral-closure valuation subring contracts to the base maximal ideal. -/
theorem idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (base : HenselianDVF.{u, v} K) (vL : _root_.Valuation L ΓL)
    [base.toDVF.valuation.HasExtension vL]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.toDVF.valuation hval
    let hvL_le : B ≤ vL.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.toDVF.valuation vL hval
    (ValuationSubring.idealOfLE B vL.valuationSubring hvL_le).comap
        (integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval) =
      base.maximalIdeal := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let hvL_le : B ≤ vL.valuationSubring :=
    integralClosureValuationSubring_le_of_hasExtension
      (L := L) base.toDVF.valuation vL hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  apply Ideal.ext
  intro a
  rw [Ideal.mem_comap]
  change B.inclusion vL.valuationSubring hvL_le (i a) ∈
      IsLocalRing.maximalIdeal vL.valuationSubring ↔
    a ∈ IsLocalRing.maximalIdeal base.toDVF.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff (v := vL)]
  rw [Valuation.mem_maximalIdeal_iff (v := base.toDVF.valuation)]
  have hcoe :
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) =
        algebraMap K L (a : K) := by
    rfl
  rw [hcoe]
  exact Valuation.HasExtension.val_map_lt_one_iff base.toDVF.valuation vL (a : K)

/-- In a finite separable extension, once the actual integral closure has the
valuation-ring dichotomy, the constructed integral-closure valuation ring has a
unique prime over the base maximal ideal. -/
theorem prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    (base : HenselianDVF.{u, v} K)
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (P :
      Ideal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval))
    (hP : P.IsPrime)
    (hcomap :
      P.comap
          (integralClosureValuationSubringIntegerMapOfMemOrInv
            (K := K) (L := L) base hval) =
        base.maximalIdeal) :
    P =
      IsLocalRing.maximalIdeal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval) := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  let : base.toDVF.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.toDVF.valuation hval
  let : IsFractionRing base.valuationSubring K :=
    base.toDVF.valuationSubring_isFractionRing
  let : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsDedekindDomain base.valuationSubring := inferInstance
  let : Algebra base.valuationSubring B := RingHom.toAlgebra i
  let : IsScalarTower base.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      rfl)
  let : IsIntegralClosure B base.valuationSubring L :=
    integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.toDVF.valuation hval
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain base.valuationSubring K L B
  have hi : Function.Injective i :=
    integralClosureValuationSubringIntegerMapOfMemOrInv_injective
      (K := K) (L := L) base hval
  have hP_ne_bot : P ≠ ⊥ := by
    have hnot_le_bot : ¬ base.maximalIdeal ≤ ⊥ := by
      intro hle
      exact base.maximalIdeal_ne_bot (le_antisymm hle bot_le)
    obtain ⟨a, ha_max, ha_not_bot⟩ := Set.not_subset.mp hnot_le_bot
    have ha_ne_zero : a ≠ 0 := by
      intro ha
      exact ha_not_bot (by simp [ha])
    intro hPbot
    have ha_comap : a ∈ P.comap i := by
      simpa [B, i, hcomap] using ha_max
    have hai_mem : i a ∈ P := by
      simpa [Ideal.mem_comap] using ha_comap
    have hai_zero : i a = 0 := by
      simpa [hPbot] using hai_mem
    exact ha_ne_zero (hi (by simpa using hai_zero))
  exact IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_ne_bot)

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Center-equality form of Henselian-DVF valuation uniqueness after the actual
integral closure has been turned into a valuation subring. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenter :
      ValuationSubring.idealOfLE
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval)
        target.toDVF.valuation.valuationSubring
        (integralClosureValuationSubring_le_of_hasExtension
          (L := L) base.toDVF.valuation target.toDVF.valuation hval) =
        IsLocalRing.maximalIdeal
          (integralClosureValuationSubringOfMemOrInv
            (L := L) base.toDVF.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (integralClosureValuationSubringOfMemOrInv
              (L := L) base.toDVF.valuation hval)
            v'.valuationSubring
            (integralClosureValuationSubring_le_of_hasExtension
              (L := L) base.toDVF.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (integralClosureValuationSubringOfMemOrInv
                (L := L) base.toDVF.valuation hval)) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  have htarget_le : B ≤ target.toDVF.valuation.valuationSubring :=
    integralClosureValuationSubring_le_of_hasExtension
      (L := L) base.toDVF.valuation target.toDVF.valuation hval
  have htarget_eq : target.toDVF.valuation.valuationSubring = B :=
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B target.toDVF.valuation.valuationSubring htarget_le
      (by simpa [B, htarget_le] using htargetCenter)
  intro Gamma' _ v' hExt
  let : base.toDVF.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    integralClosureValuationSubring_le_of_hasExtension
      (L := L) base.toDVF.valuation v' hval
  have hv_eq : v'.valuationSubring = B :=
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hcenter Gamma' inferInstance v' hExt))
  have hSubring : target.toDVF.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact HenselianDVF.valuation_isEquiv_of_valuationSubring_eq base target v' hSubring

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Prime-uniqueness form of Henselian-DVF valuation uniqueness. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (hunique :
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)
  · let htarget_le : B ≤ target.toDVF.valuation.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.toDVF.valuation target.toDVF.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.toDVF.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        simpa [B, htarget_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base target.toDVF.valuation hval)
  · intro Gamma' _ v' hExt
    let : base.toDVF.valuation.HasExtension v' := hExt
    let hv_le : B ≤ v'.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.toDVF.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        simpa [B, hv_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base v' hval)

/-- Finite-separable Henselian-DVF uniqueness once the actual integral closure
has the valuative dichotomy. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal
    base target)
    hval
    (by
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      change ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B
      intro P hP hcomap
      exact
        prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
          (K := K) (L := L) (base := base) hval P hP hcomap)

/-- Finite-separable Henselian-DVF uniqueness once the actual integral closure
is local. -/
theorem hasUniqueValuationExtension_of_integralClosure_isLocalRing
    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_isLocalRing base target)

/-- Finite-separable Henselian-DVF uniqueness once the residue fiber over the
base maximal ideal has at most one prime. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
    [Algebra.IsSeparable K L]
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

/-- Finite-separable Henselian-DVF uniqueness from idempotent lifting in the
residue fiber over the base maximal ideal. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_idempotents_lift
    [Algebra.IsSeparable K L]
    (hlift :
      ∀ e : base.maximalIdeal.Fiber (integralClosureIntegers base target),
        IsIdempotentElem e →
          ∃ b : (integralClosureIntegers base target),
            IsIdempotentElem b ∧
              Algebra.TensorProduct.includeRight b = e) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_idempotents_lift base target) hlift
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

/-- Finite-separable Henselian-DVF uniqueness from the Henselian-kernel
idempotent-lifting criterion for the residue-fiber `includeRight` map. -/
theorem IntegralClosureFiber.unique_of_includeRight_surjective_henselianRing_ker
    [Algebra.IsSeparable K L]
    (hsurj :
      Function.Surjective
        (Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_includeRight_surjective_henselianRing_ker base target)
      hsurj
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

/-- Finite-separable Henselian-DVF uniqueness from the Henselian-kernel
criterion for the residue-fiber `includeRight` map.  Surjectivity of
`includeRight` is supplied by the local base valuation ring. -/
theorem
  hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_includeRight_henselianRing_ker
    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_includeRight_henselianRing_ker base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

omit [base.toDVF.valuation.HasExtension target.toDVF.valuation] in
/-- If the base Henselian-DVF valuation ring is actually complete for its
maximal-ideal topology, then the actual integral closure is Henselian along the
ideal generated by the base maximal ideal. -/
theorem integralClosure_base_maximal_map_henselianRing_of_isAdicComplete
    [Algebra.IsSeparable K L]
    [IsAdicComplete base.maximalIdeal base.valuationSubring] :
    HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) := by
  let : IsNoetherianRing base.valuationSubring :=
    base.toDVF.valuationSubring_isNoetherianRing
  let : Module.Finite base.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  exact
    henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
      (R := base.valuationSubring) (S := (integralClosureIntegers base target))
      (I := base.maximalIdeal)

omit [base.toDVF.valuation.HasExtension target.toDVF.valuation] in
/-- If the base Henselian-DVF valuation ring is precomplete for its
maximal-ideal topology, then the actual integral closure is Henselian along the
ideal generated by the base maximal ideal.

The separatedness needed upstairs is derived from the Henselian Jacobson
condition and finite generation, so this does not assume base adic
completeness. -/
theorem integralClosure_base_maximal_map_henselianRing_of_base_isPrecomplete
    [Algebra.IsSeparable K L]
    [IsPrecomplete base.maximalIdeal base.valuationSubring] :
    HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) := by
  let : IsNoetherianRing base.valuationSubring :=
    base.toDVF.valuationSubring_isNoetherianRing
  let : Module.Finite base.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  have hHausR : IsHausdorff base.maximalIdeal base.valuationSubring :=
    IsHausdorff.of_le_jacobson
      (I := base.maximalIdeal) (M := base.valuationSubring)
      (show base.maximalIdeal ≤ Ideal.jacobson (⊥ : Ideal base.valuationSubring) from
        HenselianRing.jac)
  have hCompleteR : IsAdicComplete base.maximalIdeal base.valuationSubring :=
    { toIsHausdorff := hHausR
      toIsPrecomplete := inferInstance }
  let : IsAdicComplete base.maximalIdeal base.valuationSubring := hCompleteR
  exact
    henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
      (R := base.valuationSubring) (S := (integralClosureIntegers base target))
      (I := base.maximalIdeal)

omit [base.toDVF.valuation.HasExtension target.toDVF.valuation] in
/-- The actual integral closure is Henselian once finite-algebra transfer is
available over the base valuation ring.

This is the CFT-facing specialization of the finite-algebra transfer frontier:
the actual integral closure is module-finite over the Henselian base valuation
ring in a finite separable extension, so the monogenic `AdjoinRoot` transfer
route constructed in `Henselian.lean` gives the natural Henselian pair upstairs.
-/
theorem integralClosure_base_maximal_map_henselianRing_of_finiteTransfer
    [Algebra.IsSeparable K L]
    (hTransfer :
      ∀ {T : Type w} [CommRing T] [Algebra base.valuationSubring T]
        [Module.Finite base.valuationSubring T],
          HenselianRing T
            (base.maximalIdeal.map
              (algebraMap base.valuationSubring T))) :
    HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) := by
  let : Module.Finite base.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  change HenselianRing (integralClosure base.valuationSubring L)
    (base.maximalIdeal.map
      (algebraMap base.valuationSubring (integralClosure base.valuationSubring L)))
  exact hTransfer (T := (integralClosure base.valuationSubring L : Type w))

/-- Finite-separable Henselian-DVF uniqueness from the natural Henselian-pair
ideal in the actual integral closure. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target)))] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

/-- Finite-separable Henselian-DVF uniqueness for bases that are complete for
the maximal-ideal topology.  This is the actual-integral-closure specialization
of finite-algebra transfer in the complete-base case. -/
theorem hasUniqueValuationExtension_of_finite_separable_of_base_isAdicComplete
    [Algebra.IsSeparable K L]
    [IsAdicComplete base.maximalIdeal base.valuationSubring] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing_of_isAdicComplete base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

/-- Finite-separable Henselian-DVF uniqueness for bases whose valuation ring is
precomplete for the maximal-ideal topology.  This is the CFT-facing
specialization of finite-algebra transfer with separatedness derived from the
Henselian Jacobson condition. -/
theorem hasUniqueValuationExtension_of_finite_separable_of_base_isPrecomplete
    [Algebra.IsSeparable K L]
    [IsPrecomplete base.maximalIdeal base.valuationSubring] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing_of_base_isPrecomplete base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

/-- Finite-separable Henselian-DVF valuation uniqueness once finite-algebra
Henselian transfer is available over the base valuation ring.

This is the downstream CFT specialization of the current finite-algebra
frontier: finite transfer gives the Henselian pair on the actual integral
closure, and the existing residue-fiber/localness argument then gives
uniqueness of the extended valuation. -/
theorem hasUniqueValuationExtension_of_finite_separable_of_finiteTransfer
    [Algebra.IsSeparable K L]
    (hTransfer :
      ∀ {T : Type w} [CommRing T] [Algebra base.valuationSubring T]
        [Module.Finite base.valuationSubring T],
          HenselianRing T
            (base.maximalIdeal.map
              (algebraMap base.valuationSubring T))) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing_of_finiteTransfer base target)
      hTransfer
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
      (K := K) (L := L) (base := base) (target := target)  :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)

end ValuedExtension.Henselian

namespace HenselianDVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Target-free finite-separable valuation-subring uniqueness, reduced to the
remaining Henselian integrality frontier.

Once every valuation subring extending the base valuation is integral over the
base valuation ring, any two such valuation subrings coincide.  This is the
`B C : ValuationSubring L` form needed by the absolute route, without
packaging either side as a target `HenselianDVF`. -/
theorem valuationSubring_eq_of_finite_separable_of_forall_isIntegral
    (base : HenselianDVF.{u, v} K)
    (hintegral :
      ∀ (B : ValuationSubring L)
        [_root_.Valuation.HasExtension base.valuation B.valuation],
          Algebra.IsIntegral base.valuation.valuationSubring
            B.valuation.valuationSubring)
    (B C : ValuationSubring L)
    [_root_.Valuation.HasExtension base.valuation B.valuation]
    [_root_.Valuation.HasExtension base.valuation C.valuation] :
    B = C := by
  have hBInt : Algebra.IsIntegral base.valuation.valuationSubring
      B.valuation.valuationSubring :=
    hintegral B
  have hCInt : Algebra.IsIntegral base.valuation.valuationSubring
      C.valuation.valuationSubring :=
    hintegral C
  have hsub : B.valuation.valuationSubring = C.valuation.valuationSubring := by
    ext z
    constructor
    · intro hz
      have hz_int : z ∈ integralClosure base.valuation.valuationSubring L :=
        valuationSubring_mem_integralClosure_of_isIntegral
          (L := L) base.valuation B.valuation ⟨z, hz⟩
      exact
        integralClosure_mem_valuationSubring_of_hasExtension
          (L := L) base.valuation C.valuation ⟨z, hz_int⟩
    · intro hz
      have hz_int : z ∈ integralClosure base.valuation.valuationSubring L :=
        valuationSubring_mem_integralClosure_of_isIntegral
          (L := L) base.valuation C.valuation ⟨z, hz⟩
      exact
        integralClosure_mem_valuationSubring_of_hasExtension
          (L := L) base.valuation B.valuation ⟨z, hz_int⟩
  simpa [ValuationSubring.valuationSubring_valuation] using hsub

/-- Target-free finite-separable valuation-subring uniqueness from finite
valuation-ring extensions.

This is the module-finite form of
`valuationSubring_eq_of_finite_separable_of_forall_isIntegral`; finite
valuation-ring extensions are converted to integral extensions before applying
the integral uniqueness route. -/
theorem valuationSubring_eq_of_finite_separable_of_forall_moduleFinite
    (base : HenselianDVF.{u, v} K)
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hfinite :
      ∀ (B : ValuationSubring L)
        [_root_.Valuation.HasExtension base.valuation B.valuation],
          Module.Finite base.valuation.valuationSubring
            B.valuation.valuationSubring)
    (B C : ValuationSubring L)
    [_root_.Valuation.HasExtension base.valuation B.valuation]
    [_root_.Valuation.HasExtension base.valuation C.valuation] :
    B = C :=
  valuationSubring_eq_of_finite_separable_of_forall_isIntegral
    (base := base)
    (hintegral := by
      intro D _
      let : Module.Finite base.valuation.valuationSubring
          D.valuation.valuationSubring :=
        hfinite D
      infer_instance)
    (B := B) (C := C)

/-- In a finite separable extension, the target-free uniqueness theorem
identifies every extension valuation subring with the valuation subring
constructed from the actual integral closure.

The remaining upstream input is explicit: every valuation subring extending
the base valuation must be integral over the base valuation ring, and the
actual integral closure must satisfy the valuation-ring dichotomy. -/
theorem valuationSubring_eq_integralClosureValuationSubring_of_finite_separable
    (base : HenselianDVF.{u, v} K)
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuation.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuation.valuationSubring L).toSubring)
    (hintegral :
      ∀ (B : ValuationSubring L)
        [_root_.Valuation.HasExtension base.valuation B.valuation],
          Algebra.IsIntegral base.valuation.valuationSubring
            B.valuation.valuationSubring)
    (B : ValuationSubring L)
    [_root_.Valuation.HasExtension base.valuation B.valuation] :
    B =
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval := by
  let C :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let : _root_.Valuation.HasExtension base.valuation C.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.valuation hval
  exact
    valuationSubring_eq_of_finite_separable_of_forall_isIntegral
      (base := base) (hintegral := hintegral) (B := B) (C := C)

/-- Elementwise form of
`valuationSubring_eq_of_finite_separable_of_forall_isIntegral`. -/
theorem mem_valuationSubring_iff_of_finite_separable_of_forall_isIntegral
    (base : HenselianDVF.{u, v} K)
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hintegral :
      ∀ (B : ValuationSubring L)
        [_root_.Valuation.HasExtension base.valuation B.valuation],
          Algebra.IsIntegral base.valuation.valuationSubring
            B.valuation.valuationSubring)
    (B C : ValuationSubring L)
    [_root_.Valuation.HasExtension base.valuation B.valuation]
    [_root_.Valuation.HasExtension base.valuation C.valuation]
    (z : L) :
    z ∈ B ↔ z ∈ C := by
  rw [valuationSubring_eq_of_finite_separable_of_forall_isIntegral
    (base := base) (hintegral := hintegral) (B := B) (C := C)]

/-- Elementwise form of
`valuationSubring_eq_of_finite_separable_of_forall_moduleFinite`. -/
theorem mem_valuationSubring_iff_of_finite_separable_of_forall_moduleFinite
    (base : HenselianDVF.{u, v} K)
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hfinite :
      ∀ (B : ValuationSubring L)
        [_root_.Valuation.HasExtension base.valuation B.valuation],
          Module.Finite base.valuation.valuationSubring
            B.valuation.valuationSubring)
    (B C : ValuationSubring L)
    [_root_.Valuation.HasExtension base.valuation B.valuation]
    [_root_.Valuation.HasExtension base.valuation C.valuation]
    (z : L) :
    z ∈ B ↔ z ∈ C := by
  rw [valuationSubring_eq_of_finite_separable_of_forall_moduleFinite
    (base := base) (hfinite := hfinite) (B := B) (C := C)]

end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
