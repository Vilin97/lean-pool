/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalGraded
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.CoefficientMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSupport
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedMap
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.TensorProduct.Maps
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFraction

/-!
# Coefficient base change for the spaces `P_α`

The ordinal value of a nonpositive series is determined by its support, so it is monotone under
inclusion of supports even when the two series have different coefficient fields
(`Berarducci.ordinalValue_le_of_support_subset`). A `K`-linear map `λ : E → F` between extensions
of `K`, applied coefficientwise, can only shrink the support, and preserves it when `λ` is
injective; so it does not increase the ordinal value, and preserves it when `λ` is injective.
Coefficient extension along the structure map `K → E` is the injective case, and a coordinate
functional along a `K`-basis of `E` is the general case.

Coefficient extension therefore preserves the ordinal-value degree and induces the graded ring
homomorphism `P̂ → P̂^(E)` of associated graded rings. For every field extension `E / K` the
induced map `E ⊗[K] P_α → P_α^(E)` is injective: a vanishing expansion along a `K`-basis of `E` has
vanishing coordinates, one by one. Assembling the homogeneous components gives an injective
`E`-algebra map
`E ⊗[K] P̂ → P̂^(E)`, multiplicative because the ring homomorphism `P̂ → P̂^(E)` is, so `E ⊗[K] P̂`
is a domain. This is the input to the geometric integrality of the quotient `P̂/I`.

Degrees are `NatOrdinal`, so the degree of a product is the natural sum `⊕` of the degrees, and
the finite-degree part `P̂_{<ω}` is the part supported below `ω`.
-/

universe v w w'

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

public noncomputable section

namespace Berarducci

open Berarducci

open HahnSeries.Nonpositive

variable {K : Type v} {E : Type w} [Field K] [Field E]

/-! ### Coefficientwise linear maps and the ordinal value -/

section LinearCoefficientMap

variable {F : Type w'} [Field F] [Algebra K E] [Algebra K F]

/-- Coefficientwise application of a `K`-linear map `λ : E → F` between extensions of `K`. -/
def nonpositiveLinearCoeffMap (lam : E →ₗ[K] F) :
    HahnSeries.Nonpositive ℝ E →+ HahnSeries.Nonpositive ℝ F where
  toFun u := ⟨(u : E⟦ℝ⟧).map (lam : E →+ F), by
    refine (HahnSeries.mem_nonpositiveSubring ℝ F).mpr fun x hx ↦
      HahnSeries.Nonpositive.support_subset u ?_
    rw [HahnSeries.mem_support] at hx ⊢
    intro hzero
    exact hx (show lam ((u : E⟦ℝ⟧).coeff x) = 0 by rw [hzero, map_zero])⟩
  map_zero' := Subtype.ext (HahnSeries.map_zero (lam : E →ₗ[K] F).toAddMonoidHom.toZeroHom)
  map_add' u v := Subtype.ext (HahnSeries.map_add (lam : E →ₗ[K] F).toAddMonoidHom)

@[simp]
theorem coe_nonpositiveLinearCoeffMap (lam : E →ₗ[K] F) (u : HahnSeries.Nonpositive ℝ E)
    (x : ℝ) :
    ((nonpositiveLinearCoeffMap lam u : HahnSeries.Nonpositive ℝ F) : F⟦ℝ⟧).coeff x =
      lam ((u : E⟦ℝ⟧).coeff x) :=
  (rfl)

/-- A coefficientwise linear map does not enlarge the support. -/
theorem support_nonpositiveLinearCoeffMap_subset (lam : E →ₗ[K] F)
    (u : HahnSeries.Nonpositive ℝ E) :
    ((nonpositiveLinearCoeffMap lam u : HahnSeries.Nonpositive ℝ F) : F⟦ℝ⟧).support ⊆
      (u : E⟦ℝ⟧).support := by
  intro x hx
  rw [HahnSeries.mem_support] at hx ⊢
  intro hzero
  exact hx (by rw [coe_nonpositiveLinearCoeffMap, hzero, map_zero])

/-- A coefficientwise injective linear map preserves the support. -/
theorem support_nonpositiveLinearCoeffMap_of_injective (lam : E →ₗ[K] F)
    (hlam : Function.Injective lam) (u : HahnSeries.Nonpositive ℝ E) :
    ((nonpositiveLinearCoeffMap lam u : HahnSeries.Nonpositive ℝ F) : F⟦ℝ⟧).support =
      (u : E⟦ℝ⟧).support := by
  ext x
  rw [HahnSeries.mem_support, HahnSeries.mem_support, coe_nonpositiveLinearCoeffMap]
  exact (LinearMap.map_eq_zero_iff lam hlam).not

/-- A coefficientwise `K`-linear map between extensions of `K` does not increase the ordinal
value. -/
theorem ordinalValue_nonpositiveLinearCoeffMap_le (lam : E →ₗ[K] F)
    (u : HahnSeries.Nonpositive ℝ E) :
    ordinalValue (nonpositiveLinearCoeffMap lam u) ≤ ordinalValue u :=
  ordinalValue_le_of_support_subset _ _ (support_nonpositiveLinearCoeffMap_subset lam u)

/-- A coefficientwise injective `K`-linear map between extensions of `K` preserves the ordinal
value. -/
theorem ordinalValue_nonpositiveLinearCoeffMap_of_injective (lam : E →ₗ[K] F)
    (hlam : Function.Injective lam) (u : HahnSeries.Nonpositive ℝ E) :
    ordinalValue (nonpositiveLinearCoeffMap lam u) = ordinalValue u :=
  le_antisymm (ordinalValue_nonpositiveLinearCoeffMap_le lam u)
    (ordinalValue_le_of_support_subset _ _
      (support_nonpositiveLinearCoeffMap_of_injective lam hlam u).superset)

end LinearCoefficientMap

/-- An extension field of a field of characteristic zero has characteristic zero. -/
theorem charZero_of_algebra (L : Type v) [Field L] [CharZero L] (F : Type w) [Field F]
    [Algebra L F] : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap L F).injective

/-! ### Base change of the spaces `P_α` and `P̂`

The componentwise and ring base changes are defined for any fields `K ⊆ E`: they are the component
maps of the associated graded rings along coefficient extension, which rest only on the degree
structure of `ordinalValueDegreeValuation`. Characteristic zero of `E` enters for the domain
property of `P̂^(E)`, hence for injectivity of `ε` and for `E ⊗[K] P̂` being a domain. -/

section Layer

/-- Coefficient extension preserves the ordinal-value degree exactly. -/
private theorem ordinalValueDegreeValuation_nonpositiveCoefficientMap (f : K →+* E)
    (x : HahnSeries.Nonpositive ℝ K) :
    ordinalValueDegreeValuation E (nonpositiveCoefficientMap f x) =
      ordinalValueDegreeValuation K x := by
  rw [ordinalValueDegreeValuation_apply, ordinalValueDegreeValuation_apply]
  have hov := ordinalValue_nonpositiveCoefficientMap f x
  have key : ∀ α : NatOrdinal,
      ordinalValueDegree (nonpositiveCoefficientMap f x) ≤ (α : WithBot NatOrdinal) ↔
        ordinalValueDegree x ≤ (α : WithBot NatOrdinal) := by
    intro α
    rw [ordinalValueDegree_le_coe_iff, ordinalValueDegree_le_coe_iff, hov]
  have hbot : ordinalValueDegree (nonpositiveCoefficientMap f x) = ⊥ ↔
      ordinalValueDegree x = ⊥ := by
    rw [ordinalValueDegree_eq_bot_iff, ordinalValueDegree_eq_bot_iff, ← ordinalValue_eq_zero_iff,
      ← ordinalValue_eq_zero_iff, hov]
  refine le_antisymm ?_ ?_
  · cases hxd : ordinalValueDegree x with
    | bot => rw [hbot.mpr hxd]
    | coe α => exact (key α).mpr (le_of_eq hxd)
  · cases hyd : ordinalValueDegree (nonpositiveCoefficientMap f x) with
    | bot => rw [hbot.mp hyd]
    | coe β => exact (key β).mp (le_of_eq hyd)

/-- The additive coefficient-extension map on `P_α`: the associated-graded
component map of the degree-preserving ring homomorphism `nonpositiveCoefficientMap f`. -/
def principalComponentCoefficientExtendAddHom (f : K →+* E) (alpha : NatOrdinal) :
    PrincipalComponent K alpha →+ PrincipalComponent E alpha :=
  (ordinalValueDegreeValuation K).componentMap (ordinalValueDegreeValuation E)
    (nonpositiveCoefficientMap f)
    (fun x ↦ (ordinalValueDegreeValuation_nonpositiveCoefficientMap f x).le) alpha

/-- The additive component map sends the class of a representative to the class of its image. -/
theorem principalComponentCoefficientExtendAddHom_principalComponentMk (f : K →+* E)
    (alpha : NatOrdinal) (b : HahnSeries.Nonpositive ℝ K)
    (hb : ordinalValue b < ω^ (alpha + 1)) :
    principalComponentCoefficientExtendAddHom f alpha
        (principalComponentMk alpha b hb) =
      principalComponentMk alpha (nonpositiveCoefficientMap f b)
        (by rw [ordinalValue_nonpositiveCoefficientMap]; exact hb) := by
  rw [principalComponentCoefficientExtendAddHom, principalComponentMk_eq_componentMk,
    MaxAddDegree.componentMap_componentMk, principalComponentMk_eq_componentMk]
  congr 1
  apply Subtype.ext
  rw [MaxAddDegree.coe_mapFiltrationLE]

variable (K E) in
/-- Coefficient extension on `P_α`, semilinear along the algebra map: the
associated-graded component map of coefficient extension. -/
def principalComponentCoefficientExtend [Algebra K E] (alpha : NatOrdinal) :
    PrincipalComponent K alpha →ₛₗ[algebraMap K E] PrincipalComponent E alpha where
  toFun := principalComponentCoefficientExtendAddHom (algebraMap K E) alpha
  map_add' := map_add _
  map_smul' k x := by
    obtain ⟨b, hb, rfl⟩ := exists_principalComponentMk alpha x
    rw [smul_principalComponentMk, principalComponentCoefficientExtendAddHom_principalComponentMk,
      principalComponentCoefficientExtendAddHom_principalComponentMk, smul_principalComponentMk]
    congr 1
    rw [map_mul, nonpositiveCoefficientMap_C]

variable (K E) in
/-- The scalar-extended component map `E ⊗[K] P_α →ₗ[E] P_α^(E)`. -/
def principalComponentBaseChange [Algebra K E] (alpha : NatOrdinal) :
    E ⊗[K] PrincipalComponent K alpha →ₗ[E] PrincipalComponent E alpha := by
  letI : Module K (PrincipalComponent E alpha) :=
    Module.compHom (PrincipalComponent E alpha) (algebraMap K E)
  haveI : IsScalarTower K E (PrincipalComponent E alpha) :=
    ⟨fun k e y ↦ by
      change ((k • e : E)) • y = (algebraMap K E k) • (e • y)
      rw [Algebra.smul_def, mul_smul]⟩
  exact LinearMap.liftBaseChange E
    { toFun := principalComponentCoefficientExtend K E alpha
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := fun k x ↦
        (principalComponentCoefficientExtend K E alpha).map_smul' k x }

/-- A coefficientwise basis functional picks out one summand of a basis decomposition. -/
private theorem nonpositiveLinearCoeffMap_C_mul [Algebra K E] {ι : Type*} [DecidableEq ι]
    (bE : Module.Basis ι K E) (i j : ι) (v : HahnSeries.Nonpositive ℝ K) :
    nonpositiveLinearCoeffMap (bE.coord j)
        (HahnSeries.Nonpositive.C (bE i) * nonpositiveCoefficientMap (algebraMap K E) v) =
      if i = j then v else 0 := by
  apply Subtype.ext
  ext x
  rw [coe_nonpositiveLinearCoeffMap, Subring.coe_mul, HahnSeries.Nonpositive.coe_C,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coe_nonpositiveCoefficientMap,
    smul_eq_mul, mul_comm, ← Algebra.smul_def, map_smul, Module.Basis.coord_apply,
    Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases h : i = j <;> simp [h]

/-- A finite sum stays inside a principal filtration level. -/
private theorem ordinalValue_finsetSum_lt {ι : Type*} {K' : Type*} [Field K']
    (alpha : NatOrdinal) (g : ι → HahnSeries.Nonpositive ℝ K')
    (hg : ∀ i, ordinalValue (g i) < ω^ (alpha + 1)) (t : Finset ι) :
    ordinalValue (∑ i ∈ t, g i) < ω^ (alpha + 1) := by
  classical
  induction t using Finset.induction with
  | empty =>
    rw [Finset.sum_empty,
      ordinalValue_of_mem_negativeMonomialIdeal
        (HahnSeries.Nonpositive.negativeMonomialIdeal K').zero_mem]
    exact NatOrdinal.wpow_pos _
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact lt_of_le_of_lt (ordinalValue_add_le_max _ _) (max_lt (hg i) ih)

/-- The class of a finite sum is the sum of the classes. -/
private theorem principalComponentMk_sum {ι : Type*}
    (alpha : NatOrdinal) (g : ι → HahnSeries.Nonpositive ℝ K)
    (hg : ∀ i, ordinalValue (g i) < ω^ (alpha + 1)) (t : Finset ι)
    (hsum : ordinalValue (∑ i ∈ t, g i) < ω^ (alpha + 1)) :
    principalComponentMk alpha (∑ i ∈ t, g i) hsum =
      ∑ i ∈ t, principalComponentMk alpha (g i) (hg i) := by
  simp only [principalComponentMk_eq_componentMk]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]

/-- The scalar-extended component map on a pure tensor. -/
@[simp]
theorem principalComponentBaseChange_tmul [Algebra K E]
    (alpha : NatOrdinal) (e : E)
    (x : PrincipalComponent K alpha) :
    principalComponentBaseChange K E alpha (e ⊗ₜ[K] x) =
      e • principalComponentCoefficientExtend K E alpha x :=
  (rfl)

variable (K E) in
/-- Base change on each homogeneous component is injective for every field extension `E / K`: the
coordinates of a
vanishing expansion along a `K`-basis of `E` vanish one by one. -/
theorem principalComponentBaseChange_injective [Algebra K E]
    (alpha : NatOrdinal) :
    Function.Injective (principalComponentBaseChange K E alpha) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  let bE := Module.Free.chooseBasis K E
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left bE z
  choose b hb hbx using fun i ↦ exists_principalComponentMk alpha (c i)
  have hprod : ∀ i, ordinalValue (HahnSeries.Nonpositive.C (bE i) *
      nonpositiveCoefficientMap (algebraMap K E) (b i)) < ω^ (alpha + 1) := fun i ↦ by
    simpa only [zero_add] using ordinalValue_mul_lt_wpow_add_one
      (ordinalValue_C_lt_wpow_one (bE i))
      (by rw [ordinalValue_nonpositiveCoefficientMap]; exact hb i)
  have hsum := ordinalValue_finsetSum_lt alpha _ hprod c.support
  have himg : principalComponentBaseChange K E alpha (c.sum fun i n ↦ bE i ⊗ₜ[K] n) =
      principalComponentMk alpha
        (∑ i ∈ c.support, HahnSeries.Nonpositive.C (bE i) *
          nonpositiveCoefficientMap (algebraMap K E) (b i)) hsum := by
    rw [Finsupp.sum, map_sum, principalComponentMk_sum alpha _ hprod _ hsum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hbx i, principalComponentBaseChange_tmul]
    change (bE i) • principalComponentCoefficientExtendAddHom
      (algebraMap K E) alpha _ = _
    rw [principalComponentCoefficientExtendAddHom_principalComponentMk, smul_principalComponentMk]
  rw [himg, principalComponentMk_eq_zero_iff] at hz
  have hzero : ∀ j, c j = 0 := by
    intro j
    by_cases hj : j ∈ c.support
    · rw [← hbx j, principalComponentMk_eq_zero_iff]
      refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt
        (ordinalValue_nonpositiveLinearCoeffMap_le (bE.coord j) _) hz)
      rw [map_sum]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ c.support) ↦
        nonpositiveLinearCoeffMap_C_mul bE i j (b i)]
      rw [Finset.sum_ite_eq' c.support j b, if_pos hj]
    · exact Finsupp.notMem_support_iff.mp hj
  have hc : c = 0 := Finsupp.ext hzero
  rw [hc, Finsupp.sum_zero_index]

/-! ### The graded base change `E ⊗[K] P̂ → P̂^(E)` -/

variable (E) in
/-- The semilinear component map on the class of a representative. -/
theorem principalComponentCoefficientExtend_principalComponentMk [Algebra K E]
    (alpha : NatOrdinal)
    (b : HahnSeries.Nonpositive ℝ K) (hb : ordinalValue b < ω^ (alpha + 1)) :
    principalComponentCoefficientExtend K E alpha (principalComponentMk alpha b hb) =
      principalComponentMk alpha (nonpositiveCoefficientMap (algebraMap K E) b)
        (by rw [ordinalValue_nonpositiveCoefficientMap]; exact hb) :=
  principalComponentCoefficientExtendAddHom_principalComponentMk (algebraMap K E) alpha b hb

variable (K E) in
/-- The graded base change `E ⊗[K] P̂ → P̂^(E)`, as an `E`-linear map: the direct sum of the
componentwise base changes. -/
def principalSubringBaseChangeLinear [Algebra K E] :
    E ⊗[K] PrincipalSubring K →ₗ[E] PrincipalSubring E :=
  (DirectSum.lmap fun alpha ↦ principalComponentBaseChange K E alpha).comp
    (TensorProduct.directSumRight K E E (PrincipalComponent K)).toLinearMap

/-- The graded base change on a pure tensor of a homogeneous element. -/
theorem principalSubringBaseChangeLinear_tmul_of [Algebra K E]
    (e : E) (alpha : NatOrdinal)
    (A : PrincipalComponent K alpha) :
    principalSubringBaseChangeLinear K E
        (e ⊗ₜ[K] DirectSum.of (PrincipalComponent K) alpha A) =
      e • DirectSum.of (PrincipalComponent E) alpha
        (principalComponentCoefficientExtend K E alpha A) := by
  rw [principalSubringBaseChangeLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.lof_eq_of K, TensorProduct.directSumRight_tmul_lof, DirectSum.lmap_lof,
    principalComponentBaseChange_tmul, LinearMap.map_smul, DirectSum.lof_eq_of]

variable (K E) in
/-- The graded base change is injective, because base change on each homogeneous component is. -/
theorem principalSubringBaseChangeLinear_injective [Algebra K E] :
    Function.Injective (principalSubringBaseChangeLinear K E) :=
  ((DirectSum.lmap_injective _).mpr fun alpha ↦
    principalComponentBaseChange_injective K E alpha).comp
    (TensorProduct.directSumRight K E E (PrincipalComponent K)).injective

variable (K E) in
/-- Coefficient extension `P̂ → P̂^(E)` as a graded ring homomorphism: the associated-graded map
of the degree-preserving ring homomorphism `nonpositiveCoefficientMap (algebraMap K E)`. On the
homogeneous component `P_α` it is `principalComponentCoefficientExtend K E α`. -/
def principalSubringCoefficientExtend [Algebra K E] : PrincipalSubring K →+* PrincipalSubring E :=
  (ordinalValueDegreeValuation K).associatedGradedMap (ordinalValueDegreeValuation E)
    (nonpositiveCoefficientMap (algebraMap K E))
    fun x ↦ (ordinalValueDegreeValuation_nonpositiveCoefficientMap (algebraMap K E) x).le

/-- Coefficient extension of `P̂` on a homogeneous element. -/
theorem principalSubringCoefficientExtend_of [Algebra K E]
    (alpha : NatOrdinal)
    (A : PrincipalComponent K alpha) :
    principalSubringCoefficientExtend K E (DirectSum.of (PrincipalComponent K) alpha A) =
      DirectSum.of (PrincipalComponent E) alpha (principalComponentCoefficientExtend K E alpha A) :=
  MaxAddDegree.associatedGradedMap_of _ _ _ _ alpha A

/-- The graded base change on a pure tensor: `e ⊗ A ↦ e • ε(A)`. -/
theorem principalSubringBaseChangeLinear_tmul [Algebra K E]
    (e : E) (A : PrincipalSubring K) :
    principalSubringBaseChangeLinear K E (e ⊗ₜ[K] A) =
      e • principalSubringCoefficientExtend K E A := by
  induction A using DirectSum.induction_on with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
  | of alpha A =>
      rw [principalSubringBaseChangeLinear_tmul_of,
        principalSubringCoefficientExtend_of]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, smul_add]

variable (K E) in
/-- Coefficient extension as an `E`-algebra map `E ⊗[K] P̂ → P̂^(E)`, the paper's map `ε`;
it is injective when `E` has characteristic zero (`principalSubringBaseChange_injective`). -/
def principalSubringBaseChange [Algebra K E] :
    E ⊗[K] PrincipalSubring K →ₐ[E] PrincipalSubring E :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct (principalSubringBaseChangeLinear K E)
    (fun e f A B ↦ by
      rw [principalSubringBaseChangeLinear_tmul, principalSubringBaseChangeLinear_tmul,
        principalSubringBaseChangeLinear_tmul, map_mul, smul_mul_smul_comm])
    (by rw [principalSubringBaseChangeLinear_tmul, map_one, one_smul])

theorem principalSubringBaseChange_tmul_of [Algebra K E]
    (e : E) (alpha : NatOrdinal)
    (A : PrincipalComponent K alpha) :
    principalSubringBaseChange K E
        (e ⊗ₜ[K] DirectSum.of (PrincipalComponent K) alpha A) =
      e • DirectSum.of (PrincipalComponent E) alpha
        (principalComponentCoefficientExtend K E alpha A) :=
  principalSubringBaseChangeLinear_tmul_of e alpha A

variable (K E) in
theorem principalSubringBaseChange_injective [Algebra K E] :
    Function.Injective (principalSubringBaseChange K E) :=
  principalSubringBaseChangeLinear_injective K E

variable (K E) in
/-- `E ⊗[K] P̂` is a domain, being a subring of the domain `P̂^(E)`. -/
theorem isDomain_tensor_principalSubring [Algebra K E] [CharZero E] :
    IsDomain (E ⊗[K] PrincipalSubring K) :=
  haveI : IsDomain (PrincipalSubring E) := principalSubringIsDomain
  Function.Injective.isDomain (principalSubringBaseChange K E).toRingHom
    (principalSubringBaseChange_injective K E)

end Layer

end Berarducci
