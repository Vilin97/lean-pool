/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
/-!
# The ordinary ideal class group as an idele quotient

This file proves that quotienting the idele group by the
ideles integral at every finite place and by the principal ideles gives the
ordinary ideal class group.
-/

@[expose] public section

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- The exponent of a prime in a principal fractional ideal is the additive
form of the corresponding normalized finite-place valuation. -/
theorem count_toPrincipalIdeal (x : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        ((toPrincipalIdeal (𝓞 K) K x : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      -WithZero.log (v.valuation K (x : K)) := by
  obtain ⟨⟨n, d, hd⟩, hnd⟩ :=
    IsLocalization.surj (nonZeroDivisors (𝓞 K)) (x : K)
  let d' : nonZeroDivisors (𝓞 K) := ⟨d, hd⟩
  have hx :
      (x : K) = IsLocalization.mk' K n d' :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hnd
  have hn : n ≠ 0 := by
    intro hn
    have : (x : K) = 0 := by
      rw [hx, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
    exact x.ne_zero this
  have hspan :
      (toPrincipalIdeal (𝓞 K) K x :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            ((algebraMap (𝓞 K) K) d)⁻¹ *
          (Ideal.span {n} :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [coe_toPrincipalIdeal, hx,
      FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K v
      (Units.ne_zero (toPrincipalIdeal (𝓞 K) K x)) hspan,
    hx, v.valuation_of_mk']
  rw [v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d')]
  simp [d', sub_eq_add_neg, add_comm]

/-- The fractional ideal map sends a principal idele to the corresponding
principal fractional ideal. -/
@[simp]
theorem fractionalIdeal_principalIdele (x : Kˣ) :
    fractionalIdeal (principalIdele K x) =
      toPrincipalIdeal (𝓞 K) K x := by
  apply FractionalIdealGroup.ext_count
  intro v
  rw [count_toPrincipalIdeal]
  change FractionalIdeal.count K v
      (((FractionalIdealGroup.factorization (K := K))
        (FiniteIdeleGroup.valuationVector
          (principalIdele K x).2) : FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      -WithZero.log (v.valuation K (x : K))
  rw [FractionalIdealGroup.count_factorization]
  change -WithZero.log
      (Valued.v (((principalIdele K x).2 v :
        (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      -WithZero.log (v.valuation K (x : K))
  rw [show ((((principalIdele K x).2 v :
      (v.adicCompletion K)ˣ) : v.adicCompletion K)) = (x : K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem classGroup_mk_eq_one_iff
    (I : FractionalIdealGroup K) :
    ClassGroup.mk K I = 1 ↔
      I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  constructor
  · intro h
    have h' := congrArg (ClassGroup.equiv K) h
    simpa using h'
  · intro h
    apply (ClassGroup.equiv K).injective
    simpa using h

@[simp]
theorem idealClass_principalIdele (x : Kˣ) :
    idealClass (principalIdele K x) = 1 := by
  change ClassGroup.mk K
      (fractionalIdeal (principalIdele K x)) = 1
  rw [fractionalIdeal_principalIdele,
    classGroup_mk_eq_one_iff]
  exact ⟨x, rfl⟩

/-- The subgroup `I_K^{S∞} Kˣ` defining the ordinary ideal class quotient. -/
def ordinaryIdealClassSubgroup : Subgroup (IdeleGroup K) :=
  integralAtFinitePlaces (K := K) ⊔ principalSubgroup K

/-- The kernel of the map from ideles to the ordinary ideal class group is
exactly `I_K^{S∞} Kˣ`. -/
theorem ordinaryIdealClassSubgroup_eq_ker :
    ordinaryIdealClassSubgroup (K := K) =
      (idealClass (K := K)).ker := by
  ext a
  constructor
  · intro ha
    rw [ordinaryIdealClassSubgroup, Subgroup.mem_sup] at ha
    obtain ⟨u, hu, p, hp, rfl⟩ := ha
    obtain ⟨x, rfl⟩ := hp
    have hu' : fractionalIdeal u = 1 := by
      rw [← MonoidHom.mem_ker,
        fractionalIdeal_ker]
      exact hu
    change idealClass (u * principalIdele K x) = 1
    rw [map_mul, idealClass_principalIdele, mul_one]
    change ClassGroup.mk K (fractionalIdeal u) = 1
    rw [hu', map_one]
  · intro ha
    change ClassGroup.mk K (fractionalIdeal a) = 1 at ha
    rw [classGroup_mk_eq_one_iff] at ha
    obtain ⟨x, hx⟩ := ha
    let u : IdeleGroup K := a * (principalIdele K x)⁻¹
    have hu : u ∈ integralAtFinitePlaces (K := K) := by
      rw [← fractionalIdeal_ker, MonoidHom.mem_ker]
      change fractionalIdeal
          (a * (principalIdele K x)⁻¹) = 1
      rw [map_mul, map_inv, fractionalIdeal_principalIdele,
        ← hx, mul_inv_cancel]
    rw [ordinaryIdealClassSubgroup, Subgroup.mem_sup]
    refine ⟨u, hu, principalIdele K x, ⟨x, rfl⟩, ?_⟩
    dsimp [u]
    group

/-- The ordinary ideal class group is the quotient of
the ideles by the ideles integral at all finite places and the principal
ideles. -/
def quotientIntegralSupPrincipalEquiv :
    IdeleGroup K ⧸
        (integralAtFinitePlaces (K := K) ⊔ principalSubgroup K) ≃*
      ClassGroup (𝓞 K) := by
  let h : integralAtFinitePlaces (K := K) ⊔ principalSubgroup K =
      (idealClass (K := K)).ker := by
    simpa [ordinaryIdealClassSubgroup] using
      ordinaryIdealClassSubgroup_eq_ker (K := K)
  exact
    (QuotientGroup.congr
      (integralAtFinitePlaces (K := K) ⊔ principalSubgroup K)
      (idealClass (K := K)).ker (MulEquiv.refl (IdeleGroup K))
      (by simpa using h)).trans
        (quotientIdealClassKernelEquiv (K := K))

end IdeleGroup
