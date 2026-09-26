/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FactorCoefficients
public import LeanPool.ConwayRefinement.ConwayRefinement.FieldTheory.RelativeAlgebraicClosure

/-!
# Redistributing a coefficient between two finite-support factors

Two series with finite support have finitely many exponents between them, so both are supported
in the subgroup those exponents generate. That subgroup is finitely generated and torsion-free,
hence free of finite rank, and its group ring over a field therefore has unique factorisation.

This file records the passage from a pair of finite-support series to such a common subgroup,
which is the setting in which the redistribution argument factors a product.
-/

universe u v

namespace Berarducci

public noncomputable section

/-- Two finite-support series lie in the group ring of a common finitely generated subgroup of
the exponent group, and that group ring has unique factorisation. -/
theorem exists_common_subgroup_uniqueFactorization {G : Type u} {L : Type v} [LinearOrder G]
    [AddCommGroup G] [IsOrderedAddMonoid G] [Field L] (p q : HahnSeries G L)
    (hp : p.support.Finite) (hq : q.support.Finite) :
    ∃ H : AddSubgroup G, UniqueFactorizationMonoid (AddMonoidAlgebra L H) ∧
      p.support ⊆ (H : Set G) ∧ q.support ⊆ (H : Set G) := by
  classical
  refine ⟨AddSubgroup.closure ((hp.toFinset ∪ hq.toFinset : Finset G) : Set G),
    HahnSeries.uniqueFactorizationMonoid_subgroupAlgebra
      (HahnSeries.exists_addEquiv_fin (hp.toFinset ∪ hq.toFinset)), ?_, ?_⟩
  · exact fun x hx ↦ AddSubgroup.subset_closure
      (Finset.mem_coe.mpr (Finset.mem_union_left _ (hp.mem_toFinset.mpr hx)))
  · exact fun x hx ↦ AddSubgroup.subset_closure
      (Finset.mem_coe.mpr (Finset.mem_union_right _ (hq.mem_toFinset.mpr hx)))

section Redistribution

variable {K : Type v} [Field K] [CharZero K]

/-- The coefficient-field algebra structure on principal-subring fractions used for scalar
redistribution. -/
local instance algLocal :
    Algebra K (PrincipalSubringFractionField K) := principalSubringFractionAlgebra K

/-- Multiplying a finite-support series by a constant scales every coefficient. -/
theorem coeff_mul_finiteSupportScalarHom {L : Type*} [Field L]
    (p : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := L)) (c : L) (x : ℝ) :
    ((((p * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) c :
        HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := L)) :
        HahnSeries.Nonpositive ℝ L) : HahnSeries ℝ L)).coeff x =
      ((((p : HahnSeries.Nonpositive ℝ L) : HahnSeries ℝ L)).coeff x) * c := by
  have h1 : (((p * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) c :
      HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := L)) :
      HahnSeries.Nonpositive ℝ L) : HahnSeries ℝ L) =
      (((p : HahnSeries.Nonpositive ℝ L) : HahnSeries ℝ L)) * HahnSeries.C c := by
    rw [Subring.coe_mul, Subring.coe_mul,
      HahnSeries.Nonpositive.coe_finiteSupportScalarHom (G := ℝ) (K := L) c]
  rw [h1, mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]

omit [CharZero K] in
/-- Coefficient extension of finite-support series is coefficientwise on Hahn series. -/
theorem coe_finiteSupportMap {L : Type*} [Field L] (f : K →+* L)
    (b : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)) :
    (((HahnSeries.Nonpositive.finiteSupportMap (G := ℝ) f b :
        HahnSeries.Nonpositive ℝ L) : HahnSeries ℝ L)) =
      (((b : HahnSeries.Nonpositive ℝ K) : HahnSeries ℝ K)).map f := by
  refine HahnSeries.coeff_injective (funext fun x ↦ ?_)
  rw [HahnSeries.map_coeff]
  rcases le_or_gt x 0 with hx | hx
  · have h1 := HahnSeries.Nonpositive.finiteSupportMap_coeff (G := ℝ) f b ⟨x, hx⟩
    rw [HahnSeries.Nonpositive.finiteSupportCoefficients_apply,
      HahnSeries.Nonpositive.finiteSupportCoefficients_apply] at h1
    exact h1
  · have hzK : (((b : HahnSeries.Nonpositive ℝ K) : HahnSeries ℝ K)).coeff x = 0 := by
      by_contra hne
      exact absurd (HahnSeries.Nonpositive.support_subset _
        ((HahnSeries.mem_support _ _).mpr hne)) (by simpa using hx)
    have hzL : ((((HahnSeries.Nonpositive.finiteSupportMap (G := ℝ) f b :
        HahnSeries.Nonpositive ℝ L)) : HahnSeries ℝ L)).coeff x = 0 := by
      by_contra hne
      exact absurd (HahnSeries.Nonpositive.support_subset _
        ((HahnSeries.mem_support _ _).mpr hne)) (by simpa using hx)
    rw [hzK, hzL, map_zero]

variable (K) in
/-- The algebra map of the fraction field is the coefficient embedding. -/
theorem algebraMap_eq_coefficientMap :
    algebraMap K (PrincipalSubringFractionField K) =
      principalSubringFractionCoefficientMap K := by
  refine RingHom.ext fun k ↦ ?_
  rw [principalSubringFraction_algebraMap_apply, principalSubringFractionCoefficientMap_apply]

/-- The scalar extension acts coefficientwise on the underlying Hahn series. -/
theorem coe_scalarExtension (b : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)) :
    (((principalSubringFractionScalarExtension K b :
        HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
        HahnSeries ℝ (PrincipalSubringFractionField K))) =
      (((b : HahnSeries.Nonpositive ℝ K) : HahnSeries ℝ K)).map
        (algebraMap K (PrincipalSubringFractionField K)) := by
  refine HahnSeries.coeff_injective (funext fun x ↦ ?_)
  rw [HahnSeries.map_coeff, algebraMap_eq_coefficientMap]
  rcases le_or_gt x 0 with hx | hx
  · have h1 := principalSubringFractionScalarExtension_coeff b ⟨x, hx⟩
    rw [HahnSeries.Nonpositive.finiteSupportCoefficients_apply,
      HahnSeries.Nonpositive.finiteSupportCoefficients_apply] at h1
    exact h1
  · have hzK : (((b : HahnSeries.Nonpositive ℝ K) : HahnSeries ℝ K)).coeff x = 0 := by
      by_contra hne
      exact absurd (HahnSeries.Nonpositive.support_subset _
        ((HahnSeries.mem_support _ _).mpr hne)) (by simpa using hx)
    have hzL : (((principalSubringFractionScalarExtension K b :
        HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
        HahnSeries ℝ (PrincipalSubringFractionField K))).coeff x = 0 := by
      by_contra hne
      exact absurd (HahnSeries.Nonpositive.support_subset _
        ((HahnSeries.mem_support _ _).mpr hne)) (by simpa using hx)
    rw [hzK, hzL, map_zero]

/-- One factor is cleared into the coefficient field by a single nonzero scalar. -/
theorem exists_clearing_scalar
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K (PrincipalSubringFractionField K))
    {p q : PrincipalSubringFractionFiniteSupportRing K} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p * q ∈ principalSubringFractionCoefficientSubring K) :
    ∃ c : PrincipalSubringFractionField K, c ≠ 0 ∧
      p * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) c ∈
        principalSubringFractionCoefficientSubring K := by
  obtain ⟨a, ha⟩ := (mem_principalGradedFractionCoefficientSubring_iff _).mp hpq
  have hPfin := (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff _).mp p.2
  have hQfin := (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff _).mp q.2
  have hP0 : (((p : HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
      HahnSeries ℝ (PrincipalSubringFractionField K))) ≠ 0 := by
    intro h0
    exact hp (Subtype.ext (Subtype.ext h0))
  have hQ0 : (((q : HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
      HahnSeries ℝ (PrincipalSubringFractionField K))) ≠ 0 := by
    intro h0
    exact hq (Subtype.ext (Subtype.ext h0))
  have hrel : (((p : HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
        HahnSeries ℝ (PrincipalSubringFractionField K))) *
      (((q : HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
        HahnSeries ℝ (PrincipalSubringFractionField K))) =
      (((a : HahnSeries.Nonpositive ℝ K) : HahnSeries ℝ K)).map
        (algebraMap K (PrincipalSubringFractionField K)) := by
    have h1 : (((p * q : PrincipalSubringFractionFiniteSupportRing K) :
        HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
        HahnSeries ℝ (PrincipalSubringFractionField K)) =
        (((p : HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
          HahnSeries ℝ (PrincipalSubringFractionField K))) *
        (((q : HahnSeries.Nonpositive ℝ (PrincipalSubringFractionField K)) :
          HahnSeries ℝ (PrincipalSubringFractionField K))) := by
      rw [Subring.coe_mul, Subring.coe_mul]
    rw [← h1, ← ha]
    exact coe_scalarExtension a
  obtain ⟨c, hc, hcoeff⟩ :=
    HahnSeries.exists_scalar_of_hahn_mul_eq_map hclosed hP0 hQ0 hPfin hQfin hrel
  refine ⟨c, hc, ?_⟩
  rw [mem_principalGradedFractionCoefficientSubring_iff_coeff]
  intro g
  rw [HahnSeries.Nonpositive.finiteSupportCoefficients_apply,
    coeff_mul_finiteSupportScalarHom, mul_comm]
  have := hcoeff (g : ℝ)
  rw [algebraMap_eq_coefficientMap] at this
  exact this

/-- A constant whose value lies in the coefficient field is a coefficient series. -/
theorem finiteSupportScalarHom_mem_of_mem_range {B : PrincipalSubringFractionField K}
    (hB : B ∈ Set.range (principalSubringFractionCoefficientMap K)) :
    HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
      principalSubringFractionCoefficientSubring K := by
  obtain ⟨k, rfl⟩ := hB
  rw [mem_principalGradedFractionCoefficientSubring_iff]
  exact ⟨HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k,
    principalSubringFractionScalarExtension_scalar k⟩

/-- The product of two clearing scalars lies in the coefficient field. -/
theorem mul_clearing_scalars_mem_range
    {p₁ p₂ : PrincipalSubringFractionFiniteSupportRing K} (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hprod : p₁ * p₂ ∈ principalSubringFractionCoefficientSubring K)
    {c₁ c₂ : PrincipalSubringFractionField K}
    (hm₁ : p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) c₁ ∈
      principalSubringFractionCoefficientSubring K)
    (hm₂ : p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) c₂ ∈
      principalSubringFractionCoefficientSubring K) :
    c₁ * c₂ ∈ Set.range (principalSubringFractionCoefficientMap K) := by
  obtain ⟨a, ha⟩ := (mem_principalGradedFractionCoefficientSubring_iff _).mp hprod
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha
    exact (mul_ne_zero hp₁ hp₂) ha.symm
  refine principalSubringFractionCoefficientMap_mem_range_of_mul_scalar_mem ha0 ?_
  rw [ha, map_mul, mul_mul_mul_comm]
  exact Subring.mul_mem _ hm₁ hm₂

/-- LM24, Lemma 6.3.4: a nonzero scalar may be moved between two nonzero finite-support factors
whose product has coefficients in the coefficient field. -/
theorem principalSubringFraction_exists_scalarRedistribution_of_isRelativelyAlgebraicallyClosed
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K (PrincipalSubringFractionField K))
    {p₁ p₂ : PrincipalSubringFractionFiniteSupportRing K}
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hprod : p₁ * p₂ ∈ principalSubringFractionCoefficientSubring K) :
    ∃ B : PrincipalSubringFractionField K, B ≠ 0 ∧
      p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
        principalSubringFractionCoefficientSubring K ∧
      p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
        principalSubringFractionCoefficientSubring K := by
  obtain ⟨c₁, hc₁, hm₁⟩ := exists_clearing_scalar hclosed hp₁ hp₂ hprod
  obtain ⟨c₂, hc₂, hm₂⟩ := exists_clearing_scalar hclosed hp₂ hp₁
    (by rw [mul_comm]; exact hprod)
  have hrange := mul_clearing_scalars_mem_range hp₁ hp₂ hprod hm₁ hm₂
  refine ⟨c₁, hc₁, hm₁, ?_⟩
  have hinv : c₁⁻¹ = c₂ * (c₁ * c₂)⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_comm c₂ c₁⁻¹, mul_assoc, mul_inv_cancel₀ hc₂, mul_one]
  have hrangeinv : (c₁ * c₂)⁻¹ ∈ Set.range (principalSubringFractionCoefficientMap K) := by
    obtain ⟨k, hk⟩ := hrange
    exact ⟨k⁻¹, by rw [map_inv₀, hk]⟩
  rw [hinv, map_mul, ← mul_assoc]
  exact Subring.mul_mem _ hm₂ (finiteSupportScalarHom_mem_of_mem_range hrangeinv)

end Redistribution

end

end Berarducci
