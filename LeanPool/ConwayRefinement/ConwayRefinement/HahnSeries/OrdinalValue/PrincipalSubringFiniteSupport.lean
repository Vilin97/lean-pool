/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFraction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportScalarExtension

/-!
# Finite-support series over the principal graded fraction field

Let `L = Frac(P̂)`. This module defines the finite-support Hahn-series ring
`L(ℝ^{≤0})` used in LM24, Lemma 6.3.4, together with the coefficient extension
`K(ℝ^{≤0}) → L(ℝ^{≤0})`. Its range is bundled as the embedded coefficient-series subring.

All maps are canonical. The coefficient-field embedding is the composite `K → P̂ → Frac(P̂)`,
and finite-support scalar extension preserves every exponent and applies this composite to every
coefficient.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K] [CharZero K]

variable (K) in
/-- The canonical coefficient-field embedding `K → P̂ → Frac(P̂)`. -/
def principalSubringFractionCoefficientMap :
    K →+* PrincipalSubringFractionField K :=
  (principalSubringToFraction K).comp
    (algebraMap K (PrincipalSubring K))

/-- The coefficient-field embedding evaluates as the composite `K → P̂ → Frac(P̂)`. -/
@[simp]
theorem principalSubringFractionCoefficientMap_apply (k : K) :
    principalSubringFractionCoefficientMap K k =
      principalSubringToFraction K
        (algebraMap K (PrincipalSubring K) k) :=
  (rfl)

variable (K) in
/-- The coefficient-field embedding into the principal graded fraction field is injective. -/
theorem principalSubringFractionCoefficientMap_injective :
    Function.Injective (principalSubringFractionCoefficientMap K) :=
  (principalSubringToFraction_injective K).comp
    (principalSubring_algebraMap_injective K)

variable (K) in
/-- The finite-support nonpositive real-exponent Hahn-series ring over `Frac(P̂)`. -/
abbrev PrincipalSubringFractionFiniteSupportRing :=
  HahnSeries.Nonpositive.FiniteSupportRing
    (G := ℝ) (K := PrincipalSubringFractionField K)

variable (K) in
/-- Extend coefficients from `K` to `Frac(P̂)` in finite-support nonpositive real-exponent
series. -/
def principalSubringFractionScalarExtension :
    HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K) →+*
      PrincipalSubringFractionFiniteSupportRing K :=
  HahnSeries.Nonpositive.finiteSupportMap
    (G := ℝ) (principalSubringFractionCoefficientMap K)

/-- Principal-graded fraction scalar extension applies the coefficient embedding at every
exponent. -/
theorem principalSubringFractionScalarExtension_coeff
    (b : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K))
    (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    HahnSeries.Nonpositive.finiteSupportCoefficients
        (principalSubringFractionScalarExtension K b) g =
      principalSubringFractionCoefficientMap K
        (HahnSeries.Nonpositive.finiteSupportCoefficients b g) :=
  HahnSeries.Nonpositive.finiteSupportMap_coeff
    (principalSubringFractionCoefficientMap K) b g

variable (K) in
/-- Principal-graded fraction scalar extension is injective. -/
theorem principalSubringFractionScalarExtension_injective :
    Function.Injective (principalSubringFractionScalarExtension K) :=
  HahnSeries.Nonpositive.finiteSupportMap_injective
    (principalSubringFractionCoefficientMap K)
    (principalSubringFractionCoefficientMap_injective K)

/-- Principal-graded fraction scalar extension maps a constant series through the coefficient
embedding. -/
@[simp]
theorem principalSubringFractionScalarExtension_scalar (k : K) :
    principalSubringFractionScalarExtension K
        (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k) =
      HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ)
        (principalSubringFractionCoefficientMap K k) :=
  HahnSeries.Nonpositive.finiteSupportMap_scalar
    (principalSubringFractionCoefficientMap K) k

variable (K) in
/-- Principal-graded fraction scalar extension preserves every Hahn monomial. -/
@[simp]
theorem principalSubringFractionScalarExtension_monomial
    (g : HahnSeries.Nonpositive.exponentMonoid ℝ) :
    principalSubringFractionScalarExtension K
        (HahnSeries.Nonpositive.finiteSupportMonomial (K := K) g) =
      HahnSeries.Nonpositive.finiteSupportMonomial
        (K := PrincipalSubringFractionField K) g :=
  HahnSeries.Nonpositive.finiteSupportMap_monomial
    (principalSubringFractionCoefficientMap K) g

variable (K) in
/-- The embedded copy of `K(ℝ^{≤0})` inside `Frac(P̂)(ℝ^{≤0})`. -/
def principalSubringFractionCoefficientSubring :
    Subring (PrincipalSubringFractionFiniteSupportRing K) :=
  (principalSubringFractionScalarExtension K).range

/-- Membership in the embedded coefficient-series subring is existence of a preimage over `K`. -/
theorem mem_principalGradedFractionCoefficientSubring_iff
    (b : PrincipalSubringFractionFiniteSupportRing K) :
    b ∈ principalSubringFractionCoefficientSubring K ↔
      ∃ a, principalSubringFractionScalarExtension K a = b := by
  rw [principalSubringFractionCoefficientSubring, RingHom.mem_range]

variable (K) in
/-- Scalar redistribution for finite-support series over `Frac(P̂)`: a nonzero scalar may be
moved between two nonzero factors whose product has coefficients in the original field so that
both adjusted factors again have coefficients in that field. -/
structure PrincipalSubringFractionScalarRedistribution : Prop where
  exists_scalar :
    ∀ {p₁ p₂ : PrincipalSubringFractionFiniteSupportRing K},
      p₁ ≠ 0 → p₂ ≠ 0 →
        p₁ * p₂ ∈ principalSubringFractionCoefficientSubring K →
          ∃ B : PrincipalSubringFractionField K,
            B ≠ 0 ∧
              p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
                principalSubringFractionCoefficientSubring K ∧
              p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
                principalSubringFractionCoefficientSubring K

/-- A finite-support series over `Frac(P̂)` belongs to the embedded coefficient-series subring
exactly when every coefficient belongs to the image of `K`. -/
theorem mem_principalGradedFractionCoefficientSubring_iff_coeff
    (b : PrincipalSubringFractionFiniteSupportRing K) :
    b ∈ principalSubringFractionCoefficientSubring K ↔
      ∀ g, HahnSeries.Nonpositive.finiteSupportCoefficients b g ∈
        Set.range (principalSubringFractionCoefficientMap K) := by
  rw [principalSubringFractionCoefficientSubring,
    principalSubringFractionScalarExtension]
  exact HahnSeries.Nonpositive.mem_range_finiteSupportMap_iff
    (principalSubringFractionCoefficientMap K) b

/-- If an extended nonzero series becomes a coefficient-series after multiplication by a
constant fraction, then that fraction belongs to the image of the coefficient field. -/
theorem principalSubringFractionCoefficientMap_mem_range_of_mul_scalar_mem
    {p : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)}
    (hp : p ≠ 0) {B : PrincipalSubringFractionField K}
    (hmem : principalSubringFractionScalarExtension K p *
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
      principalSubringFractionCoefficientSubring K) :
    B ∈ Set.range (principalSubringFractionCoefficientMap K) := by
  apply HahnSeries.Nonpositive.coefficient_mem_range_of_map_mul_scalar_mem_range
    (Field.toIsField K) (principalSubringFractionCoefficientMap K) hp
  rw [principalSubringFractionCoefficientSubring, RingHom.mem_range] at hmem
  change ∃ x,
    HahnSeries.Nonpositive.finiteSupportMap
        (principalSubringFractionCoefficientMap K) x =
      HahnSeries.Nonpositive.finiteSupportMap
          (principalSubringFractionCoefficientMap K) p *
        HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B
  simpa only [principalSubringFractionScalarExtension] using hmem

/-- Scalar redistribution implies that the coefficient extension from `K(ℝ^{≤0})` to
`Frac(P̂)(ℝ^{≤0})` reflects divisibility. -/
theorem principalSubringFractionScalarExtension_dvd_iff_of_scalarRedistribution (hredistribute :
      ∀ {p₁ p₂ : PrincipalSubringFractionFiniteSupportRing K},
        p₁ ≠ 0 → p₂ ≠ 0 →
          p₁ * p₂ ∈ principalSubringFractionCoefficientSubring K →
            ∃ B : PrincipalSubringFractionField K,
              B ≠ 0 ∧
                p₁ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B ∈
                  principalSubringFractionCoefficientSubring K ∧
                p₂ * HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) B⁻¹ ∈
                  principalSubringFractionCoefficientSubring K)
    (p q : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K)) :
    principalSubringFractionScalarExtension K p ∣
        principalSubringFractionScalarExtension K q ↔
      p ∣ q := by
  apply HahnSeries.Nonpositive.finiteSupportMap_dvd_iff_of_scalarRedistribution
    (principalSubringFractionCoefficientMap K)
    (principalSubringFractionCoefficientMap_injective K) ?_ p q
  intro p₁ p₂ hp₁ hp₂ hprod
  have hprod' :
      p₁ * p₂ ∈ principalSubringFractionCoefficientSubring K := by
    rw [principalSubringFractionCoefficientSubring, RingHom.mem_range]
    exact hprod
  obtain ⟨B, hB, hleft, hright⟩ := hredistribute hp₁ hp₂ hprod'
  refine ⟨B, hB, ?_, ?_⟩
  · rw [principalSubringFractionCoefficientSubring, RingHom.mem_range] at hleft
    exact hleft
  · rw [principalSubringFractionCoefficientSubring, RingHom.mem_range] at hright
    exact hright

/-- Scalar redistribution and greatest-common-divisor existence over `Frac(P̂)` descend primal
factor witnesses through the coefficient extension. Both descended factors remain finite-support
series over the original coefficient field. -/
theorem principalSubringFractionScalarExtension_exists_factor_dvd_of_scalarRedistribution
    (hredistribute : PrincipalSubringFractionScalarRedistribution K)
    (hgcd : ∀ p q : PrincipalSubringFractionFiniteSupportRing K,
      ∃ d : PrincipalSubringFractionFiniteSupportRing K,
        ∀ e : PrincipalSubringFractionFiniteSupportRing K,
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (p : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K))
    (b c : PrincipalSubringFractionFiniteSupportRing K)
    (hp : principalSubringFractionScalarExtension K p ∣ b * c) :
    ∃ p₁ p₂ : HahnSeries.Nonpositive.FiniteSupportRing (G := ℝ) (K := K),
      p = p₁ * p₂ ∧
        principalSubringFractionScalarExtension K p₁ ∣ b ∧
        principalSubringFractionScalarExtension K p₂ ∣ c := by
  apply HahnSeries.Nonpositive.finiteSupportMap_exists_factor_dvd_of_scalarRedistribution
    (principalSubringFractionCoefficientMap K)
    (principalSubringFractionCoefficientMap_injective K) ?_ hgcd p b c hp
  intro p₁ p₂ hp₁ hp₂ hprod
  have hprod' :
      p₁ * p₂ ∈ principalSubringFractionCoefficientSubring K := by
    rw [principalSubringFractionCoefficientSubring, RingHom.mem_range]
    exact hprod
  obtain ⟨B, hB, hleft, hright⟩ :=
    hredistribute.exists_scalar hp₁ hp₂ hprod'
  refine ⟨B, hB, ?_, ?_⟩
  · rw [principalSubringFractionCoefficientSubring, RingHom.mem_range] at hleft
    exact hleft
  · rw [principalSubringFractionCoefficientSubring, RingHom.mem_range] at hright
    exact hright

end

end Berarducci
