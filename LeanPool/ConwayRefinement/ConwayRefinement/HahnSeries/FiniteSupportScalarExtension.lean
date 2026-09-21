/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportMonoidAlgebra
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Coefficient extension for finite-support Hahn series

A ring homomorphism between coefficient rings induces a ring homomorphism between the
corresponding finite-support nonpositive Hahn-series rings. The construction is intrinsic: under
the canonical additive-monoid-algebra presentation, it applies the coefficient homomorphism and
leaves every exponent unchanged.

The range characterization identifies the image with the series whose coefficients all belong to
the image of the coefficient homomorphism. In particular, scalar extension realizes the inclusion
of `K(ℝ^{≤0})` in `L(ℝ^{≤0})` used in LM24, Lemma 6.3.4.
-/

open scoped HahnSeries

universe u v w

namespace HahnSeries.Nonpositive

public noncomputable section

variable {G : Type u} {K : Type v} {L : Type w}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [CommRing K] [CommRing L]

/-- Apply a coefficient-ring homomorphism to a finite-support nonpositive Hahn series. -/
def finiteSupportMap (f : K →+* L) :
    FiniteSupportRing (G := G) (K := K) →+*
      FiniteSupportRing (G := G) (K := L) :=
  (finiteSupportAddMonoidAlgebraEquiv (G := G) (K := L)).symm.toRingHom.comp
    ((AddMonoidAlgebra.mapRingHom (exponentMonoid G) f).comp
      (finiteSupportAddMonoidAlgebraEquiv (G := G) (K := K)).toRingHom)

/-- Under the additive-monoid-algebra presentation, `finiteSupportMap` applies the coefficient
homomorphism. -/
@[simp]
theorem finiteSupportAddMonoidAlgebraEquiv_map (f : K →+* L)
    (b : FiniteSupportRing (G := G) (K := K)) :
    finiteSupportAddMonoidAlgebraEquiv (finiteSupportMap f b) =
      AddMonoidAlgebra.mapRingHom (exponentMonoid G) f
        (finiteSupportAddMonoidAlgebraEquiv b) := by
  rw [finiteSupportMap, RingHom.comp_apply, RingHom.comp_apply]
  exact finiteSupportAddMonoidAlgebraEquiv.apply_symm_apply _

/-- `finiteSupportMap` applies the coefficient homomorphism at every exponent. -/
theorem finiteSupportMap_coeff (f : K →+* L)
    (b : FiniteSupportRing (G := G) (K := K))
    (g : exponentMonoid G) :
    finiteSupportCoefficients (finiteSupportMap f b) g =
      f (finiteSupportCoefficients b g) := by
  calc
    finiteSupportCoefficients (finiteSupportMap f b) g =
        AddMonoidAlgebra.coeff
          (finiteSupportAddMonoidAlgebraEquiv (finiteSupportMap f b)) g :=
      (congrArg (fun q : exponentMonoid G →₀ L ↦ q g)
        (coeff_finiteSupportAddMonoidAlgebraEquiv
          (G := G) (K := L) (finiteSupportMap f b))).symm
    _ = f (finiteSupportCoefficients b g) := by
      rw [finiteSupportAddMonoidAlgebraEquiv_map]
      change
        (AddMonoidAlgebra.mapRingHom (exponentMonoid G) f
            (finiteSupportAddMonoidAlgebraEquiv b)).coeff g = _
      rw [AddMonoidAlgebra.coeff_mapRingHom]
      exact congrArg f (congrArg (fun q : exponentMonoid G →₀ K ↦ q g)
        (coeff_finiteSupportAddMonoidAlgebraEquiv (G := G) (K := K) b))

/-- An injective coefficient homomorphism induces an injective finite-support map. -/
theorem finiteSupportMap_injective (f : K →+* L)
    (hf : Function.Injective f) :
    Function.Injective (finiteSupportMap (G := G) f) := by
  intro b c hbc
  apply finiteSupportFinsuppEquiv.injective
  rw [finiteSupportFinsuppEquiv_apply, finiteSupportFinsuppEquiv_apply]
  ext g
  apply hf
  have hcoeff := congrArg
    (fun q : FiniteSupportRing (G := G) (K := L) ↦
      finiteSupportCoefficients q g) hbc
  simpa only [finiteSupportMap_coeff] using hcoeff

/-- Applying the identity coefficient homomorphism is the identity on finite-support series. -/
@[simp]
theorem finiteSupportMap_id :
    finiteSupportMap (G := G) (RingHom.id K) = RingHom.id _ := by
  apply RingHom.ext
  intro b
  apply finiteSupportAddMonoidAlgebraEquiv.injective
  rw [finiteSupportAddMonoidAlgebraEquiv_map,
    AddMonoidAlgebra.mapRingHom_id]
  rfl

/-- Coefficient maps respect composition. -/
@[simp]
theorem finiteSupportMap_comp {M : Type*} [CommRing M]
    (g : L →+* M) (f : K →+* L) :
    finiteSupportMap (G := G) (g.comp f) =
      (finiteSupportMap (G := G) g).comp (finiteSupportMap (G := G) f) := by
  apply RingHom.ext
  intro b
  apply finiteSupportAddMonoidAlgebraEquiv.injective
  rw [finiteSupportAddMonoidAlgebraEquiv_map,
    RingHom.comp_apply, finiteSupportAddMonoidAlgebraEquiv_map,
    finiteSupportAddMonoidAlgebraEquiv_map,
    AddMonoidAlgebra.mapRingHom_comp]
  rfl

/-- A coefficient map preserves every finite-support Hahn monomial. -/
@[simp]
theorem finiteSupportMap_monomial (f : K →+* L)
    (g : exponentMonoid G) :
    finiteSupportMap f (finiteSupportMonomial (K := K) g) =
      finiteSupportMonomial (K := L) g := by
  apply finiteSupportAddMonoidAlgebraEquiv.injective
  rw [finiteSupportAddMonoidAlgebraEquiv_map,
    finiteSupportAddMonoidAlgebraEquiv_monomial,
    AddMonoidAlgebra.mapRingHom_single, map_one,
    finiteSupportAddMonoidAlgebraEquiv_monomial]

/-- A coefficient map sends a constant series to the constant series with mapped coefficient. -/
@[simp]
theorem finiteSupportMap_scalar (f : K →+* L) (k : K) :
    finiteSupportMap f (finiteSupportScalarHom (G := G) k) =
      finiteSupportScalarHom (G := G) (f k) := by
  apply finiteSupportAddMonoidAlgebraEquiv.injective
  rw [finiteSupportAddMonoidAlgebraEquiv_map]
  change
    AddMonoidAlgebra.mapRingHom (exponentMonoid G) f
        (finiteSupportAddMonoidAlgebraEquiv
          (algebraMap K (FiniteSupportRing (G := G) (K := K)) k)) =
      finiteSupportAddMonoidAlgebraEquiv
        (algebraMap L (FiniteSupportRing (G := G) (K := L)) (f k))
  rw [AlgEquiv.commutes, AlgEquiv.commutes]
  change
    AddMonoidAlgebra.mapRingHom (exponentMonoid G) f
        (AddMonoidAlgebra.single 0 k) =
      AddMonoidAlgebra.single 0 (f k)
  exact AddMonoidAlgebra.mapRingHom_single f 0 k

/-- A finite-support series belongs to the range of a coefficient map exactly when each of its
coefficients belongs to the range of the coefficient homomorphism. -/
theorem mem_range_finiteSupportMap_iff (f : K →+* L)
    (b : FiniteSupportRing (G := G) (K := L)) :
    b ∈ Set.range (finiteSupportMap (G := G) f) ↔
      ∀ g, finiteSupportCoefficients b g ∈ Set.range f := by
  constructor
  · rintro ⟨a, rfl⟩ g
    exact ⟨finiteSupportCoefficients a g, (finiteSupportMap_coeff f a g).symm⟩
  · intro hb
    have hcoeff : ∀ g,
        AddMonoidAlgebra.coeff (finiteSupportAddMonoidAlgebraEquiv b) g ∈
          Set.range f.toAddMonoidHom := by
      intro g
      rw [show AddMonoidAlgebra.coeff
          (finiteSupportAddMonoidAlgebraEquiv b) g =
            finiteSupportCoefficients b g from
        congrArg (fun q : exponentMonoid G →₀ L ↦ q g)
          (coeff_finiteSupportAddMonoidAlgebraEquiv
            (G := G) (K := L) b)]
      exact hb g
    have hrange : finiteSupportAddMonoidAlgebraEquiv b ∈
        Set.range (AddMonoidAlgebra.map
          (M := exponentMonoid G) f.toAddMonoidHom) := by
      rw [AddMonoidAlgebra.range_map]
      exact hcoeff
    obtain ⟨a, ha⟩ := hrange
    refine ⟨finiteSupportAddMonoidAlgebraEquiv.symm a, ?_⟩
    apply finiteSupportAddMonoidAlgebraEquiv.injective
    rw [finiteSupportAddMonoidAlgebraEquiv_map,
      finiteSupportAddMonoidAlgebraEquiv.apply_symm_apply]
    change AddMonoidAlgebra.map f.toAddMonoidHom a =
      finiteSupportAddMonoidAlgebraEquiv b
    exact ha

/-- If a nonzero finite-support series over `K` becomes a scalar multiple whose coefficients are
still in the image of `K`, then the scalar itself belongs to the image of `K`. -/
theorem coefficient_mem_range_of_map_mul_scalar_mem_range
    (hK : IsField K) (f : K →+* L)
    {p : FiniteSupportRing (G := G) (K := K)} (hp : p ≠ 0)
    {B : L}
    (hmem : finiteSupportMap f p * finiteSupportScalarHom (G := G) B ∈
      Set.range (finiteSupportMap (G := G) f)) :
    B ∈ Set.range f := by
  have hpCoefficients : finiteSupportCoefficients p ≠ 0 := by
    rw [← finiteSupportFinsuppEquiv_apply]
    exact (finiteSupportFinsuppEquiv (G := G) (K := K)).map_ne_zero_iff.mpr hp
  obtain ⟨g, hg⟩ := Finsupp.ne_iff.mp hpCoefficients
  obtain ⟨q, hq⟩ := hmem
  have hcoeff := congrArg
    (fun r : FiniteSupportRing (G := G) (K := L) ↦
      finiteSupportCoefficients r g) hq
  rw [finiteSupportMap_coeff, mul_comm,
    ← smul_finiteSupport_eq_scalar_mul, map_smul, Finsupp.smul_apply,
    finiteSupportMap_coeff] at hcoeff
  obtain ⟨a, ha⟩ := hK.mul_inv_cancel hg
  refine ⟨a * finiteSupportCoefficients q g, ?_⟩
  rw [map_mul, hcoeff]
  change f a * (B * f (finiteSupportCoefficients p g)) = B
  calc
    _ = B * f (finiteSupportCoefficients p g * a) := by rw [map_mul]; ring
    _ = B := by rw [ha, map_one, mul_one]

section ScalarExtension

variable [Algebra K L]

/-- Extend the coefficients of a finite-support Hahn series along a coefficient algebra. -/
def finiteSupportScalarExtension :
    FiniteSupportRing (G := G) (K := K) →+*
      FiniteSupportRing (G := G) (K := L) :=
  finiteSupportMap (G := G) (algebraMap K L)

/-- Under the additive-monoid-algebra presentation, scalar extension applies the coefficient
algebra map. -/
@[simp]
theorem finiteSupportAddMonoidAlgebraEquiv_scalarExtension
    (b : FiniteSupportRing (G := G) (K := K)) :
    finiteSupportAddMonoidAlgebraEquiv
        (finiteSupportScalarExtension (G := G) (K := K) (L := L) b) =
      AddMonoidAlgebra.mapRingHom (exponentMonoid G) (algebraMap K L)
        (finiteSupportAddMonoidAlgebraEquiv b) := by
  rw [finiteSupportScalarExtension, finiteSupportAddMonoidAlgebraEquiv_map]

/-- Scalar extension applies the coefficient algebra map at every exponent. -/
theorem finiteSupportScalarExtension_coeff
    (b : FiniteSupportRing (G := G) (K := K))
    (g : exponentMonoid G) :
    finiteSupportCoefficients
        (finiteSupportScalarExtension (G := G) (K := K) (L := L) b) g =
      algebraMap K L (finiteSupportCoefficients b g) :=
  finiteSupportMap_coeff (algebraMap K L) b g

/-- Scalar extension preserves every finite-support Hahn monomial. -/
@[simp]
theorem finiteSupportScalarExtension_monomial (g : exponentMonoid G) :
    finiteSupportScalarExtension (G := G) (K := K) (L := L)
        (finiteSupportMonomial (K := K) g) =
      finiteSupportMonomial (K := L) g :=
  finiteSupportMap_monomial (algebraMap K L) g

/-- Scalar extension sends a constant series through the coefficient algebra map. -/
@[simp]
theorem finiteSupportScalarExtension_scalar (k : K) :
    finiteSupportScalarExtension (G := G) (K := K) (L := L)
        (finiteSupportScalarHom (G := G) k) =
      finiteSupportScalarHom (G := G) (algebraMap K L k) :=
  finiteSupportMap_scalar (algebraMap K L) k

/-- Scalar extension is injective when the coefficient algebra map is injective. -/
theorem finiteSupportScalarExtension_injective
    (hKL : Function.Injective (algebraMap K L)) :
    Function.Injective
      (finiteSupportScalarExtension (G := G) (K := K) (L := L)) :=
  finiteSupportMap_injective (algebraMap K L) hKL

/-- The range of scalar extension consists exactly of the finite-support series whose coefficients
belong to the image of the coefficient algebra map. -/
theorem mem_range_finiteSupportScalarExtension_iff
    (b : FiniteSupportRing (G := G) (K := L)) :
    b ∈ Set.range (finiteSupportScalarExtension (G := G) (K := K) (L := L)) ↔
      ∀ g, finiteSupportCoefficients b g ∈ Set.range (algebraMap K L) :=
  mem_range_finiteSupportMap_iff (algebraMap K L) b

end ScalarExtension

end

end HahnSeries.Nonpositive

namespace HahnSeries.Nonpositive

public noncomputable section

variable {G : Type u} {K : Type v} {L : Type w}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [Field K] [Field L]

private theorem mul_scalar_mul_inv_scalar
    (B : L) (hB : B ≠ 0)
    (x y : FiniteSupportRing (G := G) (K := L)) :
    (x * finiteSupportScalarHom (G := G) B) *
        (y * finiteSupportScalarHom (G := G) B⁻¹) =
      x * y := by
  calc
    _ = x * y *
        (finiteSupportScalarHom (G := G) B *
          finiteSupportScalarHom (G := G) B⁻¹) := by ac_rfl
    _ = x * y * finiteSupportScalarHom (G := G) (B * B⁻¹) := by
      rw [map_mul]
    _ = x * y := by rw [mul_inv_cancel₀ hB, map_one, mul_one]

private theorem eq_mul_of_scalar_redistribution
    (f : K →+* L) (hf : Function.Injective f)
    (B : L) (hB : B ≠ 0)
    {p p₁ p₂ : FiniteSupportRing (G := G) (K := K)}
    {q₁ q₂ : FiniteSupportRing (G := G) (K := L)}
    (hpq : finiteSupportMap f p = q₁ * q₂)
    (hp₁ : finiteSupportMap f p₁ =
      q₁ * finiteSupportScalarHom (G := G) B)
    (hp₂ : finiteSupportMap f p₂ =
      q₂ * finiteSupportScalarHom (G := G) B⁻¹) :
    p = p₁ * p₂ := by
  apply finiteSupportMap_injective f hf
  calc
    finiteSupportMap f p = q₁ * q₂ := hpq
    _ = (q₁ * finiteSupportScalarHom (G := G) B) *
        (q₂ * finiteSupportScalarHom (G := G) B⁻¹) :=
      (mul_scalar_mul_inv_scalar B hB q₁ q₂).symm
    _ = finiteSupportMap f p₁ * finiteSupportMap f p₂ := by rw [← hp₁, ← hp₂]
    _ = finiteSupportMap f (p₁ * p₂) :=
      ((finiteSupportMap f).map_mul p₁ p₂).symm

private theorem map_dvd_of_eq_mul_scalar
    (f : K →+* L) (B : L) (hB : B ≠ 0)
    {p : FiniteSupportRing (G := G) (K := K)}
    {q b : FiniteSupportRing (G := G) (K := L)}
    (hp : finiteSupportMap f p = q * finiteSupportScalarHom (G := G) B)
    (hq : q ∣ b) :
    finiteSupportMap f p ∣ b := by
  obtain ⟨r, hr⟩ := hq
  refine ⟨r * finiteSupportScalarHom (G := G) B⁻¹, ?_⟩
  calc
    b = q * r := hr
    _ = (q * finiteSupportScalarHom (G := G) B) *
        (r * finiteSupportScalarHom (G := G) B⁻¹) :=
      (mul_scalar_mul_inv_scalar B hB q r).symm
    _ = finiteSupportMap f p *
        (r * finiteSupportScalarHom (G := G) B⁻¹) := by rw [hp]

/-- An injective coefficient map reflects divisibility of finite-support series provided that
nonzero factorisations whose product lies in its range can be scalar-redistributed into the
range. -/
theorem finiteSupportMap_dvd_iff_of_scalarRedistribution
    (f : K →+* L) (hf : Function.Injective f)
    (hredistribute :
      ∀ {p₁ p₂ : FiniteSupportRing (G := G) (K := L)},
        p₁ ≠ 0 → p₂ ≠ 0 →
          p₁ * p₂ ∈ Set.range (finiteSupportMap (G := G) f) →
            ∃ B : L,
              B ≠ 0 ∧
                p₁ * finiteSupportScalarHom (G := G) B ∈
                  Set.range (finiteSupportMap (G := G) f) ∧
                p₂ * finiteSupportScalarHom (G := G) B⁻¹ ∈
                  Set.range (finiteSupportMap (G := G) f))
    (p q : FiniteSupportRing (G := G) (K := K)) :
    finiteSupportMap f p ∣ finiteSupportMap f q ↔ p ∣ q := by
  constructor
  · rintro ⟨r, hr⟩
    by_cases hp : p = 0
    · subst p
      have hqImage : finiteSupportMap f q = 0 := by simpa using hr
      have hq : q = 0 :=
        (finiteSupportMap_injective f hf) (hqImage.trans (map_zero _).symm)
      simp [hq]
    by_cases hq : q = 0
    · simp [hq]
    have hpImage : finiteSupportMap f p ≠ 0 :=
      (map_ne_zero_iff _ (finiteSupportMap_injective f hf)).mpr hp
    have hqImage : finiteSupportMap f q ≠ 0 :=
      (map_ne_zero_iff _ (finiteSupportMap_injective f hf)).mpr hq
    have hrNe : r ≠ 0 := by
      intro hrZero
      rw [hrZero, mul_zero] at hr
      exact hqImage hr
    have hprod :
        finiteSupportMap f p * r ∈
          Set.range (finiteSupportMap (G := G) f) := by
      exact ⟨q, hr⟩
    obtain ⟨B, hB, hleft, hright⟩ :=
      hredistribute hpImage hrNe hprod
    have hBRange : B ∈ Set.range f :=
      coefficient_mem_range_of_map_mul_scalar_mem_range
        (Field.toIsField K) f hp hleft
    obtain ⟨k, hk⟩ := hBRange
    obtain ⟨t, ht⟩ := hright
    have hrRange : r ∈ Set.range (finiteSupportMap (G := G) f) := by
      refine ⟨t * finiteSupportScalarHom (G := G) k, ?_⟩
      rw [map_mul, ht, finiteSupportMap_scalar, hk]
      simp only [mul_assoc, ← map_mul, inv_mul_cancel₀ hB, map_one, mul_one]
    obtain ⟨s, hs⟩ := hrRange
    refine ⟨s, ?_⟩
    apply finiteSupportMap_injective f hf
    rw [map_mul, hs, hr]
  · rintro ⟨r, rfl⟩
    exact ⟨finiteSupportMap f r, map_mul _ _ _⟩

/-- Scalar redistribution descends the primal factor witnesses supplied by greatest-common-
divisor existence after coefficient extension. In particular, both descended factors remain in
the finite-support ring over the original coefficient field. -/
theorem finiteSupportMap_exists_factor_dvd_of_scalarRedistribution
    (f : K →+* L) (hf : Function.Injective f)
    (hredistribute :
      ∀ {p₁ p₂ : FiniteSupportRing (G := G) (K := L)},
        p₁ ≠ 0 → p₂ ≠ 0 →
          p₁ * p₂ ∈ Set.range (finiteSupportMap (G := G) f) →
            ∃ B : L,
              B ≠ 0 ∧
                p₁ * finiteSupportScalarHom (G := G) B ∈
                  Set.range (finiteSupportMap (G := G) f) ∧
                p₂ * finiteSupportScalarHom (G := G) B⁻¹ ∈
                  Set.range (finiteSupportMap (G := G) f))
    (hgcd : ∀ p q : FiniteSupportRing (G := G) (K := L),
      ∃ d : FiniteSupportRing (G := G) (K := L),
        ∀ e : FiniteSupportRing (G := G) (K := L),
          e ∣ p ∧ e ∣ q ↔ e ∣ d)
    (p : FiniteSupportRing (G := G) (K := K))
    (b c : FiniteSupportRing (G := G) (K := L))
    (hp : finiteSupportMap f p ∣ b * c) :
    ∃ p₁ p₂ : FiniteSupportRing (G := G) (K := K),
      p = p₁ * p₂ ∧
        finiteSupportMap f p₁ ∣ b ∧
        finiteSupportMap f p₂ ∣ c := by
  classical
  by_cases hpZero : p = 0
  · obtain ⟨q, hq⟩ := hp
    have hbc : b * c = 0 := by simpa [hpZero] using hq
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hbc with hb | hc
    · exact ⟨0, 1, by simp [hpZero], by simp [hb], by simp⟩
    · exact ⟨1, 0, by simp [hpZero], by simp, by simp [hc]⟩
  · letI : GCDMonoid (FiniteSupportRing (G := G) (K := L)) :=
      gcdMonoidOfExistsGCD hgcd
    obtain ⟨q₁, q₂, hq₁b, hq₂c, hpq⟩ :=
      exists_dvd_and_dvd_of_dvd_mul hp
    have hpImage : finiteSupportMap f p ≠ 0 :=
      (map_ne_zero_iff _ (finiteSupportMap_injective f hf)).mpr hpZero
    have hq₁ : q₁ ≠ 0 := by
      intro hzero
      apply hpImage
      simpa [hzero] using hpq
    have hq₂ : q₂ ≠ 0 := by
      intro hzero
      apply hpImage
      simpa [hzero] using hpq
    obtain ⟨B, hB, hleft, hright⟩ :=
      hredistribute hq₁ hq₂ ⟨p, hpq⟩
    obtain ⟨p₁, hp₁⟩ := hleft
    obtain ⟨p₂, hp₂⟩ := hright
    refine ⟨p₁, p₂, eq_mul_of_scalar_redistribution f hf B hB hpq hp₁ hp₂,
      map_dvd_of_eq_mul_scalar f B hB hp₁ hq₁b, ?_⟩
    simpa using map_dvd_of_eq_mul_scalar f B⁻¹ (inv_ne_zero hB) hp₂ hq₂c

end

end HahnSeries.Nonpositive
