/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.CoordinateChange
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.WeierstrassPreparation

/-!
# Polynomials with analytic-germ coefficients

Evaluation in the last coordinate maps `Polynomial (AnalyticGerm ℂ 0)` into the analytic germs on
the product with `ℂ`. Weierstrass polynomials are expressed using Mathlib's
`Polynomial.IsDistinguishedAt` at the coefficient ring's maximal ideal.

Polynomial injectivity is proved by restriction to the zero section and Horner induction.
Normalization of factors of distinguished polynomials (Lemma 1.8.2) is proved by reduction
modulo the maximal ideal. Irreducibility (Lemma 1.8.1(b)) is proved in `Weierstrass.lean`; the
coefficient bookkeeping behind Weierstrass division and preparation, and the resulting quotient
comparison (Lemma 1.8.1(a)), are in `CoefficientPolynomial.lean` and `Weierstrass.lean`. The
irreducibility statement explicitly excludes units in the analytic germ ring: without that
hypothesis the source's Lemma 1.8.1(b) fails, for example for `X - 1`.

## Main definitions

* `parameterHom`: Parameter germs pull back to the product by forgetting its last coordinate.
* `lastCoordinate`: The analytic germ of the last coordinate.
* `polynomialHom`: Evaluate a polynomial in the last coordinate, pulling back its coefficient germs.

## Main results

* `polynomialHom_injective`: Polynomial expressions in the last coordinate have unique coefficient
  germs.
* `isDistinguishedAt_iff`: Distinguished polynomials have precisely the usual Weierstrass
  coefficient conditions.
* `isDistinguishedAt_of_monic_dvd`: A monic divisor of a distinguished polynomial is distinguished.
* `exists_distinguished_factors`: Factors of a distinguished polynomial become distinguished after
  multiplying by reciprocal coefficient units (Lemma 1.8.2).
-/

public noncomputable section

namespace SeveralComplexVariables.AnalyticGerm

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Parameter germs pull back to the product by forgetting its last coordinate. -/
@[expose] def parameterHom : AnalyticGerm ℂ (0 : E) →ₐ[ℂ] AnalyticGerm ℂ (0 : E × ℂ) :=
  pullback (x := (0 : E × ℂ)) Prod.fst analyticAt_fst

/-- The analytic germ of the last coordinate. -/
@[expose] def lastCoordinate : AnalyticGerm ℂ (0 : E × ℂ) :=
  ofAnalyticAt Prod.snd analyticAt_snd

/-- Evaluate a polynomial in the last coordinate, pulling back its coefficient germs. -/
@[expose] def polynomialHom : Polynomial (AnalyticGerm ℂ (0 : E)) →+* AnalyticGerm ℂ (0 : E × ℂ) :=
  Polynomial.eval₂RingHom parameterHom.toRingHom lastCoordinate

/-- A constant polynomial gives the corresponding parameter germ on the product. -/
@[simp] theorem polynomialHom_C (a : AnalyticGerm ℂ (0 : E)) :
    polynomialHom (Polynomial.C a) = parameterHom a := by
  simp [polynomialHom]

/-- The indeterminate gives the last-coordinate germ. -/
@[simp] theorem polynomialHom_X :
    polynomialHom (Polynomial.X : Polynomial (AnalyticGerm ℂ (0 : E))) = lastCoordinate := by
  simp [polynomialHom]

/-- Distinguished polynomials have precisely the usual Weierstrass coefficient conditions. -/
theorem isDistinguishedAt_iff (p : Polynomial (AnalyticGerm ℂ (0 : E))) :
    p.IsDistinguishedAt (IsLocalRing.maximalIdeal _) ↔
      p.Monic ∧ ∀ i < p.natDegree, eval 0 (p.coeff i) = 0 := by
  constructor
  · intro h
    exact ⟨h.monic, fun i hi => (mem_maximalIdeal_iff _).mp (h.mem hi)⟩
  · rintro ⟨hm, h⟩
    exact ⟨⟨fun {i} hi => (mem_maximalIdeal_iff _).mpr (h i hi)⟩, hm⟩

/-- Restricting a polynomial germ to the zero section recovers its constant coefficient. -/
@[simp] theorem pullback_zeroSection_polynomialHom
    (p : Polynomial (AnalyticGerm ℂ (0 : E))) :
    pullback (fun z : E => (z, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
      (polynomialHom p) = p.coeff 0 := by
  have h : (pullback (fun z : E => (z, (0 : ℂ)))
      (analyticAt_id.prod analyticAt_const)).toRingHom.comp polynomialHom =
      Polynomial.constantCoeff := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨f, hf, rfl⟩ := exists_rep a
      change pullback (fun z : E => (z, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
        (polynomialHom (Polynomial.C (ofAnalyticAt f hf))) =
        (Polynomial.C (ofAnalyticAt f hf)).coeff 0
      rw [polynomialHom_C, Polynomial.coeff_C_zero]
      rfl
    · change pullback (fun z : E => (z, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
        (polynomialHom (Polynomial.X : Polynomial (AnalyticGerm ℂ (0 : E)))) =
          (Polynomial.X : Polynomial (AnalyticGerm ℂ (0 : E))).coeff 0
      rw [polynomialHom_X, Polynomial.coeff_X_zero]
      rfl
  exact DFunLike.congr_fun h p

/-- The distinguished coordinate is a nonzero germ, even with no parameter variables. -/
theorem lastCoordinate_ne_zero : (lastCoordinate (E := E)) ≠ 0 := by
  intro h
  have he : (Prod.snd : E × ℂ → ℂ) =ᶠ[𝓝 0] 0 :=
    Germ.coe_eq.mp (congrArg Subtype.val h)
  have ht : Tendsto (fun w : ℂ => ((0 : E), w)) (𝓝 0) (𝓝 0) :=
    continuous_const.prodMk continuous_id |>.tendsto 0
  have hi : (id : ℂ → ℂ) =ᶠ[𝓝 0] 0 := he.comp_tendsto ht
  exact one_ne_zero ((hasDerivAt_id (0 : ℂ)).congr_of_eventuallyEq hi.symm |>.unique
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)))

/-- Polynomial expressions in the last coordinate have unique coefficient germs. Restriction to the
zero section detects constants; Horner induction and cancellation of the nonzero last-coordinate
germ detect all remaining coefficients. -/
theorem polynomialHom_injective : Function.Injective (polynomialHom (E := E)) := by
  have hker : ∀ p : Polynomial (AnalyticGerm ℂ (0 : E)), polynomialHom p = 0 → p = 0 := by
    intro p
    induction p using Polynomial.recOnHorner with
    | M0 => exact fun _ => rfl
    | MC p a hp ha ih =>
      intro h
      have hc := congrArg (pullback (fun z : E => (z, (0 : ℂ)))
        (analyticAt_id.prod analyticAt_const)) h
      have : a = 0 := by
        simpa only [pullback_zeroSection_polynomialHom, map_zero,
          Polynomial.coeff_add, Polynomial.coeff_C_zero, hp, zero_add] using hc
      exact (ha this).elim
    | MX p hp ih =>
      intro h
      have hz : polynomialHom p = 0 :=
        (mul_eq_zero.mp (by simpa using h)).resolve_right lastCoordinate_ne_zero
      simp [ih hz]
  intro p q h
  have hz := hker (p - q) (by simp [h])
  exact sub_eq_zero.mp hz

/-- A monic divisor of a distinguished polynomial is distinguished. Reduction modulo the maximal
ideal makes it a monic divisor of a power of `X`, hence itself a power of `X`. -/
theorem isDistinguishedAt_of_monic_dvd {p w : Polynomial (AnalyticGerm ℂ (0 : E))}
    (hp : p.Monic) (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) (hd : p ∣ w) :
    p.IsDistinguishedAt (IsLocalRing.maximalIdeal _) := by
  classical
  let I := IsLocalRing.maximalIdeal (AnalyticGerm ℂ (0 : E))
  let π := Ideal.Quotient.mk I
  have hdiv : p.map π ∣ Polynomial.X ^ w.natDegree := by
    rw [← hw.map_eq_X_pow]
    exact Polynomial.map_dvd π hd
  obtain ⟨k, _, hk⟩ := (dvd_prime_pow Polynomial.prime_X w.natDegree).mp hdiv
  have he : p.map π = Polynomial.X ^ k :=
    Polynomial.eq_of_monic_of_associated (hp.map π) (Polynomial.monic_X_pow k) hk
  have hdeg : p.natDegree = k := by
    simpa only [hp.natDegree_map, Polynomial.natDegree_X_pow] using congrArg Polynomial.natDegree he
  refine ⟨⟨fun {j} hj => ?_⟩, hp⟩
  have hc := congrArg (fun r => Polynomial.coeff r j) he
  have hjk : j ≠ k := ne_of_lt (hdeg ▸ hj)
  have hz : π (p.coeff j) = 0 := by
    simpa only [Polynomial.coeff_map, Polynomial.coeff_X_pow, ite_eq_right hjk] using hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/-- Factors of a distinguished polynomial become distinguished after multiplying by reciprocal
coefficient units (Lemma 1.8.2). Normalize leading coefficients and use that monic divisors
remain distinguished after reduction modulo the maximal ideal. -/
theorem exists_distinguished_factors (p q : Polynomial (AnalyticGerm ℂ (0 : E)))
    (h : (p * q).IsDistinguishedAt (IsLocalRing.maximalIdeal _)) :
    ∃ u : (AnalyticGerm ℂ (0 : E))ˣ,
      (Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p).IsDistinguishedAt
        (IsLocalRing.maximalIdeal _) ∧
      (Polynomial.C (↑(u⁻¹) : AnalyticGerm ℂ (0 : E)) * q).IsDistinguishedAt
        (IsLocalRing.maximalIdeal _) := by
  have hlc : p.leadingCoeff * q.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul]
    exact h.monic
  let u : (AnalyticGerm ℂ (0 : E))ˣ :=
    ⟨q.leadingCoeff, p.leadingCoeff, by simpa only [mul_comm] using hlc, hlc⟩
  have hp : (Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one u.val_inv
  have hq : (Polynomial.C (↑(u⁻¹) : AnalyticGerm ℂ (0 : E)) * q).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one u.inv_val
  have he : (Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p) *
      (Polynomial.C (↑(u⁻¹) : AnalyticGerm ℂ (0 : E)) * q) = p * q := by
    calc
      _ = Polynomial.C (u : AnalyticGerm ℂ (0 : E)) *
          Polynomial.C (↑(u⁻¹) : AnalyticGerm ℂ (0 : E)) * (p * q) := by ring
      _ = _ := by rw [← Polynomial.C_mul]; simp
  refine ⟨u, isDistinguishedAt_of_monic_dvd hp h ?_,
    isDistinguishedAt_of_monic_dvd hq h ?_⟩
  · rw [← he]
    exact dvd_mul_right _ _
  · rw [← he]
    exact dvd_mul_left _ _

/-- The product of two distinguished polynomials is distinguished, of the sum of their degrees.
Reduction modulo the maximal ideal sends the product to a product of powers of `X`, hence to a
power of `X` of the total degree. -/
theorem isDistinguishedAt_mul {p q : Polynomial (AnalyticGerm ℂ (0 : E))}
    (hp : p.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (hq : q.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) :
    (p * q).IsDistinguishedAt (IsLocalRing.maximalIdeal _) := by
  have hpq : (p * q).Monic := hp.monic.mul hq.monic
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree := hp.monic.natDegree_mul hq.monic
  refine ⟨⟨fun {j} hj => ?_⟩, hpq⟩
  have he : (p * q).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AnalyticGerm ℂ (0 : E)))) =
      Polynomial.X ^ (p * q).natDegree := by
    rw [Polynomial.map_mul, hp.map_eq_X_pow, hq.map_eq_X_pow, hdeg, pow_add]
  have hc := congrArg (fun r => Polynomial.coeff r j) he
  have hz : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AnalyticGerm ℂ (0 : E))))
      ((p * q).coeff j)
      = 0 := by
    simpa only [Polynomial.coeff_map, Polynomial.coeff_X_pow, ite_eq_right hj.ne] using hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end SeveralComplexVariables.AnalyticGerm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
