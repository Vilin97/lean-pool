/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.GenericFiber
import LeanPool.LocalComplexGeometry.Nullstellensatz.QuotientPolynomialSpecialization
import LeanPool.LocalComplexGeometry.Nullstellensatz.ResultantSpecialization
import LeanPool.LocalComplexGeometry.Germs.Representatives

/-!
# A nonvanishing resultant for the cleared generic minimal polynomial

The denominator-cleared minimal polynomial is generally not monic over the
base germ ring.  Its leading coefficient and its fixed-size derivative
resultant nevertheless stay outside the contracted prime.  Consequently,
away from one analytic exceptional factor, its complex specializations keep
their generic degree and have only simple roots.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

section Prime

variable {n : ℕ} (P : Ideal (HolomorphicGerm (n + 1))) [P.IsPrime]

/-- The chosen representative family of all coefficients of a polynomial up
to its exact natural degree. -/
def polynomialCoefficientRepresentatives
    (Q : Polynomial (HolomorphicGerm n)) :
    Fin (Q.natDegree + 1) → ComplexEuclidean n → ℂ :=
  fun i ↦ HolomorphicGerm.representative (Q.coeff (i : ℕ))

theorem analyticAt_polynomialCoefficientRepresentatives
    (Q : Polynomial (HolomorphicGerm n)) (i : Fin (Q.natDegree + 1)) :
    AnalyticAt ℂ (polynomialCoefficientRepresentatives Q i) 0 :=
  HolomorphicGerm.analyticAt_representative (Q.coeff (i : ℕ))

/-- Reassembling the coefficient germs used by
`polynomialCoefficientRepresentatives` recovers the original polynomial. -/
theorem fixedDegreePolynomial_coeff_polynomial (Q : Polynomial (HolomorphicGerm n)) :
    fixedDegreePolynomial
        (fun i : Fin (Q.natDegree + 1) ↦ Q.coeff (i : ℕ)) = Q :=
  fixedDegreePolynomial_coefficients_eq Q le_rfl

/-- The chosen analytic representative of the algebraic derivative
resultant agrees near the origin with the pointwise fixed-size resultant of
the chosen coefficient representatives. -/
theorem eventually_genericMinpolyLift_resultant_representative {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    let e := c.polynomial.natDegree
    let Δ := Polynomial.resultant c.polynomial c.polynomial.derivative e (e - 1)
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      HolomorphicGerm.representative Δ z =
        Polynomial.resultant
          (fixedDegreePolynomialAt
            (polynomialCoefficientRepresentatives c.polynomial) z)
          (fixedDegreePolynomialAt
            (polynomialCoefficientRepresentatives c.polynomial) z).derivative
          e (e - 1) := by
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let Q := c.polynomial
  let e := Q.natDegree
  let q : Fin (e + 1) → ComplexEuclidean n → ℂ :=
    polynomialCoefficientRepresentatives Q
  have hq : ∀ i, AnalyticAt ℂ (q i) 0 :=
    analyticAt_polynomialCoefficientRepresentatives Q
  obtain ⟨Δfun, hΔfun, hΔpoint⟩ :=
    exists_analytic_resultant_derivative c.natDegree_pos q hq
  let Δ : HolomorphicGerm n :=
    Polynomial.resultant Q Q.derivative e (e - 1)
  let qg : Fin (e + 1) → HolomorphicGerm n :=
    fun i ↦ Q.coeff (i : ℕ)
  let A : Polynomial (ComplexEuclidean n → ℂ) :=
    fixedDegreePolynomial q
  let Rfun : ComplexEuclidean n → ℂ :=
    Polynomial.resultant A A.derivative e (e - 1)
  let ρ : HolomorphicGerm n →+* FunctionGerm n :=
    (holomorphicGermSubring n).subtype
  let γ : (ComplexEuclidean n → ℂ) →+* FunctionGerm n :=
    Filter.Germ.coeRingHom (nhds (0 : ComplexEuclidean n))
  have hQcoeff : fixedDegreePolynomial qg = Q := by
    exact fixedDegreePolynomial_coefficients_eq Q le_rfl
  have hAmap : Q.map ρ = A.map γ := by
    rw [← hQcoeff]
    simp only [fixedDegreePolynomial_map]
    rw [show A.map γ = fixedDegreePolynomial (fun i ↦ γ (q i)) by
      simp only [A, fixedDegreePolynomial_map]]
    apply congrArg fixedDegreePolynomial
    funext i
    change (Q.coeff (i : ℕ) : FunctionGerm n) =
      (HolomorphicGerm.representative (Q.coeff (i : ℕ)) : FunctionGerm n)
    exact (HolomorphicGerm.coe_representative (Q.coeff (i : ℕ))).symm
  have hderivemap : Q.derivative.map ρ = A.derivative.map γ := by
    rw [← Polynomial.derivative_map, ← Polynomial.derivative_map, hAmap]
  have hresMap : ρ Δ = γ Rfun := by
    calc
      ρ Δ = Polynomial.resultant (Q.map ρ) (Q.derivative.map ρ)
          e (e - 1) :=
        (Polynomial.resultant_map_map Q Q.derivative e (e - 1) ρ).symm
      _ = Polynomial.resultant (A.map γ) (A.derivative.map γ)
          e (e - 1) := by rw [hAmap, hderivemap]
      _ = γ Rfun :=
        Polynomial.resultant_map_map A A.derivative e (e - 1) γ
  have hpointfun :
      (fun z ↦ Polynomial.resultant
          (fixedDegreePolynomialAt q z)
          (fixedDegreePolynomialAt q z).derivative e (e - 1)) = Rfun := by
    funext z
    change Polynomial.resultant
        (fixedDegreePolynomialAt q z)
        (fixedDegreePolynomialAt q z).derivative e (e - 1) =
      (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z) Rfun
    rw [← Polynomial.resultant_map_map]
    change Polynomial.resultant
        (fixedDegreePolynomialAt q z)
        (fixedDegreePolynomialAt q z).derivative e (e - 1) =
      Polynomial.resultant
        (A.map (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z))
        (A.derivative.map
          (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z)) e (e - 1)
    rw [← Polynomial.derivative_map]
    rw [show A.map (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z) =
      fixedDegreePolynomialAt q z by simp only [A, fixedDegreePolynomial_map_eval]]
  have hΔgerm : HolomorphicGerm.ofFunction Δfun hΔfun = Δ := by
    apply Subtype.ext
    change (Δfun : FunctionGerm n) = (Δ : FunctionGerm n)
    have hfun : (Δfun : FunctionGerm n) = (Rfun : FunctionGerm n) := by
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hΔpoint] with z hz
      rw [hz]
      exact congrFun hpointfun z
    exact hfun.trans hresMap.symm
  have hrep :
      (HolomorphicGerm.representative Δ : FunctionGerm n) =
        (Δfun : FunctionGerm n) :=
    (HolomorphicGerm.coe_representative Δ).trans
      (congrArg (fun x : HolomorphicGerm n ↦ (x : FunctionGerm n))
        hΔgerm.symm)
  filter_upwards [Filter.Germ.coe_eq.mp hrep, hΔpoint] with z hzrep hzpoint
  exact hzrep.trans hzpoint

/-- The resultant representative theorem in the common
`germPolynomialRepresentativeAt` notation used by quotient specialization. -/
theorem eventually_genericMinpolyLift_resultant_germPolynomialRepresentativeAt
    {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    let e := c.polynomial.natDegree
    let Δ := Polynomial.resultant c.polynomial c.polynomial.derivative e (e - 1)
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      HolomorphicGerm.representative Δ z =
        Polynomial.resultant
          (germPolynomialRepresentativeAt e c.polynomial z)
          (germPolynomialRepresentativeAt e c.polynomial z).derivative
          e (e - 1) := by
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let Q := c.polynomial
  let e := Q.natDegree
  let Δ := Polynomial.resultant Q Q.derivative e (e - 1)
  have hresultant := eventually_genericMinpolyLift_resultant_representative
    P a ha ha0 hmem
  filter_upwards [hresultant] with z hz
  change HolomorphicGerm.representative Δ z =
    Polynomial.resultant (germPolynomialRepresentativeAt e Q z)
      (germPolynomialRepresentativeAt e Q z).derivative e (e - 1)
  change HolomorphicGerm.representative Δ z =
    Polynomial.resultant
      (fixedDegreePolynomialAt (polynomialCoefficientRepresentatives Q) z)
      (fixedDegreePolynomialAt
        (polynomialCoefficientRepresentatives Q) z).derivative e (e - 1) at hz
  have hfamilies : polynomialCoefficientRepresentatives Q =
      germPolynomialCoefficientRepresentatives (m := e) Q := rfl
  unfold germPolynomialRepresentativeAt
  rw [← hfamilies]
  exact hz

/-- Off the leading-coefficient and derivative-resultant exceptional loci,
the lifted minimal-polynomial specialization keeps its exact positive degree
and is separable. -/
theorem eventually_genericMinpolyLift_natDegree_eq_and_separable
    {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    let e := c.polynomial.natDegree
    let Δ := Polynomial.resultant c.polynomial c.polynomial.derivative e (e - 1)
    ∀ᶠ z in nhds (0 : ComplexEuclidean n),
      HolomorphicGerm.representative c.polynomial.leadingCoeff z ≠ 0 →
      HolomorphicGerm.representative Δ z ≠ 0 →
        (germPolynomialRepresentativeAt e c.polynomial z).natDegree = e ∧
          (germPolynomialRepresentativeAt e c.polynomial z).Separable := by
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let Q := c.polynomial
  let e := Q.natDegree
  let Δ := Polynomial.resultant Q Q.derivative e (e - 1)
  have hresultant :=
    eventually_genericMinpolyLift_resultant_germPolynomialRepresentativeAt
      P a ha ha0 hmem
  filter_upwards [hresultant] with z hres
  intro hlead hΔ
  let A := germPolynomialCoefficientRepresentatives (m := e) Q
  have htop : A ⟨e, Nat.lt_succ_self e⟩ z ≠ 0 := by
    simpa only [A, germPolynomialCoefficientRepresentatives,
      Polynomial.leadingCoeff, e, Q] using hlead
  have hdegree : (germPolynomialRepresentativeAt e Q z).natDegree = e := by
    exact fixedDegreePolynomialAt_natDegree_eq A z htop
  refine ⟨hdegree, ?_⟩
  apply
    fixedDegreePolynomialAt_separable_of_top_ne_zero_of_resultant_derivative_ne_zero
      c.natDegree_pos A z htop
  change Polynomial.resultant
      (germPolynomialRepresentativeAt e Q z)
      (germPolynomialRepresentativeAt e Q z).derivative e (e - 1) ≠ 0
  rw [← hres]
  exact hΔ

end Prime

end

end LocalComplexGeometry
