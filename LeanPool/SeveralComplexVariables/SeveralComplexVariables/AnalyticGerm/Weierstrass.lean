/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.CoefficientPolynomial

/-!
# Weierstrass theorems in the germ ring

These interfaces express division and preparation directly in the analytic germ ring, using
ordinary polynomials over parameter germs and Mathlib's distinguished-polynomial predicate.
Polynomial degree (rather than natural degree) handles the zero remainder and degree-zero
divisors uniformly. Units are represented by the existing units group.

Existence and uniqueness of both division and preparation are proved by choosing analytic
representatives, applying the analytic Weierstrass theorems on any finite-dimensional parameter
space, and reassembling the polynomial coefficients using the bookkeeping in
`CoefficientPolynomial.lean`. Polynomial preservation under division (Lemma 1.8.1(a)) follows by
comparing ordinary Euclidean division of polynomials with germ division uniqueness. The
irreducibility equivalence is proved. Finite simultaneous preparation follows from the proved
finite normalization theorem and the existing analytic preparation theorem.

## Main results

* `existsUnique_division`: Division by a distinguished polynomial has a unique germ quotient and
  polynomial remainder of smaller degree.
* `existsUnique_preparation`: Preparation has a unique unit and distinguished polynomial of the
  prescribed order.
* `irreducible_polynomialHom_iff`: A distinguished polynomial is irreducible exactly when its
  analytic germ is.
* `prime_polynomialHom_of_isDistinguishedAt`: The image of a prime distinguished polynomial is
  itself prime.
* `exists_equiv_forall_isWeierstrassPreparationAt`: One coordinate system permits preparation of all
  members of a finite family.
-/

public noncomputable
section

open Filter
open scoped Topology

namespace SeveralComplexVariables
namespace AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Division by a distinguished polynomial has a unique germ quotient and polynomial remainder of
smaller degree. Choose representatives and apply analytic Weierstrass division, then identify
the germ quotient and coefficient germs by uniqueness. -/
theorem existsUnique_division [FiniteDimensional ℂ E]
    (w : Polynomial (AnalyticGerm ℂ (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) (f : AnalyticGerm ℂ (0 : E × ℂ)) :
    ∃! qr : AnalyticGerm ℂ (0 : E × ℂ) × Polynomial (AnalyticGerm ℂ (0 : E)),
      qr.2.degree < (w.natDegree : WithBot ℕ) ∧
      f = qr.1 * polynomialHom w + polynomialHom qr.2 := by
  set d := w.natDegree with hd_def
  obtain ⟨hwmon, hwcoeff0⟩ := (isDistinguishedAt_iff w).mp hw
  have hweq : w = ofCoefficients (fun j : Fin d => w.coeff (j : ℕ)) :=
    eq_ofCoefficients_of_monic hwmon hd_def
  choose a0 ha0 haeq using fun j : Fin d => exists_rep (w.coeff (j : ℕ))
  have ha00 : ∀ j : Fin d, a0 j 0 = 0 := by
    intro j
    have h0 := hwcoeff0 (j : ℕ) (hd_def ▸ j.isLt)
    rw [← haeq j, eval_ofAnalyticAt] at h0
    exact h0
  have hweq2 : w = ofCoefficients (fun j : Fin d => ofAnalyticAt (a0 j) (ha0 j)) := by
    rw [hweq]; congr 1; funext j; exact (haeq j).symm
  have hwhom : polynomialHom w = ofAnalyticAt (weierstrassPolynomial a0)
      (analyticAt_weierstrassPolynomial ha0) := by
    rw [hweq2]; exact polynomialHom_ofCoefficients a0 ha0
  have horder : analyticOrderAt (fun t : ℂ => weierstrassPolynomial a0 (0, t)) 0 = d := by
    have hcentral : (fun t : ℂ => weierstrassPolynomial a0 (0, t)) = fun t : ℂ => t ^ d :=
      funext (weierstrassPolynomial_central ha00)
    rw [hcentral]
    change analyticOrderAt ((id : ℂ → ℂ) ^ d) 0 = d
    rw [analyticOrderAt_pow (analyticAt_id (𝕜 := ℂ)) d, analyticOrderAt_id]; simp
  obtain ⟨f0, hf0, rfl⟩ := exists_rep f
  obtain ⟨q, a, Hdiv, huniqdiv⟩ :=
    exists_isWeierstrassDivisionAt_of_finiteDimensional
      (analyticAt_weierstrassPolynomial ha0) hf0 horder
  set r : Polynomial (AnalyticGerm ℂ (0 : E)) :=
    remainderOfCoefficients (fun j => ofAnalyticAt (a j) (Hdiv.analyticAt_coeff j)) with hr_def
  have hrdeg : r.degree < (d : WithBot ℕ) := degree_remainderOfCoefficients_lt _
  have hrhom : polynomialHom r = ofAnalyticAt (weierstrassRemainder a)
      (analyticAt_weierstrassRemainder Hdiv.analyticAt_coeff) :=
    polynomialHom_remainderOfCoefficients a Hdiv.analyticAt_coeff
  refine ⟨(ofAnalyticAt q Hdiv.analyticAt_quotient, r), ⟨hrdeg, ?_⟩, ?_⟩
  · have hgerm : ofAnalyticAt f0 hf0 = ofAnalyticAt q Hdiv.analyticAt_quotient *
        ofAnalyticAt (weierstrassPolynomial a0) (analyticAt_weierstrassPolynomial ha0) +
        ofAnalyticAt (weierstrassRemainder a)
          (analyticAt_weierstrassRemainder Hdiv.analyticAt_coeff) := by
      rw [← ofAnalyticAt_mul, ← ofAnalyticAt_add]
      exact ofAnalyticAt_eq_iff.mpr Hdiv.eq
    simp only
    rw [hgerm, hwhom, hrhom]
  · rintro ⟨q', r'⟩ ⟨hr'deg, hfeq⟩
    simp only at hr'deg hfeq ⊢
    have hr'eq : r' = remainderOfCoefficients (fun j : Fin d => r'.coeff (j : ℕ)) :=
      eq_remainderOfCoefficients_of_degree_lt hr'deg
    choose a' ha' haeq' using fun j : Fin d => exists_rep (r'.coeff (j : ℕ))
    have hr'eq2 : r' = remainderOfCoefficients (fun j : Fin d => ofAnalyticAt (a' j) (ha' j)) := by
      rw [hr'eq]; congr 1; funext j; exact (haeq' j).symm
    have hr'hom : polynomialHom r' = ofAnalyticAt (weierstrassRemainder a')
        (analyticAt_weierstrassRemainder ha') := by
      rw [hr'eq2]; exact polynomialHom_remainderOfCoefficients a' ha'
    obtain ⟨q0', hq0', hq0'eq⟩ := exists_rep q'
    have Hdiv' : IsWeierstrassDivisionAt (weierstrassPolynomial a0) f0 q0' a' := by
      refine ⟨hq0', ha', ?_⟩
      have hgerm : ofAnalyticAt f0 hf0 = ofAnalyticAt q0' hq0' *
          ofAnalyticAt (weierstrassPolynomial a0) (analyticAt_weierstrassPolynomial ha0) +
          ofAnalyticAt (weierstrassRemainder a') (analyticAt_weierstrassRemainder ha') := by
        rw [hq0'eq, ← hwhom, ← hr'hom]; exact hfeq
      exact (ofAnalyticAt_eq_iff (hg := (hq0'.mul (analyticAt_weierstrassPolynomial ha0)).add
        (analyticAt_weierstrassRemainder ha'))).mp hgerm
    obtain ⟨hqeqq0', haeqa'⟩ := huniqdiv q0' a' Hdiv'
    have hqeq : ofAnalyticAt q Hdiv.analyticAt_quotient = q' := by
      rw [(ofAnalyticAt_eq_iff (hg := hq0')).mpr hqeqq0', hq0'eq]
    have hreq : r = r' := by
      rw [hr_def, hr'eq2]
      congr 1
      funext j
      exact ofAnalyticAt_eq_iff.mpr (haeqa' j)
    rw [Prod.mk.injEq]
    exact ⟨hqeq.symm, hreq.symm⟩

/-- Preparation has a unique unit and distinguished polynomial of the prescribed order. Order zero
gives polynomial one. The proof converts the analytic preparation and uniqueness theorems into
polynomial and unit equalities in the germ ring. -/
theorem existsUnique_preparation [FiniteDimensional ℂ E]
    (f : AnalyticGerm ℂ (0 : E × ℂ)) {d : ℕ} (hd : orderInLastVariable f = d) :
    ∃! up : (AnalyticGerm ℂ (0 : E × ℂ))ˣ × Polynomial (AnalyticGerm ℂ (0 : E)),
      up.2.IsDistinguishedAt (IsLocalRing.maximalIdeal _) ∧ up.2.natDegree = d ∧
      f = ↑up.1 * polynomialHom up.2 := by
  obtain ⟨f0, hf0, rfl⟩ := exists_rep f
  rw [orderInLastVariable_ofAnalyticAt] at hd
  obtain ⟨u, a, H, huniq⟩ := exists_isWeierstrassPreparationAt_of_finiteDimensional hf0 hd
  obtain ⟨hunit, hfact⟩ := H.germ_factorization hf0
  set w : Polynomial (AnalyticGerm ℂ (0 : E)) :=
    ofCoefficients (fun j => ofAnalyticAt (a j) (H.analyticAt_coeff j)) with hw_def
  have hwdist : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _) :=
    isDistinguishedAt_ofCoefficients _ (fun j => by
      rw [eval_ofAnalyticAt]; exact H.coeff_zero j)
  have hwdeg : w.natDegree = d := natDegree_ofCoefficients _
  have hwhom : polynomialHom w = ofAnalyticAt (weierstrassPolynomial a)
      (analyticAt_weierstrassPolynomial H.analyticAt_coeff) :=
    polynomialHom_ofCoefficients a H.analyticAt_coeff
  refine ⟨(hunit.unit, w), ⟨hwdist, hwdeg, ?_⟩, ?_⟩
  · rw [hunit.unit_spec, hwhom]; exact hfact
  · rintro ⟨u', w'⟩ ⟨hw'dist, hw'deg, hfeq⟩
    simp only at hw'dist hw'deg hfeq ⊢
    obtain ⟨hw'mon, hw'coeff0⟩ := (isDistinguishedAt_iff w').mp hw'dist
    have hw'eq : w' = ofCoefficients (fun j : Fin d => w'.coeff (j : ℕ)) :=
      eq_ofCoefficients_of_monic hw'mon hw'deg
    choose a' ha' haeq using fun j : Fin d => exists_rep (w'.coeff (j : ℕ))
    obtain ⟨v0, hv0, hveq⟩ := exists_rep (↑u' : AnalyticGerm ℂ (0 : E × ℂ))
    have hv0ne : v0 0 ≠ 0 := by
      have hu' := (isUnit_iff (↑u' : AnalyticGerm ℂ (0 : E × ℂ))).mp u'.isUnit
      rwa [← hveq, eval_ofAnalyticAt] at hu'
    have ha'0 : ∀ j : Fin d, a' j 0 = 0 := by
      intro j
      have hlt : (j : ℕ) < w'.natDegree := by rw [hw'deg]; exact j.isLt
      have h0 := hw'coeff0 (j : ℕ) hlt
      rw [← haeq j, eval_ofAnalyticAt] at h0
      exact h0
    have hw'eq2 : w' = ofCoefficients (fun j : Fin d => ofAnalyticAt (a' j) (ha' j)) := by
      rw [hw'eq]; congr 1; funext j; exact (haeq j).symm
    have Hprep' : IsWeierstrassPreparationAt f0 v0 a' := by
      refine ⟨hv0, hv0ne, ha', ha'0, ?_⟩
      have hgerm : ofAnalyticAt f0 hf0 = ofAnalyticAt (v0 * weierstrassPolynomial a')
          (hv0.mul (analyticAt_weierstrassPolynomial ha')) := by
        rw [hfeq, ← hveq, hw'eq2, polynomialHom_ofCoefficients, ← ofAnalyticAt_mul]
      exact ofAnalyticAt_eq_iff.mp hgerm
    obtain ⟨hueqv0, haeqa'⟩ := huniq v0 a' Hprep'
    have hueq : hunit.unit = u' := Units.ext (by
      rw [hunit.unit_spec, (ofAnalyticAt_eq_iff (hg := hv0)).mpr hueqv0, hveq])
    have hweq : w = w' := by
      rw [hw_def, hw'eq2]
      congr 1
      funext j
      exact ofAnalyticAt_eq_iff.mpr (haeqa' j)
    rw [Prod.mk.injEq]
    exact ⟨hueq.symm, hweq.symm⟩

/-- Division by a distinguished polynomial preserves polynomial germs (Lemma 1.8.1(a)). The
Euclidean remainder of ordinary polynomial division by the monic divisor gives a second
decomposition; germ division uniqueness identifies it with the hypothesised one. -/
theorem exists_polynomial_quotient [FiniteDimensional ℂ E]
    (p w : Polynomial (AnalyticGerm ℂ (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (g : AnalyticGerm ℂ (0 : E × ℂ)) (h : polynomialHom p = g * polynomialHom w) :
    ∃ q : Polynomial (AnalyticGerm ℂ (0 : E)), polynomialHom q = g := by
  have hwne : w ≠ 0 := hw.monic.ne_zero
  have hrdeg : (p %ₘ w).degree < (w.natDegree : WithBot ℕ) := by
    rw [← Polynomial.degree_eq_natDegree hwne]
    exact Polynomial.degree_modByMonic_lt p hw.monic
  have hpeq : polynomialHom p = polynomialHom (p /ₘ w) * polynomialHom w +
      polynomialHom (p %ₘ w) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p w]
    rw [map_add, map_mul]
    ring
  have hveq : polynomialHom p = g * polynomialHom w +
      polynomialHom (0 : Polynomial (AnalyticGerm ℂ (0 : E))) := by simp [h]
  have hzerodeg : (0 : Polynomial (AnalyticGerm ℂ (0 : E))).degree < (w.natDegree : WithBot ℕ) := by
    rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe w.natDegree
  have hp1 : (p %ₘ w).degree < (w.natDegree : WithBot ℕ) ∧
      polynomialHom p = polynomialHom (p /ₘ w) * polynomialHom w + polynomialHom (p %ₘ w) :=
    ⟨hrdeg, hpeq⟩
  have hp2 : (0 : Polynomial (AnalyticGerm ℂ (0 : E))).degree < (w.natDegree : WithBot ℕ) ∧
      polynomialHom p = g * polynomialHom w +
        polynomialHom (0 : Polynomial (AnalyticGerm ℂ (0 : E))) :=
    ⟨hzerodeg, hveq⟩
  obtain ⟨y, _, huniq⟩ := existsUnique_division w hw (polynomialHom p)
  have h1 := huniq (polynomialHom (p /ₘ w), p %ₘ w) hp1
  have h2 := huniq (g, 0) hp2
  exact ⟨p /ₘ w, (Prod.mk.injEq ..).mp (h1.trans h2.symm) |>.1⟩

/-- If the numerator in a distinguished division is polynomial, so is the quotient. This applies
with a nonzero remainder as well as to exact divisibility. -/
theorem exists_polynomial_division_quotient [FiniteDimensional ℂ E]
    (p w r : Polynomial (AnalyticGerm ℂ (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _))
    (q : AnalyticGerm ℂ (0 : E × ℂ))
    (h : polynomialHom p = q * polynomialHom w + polynomialHom r) :
    ∃ s : Polynomial (AnalyticGerm ℂ (0 : E)), polynomialHom s = q := by
  apply exists_polynomial_quotient (p - r) w hw q
  rw [map_sub, h, add_sub_cancel_right]

/-- A distinguished polynomial of positive degree that is irreducible has irreducible image. Any
factorization of the image has orders adding to the degree; a factor of positive order would
prepare to a nonunit distinguished polynomial, and comparing the resulting polynomial
factorization of `w` with irreducibility of `w` forces the other factor to be a unit,
contradicting positivity of both orders. -/
theorem irreducible_polynomialHom_of_isDistinguishedAt [FiniteDimensional ℂ E]
    {w : Polynomial (AnalyticGerm ℂ (0 : E))}
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) (hd : w.natDegree ≠ 0)
    (hirr : Irreducible w) : Irreducible (polynomialHom w) := by
  have hworder : orderInLastVariable (polynomialHom w) = (w.natDegree : ℕ∞) :=
    orderInLastVariable_polynomialHom_of_isDistinguishedAt hw
  constructor
  · rw [isUnit_iff_orderInLastVariable_eq_zero, hworder]
    exact_mod_cast hd
  · intro A B hAB
    have horder : orderInLastVariable A + orderInLastVariable B = (w.natDegree : ℕ∞) := by
      rw [← orderInLastVariable_mul, ← hAB, hworder]
    rcases eq_or_ne (orderInLastVariable A) 0 with hA0 | hA0
    · exact Or.inl ((isUnit_iff_orderInLastVariable_eq_zero A).mpr hA0)
    rcases eq_or_ne (orderInLastVariable B) 0 with hB0 | hB0
    · exact Or.inr ((isUnit_iff_orderInLastVariable_eq_zero B).mpr hB0)
    exfalso
    have hAfin : orderInLastVariable A ≠ ⊤ := by
      intro h; rw [h] at horder; simp at horder
    have hBfin : orderInLastVariable B ≠ ⊤ := by
      intro h; rw [h] at horder; simp at horder
    lift orderInLastVariable A to ℕ using hAfin with dA hdA
    lift orderInLastVariable B to ℕ using hBfin with dB hdB
    have hdA0 : dA ≠ 0 := by exact_mod_cast hA0
    have hdB0 : dB ≠ 0 := by exact_mod_cast hB0
    obtain ⟨⟨uA, wA⟩, ⟨hwAdist, hwAdeg, hAeq⟩, -⟩ := existsUnique_preparation A hdA.symm
    obtain ⟨⟨uB, wB⟩, ⟨hwBdist, hwBdeg, hBeq⟩, -⟩ := existsUnique_preparation B hdB.symm
    simp only at hwAdist hwAdeg hAeq hwBdist hwBdeg hBeq
    have heq2 : polynomialHom w = ((uA : AnalyticGerm ℂ (0 : E × ℂ)) * uB) *
        polynomialHom (wA * wB) := by
      rw [hAB, hAeq, hBeq, map_mul]; ring
    obtain ⟨q, hq⟩ := exists_polynomial_quotient w (wA * wB) (isDistinguishedAt_mul hwAdist hwBdist)
      ((uA : AnalyticGerm ℂ (0 : E × ℂ)) * uB) heq2
    have heq3 : w = (q * wA) * wB := by
      apply polynomialHom_injective
      rw [heq2, ← hq]
      simp only [map_mul]
      ring
    have hwAnu : ¬ IsUnit wA := fun h =>
      hdA0 (by rw [← hwAdeg]; exact Polynomial.natDegree_eq_zero_of_isUnit h)
    have hwBnu : ¬ IsUnit wB := fun h =>
      hdB0 (by rw [← hwBdeg]; exact Polynomial.natDegree_eq_zero_of_isUnit h)
    rcases hirr.isUnit_or_isUnit heq3 with hqwA | hwBu
    · exact hwAnu (isUnit_of_mul_isUnit_right hqwA)
    · exact hwBnu hwBu

/-- A distinguished polynomial is irreducible exactly when its analytic germ is. Degree zero is
allowed: `w = 1` and both sides are then false. Positive degree splits into the forward
direction above and, for the converse, comparing a germ factorization against a distinguished
normalization (Lemma 1.8.2) of any polynomial factorization. -/
theorem irreducible_polynomialHom_iff [FiniteDimensional ℂ E]
    (w : Polynomial (AnalyticGerm ℂ (0 : E)))
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) :
    Irreducible (polynomialHom w) ↔ Irreducible w := by
  rcases eq_or_ne w.natDegree 0 with hd0 | hd0
  · have hw1 : w = 1 := Polynomial.eq_one_of_monic_natDegree_zero hw.monic hd0
    subst hw1
    simp only [map_one]
    exact ⟨fun h => absurd isUnit_one h.not_isUnit, fun h => absurd isUnit_one h.not_isUnit⟩
  · refine ⟨fun hirrHom => ⟨fun hu => hirrHom.not_isUnit (hu.map (polynomialHom (E := E))),
      fun p q hpq => ?_⟩, fun hirr => irreducible_polynomialHom_of_isDistinguishedAt hw hd0 hirr⟩
    obtain ⟨u, hup, huq⟩ := exists_distinguished_factors p q (hpq ▸ hw)
    have hp'q' : Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p *
        (Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) * q) = w := by
      rw [hpq]
      calc
        _ = Polynomial.C (u : AnalyticGerm ℂ (0 : E)) *
            Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) * (p * q) := by ring
        _ = _ := by rw [← Polynomial.C_mul]; simp
    have hhom : polynomialHom w = polynomialHom (Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p) *
        polynomialHom (Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) * q) := by
      rw [← map_mul, hp'q']
    rcases hirrHom.isUnit_or_isUnit hhom with h1 | h2
    · left
      have hord : orderInLastVariable
          (polynomialHom (Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p)) = 0 :=
        (isUnit_iff_orderInLastVariable_eq_zero _).mp h1
      rw [orderInLastVariable_polynomialHom_of_isDistinguishedAt hup] at hord
      have hdeg0 : (Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p).natDegree = 0 := by
        exact_mod_cast hord
      have h1' : Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * p = 1 :=
        Polynomial.eq_one_of_monic_natDegree_zero hup.monic hdeg0
      have hp1 : p = Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) := by
        have hc := congrArg (fun r => Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) * r) h1'
        simpa [← mul_assoc, ← Polynomial.C_mul] using hc
      rw [hp1]
      exact Polynomial.isUnit_C.mpr u⁻¹.isUnit
    · right
      have hord : orderInLastVariable
          (polynomialHom (Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) * q)) = 0 :=
        (isUnit_iff_orderInLastVariable_eq_zero _).mp h2
      rw [orderInLastVariable_polynomialHom_of_isDistinguishedAt huq] at hord
      have hdeg0 : (Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) * q).natDegree = 0 := by
        exact_mod_cast hord
      have h2' : Polynomial.C (↑u⁻¹ : AnalyticGerm ℂ (0 : E)) * q = 1 :=
        Polynomial.eq_one_of_monic_natDegree_zero huq.monic hdeg0
      have hq1 : q = Polynomial.C (u : AnalyticGerm ℂ (0 : E)) := by
        have hc := congrArg (fun r => Polynomial.C (u : AnalyticGerm ℂ (0 : E)) * r) h2'
        simpa [← mul_assoc, ← Polynomial.C_mul] using hc
      rw [hq1]
      exact Polynomial.isUnit_C.mpr u.isUnit

/-- A common factor of two germs that is the image of a prime distinguished polynomial divides one
of them: Weierstrass-divide each factor, reduce the product of the two polynomial remainders by
ordinary division against the distinguishing polynomial, and match the resulting decomposition
of the germ product against germ division uniqueness to reduce to primality of the
distinguishing polynomial itself. -/
theorem dvd_or_dvd_of_isDistinguishedAt [FiniteDimensional ℂ E]
    {w : Polynomial (AnalyticGerm ℂ (0 : E))}
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) (hwp : Prime w)
    {f g : AnalyticGerm ℂ (0 : E × ℂ)} (hfg : polynomialHom w ∣ f * g) :
    polynomialHom w ∣ f ∨ polynomialHom w ∣ g := by
  obtain ⟨⟨qf, rf⟩, ⟨hrfdeg, hfeq⟩, -⟩ := existsUnique_division w hw f
  obtain ⟨⟨qg, rg⟩, ⟨hrgdeg, hgeq⟩, -⟩ := existsUnique_division w hw g
  simp only at hrfdeg hfeq hrgdeg hgeq
  have hr0eq : rf * rg = (rf * rg) %ₘ w + w * ((rf * rg) /ₘ w) :=
    (Polynomial.modByMonic_add_div (rf * rg) w).symm
  have hr0deg : ((rf * rg) %ₘ w).degree < (w.natDegree : WithBot ℕ) := by
    rw [← Polynomial.degree_eq_natDegree hw.monic.ne_zero]
    exact Polynomial.degree_modByMonic_lt (rf * rg) hw.monic
  set bigC : AnalyticGerm ℂ (0 : E × ℂ) :=
    qf * qg * polynomialHom w + qf * polynomialHom rg + qg * polynomialHom rf +
      polynomialHom ((rf * rg) /ₘ w) with hbigC_def
  have hfg2 : f * g = bigC * polynomialHom w + polynomialHom ((rf * rg) %ₘ w) := by
    have hmul : polynomialHom rf * polynomialHom rg = polynomialHom (rf * rg) :=
      (map_mul polynomialHom rf rg).symm
    have hM : polynomialHom (rf * rg) = polynomialHom ((rf * rg) %ₘ w) +
        polynomialHom w * polynomialHom ((rf * rg) /ₘ w) := by
      conv_lhs => rw [hr0eq]
      rw [map_add, map_mul]
    rw [hbigC_def, hfeq, hgeq]
    rw [show (qf * polynomialHom w + polynomialHom rf) * (qg * polynomialHom w +
        polynomialHom rg) = qf * qg * polynomialHom w * polynomialHom w +
          qf * polynomialHom w * polynomialHom rg + polynomialHom rf * qg * polynomialHom w +
            polynomialHom rf * polynomialHom rg from by ring]
    rw [hmul, hM]; ring
  obtain ⟨c, hc⟩ := hfg
  obtain ⟨⟨qfg, rfg⟩, ⟨hrfgdeg, hfgeq⟩, huniqfg⟩ := existsUnique_division w hw (f * g)
  simp only at hrfgdeg hfgeq huniqfg
  have hzerodeg : (0 : Polynomial (AnalyticGerm ℂ (0 : E))).degree < (w.natDegree : WithBot ℕ) := by
    rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe w.natDegree
  have hceq : f * g = c * polynomialHom w + polynomialHom (0 : Polynomial (AnalyticGerm ℂ (0 : E)))
    := by
    rw [hc, map_zero, add_zero]; ring
  have heq1 := huniqfg (bigC, (rf * rg) %ₘ w) ⟨hr0deg, hfg2⟩
  have heq2 := huniqfg (c, 0) ⟨hzerodeg, hceq⟩
  have hr0 : (rf * rg) %ₘ w = 0 := ((Prod.mk.injEq ..).mp (heq1.trans heq2.symm)).2
  have hwdvd : w ∣ rf * rg := ⟨(rf * rg) /ₘ w, hr0eq.trans (by rw [hr0, zero_add])⟩
  rcases hwp.2.2 rf rg hwdvd with hwrf | hwrg
  · obtain ⟨c0, hc0⟩ := hwrf
    refine Or.inl ⟨qf + polynomialHom c0, ?_⟩
    rw [hfeq, hc0, map_mul]; ring
  · obtain ⟨c0, hc0⟩ := hwrg
    refine Or.inr ⟨qg + polynomialHom c0, ?_⟩
    rw [hgeq, hc0, map_mul]; ring

/-- The image of a prime distinguished polynomial is itself prime. Non-vanishing and
non-invertibility come from irreducibility of the image; the dividing property comes from
`dvd_or_dvd_of_isDistinguishedAt`. -/
theorem prime_polynomialHom_of_isDistinguishedAt [FiniteDimensional ℂ E]
    {w : Polynomial (AnalyticGerm ℂ (0 : E))}
    (hw : w.IsDistinguishedAt (IsLocalRing.maximalIdeal _)) (hwp : Prime w) :
    Prime (polynomialHom w) := by
  have hd0 : w.natDegree ≠ 0 := fun h0 =>
    hwp.not_isUnit (Polynomial.eq_one_of_monic_natDegree_zero hw.monic h0 ▸ isUnit_one)
  have hpolyirr : Irreducible (polynomialHom w) :=
    irreducible_polynomialHom_of_isDistinguishedAt hw hd0 hwp.irreducible
  exact ⟨hpolyirr.ne_zero, hpolyirr.not_isUnit, fun f g => dvd_or_dvd_of_isDistinguishedAt hw hwp⟩

end AnalyticGerm

/-- One coordinate system permits preparation of all members of a finite family. This depends on the
preparation theorem and hence on analytic division. Empty parameter types, empty families, and
unit germs are all included. -/
theorem exists_equiv_forall_isWeierstrassPreparationAt {ι κ : Type*} [Fintype ι] [Finite κ]
    {f : κ → (ι → ℂ) × ℂ → ℂ} (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hne : ∀ i, ¬ f i =ᶠ[𝓝 0] 0) :
    ∃ (L : ((ι → ℂ) × ℂ) ≃L[ℂ] ((ι → ℂ) × ℂ)) (d : κ → ℕ), ∀ i,
      ∃ (u : (ι → ℂ) × ℂ → ℂ) (a : Fin (d i) → (ι → ℂ) → ℂ),
        IsWeierstrassPreparationAt (fun z => f i (L z)) u a := by
  classical
  let := Fintype.ofFinite κ
  obtain ⟨L, d, hd⟩ := exists_regular_coordinate_change_finite hf hne
  refine ⟨L, d, fun i => ?_⟩
  have ha : AnalyticAt ℂ (fun z => f i (L z)) 0 :=
    (hf i).comp_of_eq (L.toContinuousLinearMap.analyticAt 0) L.map_zero
  obtain ⟨u, a, h, _⟩ := exists_isWeierstrassPreparationAt ha (hd i)
  exact ⟨u, a, h⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
