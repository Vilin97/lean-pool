/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/

import LeanPool.PythagoreanPolynomialParametrization.Basic

/-! # Integer-coefficient obstruction

This file contains the paper's impossibility result for a single triple of
integer-coefficient polynomials.
-/

namespace LeanPool.PythagoreanPolynomialParametrization

private lemma intPolyParametrizes_hits {n : ℕ} {f g h : IntPoly n} {x y z : ℤ}
    (hp : IntPolyParametrizes f g h pythagoreanTriples)
    (hxyz : IsPythagoreanTriple x y z) :
    ∃ a : Fin n → ℤ,
      intPolyEval f a = x ∧ intPolyEval g a = y ∧ intPolyEval h a = z := by
  have hmem : (x, y, z) ∈ pythagoreanTriples := by
    simpa [pythagoreanTriples] using hxyz
  rw [hp] at hmem
  simpa using hmem

private lemma intPolyParametrizes_identity {n : ℕ} {f g h : IntPoly n}
    (hp : IntPolyParametrizes f g h pythagoreanTriples) :
    f ^ 2 + g ^ 2 = h ^ 2 := by
  apply MvPolynomial.funext
  intro a
  have hmem : (intPolyEval f a, intPolyEval g a, intPolyEval h a) ∈
      {(x, y, z) | ∃ a : Fin n → ℤ,
        intPolyEval f a = x ∧ intPolyEval g a = y ∧ intPolyEval h a = z} := by
    exact ⟨a, rfl, rfl, rfl⟩
  have hpy : (intPolyEval f a, intPolyEval g a, intPolyEval h a) ∈ pythagoreanTriples := by
    rw [hp]
    simpa using hmem
  have hEq : intPolyEval f a ^ 2 + intPolyEval g a ^ 2 = intPolyEval h a ^ 2 := by
    simpa [pythagoreanTriples, IsPythagoreanTriple] using hpy
  simpa [intPolyEval] using hEq

private lemma parametrization_not_C_two_dvd_second {n : ℕ} {f g h : IntPoly n}
    (hp : IntPolyParametrizes f g h pythagoreanTriples) :
    ¬ MvPolynomial.C (2 : ℤ) ∣ g := by
  intro hg
  rcases hg with ⟨q, hq⟩
  have h435 : IsPythagoreanTriple 4 3 5 := by
    norm_num [IsPythagoreanTriple]
  rcases intPolyParametrizes_hits hp h435 with ⟨a, _hf, hgval, _hh⟩
  have hEval : intPolyEval g a = 2 * intPolyEval q a := by
    rw [hq]
    simp [intPolyEval]
  have hodd : (3 : ℤ) = 2 * intPolyEval q a := by
    rw [← hgval]
    exact hEval
  omega

/-- Frisch--Vaserstein's obstruction: no finite-variable triple of integer-coefficient
polynomials parametrizes all Pythagorean triples. -/
theorem no_int_poly_parametrization :
    ¬∃ (n : ℕ) (f g h : IntPoly n), IntPolyParametrizes f g h pythagoreanTriples := by
  rintro ⟨n, f, g, h, hp⟩
  let two : IntPoly n := 2
  have hId : f ^ 2 + g ^ 2 = h ^ 2 := intPolyParametrizes_identity hp
  have htwo_ne : two ≠ 0 := by
    dsimp [two]
    norm_num
  have htwo_prime : Prime two := by
    dsimp [two]
    simpa using ((MvPolynomial.prime_C_iff (σ := Fin n) (R := ℤ) (r := (2 : ℤ))).2
      (by norm_num : Prime (2 : ℤ)))
  have hfac : (h - f - g) * (h + f + g) = two * (-(f * g)) := by
    dsimp [two]
    calc
      (h - f - g) * (h + f + g) =
          h ^ 2 - (f ^ 2 + g ^ 2) - (2 : IntPoly n) * (f * g) := by
        ring
      _ = (2 : IntPoly n) * (-(f * g)) := by
        rw [← hId]
        ring
  have hfac_dvd : two ∣ (h - f - g) * (h + f + g) := by
    refine ⟨-(f * g), ?_⟩
    exact hfac
  have hfg_of_left (hleft : two ∣ h - f - g) : two ∣ f * g := by
    rcases hleft with ⟨r, hr⟩
    have hleft' : two ∣ h - f - g := ⟨r, hr⟩
    have hright : two ∣ h + f + g := by
      refine ⟨r + f + g, ?_⟩
      calc
        h + f + g = (h - f - g) + two * (f + g) := by
          dsimp [two]
          ring
        _ = two * r + two * (f + g) := by rw [hr]
        _ = two * (r + f + g) := by ring
    have hfour : two * two ∣ (h - f - g) * (h + f + g) :=
      mul_dvd_mul hleft' hright
    have hfour' : two * two ∣ two * (-(f * g)) := by
      simpa [hfac] using hfour
    have hdivneg : two ∣ -(f * g) := (mul_dvd_mul_iff_left htwo_ne).mp hfour'
    rcases hdivneg with ⟨s, hs⟩
    refine ⟨-s, ?_⟩
    rw [← neg_neg (f * g), hs]
    ring
  have hfg_of_right (hright : two ∣ h + f + g) : two ∣ f * g := by
    rcases hright with ⟨r, hr⟩
    have hleft : two ∣ h - f - g := by
      refine ⟨r - f - g, ?_⟩
      calc
        h - f - g = (h + f + g) - two * (f + g) := by
          dsimp [two]
          ring
        _ = two * r - two * (f + g) := by rw [hr]
        _ = two * (r - f - g) := by ring
    exact hfg_of_left hleft
  have hfg : two ∣ f * g := by
    rcases htwo_prime.dvd_or_dvd hfac_dvd with hleft | hright
    · exact hfg_of_left hleft
    · exact hfg_of_right hright
  have hfg_or : two ∣ f ∨ two ∣ g := htwo_prime.dvd_or_dvd hfg
  have hnotf : ¬ two ∣ f := by
    intro hf
    rcases hf with ⟨q, hq⟩
    have h345 : IsPythagoreanTriple 3 4 5 := by
      norm_num [IsPythagoreanTriple]
    rcases intPolyParametrizes_hits hp h345 with ⟨a, hfval, _hgval, _hhval⟩
    have hEval : intPolyEval f a = 2 * intPolyEval q a := by
      rw [hq]
      simp [intPolyEval, two]
    have hodd : (3 : ℤ) = 2 * intPolyEval q a := by
      rw [← hfval]
      exact hEval
    omega
  have hnotg : ¬ two ∣ g := by
    dsimp [two]
    exact parametrization_not_C_two_dvd_second hp
  exact hfg_or.elim hnotf hnotg

end LeanPool.PythagoreanPolynomialParametrization
