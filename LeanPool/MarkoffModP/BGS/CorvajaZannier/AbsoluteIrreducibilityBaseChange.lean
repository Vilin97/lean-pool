/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PerfectConstants
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Nullstellensatz

/-!
# Base change of absolutely irreducible multivariate polynomials

An irreducible multivariate polynomial over an algebraic closure remains
irreducible after extending its original coefficient field to an arbitrary
field.  The proof is a direct Nullstellensatz descent.  Given a hypothetical
factorization over the target field, introduce one variable for each of its
finitely many coefficients and two additional variables for inverses of
chosen nonconstant coefficients.  A closed point of a maximal ideal over the
kernel specializes the factorization to the algebraically closed field, while
the inverse relations ensure that both specialized factors remain nonunits.

The final theorem supplies the exact constant-field base-change step used in
Corvaja--Zannier's auxiliary-family argument.
-/

open scoped BigOperators

noncomputable section

namespace BGS.CorvajaZannier

open MvPolynomial

variable {K E F σ : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [IsAlgClosed E]

private theorem exists_nonconstant_coeff_of_nonzero_nonunit
    (g : MvPolynomial σ F) (hg0 : g ≠ 0) (hgu : ¬ IsUnit g) :
    ∃ m, m ≠ 0 ∧ g.coeff m ≠ 0 := by
  classical
  by_contra h
  have h : ∀ m, m ≠ 0 → g.coeff m = 0 := by
    intro m hm
    by_contra hcoeff
    exact h ⟨m, hm, hcoeff⟩
  have heq : g = MvPolynomial.C (g.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · subst m
      simp
    · simpa [MvPolynomial.coeff_C, Ne.symm hm] using h m hm
  have hc : g.coeff 0 ≠ 0 := by
    intro hc
    apply hg0
    rw [heq, hc]
    simp
  apply hgu
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

/-- If a multivariate polynomial is irreducible after extension to an
algebraically closed field, it remains irreducible after any other injective
field extension of its original coefficient field. -/
theorem irreducible_map_of_irreducible_map_isAlgClosed
    (iF : K →+* F) (f : MvPolynomial σ K)
    (hE : Irreducible (MvPolynomial.map (algebraMap K E) f)) :
    Irreducible (MvPolynomial.map iF f) := by
  refine ⟨?_, ?_⟩
  · intro hu
    have huE : IsUnit (MvPolynomial.map (algebraMap K E) f) := by
      rw [MvPolynomial.isUnit_iff]
      constructor
      · have h0 := (MvPolynomial.isUnit_iff.mp hu).1
        rw [MvPolynomial.coeff_map] at h0 ⊢
        rw [isUnit_iff_ne_zero] at h0 ⊢
        intro hcE
        have hc : f.coeff 0 = 0 :=
          (algebraMap K E).injective (by simpa using hcE)
        exact h0 (by simp [hc])
      · intro m hm
        have hmF := (MvPolynomial.isUnit_iff.mp hu).2 m hm
        simp only [MvPolynomial.coeff_map, isNilpotent_iff_eq_zero] at hmF ⊢
        have hc : f.coeff m = 0 := iF.injective (by simpa using hmF)
        simp [hc]
    exact hE.not_isUnit huE
  · intro g h hfac
    classical
    by_contra hnot
    have hnot : ¬ IsUnit g ∧ ¬ IsUnit h := not_or.mp hnot
    have hf0 : f ≠ 0 := by
      intro hf
      exact hE.ne_zero (by simp [hf])
    have hmap0 : MvPolynomial.map iF f ≠ 0 := by
      intro hm
      apply hf0
      apply MvPolynomial.map_injective iF iF.injective
      simpa using hm
    have hg0 : g ≠ 0 := by
      intro hg
      rw [hg, zero_mul] at hfac
      exact hmap0 hfac
    have hh0 : h ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hfac
      exact hmap0 hfac
    obtain ⟨mg, hmg0, hmg⟩ :=
      exists_nonconstant_coeff_of_nonzero_nonunit g hg0 hnot.1
    obtain ⟨mh, hmh0, hmh⟩ :=
      exists_nonconstant_coeff_of_nonzero_nonunit h hh0 hnot.2
    let V := Sum (Sum {m // m ∈ g.support} {m // m ∈ h.support}) (Fin 2)
    let invG : V := Sum.inr 0
    let invH : V := Sum.inr 1
    let gVar : (σ →₀ ℕ) → V := fun m =>
      if hm : m ∈ g.support then Sum.inl (Sum.inl ⟨m, hm⟩) else invG
    let hVar : (σ →₀ ℕ) → V := fun m =>
      if hm : m ∈ h.support then Sum.inl (Sum.inr ⟨m, hm⟩) else invH
    let val : V → F := fun v =>
      match v with
      | Sum.inl (Sum.inl m) => g.coeff m.1
      | Sum.inl (Sum.inr m) => h.coeff m.1
      | Sum.inr j => if j = 0 then (g.coeff mg)⁻¹ else (h.coeff mh)⁻¹
    let ψ : MvPolynomial V K →+* F := MvPolynomial.eval₂Hom iF val
    let G : MvPolynomial σ (MvPolynomial V K) :=
      g.support.sum fun m => MvPolynomial.monomial m (MvPolynomial.X (gVar m))
    let H : MvPolynomial σ (MvPolynomial V K) :=
      h.support.sum fun m => MvPolynomial.monomial m (MvPolynomial.X (hVar m))
    have hmapG : MvPolynomial.map ψ G = g := by
      rw [g.as_sum]
      simp only [G, map_sum, map_monomial]
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : g.coeff m ≠ 0 := by
        simpa [MvPolynomial.mem_support_iff] using hm
      simp [ψ, val, gVar, hm0]
    have hmapH : MvPolynomial.map ψ H = h := by
      rw [h.as_sum]
      simp only [H, map_sum, map_monomial]
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : h.coeff m ≠ 0 := by
        simpa [MvPolynomial.mem_support_iff] using hm
      simp [ψ, val, hVar, hm0]
    let fA : MvPolynomial σ (MvPolynomial V K) :=
      MvPolynomial.map MvPolynomial.C f
    have hmapfA : MvPolynomial.map ψ fA = MvPolynomial.map iF f := by
      calc
        MvPolynomial.map ψ fA =
            MvPolynomial.map (ψ.comp MvPolynomial.C) f := by
              simp only [fA, MvPolynomial.map_map]
        _ = MvPolynomial.map iF f := by
          have hcomp : ψ.comp MvPolynomial.C = iF := by
            ext c
            simp [ψ]
          rw [hcomp]
    let D : MvPolynomial σ (MvPolynomial V K) := G * H - fA
    have hcoeffD (m : σ →₀ ℕ) : D.coeff m ∈ RingHom.ker ψ := by
      change ψ (D.coeff m) = 0
      rw [← MvPolynomial.coeff_map]
      simp only [D, map_sub, map_mul, hmapG, hmapH, hmapfA, hfac]
      simp
    let P : Ideal (MvPolynomial V K) := RingHom.ker ψ
    have hPprime : P.IsPrime := RingHom.ker_isPrime ψ
    obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal P hPprime.ne_top
    let : Finite V := by infer_instance
    obtain ⟨x, hx⟩ :=
      MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal E hMmax
    let θ : MvPolynomial V K →+* E :=
      MvPolynomial.eval₂Hom (algebraMap K E) x
    have hker_specialize {q : MvPolynomial V K} (hq : q ∈ RingHom.ker ψ) :
        θ q = 0 := by
      have hqM : q ∈ M := hPM hq
      rw [hx] at hqM
      simpa [θ, MvPolynomial.aeval_def] using hqM x rfl
    let gE : MvPolynomial σ E := MvPolynomial.map θ G
    let hE' : MvPolynomial σ E := MvPolynomial.map θ H
    have hfactorE : MvPolynomial.map (algebraMap K E) f = gE * hE' := by
      have hDzero : MvPolynomial.map θ D = 0 := by
        ext m
        rw [MvPolynomial.coeff_map]
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
        exact hker_specialize (hcoeffD m)
      simp only [D, map_sub, map_mul] at hDzero
      have hmapfAE : MvPolynomial.map θ fA =
          MvPolynomial.map (algebraMap K E) f := by
        calc
          MvPolynomial.map θ fA =
              MvPolynomial.map (θ.comp MvPolynomial.C) f := by
                simp only [fA, MvPolynomial.map_map]
          _ = MvPolynomial.map (algebraMap K E) f := by
            have hcomp : θ.comp MvPolynomial.C = algebraMap K E := by
              ext c
              simp [θ]
            rw [hcomp]
      rw [hmapfAE] at hDzero
      exact sub_eq_zero.mp hDzero |>.symm
    have hgCoeff : gE.coeff mg ≠ 0 := by
      have hmgMem : mg ∈ g.support :=
        MvPolynomial.mem_support_iff.mpr hmg
      let qG : MvPolynomial V K :=
        MvPolynomial.X (gVar mg) * MvPolynomial.X invG - 1
      have hqG : qG ∈ RingHom.ker ψ := by
        change ψ qG = 0
        dsimp only [qG]
        rw [map_sub, map_mul, map_one]
        simp [ψ, val, gVar, invG, hmg]
      have hqGE := hker_specialize hqG
      have hxG : x (gVar mg) ≠ 0 := by
        have hprod : x (gVar mg) * x invG = 1 := by
          apply sub_eq_zero.mp
          change θ (MvPolynomial.X (gVar mg) * MvPolynomial.X invG - 1) = 0 at hqGE
          rw [map_sub, map_mul, map_one] at hqGE
          simpa only [θ, MvPolynomial.eval₂Hom_X'] using hqGE
        exact left_ne_zero_of_mul_eq_one hprod
      have hcoeffFormula : gE.coeff mg = x (gVar mg) := by
        simp [gE, G, MvPolynomial.coeff_sum,
          MvPolynomial.coeff_monomial, hmgMem, θ]
      rw [hcoeffFormula]
      exact hxG
    have hhCoeff : hE'.coeff mh ≠ 0 := by
      have hmhMem : mh ∈ h.support :=
        MvPolynomial.mem_support_iff.mpr hmh
      let qH : MvPolynomial V K :=
        MvPolynomial.X (hVar mh) * MvPolynomial.X invH - 1
      have hqH : qH ∈ RingHom.ker ψ := by
        change ψ qH = 0
        dsimp only [qH]
        rw [map_sub, map_mul, map_one]
        simp [ψ, val, hVar, invH, hmh]
      have hqHE := hker_specialize hqH
      have hxH : x (hVar mh) ≠ 0 := by
        have hprod : x (hVar mh) * x invH = 1 := by
          apply sub_eq_zero.mp
          change θ (MvPolynomial.X (hVar mh) * MvPolynomial.X invH - 1) = 0 at hqHE
          rw [map_sub, map_mul, map_one] at hqHE
          simpa only [θ, MvPolynomial.eval₂Hom_X'] using hqHE
        exact left_ne_zero_of_mul_eq_one hprod
      have hcoeffFormula : hE'.coeff mh = x (hVar mh) := by
        simp [hE', H, MvPolynomial.coeff_sum,
          MvPolynomial.coeff_monomial, hmhMem, θ]
      rw [hcoeffFormula]
      exact hxH
    have hgENonunit : ¬ IsUnit gE := by
      intro hu
      have := (MvPolynomial.isUnit_iff.mp hu).2 mg hmg0
      simp only [isNilpotent_iff_eq_zero] at this
      exact hgCoeff this
    have hhENonunit : ¬ IsUnit hE' := by
      intro hu
      have := (MvPolynomial.isUnit_iff.mp hu).2 mh hmh0
      simp only [isNilpotent_iff_eq_zero] at this
      exact hhCoeff this
    exact hE.isUnit_or_isUnit hfactorE |>.elim hgENonunit hhENonunit

/-- Absolute irreducibility, stated using `AlgebraicClosure K`, implies
irreducibility after an arbitrary field-valued coefficient embedding. -/
theorem irreducible_map_of_irreducible_map_algebraicClosure
    {K F σ : Type*} [Field K] [Field F]
    (iF : K →+* F) (f : MvPolynomial σ K)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    Irreducible (MvPolynomial.map iF f) :=
  irreducible_map_of_irreducible_map_isAlgClosed
    (E := AlgebraicClosure K) iF f habsolute

variable {K L : Type*} [Field K] [Field L] {p : ℕ}
  [Fact p.Prime] [CharP K p] [CharP L p] [PerfectField K] [Algebra K L]

/-- The exact base-change bridge needed by the plane-curve auxiliary-family
theorem: absolute irreducibility over `K` implies irreducibility after
extension of constants to the Frobenius subfield `L^p`. -/
theorem irreducible_map_perfectConstantsToFrobeniusSubfield
    (f : MvPolynomial (Fin 2) K)
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    Irreducible
      (MvPolynomial.map
        (perfectConstantsToFrobeniusSubfield
          (K := K) (L := L) (p := p)) f) :=
  irreducible_map_of_irreducible_map_algebraicClosure
    (perfectConstantsToFrobeniusSubfield
      (K := K) (L := L) (p := p)) f habsolute

end BGS.CorvajaZannier
