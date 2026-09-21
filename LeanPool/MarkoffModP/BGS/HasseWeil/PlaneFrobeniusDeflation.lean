/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneCoordinateShear
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# Frobenius deflation for affine plane curves

If the first partial derivative vanishes in characteristic `p`, every first
coordinate exponent is divisible by `p`.  This module contracts those
exponents, proves that substitution `X₀ ↦ X₀^p` reconstructs the original
polynomial, and records the exact invariants needed by the affine
Hasse--Weil reduction: absolute irreducibility, the other partial derivative,
the supplied bidegree bound, and the finite-field affine point count.

Unlike a coordinate shear, this operation does not enlarge the other
coordinate degree, and it strictly lowers the actual first coordinate degree
whenever that degree is positive.
-/

namespace BGS.HasseWeil

open MvPolynomial

noncomputable section

variable (R : Type*) [CommRing R]

/-- Substitute `X₀^p` for `X₀`, leaving `X₁` unchanged. -/
def planeFirstInflateSubstitution (p : ℕ) :
    Fin 2 → MvPolynomial (Fin 2) R :=
  ![X 0 ^ p, X 1]

/-- The one-coordinate Frobenius expansion homomorphism. -/
def planeFirstInflateHom (p : ℕ) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  bind₁ (planeFirstInflateSubstitution R p)

@[simp] theorem planeFirstInflateHom_C (p : ℕ) (r : R) :
    planeFirstInflateHom R p (C r) = C r := by
  simp [planeFirstInflateHom]

@[simp] theorem planeFirstInflateHom_X_zero (p : ℕ) :
    planeFirstInflateHom R p (X 0) = X 0 ^ p := by
  simp [planeFirstInflateHom, planeFirstInflateSubstitution]

@[simp] theorem planeFirstInflateHom_X_one (p : ℕ) :
    planeFirstInflateHom R p (X 1) = X 1 := by
  simp [planeFirstInflateHom, planeFirstInflateSubstitution]

theorem finSuccEquiv_planeFirstInflateHom (p : ℕ)
    (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.finSuccEquiv R 1 (planeFirstInflateHom R p f) =
      Polynomial.expand (MvPolynomial (Fin 1) R) p
        (MvPolynomial.finSuccEquiv R 1 f) := by
  let lhs : MvPolynomial (Fin 2) R →ₐ[R]
      Polynomial (MvPolynomial (Fin 1) R) :=
    (MvPolynomial.finSuccEquiv R 1).toAlgHom.comp
      (planeFirstInflateHom R p)
  let rhs : MvPolynomial (Fin 2) R →ₐ[R]
      Polynomial (MvPolynomial (Fin 1) R) :=
    ((Polynomial.expand (MvPolynomial (Fin 1) R) p).restrictScalars R).comp
      (MvPolynomial.finSuccEquiv R 1).toAlgHom
  change lhs f = rhs f
  apply DFunLike.congr_fun
  apply MvPolynomial.algHom_ext
  exact Fin.forall_fin_two.2 ⟨
    by simp [lhs, rhs, planeFirstInflateHom,
      planeFirstInflateSubstitution, MvPolynomial.finSuccEquiv_apply],
    by
      have hcases :
          Fin.cases
              (Polynomial.X : Polynomial (MvPolynomial (Fin 1) R))
              (fun k : Fin 1 => Polynomial.C
                (X k : MvPolynomial (Fin 1) R))
              (1 : Fin 2) =
            Polynomial.C (X (0 : Fin 1) : MvPolynomial (Fin 1) R) := by
        exact @Fin.cases_succ 1
          (fun _ => Polynomial (MvPolynomial (Fin 1) R))
          Polynomial.X
          (fun k : Fin 1 => Polynomial.C
            (X k : MvPolynomial (Fin 1) R)) 0
      simp [lhs, rhs, planeFirstInflateHom,
        planeFirstInflateSubstitution, MvPolynomial.finSuccEquiv_apply,
        hcases]⟩

/-- Divide the exponents of `X₀` by `p`, discarding coefficients whose
exponents are not divisible by `p`. -/
def planeFirstDeflate (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    MvPolynomial (Fin 2) R :=
  (MvPolynomial.finSuccEquiv R 1).symm
    (Polynomial.contract p (MvPolynomial.finSuccEquiv R 1 f))

theorem derivative_finSuccEquiv_eq_finSuccEquiv_pderiv_zero
    (f : MvPolynomial (Fin 2) R) :
    Polynomial.derivative (MvPolynomial.finSuccEquiv R 1 f) =
      MvPolynomial.finSuccEquiv R 1 (pderiv 0 f) := by
  ext n m
  rw [Polynomial.coeff_derivative, mul_comm]
  rw [← Nat.cast_succ, ← nsmul_eq_mul, coeff_smul,
    MvPolynomial.finSuccEquiv_coeff_coeff,
    MvPolynomial.finSuccEquiv_coeff_coeff,
    coeff_pderiv, nsmul_eq_mul, mul_comm]
  congr 1
  · apply congrArg (coeff · f)
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · simp

variable {R}

theorem planeFirstInflateHom_planeFirstDeflate
    [IsDomain R] (p : ℕ) [CharP R p] (hp : p ≠ 0)
    (f : MvPolynomial (Fin 2) R) (hderiv : pderiv 0 f = 0) :
    planeFirstInflateHom R p (planeFirstDeflate R p f) = f := by
  apply (MvPolynomial.finSuccEquiv R 1).injective
  rw [finSuccEquiv_planeFirstInflateHom, planeFirstDeflate,
    AlgEquiv.apply_symm_apply]
  apply Polynomial.expand_contract p
  · rw [derivative_finSuccEquiv_eq_finSuccEquiv_pderiv_zero, hderiv, map_zero]
  · exact hp

theorem planeFirstInflateHom_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (planeFirstInflateHom R p) := by
  intro f g hfg
  apply (MvPolynomial.finSuccEquiv R 1).injective
  have hfg' := congrArg (MvPolynomial.finSuccEquiv R 1) hfg
  rw [finSuccEquiv_planeFirstInflateHom,
    finSuccEquiv_planeFirstInflateHom] at hfg'
  exact Polynomial.expand_injective hp hfg'

theorem irreducible_of_planeFirstInflateHom_irreducible
    [IsDomain R] (p : ℕ) (hp : p ≠ 0) {f : MvPolynomial (Fin 2) R}
    (hf : Irreducible (planeFirstInflateHom R p f)) :
    Irreducible f := by
  have hpoly : Irreducible
      (Polynomial.expand (MvPolynomial (Fin 1) R) p
        (MvPolynomial.finSuccEquiv R 1 f)) := by
    rw [← finSuccEquiv_planeFirstInflateHom]
    exact hf.map (MvPolynomial.finSuccEquiv R 1).toMulEquiv
  have hbase : Irreducible (MvPolynomial.finSuccEquiv R 1 f) :=
    Polynomial.of_irreducible_expand hp hpoly
  simpa using hbase.map (MvPolynomial.finSuccEquiv R 1).symm.toMulEquiv

theorem eval_planeFirstInflateHom
    (p : ℕ) (f : MvPolynomial (Fin 2) R) (x y : R) :
    eval ![x, y] (planeFirstInflateHom R p f) =
      eval ![x ^ p, y] f := by
  change aeval ![x, y] (bind₁ (planeFirstInflateSubstitution R p) f) = _
  rw [aeval_bind₁]
  apply congrArg (fun z : Fin 2 → R => aeval z f)
  funext i
  fin_cases i <;> simp [planeFirstInflateSubstitution]

theorem pderiv_one_planeFirstInflateHom
    (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    pderiv 1 (planeFirstInflateHom R p f) =
      planeFirstInflateHom R p (pderiv 1 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f i hf =>
      fin_cases i <;> simp [map_mul, hf]

theorem map_planeFirstInflateHom
    {S : Type*} [CommRing S] (p : ℕ) (φ : R →+* S)
    (f : MvPolynomial (Fin 2) R) :
    map φ (planeFirstInflateHom R p f) =
      planeFirstInflateHom S p (map φ f) := by
  change map φ (bind₁ (planeFirstInflateSubstitution R p) f) = _
  rw [map_bind₁]
  congr 1
  ext i
  fin_cases i <;> simp [planeFirstInflateSubstitution]

/-- Multiply only the first exponent of a plane monomial by `p`. -/
def scaleFirstExponent (p : ℕ) (m : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  m.tail.cons (m 0 * p)

@[simp] theorem scaleFirstExponent_zero (p : ℕ) (m : Fin 2 →₀ ℕ) :
    scaleFirstExponent p m 0 = m 0 * p := by
  simp [scaleFirstExponent]

@[simp] theorem scaleFirstExponent_one (p : ℕ) (m : Fin 2 →₀ ℕ) :
    scaleFirstExponent p m 1 = m 1 := by
  change m.tail 0 = m 1
  rw [Finsupp.tail_apply]
  rfl

theorem scaleFirstExponent_mem_support_planeFirstInflateHom
    (p : ℕ) (hp : 0 < p) {f : MvPolynomial (Fin 2) R}
    {m : Fin 2 →₀ ℕ} (hm : m ∈ f.support) :
    scaleFirstExponent p m ∈ (planeFirstInflateHom R p f).support := by
  change m.tail.cons (m 0 * p) ∈ (planeFirstInflateHom R p f).support
  rw [← MvPolynomial.mem_support_coeff_finSuccEquiv,
    finSuccEquiv_planeFirstInflateHom,
    Polynomial.coeff_expand_mul hp,
    MvPolynomial.mem_support_coeff_finSuccEquiv]
  simpa using hm

/-- A bidegree bound for a one-coordinate inflation descends to the
unexpanded polynomial without loss. -/
theorem hasBidegreeAtMost_of_planeFirstInflateHom
    (p : ℕ) (hp : 0 < p) {f : MvPolynomial (Fin 2) R}
    {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost
      (planeFirstInflateHom R p f) firstDegree secondDegree) :
    BGS.External.HasBidegreeAtMost f firstDegree secondDegree := by
  intro m hm
  have hs := hdegree (scaleFirstExponent p m)
    (scaleFirstExponent_mem_support_planeFirstInflateHom p hp hm)
  exact ⟨(Nat.le_mul_of_pos_right (m 0) hp).trans (by simpa using hs.1),
    by simpa using hs.2⟩

theorem degreeOf_zero_planeFirstInflateHom
    (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    degreeOf 0 (planeFirstInflateHom R p f) = degreeOf 0 f * p := by
  rw [← MvPolynomial.natDegree_finSuccEquiv,
    finSuccEquiv_planeFirstInflateHom,
    Polynomial.natDegree_expand,
    MvPolynomial.natDegree_finSuccEquiv]

theorem absolutelyIrreducible_of_planeFirstInflateHom_eq
    {K : Type*} [Field K] (p : ℕ) (hp : p ≠ 0)
    {f g : MvPolynomial (Fin 2) K}
    (hfg : planeFirstInflateHom K p g = f)
    (hf : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f)) :
    Irreducible (map (algebraMap K (AlgebraicClosure K)) g) := by
  apply irreducible_of_planeFirstInflateHom_irreducible p hp
  rw [← map_planeFirstInflateHom, hfg]
  exact hf

theorem pderiv_one_ne_zero_of_planeFirstInflateHom_eq
    {K : Type*} [Field K] (p : ℕ)
    {f g : MvPolynomial (Fin 2) K}
    (hfg : planeFirstInflateHom K p g = f)
    (hf : pderiv 1 f ≠ 0) :
    pderiv 1 g ≠ 0 := by
  intro hg
  apply hf
  rw [← hfg, pderiv_one_planeFirstInflateHom, hg, map_zero]

theorem degreeOf_zero_lt_of_planeFirstInflateHom_eq
    {K : Type*} [Field K] (p : ℕ) (hp : 1 < p)
    {f g : MvPolynomial (Fin 2) K}
    (hfg : planeFirstInflateHom K p g = f)
    (hfpos : 0 < degreeOf 0 f) :
    degreeOf 0 g < degreeOf 0 f := by
  have hdegree := degreeOf_zero_planeFirstInflateHom p g
  rw [hfg] at hdegree
  have hgpos : 0 < degreeOf 0 g := by
    by_contra hg
    rw [Nat.not_lt, Nat.le_zero] at hg
    rw [hg, zero_mul] at hdegree
    omega
  calc
    degreeOf 0 g < degreeOf 0 g * p :=
      (Nat.lt_mul_iff_one_lt_right hgpos).2 hp
    _ = degreeOf 0 f := hdegree.symm

section FiniteField

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Frobenius in the first coordinate, identity in the second. -/
def planeFirstFrobeniusPointEquiv : K × K ≃ K × K :=
  (frobeniusEquiv K p).toEquiv.prodCongr (Equiv.refl K)

@[simp] theorem planeFirstFrobeniusPointEquiv_apply (z : K × K) :
    planeFirstFrobeniusPointEquiv K p z = (z.1 ^ p, z.2) := by
  rcases z with ⟨x, y⟩
  rfl

/-- Frobenius bijects the affine zero set of an inflation with the affine
zero set of the unexpanded polynomial. -/
def planeFirstInflateAffineZeroEquiv (f : MvPolynomial (Fin 2) K) :
    {z // z ∈ BGS.External.affinePlaneCurveZeros K
      (planeFirstInflateHom K p f)} ≃
      {z // z ∈ BGS.External.affinePlaneCurveZeros K f} :=
  (planeFirstFrobeniusPointEquiv K p).subtypeEquiv fun z => by
    simp only [BGS.External.mem_affinePlaneCurveZeros_iff,
      planeFirstFrobeniusPointEquiv_apply]
    exact (eval_planeFirstInflateHom p f z.1 z.2).congr_left

theorem card_affinePlaneCurveZeros_planeFirstInflateHom
    (f : MvPolynomial (Fin 2) K) :
    (BGS.External.affinePlaneCurveZeros K
      (planeFirstInflateHom K p f)).card =
      (BGS.External.affinePlaneCurveZeros K f).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (planeFirstInflateAffineZeroEquiv K p f)

theorem card_affinePlaneCurveZeros_eq_of_planeFirstInflateHom_eq
    {f g : MvPolynomial (Fin 2) K}
    (hfg : planeFirstInflateHom K p g = f) :
    (BGS.External.affinePlaneCurveZeros K g).card =
      (BGS.External.affinePlaneCurveZeros K f).card := by
  rw [← hfg, card_affinePlaneCurveZeros_planeFirstInflateHom]

end FiniteField

/-- One strict Frobenius-deflation step in the first coordinate.  The
second partial derivative is retained, absolute irreducibility and the
affine point count descend, and no supplied bidegree bound is enlarged. -/
theorem exists_planeFirstFrobeniusDeflationStep
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstDegree secondDegree : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : pderiv 0 f = 0)
    (hpartialSecond : pderiv 1 f ≠ 0)
    (hfirstDegree : 0 < degreeOf 0 f) :
    ∃ g : MvPolynomial (Fin 2) K,
      planeFirstInflateHom K (ringChar K) g = f ∧
      BGS.External.HasBidegreeAtMost g firstDegree secondDegree ∧
      Irreducible (map (algebraMap K (AlgebraicClosure K)) g) ∧
      pderiv 1 g ≠ 0 ∧
      degreeOf 0 g < degreeOf 0 f ∧
      (BGS.External.affinePlaneCurveZeros K g).card =
        (BGS.External.affinePlaneCurveZeros K f).card := by
  let p := ringChar K
  letI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let g := planeFirstDeflate K p f
  have hfg : planeFirstInflateHom K p g = f :=
    planeFirstInflateHom_planeFirstDeflate p
      ((Fact.out : p.Prime).ne_zero) f hpartialFirst
  refine ⟨g, hfg, ?_, ?_, ?_, ?_, ?_⟩
  · apply hasBidegreeAtMost_of_planeFirstInflateHom p
      (Fact.out : p.Prime).pos
    simpa [hfg] using hdegree
  · exact absolutelyIrreducible_of_planeFirstInflateHom_eq
      p (Fact.out : p.Prime).ne_zero hfg habsolute
  · exact pderiv_one_ne_zero_of_planeFirstInflateHom_eq
      p hfg hpartialSecond
  · exact degreeOf_zero_lt_of_planeFirstInflateHom_eq
      p (Fact.out : p.Prime).one_lt hfg hfirstDegree
  · exact card_affinePlaneCurveZeros_eq_of_planeFirstInflateHom_eq
      K p hfg

/-- Iterating the strict first-coordinate step terminates.  Unless the
original polynomial has actual first degree zero, it produces a polynomial
with both coordinate partials nonzero, without increasing the supplied
bidegree bounds or changing the affine point count. -/
theorem exists_planeFirstSeparatingDeflation_or_degreeOf_zero
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstDegree secondDegree : ℕ)
    (hdegree : BGS.External.HasBidegreeAtMost
      f firstDegree secondDegree)
    (habsolute : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialSecond : pderiv 1 f ≠ 0) :
    degreeOf 0 f = 0 ∨
      ∃ g : MvPolynomial (Fin 2) K,
        BGS.External.HasBidegreeAtMost g firstDegree secondDegree ∧
        Irreducible (map (algebraMap K (AlgebraicClosure K)) g) ∧
        pderiv 0 g ≠ 0 ∧
        pderiv 1 g ≠ 0 ∧
        (BGS.External.affinePlaneCurveZeros K g).card =
          (BGS.External.affinePlaneCurveZeros K f).card := by
  let P : ℕ → Prop := fun n =>
    ∀ f : MvPolynomial (Fin 2) K,
      degreeOf 0 f = n →
      BGS.External.HasBidegreeAtMost f firstDegree secondDegree →
      Irreducible (map (algebraMap K (AlgebraicClosure K)) f) →
      pderiv 1 f ≠ 0 →
      degreeOf 0 f = 0 ∨
        ∃ g : MvPolynomial (Fin 2) K,
          BGS.External.HasBidegreeAtMost g firstDegree secondDegree ∧
          Irreducible (map (algebraMap K (AlgebraicClosure K)) g) ∧
          pderiv 0 g ≠ 0 ∧
          pderiv 1 g ≠ 0 ∧
          (BGS.External.affinePlaneCurveZeros K g).card =
            (BGS.External.affinePlaneCurveZeros K f).card
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f hfn hdegree habsolute hpartialSecond
        by_cases hdegreeZero : degreeOf 0 f = 0
        · exact Or.inl hdegreeZero
        by_cases hpartialFirst : pderiv 0 f = 0
        · obtain ⟨g, hfg, hgdegree, hgabsolute, hgpartialSecond,
              hglt, hgcard⟩ :=
            exists_planeFirstFrobeniusDeflationStep K f
              firstDegree secondDegree hdegree habsolute hpartialFirst
              hpartialSecond (Nat.pos_of_ne_zero hdegreeZero)
          have hgn : degreeOf 0 g < n := by
            simpa [← hfn] using hglt
          have hgout := ih (degreeOf 0 g) hgn g rfl hgdegree
            hgabsolute hgpartialSecond
          rcases hgout with hgzero | ⟨u, hudegree, huabsolute,
              hupartialFirst, hupartialSecond, hucard⟩
          · have hdegInflate :=
              degreeOf_zero_planeFirstInflateHom (ringChar K) g
            rw [hfg, hgzero, zero_mul] at hdegInflate
            exact (hdegreeZero hdegInflate).elim
          · exact Or.inr ⟨u, hudegree, huabsolute, hupartialFirst,
              hupartialSecond, hucard.trans hgcard⟩
        · exact Or.inr ⟨f, hdegree, habsolute, hpartialFirst,
            hpartialSecond, rfl⟩
  exact hP (degreeOf 0 f) f rfl hdegree habsolute hpartialSecond

end

end BGS.HasseWeil
