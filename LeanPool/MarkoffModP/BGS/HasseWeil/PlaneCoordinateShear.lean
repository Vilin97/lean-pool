/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# A separating coordinate shear for affine plane curves

This file formalizes the invertible linear change of variables
`(x, y) ↦ (x, x + y)`.  If the first partial derivative of `f` vanishes but
the second does not, the transformed equation has both partial derivatives
nonzero.  The shear preserves affine point counts and geometric
irreducibility, including after extension to an algebraic closure.

The case in which both partial derivatives vanish is deliberately not hidden
here: over a finite field it requires the separate characteristic-`p`
argument that an absolutely irreducible nonconstant polynomial cannot be a
polynomial in `x^p` and `y^p`.
-/

namespace BGS.HasseWeil

open MvPolynomial

noncomputable section

section VanishingPartials

variable {R σ : Type*} [Field R]

/-- Divide every exponent of a multivariate monomial by `p`.  On the
support of a polynomial whose partial derivatives vanish in characteristic
`p`, this is an exact inverse to multiplication of exponents by `p`. -/
def divideExponents (p : ℕ) (m : σ →₀ ℕ) : σ →₀ ℕ :=
  m.mapRange (fun n => n / p) (Nat.zero_div p)

variable (p : ℕ) [CharP R p]

/-- In characteristic `p`, every exponent occurring in a variable with
vanishing partial derivative is divisible by `p`. -/
theorem dvd_exponent_of_pderiv_eq_zero
    {f : MvPolynomial σ R} {i : σ}
    (hderiv : pderiv i f = 0) {m : σ →₀ ℕ} (hm : m ∈ f.support) :
    p ∣ m i := by
  by_contra hnot
  have hi : m i ≠ 0 := by
    intro hi
    apply hnot
    simp [hi]
  let n : σ →₀ ℕ := m - Finsupp.single i 1
  have hn : n + Finsupp.single i 1 = m := by
    exact Finsupp.sub_add_single_one_cancel hi
  have hni : n i + 1 = m i := by
    simpa [n] using congrArg (fun v : σ →₀ ℕ => v i) hn
  have hcoeff : f.coeff m ≠ 0 := by
    simpa [mem_support_iff] using hm
  have hcast : (m i : R) ≠ 0 := by
    exact (CharP.cast_eq_zero_iff R p (m i)).not.mpr hnot
  have hz := congrArg (fun g : MvPolynomial σ R ↦ g.coeff n) hderiv
  rw [coeff_pderiv] at hz
  simp only [AddMonoidAlgebra.coeff_zero] at hz
  rw [hn] at hz
  have hfactor : ((n i : R) + 1) = (m i : R) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun a : ℕ => (a : R)) hni
  rw [hfactor] at hz
  exact (mul_ne_zero hcoeff hcast) hz

theorem smul_divideExponents_eq
    {f : MvPolynomial σ R}
    (hderiv : ∀ i, pderiv i f = 0)
    {m : σ →₀ ℕ} (hm : m ∈ f.support) :
    p • divideExponents p m = m := by
  ext i
  simp only [Finsupp.smul_apply, nsmul_eq_mul, divideExponents,
    Finsupp.mapRange_apply]
  exact Nat.mul_div_cancel' (dvd_exponent_of_pderiv_eq_zero p (hderiv i) hm)

variable [Fact p.Prime] [PerfectRing R p]

/-- Over a perfect field of positive characteristic, a multivariate
polynomial with every partial derivative zero is a `p`-th power. -/
theorem exists_pow_eq_of_forall_pderiv_eq_zero
    (f : MvPolynomial σ R) (hderiv : ∀ i, pderiv i f = 0) :
    ∃ g : MvPolynomial σ R, g ^ p = f := by
  let g : MvPolynomial σ R :=
    ∑ m ∈ f.support,
      monomial (divideExponents p m)
        ((frobeniusEquiv R p).symm (f.coeff m))
  refine ⟨g, ?_⟩
  rw [← map_frobenius_expand p]
  calc
    map (frobenius R p) (expand p g) =
        ∑ m ∈ f.support, monomial m (f.coeff m) := by
      simp only [g, map_sum, map_monomial, expand_monomial]
      apply Finset.sum_congr rfl
      intro m hm
      rw [smul_divideExponents_eq p hderiv hm]
      simp
    _ = f := f.as_sum.symm

/-- Hence a polynomial with every partial derivative zero cannot be
irreducible over a perfect field of characteristic `p`. -/
theorem not_irreducible_of_forall_pderiv_eq_zero
    (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (f : MvPolynomial σ R) (hderiv : ∀ i, pderiv i f = 0) :
    ¬ Irreducible f := by
  obtain ⟨g, rfl⟩ := exists_pow_eq_of_forall_pderiv_eq_zero p f hderiv
  exact not_irreducible_pow (Fact.out : p.Prime).ne_one

end VanishingPartials

variable (R : Type*) [CommRing R]

/-- The substitution `(x, y) ↦ (x, x + y)`. -/
def planeYShearSubstitution : Fin 2 → MvPolynomial (Fin 2) R :=
  ![X 0, X 0 + X 1]

/-- The inverse substitution `(x, y) ↦ (x, y - x)`. -/
def planeYUnShearSubstitution : Fin 2 → MvPolynomial (Fin 2) R :=
  ![X 0, X 1 - X 0]

@[simp] theorem planeYShearSubstitution_zero :
    planeYShearSubstitution R 0 = X 0 := rfl

@[simp] theorem planeYShearSubstitution_one :
    planeYShearSubstitution R 1 = X 0 + X 1 := rfl

def planeYShearHom : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  bind₁ (planeYShearSubstitution R)

def planeYUnShearHom : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  bind₁ (planeYUnShearSubstitution R)

theorem planeYShearHom_comp_planeYUnShearHom :
    (planeYShearHom R).comp (planeYUnShearHom R) = AlgHom.id R _ := by
  ext i
  fin_cases i <;> simp [planeYShearHom, planeYUnShearHom,
    planeYShearSubstitution, planeYUnShearSubstitution]

theorem planeYUnShearHom_comp_planeYShearHom :
    (planeYUnShearHom R).comp (planeYShearHom R) = AlgHom.id R _ := by
  ext i
  fin_cases i <;> simp [planeYShearHom, planeYUnShearHom,
    planeYShearSubstitution, planeYUnShearSubstitution]

/-- The polynomial automorphism induced by `(x, y) ↦ (x, x + y)`. -/
def planeYShearAlgEquiv :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (planeYShearHom R) (planeYUnShearHom R)
    (planeYShearHom_comp_planeYUnShearHom R)
    (planeYUnShearHom_comp_planeYShearHom R)

@[simp] theorem planeYShearAlgEquiv_apply (f : MvPolynomial (Fin 2) R) :
    planeYShearAlgEquiv R f = bind₁ (planeYShearSubstitution R) f := rfl

/-- The corresponding bijection of affine points. -/
def planeYShearPointEquiv : R × R ≃ R × R where
  toFun z := (z.1, z.1 + z.2)
  invFun z := (z.1, z.2 - z.1)
  left_inv := by rintro ⟨x, y⟩; simp
  right_inv := by rintro ⟨x, y⟩; simp

@[simp] theorem eval_planeYShearAlgEquiv
    (f : MvPolynomial (Fin 2) R) (z : R × R) :
    eval ![z.1, z.2] (planeYShearAlgEquiv R f) =
      eval ![(planeYShearPointEquiv R z).1, (planeYShearPointEquiv R z).2] f := by
  change aeval ![z.1, z.2] (bind₁ (planeYShearSubstitution R) f) =
    aeval ![z.1, z.1 + z.2] f
  rw [aeval_bind₁]
  congr 1
  ext i
  fin_cases i <;> simp [planeYShearSubstitution]

theorem planeYShearAlgEquiv_irreducible_iff
    (f : MvPolynomial (Fin 2) R) :
    Irreducible (planeYShearAlgEquiv R f) ↔ Irreducible f := by
  constructor
  · intro h
    have h' : Irreducible
        ((planeYShearAlgEquiv R).symm (planeYShearAlgEquiv R f)) :=
      h.map (planeYShearAlgEquiv R).symm.toMulEquiv
    simpa only [AlgEquiv.symm_apply_apply] using h'
  · intro h
    exact h.map (planeYShearAlgEquiv R).toMulEquiv

/-- Chain rule in the first coordinate for the shear. -/
theorem pderiv_zero_planeYShearAlgEquiv (f : MvPolynomial (Fin 2) R) :
    pderiv 0 (planeYShearAlgEquiv R f) =
      planeYShearAlgEquiv R (pderiv 0 f + pderiv 1 f) := by
  change pderiv 0 (bind₁ (planeYShearSubstitution R) f) =
    bind₁ (planeYShearSubstitution R) (pderiv 0 f + pderiv 1 f)
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, map_add]; abel
  | mul_X f i hf =>
      fin_cases i <;>
        simp [hf] <;>
        ring

/-- Chain rule in the second coordinate for the shear. -/
theorem pderiv_one_planeYShearAlgEquiv (f : MvPolynomial (Fin 2) R) :
    pderiv 1 (planeYShearAlgEquiv R f) =
      planeYShearAlgEquiv R (pderiv 1 f) := by
  change pderiv 1 (bind₁ (planeYShearSubstitution R) f) =
    bind₁ (planeYShearSubstitution R) (pderiv 1 f)
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, map_add]
  | mul_X f i hf =>
      fin_cases i <;>
        simp [hf]

/-- If only the second coordinate is separating, the shear makes both
coordinates separating. -/
theorem planeYShearAlgEquiv_pderivs_ne_zero_of_zero_ne
    (f : MvPolynomial (Fin 2) R)
    (hzero : pderiv 0 f = 0) (hne : pderiv 1 f ≠ 0) :
    pderiv 0 (planeYShearAlgEquiv R f) ≠ 0 ∧
      pderiv 1 (planeYShearAlgEquiv R f) ≠ 0 := by
  have hs : planeYShearAlgEquiv R (pderiv 1 f) ≠ 0 := by
    intro hs
    apply hne
    apply (planeYShearAlgEquiv R).injective
    simpa using hs
  rw [pderiv_zero_planeYShearAlgEquiv,
    pderiv_one_planeYShearAlgEquiv, hzero, zero_add]
  exact ⟨hs, hs⟩

/-- The shear commutes with extension of coefficients. -/
theorem map_planeYShearAlgEquiv {S : Type*} [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Fin 2) R) :
    map φ (planeYShearAlgEquiv R f) = planeYShearAlgEquiv S (map φ f) := by
  rw [planeYShearAlgEquiv_apply, planeYShearAlgEquiv_apply, map_bind₁]
  congr 1
  ext i
  fin_cases i <;> simp [planeYShearSubstitution]

/-- The symmetric substitution `(x, y) ↦ (x + y, y)`. -/
def planeXShearSubstitution : Fin 2 → MvPolynomial (Fin 2) R :=
  ![X 0 + X 1, X 1]

/-- The inverse symmetric substitution `(x, y) ↦ (x - y, y)`. -/
def planeXUnShearSubstitution : Fin 2 → MvPolynomial (Fin 2) R :=
  ![X 0 - X 1, X 1]

@[simp] theorem planeXShearSubstitution_zero :
    planeXShearSubstitution R 0 = X 0 + X 1 := rfl

@[simp] theorem planeXShearSubstitution_one :
    planeXShearSubstitution R 1 = X 1 := rfl

def planeXShearHom : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  bind₁ (planeXShearSubstitution R)

def planeXUnShearHom : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  bind₁ (planeXUnShearSubstitution R)

theorem planeXShearHom_comp_planeXUnShearHom :
    (planeXShearHom R).comp (planeXUnShearHom R) = AlgHom.id R _ := by
  ext i
  fin_cases i <;> simp [planeXShearHom, planeXUnShearHom,
    planeXShearSubstitution, planeXUnShearSubstitution]

theorem planeXUnShearHom_comp_planeXShearHom :
    (planeXUnShearHom R).comp (planeXShearHom R) = AlgHom.id R _ := by
  ext i
  fin_cases i <;> simp [planeXShearHom, planeXUnShearHom,
    planeXShearSubstitution, planeXUnShearSubstitution]

/-- The polynomial automorphism induced by `(x, y) ↦ (x + y, y)`. -/
def planeXShearAlgEquiv :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (planeXShearHom R) (planeXUnShearHom R)
    (planeXShearHom_comp_planeXUnShearHom R)
    (planeXUnShearHom_comp_planeXShearHom R)

@[simp] theorem planeXShearAlgEquiv_apply (f : MvPolynomial (Fin 2) R) :
    planeXShearAlgEquiv R f = bind₁ (planeXShearSubstitution R) f := rfl

/-- The symmetric shear on affine points. -/
def planeXShearPointEquiv : R × R ≃ R × R where
  toFun z := (z.1 + z.2, z.2)
  invFun z := (z.1 - z.2, z.2)
  left_inv := by rintro ⟨x, y⟩; simp
  right_inv := by rintro ⟨x, y⟩; simp

@[simp] theorem eval_planeXShearAlgEquiv
    (f : MvPolynomial (Fin 2) R) (z : R × R) :
    eval ![z.1, z.2] (planeXShearAlgEquiv R f) =
      eval ![(planeXShearPointEquiv R z).1, (planeXShearPointEquiv R z).2] f := by
  change aeval ![z.1, z.2] (bind₁ (planeXShearSubstitution R) f) =
    aeval ![z.1 + z.2, z.2] f
  rw [aeval_bind₁]
  congr 1
  ext i
  fin_cases i <;> simp [planeXShearSubstitution]

theorem planeXShearAlgEquiv_irreducible_iff
    (f : MvPolynomial (Fin 2) R) :
    Irreducible (planeXShearAlgEquiv R f) ↔ Irreducible f := by
  constructor
  · intro h
    have h' : Irreducible
        ((planeXShearAlgEquiv R).symm (planeXShearAlgEquiv R f)) :=
      h.map (planeXShearAlgEquiv R).symm.toMulEquiv
    simpa only [AlgEquiv.symm_apply_apply] using h'
  · intro h
    exact h.map (planeXShearAlgEquiv R).toMulEquiv

/-- Chain rule in the first coordinate for the symmetric shear. -/
theorem pderiv_zero_planeXShearAlgEquiv (f : MvPolynomial (Fin 2) R) :
    pderiv 0 (planeXShearAlgEquiv R f) =
      planeXShearAlgEquiv R (pderiv 0 f) := by
  change pderiv 0 (bind₁ (planeXShearSubstitution R) f) =
    bind₁ (planeXShearSubstitution R) (pderiv 0 f)
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, map_add]
  | mul_X f i hf =>
      fin_cases i <;> simp [hf]

/-- Chain rule in the second coordinate for the symmetric shear. -/
theorem pderiv_one_planeXShearAlgEquiv (f : MvPolynomial (Fin 2) R) :
    pderiv 1 (planeXShearAlgEquiv R f) =
      planeXShearAlgEquiv R (pderiv 0 f + pderiv 1 f) := by
  change pderiv 1 (bind₁ (planeXShearSubstitution R) f) =
    bind₁ (planeXShearSubstitution R) (pderiv 0 f + pderiv 1 f)
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, map_add]; abel
  | mul_X f i hf =>
      fin_cases i <;> simp [hf] <;> ring

/-- If only the first coordinate is separating, the symmetric shear makes
both coordinates separating. -/
theorem planeXShearAlgEquiv_pderivs_ne_zero_of_ne_zero
    (f : MvPolynomial (Fin 2) R)
    (hne : pderiv 0 f ≠ 0) (hzero : pderiv 1 f = 0) :
    pderiv 0 (planeXShearAlgEquiv R f) ≠ 0 ∧
      pderiv 1 (planeXShearAlgEquiv R f) ≠ 0 := by
  have hs : planeXShearAlgEquiv R (pderiv 0 f) ≠ 0 := by
    intro hs
    apply hne
    apply (planeXShearAlgEquiv R).injective
    simpa using hs
  rw [pderiv_zero_planeXShearAlgEquiv,
    pderiv_one_planeXShearAlgEquiv, hzero, add_zero]
  exact ⟨hs, hs⟩

/-- The symmetric shear commutes with extension of coefficients. -/
theorem map_planeXShearAlgEquiv {S : Type*} [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Fin 2) R) :
    map φ (planeXShearAlgEquiv R f) = planeXShearAlgEquiv S (map φ f) := by
  rw [planeXShearAlgEquiv_apply, planeXShearAlgEquiv_apply, map_bind₁]
  congr 1
  ext i
  fin_cases i <;> simp [planeXShearSubstitution]

end

section AbsoluteIrreducibility

variable (K : Type*) [Field K]

/-- Absolute irreducibility is invariant under the coordinate shear. -/
theorem planeYShearAlgEquiv_absolutelyIrreducible_iff
    (f : MvPolynomial (Fin 2) K) :
    Irreducible
        (map (algebraMap K (AlgebraicClosure K)) (planeYShearAlgEquiv K f)) ↔
      Irreducible (map (algebraMap K (AlgebraicClosure K)) f) := by
  rw [map_planeYShearAlgEquiv]
  exact planeYShearAlgEquiv_irreducible_iff _ _

/-- Absolute irreducibility is invariant under the symmetric shear. -/
theorem planeXShearAlgEquiv_absolutelyIrreducible_iff
    (f : MvPolynomial (Fin 2) K) :
    Irreducible
        (map (algebraMap K (AlgebraicClosure K)) (planeXShearAlgEquiv K f)) ↔
      Irreducible (map (algebraMap K (AlgebraicClosure K)) f) := by
  rw [map_planeXShearAlgEquiv]
  exact planeXShearAlgEquiv_irreducible_iff _ _

/-- An absolutely irreducible bivariate polynomial over a field of positive
characteristic cannot have both partial derivatives zero.  The proof passes
to the algebraic closure, where perfectness turns simultaneous vanishing
into a `p`-th power. -/
theorem pderiv_zero_ne_zero_or_pderiv_one_ne_zero_of_absolutelyIrreducible
    [Finite K]
    (f : MvPolynomial (Fin 2) K)
    (hirr : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f)) :
    pderiv 0 f ≠ 0 ∨ pderiv 1 f ≠ 0 := by
  let p := ringChar K
  let : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  by_contra h
  rw [not_or] at h
  have hzero : pderiv 0 f = 0 := not_ne_iff.mp h.1
  have hone : pderiv 1 f = 0 := not_ne_iff.mp h.2
  have hderivMapped : ∀ i,
      pderiv i (map (algebraMap K (AlgebraicClosure K)) f) = 0 := by
    intro i
    fin_cases i
    · rw [pderiv_map]
      simpa using congrArg (map (algebraMap K (AlgebraicClosure K))) hzero
    · rw [pderiv_map]
      simpa using congrArg (map (algebraMap K (AlgebraicClosure K))) hone
  exact (not_irreducible_of_forall_pderiv_eq_zero p
    (map (algebraMap K (AlgebraicClosure K)) f) hderivMapped) hirr

/-- For an absolutely irreducible plane polynomial over a finite field,
either both coordinates already separate or one of the two elementary
shears makes both partial derivatives nonzero. -/
theorem pderivs_ne_zero_or_planeYShear_or_planeXShear_of_absolutelyIrreducible
    [Finite K]
    (f : MvPolynomial (Fin 2) K)
    (hirr : Irreducible
      (map (algebraMap K (AlgebraicClosure K)) f)) :
    (pderiv 0 f ≠ 0 ∧ pderiv 1 f ≠ 0) ∨
      (pderiv 0 (planeYShearAlgEquiv K f) ≠ 0 ∧
        pderiv 1 (planeYShearAlgEquiv K f) ≠ 0) ∨
      (pderiv 0 (planeXShearAlgEquiv K f) ≠ 0 ∧
        pderiv 1 (planeXShearAlgEquiv K f) ≠ 0) := by
  rcases pderiv_zero_ne_zero_or_pderiv_one_ne_zero_of_absolutelyIrreducible
      K f hirr with hzero | hone
  · by_cases hone' : pderiv 1 f = 0
    · exact Or.inr (Or.inr
        (planeXShearAlgEquiv_pderivs_ne_zero_of_ne_zero K f hzero hone'))
    · exact Or.inl ⟨hzero, hone'⟩
  · by_cases hzero' : pderiv 0 f = 0
    · exact Or.inr (Or.inl
        (planeYShearAlgEquiv_pderivs_ne_zero_of_zero_ne K f hzero' hone))
    · exact Or.inl ⟨hzero', hone⟩

end AbsoluteIrreducibility

section FiniteField

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- The shear bijects the affine zero sets before and after substitution. -/
def planeYShearAffineZeroEquiv (f : MvPolynomial (Fin 2) K) :
    ↥(BGS.External.affinePlaneCurveZeros K (planeYShearAlgEquiv K f)) ≃
      ↥(BGS.External.affinePlaneCurveZeros K f) :=
  (planeYShearPointEquiv K).subtypeEquiv fun z => by
    simp only [BGS.External.mem_affinePlaneCurveZeros_iff]
    exact (eval_planeYShearAlgEquiv K f z).congr_left

theorem card_affinePlaneCurveZeros_planeYShearAlgEquiv
    (f : MvPolynomial (Fin 2) K) :
    (BGS.External.affinePlaneCurveZeros K (planeYShearAlgEquiv K f)).card =
      (BGS.External.affinePlaneCurveZeros K f).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (planeYShearAffineZeroEquiv K f)

/-- The symmetric shear bijects the affine zero sets. -/
def planeXShearAffineZeroEquiv (f : MvPolynomial (Fin 2) K) :
    ↥(BGS.External.affinePlaneCurveZeros K (planeXShearAlgEquiv K f)) ≃
      ↥(BGS.External.affinePlaneCurveZeros K f) :=
  (planeXShearPointEquiv K).subtypeEquiv fun z => by
    simp only [BGS.External.mem_affinePlaneCurveZeros_iff]
    exact (eval_planeXShearAlgEquiv K f z).congr_left

theorem card_affinePlaneCurveZeros_planeXShearAlgEquiv
    (f : MvPolynomial (Fin 2) K) :
    (BGS.External.affinePlaneCurveZeros K (planeXShearAlgEquiv K f)).card =
      (BGS.External.affinePlaneCurveZeros K f).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (planeXShearAffineZeroEquiv K f)

end FiniteField

end BGS.HasseWeil
