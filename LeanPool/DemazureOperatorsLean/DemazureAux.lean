/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/

import LeanPool.DemazureOperatorsLean.Demazure


noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

/- We are going to define the Demazure operator acting on polynomial fractions. For this,
we first define a structure to represent these fractions, and then we will quotient it by
the proportionality equivalence relation.

This local quotient is auxiliary proof infrastructure for the Demazure relations below; it
is not intended as reusable fraction-field or localization theory.
-/

/-- A numerator-denominator representative for a rational expression in the polynomial ring. -/
structure PolyFraction' (n : ℕ) where
  /-- The numerator polynomial. -/
  numerator : MvPolynomial (Fin (n + 1)) ℂ
  /-- The denominator polynomial. -/
  denominator : MvPolynomial (Fin (n + 1)) ℂ
  /-- The denominator is nonzero. -/
  denominator_ne_zero : denominator ≠ 0

example : PolyFraction' 2 := ⟨X 0 + X 1, 1, one_ne_zero⟩
/-- View a polynomial as a fraction with denominator one. -/
def to_frac (p : MvPolynomial (Fin (n + 1)) ℂ) : PolyFraction' n := ⟨p, 1, one_ne_zero⟩

/-- The proportionality relation on polynomial fractions. -/
def r (n : ℕ) : PolyFraction' n → PolyFraction' n → Prop :=
  fun p q => p.numerator * q.denominator = q.numerator * p.denominator

lemma r_equiv : Equivalence (r n) := by
  constructor
  · intro p
    rfl
  · intro p q h
    exact h.symm
  · intro x y z h1 h2
    change x.numerator * z.denominator = z.numerator * x.denominator
    change x.numerator * y.denominator = y.numerator * x.denominator at h1
    change y.numerator * z.denominator = z.numerator * y.denominator at h2
    by_cases h3 : y.numerator = 0
    · simp[h3, y.denominator_ne_zero] at h1
      simp[h3, y.denominator_ne_zero] at h2
      simp[h1, h2]
    · apply poly_cancel_left y.denominator_ne_zero
      apply poly_cancel_left h3
      ring_nf
      rw[mul_assoc y.numerator]
      rw[mul_comm y.denominator x.numerator]
      rw[h1]
      rw[mul_comm y.numerator (y.numerator * x.denominator)]
      rw[mul_assoc]
      rw[h2]
      ring_nf

instance s (n : ℕ) : Setoid (PolyFraction' n) where
  r := r n
  iseqv := r_equiv

instance has_equiv : HasEquiv (PolyFraction' n) := instHasEquivOfSetoid

lemma equiv_r {a b : PolyFraction' n} : (r n) a b ↔ a ≈ b := by
  rfl


/-- The quotient type of polynomial fractions modulo proportionality. -/
def PolyFraction (n : ℕ) := (Quotient (s n))

/-- The quotient map from fraction representatives. -/
def mk (p : PolyFraction' n) : PolyFraction n := Quotient.mk (s n) p

/-- The quotient map from polynomials, viewed as fractions with denominator one. -/
def mk' (p : MvPolynomial (Fin (n + 1)) ℂ) : PolyFraction n := mk ⟨p, 1, one_ne_zero⟩


/- This lemmas enables us to compute the result of a lift of a function applied at a
 representant class. -/
lemma lift_r {a : PolyFraction' n} {f : PolyFraction' n → PolyFraction' n}
    {c : ∀ (a₁ a₂ : PolyFraction' n), a₁ ≈ a₂ → (mk ∘ f) a₁ = (mk ∘ f) a₂} :
    Quotient.lift (mk ∘ f) c (mk a) = mk (f a) := by
  rfl
@[simp]
lemma lift2_r {a b : PolyFraction' n}
    {f : PolyFraction' n → PolyFraction' n → PolyFraction n}
    {c : ∀ (a₁ b₁ a₂ b₂ : PolyFraction' n), a₁ ≈ a₂ → b₁ ≈ b₂ →
      f a₁ b₁ = f a₂ b₂} :
    Quotient.lift₂ f c (mk a) (mk b) = f a b := by
  rfl

/- Two projections are equal iff the representants are proportional -/
@[simp]
lemma mk_eq {a b : PolyFraction' n} :
    mk a = mk b ↔ a.numerator*b.denominator = a.denominator*b.numerator := by
  constructor
  · intro h
    have hr : a ≈ b := Quotient.exact h
    rw[← equiv_r] at hr
    simpa [r, mul_comm] using hr
  · intro h
    change Quotient.mk (s n) a = Quotient.mk (s n) b
    apply Quotient.sound
    rw[← equiv_r]
    simpa [r, mul_comm] using h

-- function to get a representant of a fraction
lemma get_polyfraction_rep (p : PolyFraction n) : ∃p' : PolyFraction' n, mk p' = p := by
  exact Quotient.exists_rep p

/-- Addition of polynomial-fraction representatives. -/
def add' {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction' n :=
  fun p q => ⟨p.numerator * q.denominator + q.numerator * p.denominator,
    p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

/-- Addition of representatives followed by the quotient map. -/
def add_mk {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q => mk (add' p q)

lemma add'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ →
    add_mk a₁ b₁ = add_mk a₂ b₂ := by
  intro a1 b1 a2 b2 h1 h2
  simp only [add_mk, add', mk_eq]
  ring_nf
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  change a1.numerator * a2.denominator = a2.numerator * a1.denominator at h1
  change b1.numerator * b2.denominator = b2.numerator * b1.denominator at h2
  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.denominator]
  rw[h1]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_assoc a2.denominator]
  rw[h2]
  ring_nf

/-- Addition on quotient polynomial fractions. -/
def add : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (add_mk) (add'_s) p q

-- Enable use of + notation
instance addition : Add (PolyFraction n) := ⟨add⟩
instance addition' : Add (PolyFraction' n) := ⟨add'⟩

/-- Subtraction of polynomial-fraction representatives, followed by the quotient map. -/
def sub' {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q ↦ mk ⟨p.numerator * q.denominator - q.numerator * p.denominator,
    p.denominator * q.denominator, mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

lemma sub'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ →
    (sub' a₁ b₁) = (sub' a₂ b₂) := by
  intro a1 b1 a2 b2 h1 h2
  simp only [sub', mk_eq]
  ring_nf
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  change a1.numerator * a2.denominator = a2.numerator * a1.denominator at h1
  change b1.numerator * b2.denominator = b2.numerator * b1.denominator at h2
  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.denominator]
  rw[h1]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_comm b1.numerator]
  rw[mul_assoc a1.denominator]
  rw[mul_assoc a2.denominator]
  rw[h2]
  ring_nf

/-- Subtraction on quotient polynomial fractions. -/
def sub : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (sub') (sub'_s) p q

/-- Multiplication of polynomial-fraction representatives. -/
def mul' {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction' n :=
  fun p q => ⟨p.numerator * q.numerator, p.denominator * q.denominator,
    mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩

/-- Multiplication of representatives followed by the quotient map. -/
def mul_mk {n : ℕ} : PolyFraction' n → PolyFraction' n → PolyFraction n :=
  fun p q => mk (mul' p q)

lemma mul'_s {n : ℕ} : ∀ a₁ b₁ a₂ b₂ : PolyFraction' n, a₁ ≈ a₂ → b₁ ≈ b₂ →
    (mul_mk a₁ b₁) = (mul_mk a₂ b₂) := by
  intro a1 b1 a2 b2 h1 h2
  simp only [mul_mk, mul', mk_eq]
  ring_nf
  rw[← equiv_r] at h1
  rw[← equiv_r] at h2
  change a1.numerator * a2.denominator = a2.numerator * a1.denominator at h1
  change b1.numerator * b2.denominator = b2.numerator * b1.denominator at h2
  rw[mul_comm a1.numerator]
  rw[mul_assoc b1.numerator]
  rw[h1]
  rw[mul_comm b1.numerator]
  rw[mul_assoc (a2.numerator * a1.denominator)]
  rw[h2]
  ring_nf

/-- Multiplication on quotient polynomial fractions. -/
def mul : PolyFraction n → PolyFraction n → PolyFraction n :=
  fun p q ↦ Quotient.lift₂ (mul_mk) (mul'_s) p q

-- Enable use of * notation
instance multiplication' : Mul (PolyFraction' n) := ⟨mul'⟩
instance multiplication : Mul (PolyFraction n) := ⟨mul⟩

/-- The multiplicative identity as a fraction representative. -/
@[simp]
def one' : PolyFraction' n where
  numerator := 1
  denominator := 1
  denominator_ne_zero := one_ne_zero

/-- The multiplicative identity as a quotient fraction. -/
def one : PolyFraction n := mk one'

/-- The additive identity as a fraction representative. -/
@[simp]
def zero' : PolyFraction' n where
  numerator := 0
  denominator := 1
  denominator_ne_zero := one_ne_zero

/-- The additive identity as a quotient fraction. -/
def zero : PolyFraction n := mk zero'

/-- Negation of polynomial-fraction representatives. -/
def neg' (p : PolyFraction' n) : PolyFraction' n :=
  ⟨-p.numerator, p.denominator, p.denominator_ne_zero⟩

/-- Negation of representatives followed by the quotient map. -/
def neg_mk (p : PolyFraction' n) : PolyFraction n := mk (neg' p)

lemma neg_s (n : ℕ) : ∀ (a₁ a₂ : PolyFraction' n), a₁ ≈ a₂ → (neg_mk a₁) = (neg_mk a₂) := by
  intro a1 a2 h
  simp only [neg_mk, neg', mk_eq, neg_mul, mul_neg, neg_inj]
  ring_nf
  rw[← equiv_r] at h
  change a1.numerator * a2.denominator = a2.numerator * a1.denominator at h
  rw[h]
  ring_nf

/-- Negation on quotient polynomial fractions. -/
def neg (p : PolyFraction n) : PolyFraction n := Quotient.lift neg_mk (neg_s n) p

-- some basic properties of these operations
lemma add_comm (p q : PolyFraction n) : add p q = add q p := by
  rcases get_polyfraction_rep p with ⟨p', hp⟩
  rcases get_polyfraction_rep q with ⟨q', hq⟩
  simp only [add]
  rw[← hp]
  rw[← hq]
  simp[lift2_r]
  simp[add_mk, add']
  ring_nf

lemma add_assoc (p q r : PolyFraction n) : add (add p q) r = add p (add q r) := by
  rcases get_polyfraction_rep p with ⟨p', hp⟩
  rcases get_polyfraction_rep q with ⟨q', hq⟩
  rcases get_polyfraction_rep r with ⟨r', hr⟩
  rw[← hp]
  rw[← hq]
  rw[← hr]
  have hpq : (add (mk p') (mk q')) = mk (add' p' q') := by
    simp[add, add_mk]
  have hqr : (add (mk q') (mk r')) = mk (add' q' r') := by
    simp[add, add_mk]
  rw[hpq, hqr]
  simp only [add, lift2_r]
  simp only [add']
  apply Quotient.sound
  apply equiv_r.mp
  simp[Demazure.r, add']
  ring_nf

-- We don't prove that it is a ring since we don't need all the properties for our use

/- We directly define the Demazure operator on fractions (even though we proved that
the result is a polynomial, for the proofs it's better to keep the result as a fraction)-/
/-- The auxiliary Demazure operator on fraction representatives. -/
def DemAux' (i : Fin n) : PolyFraction' n → PolyFraction' n := fun p =>
  ⟨
    p.numerator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) -
      (SwapVariables (Fin.castSucc i) (Fin.succ i) p.numerator) * p.denominator,
    p.denominator * (SwapVariables (Fin.castSucc i) (Fin.succ i) p.denominator) *
      (X (Fin.castSucc i) - X (Fin.succ i)),
    mul_ne_zero
      (mul_ne_zero p.denominator_ne_zero
        (swap_variables_ne_zero (Fin.castSucc i) (Fin.succ i) p.denominator
          p.denominator_ne_zero))
      (demazure_denominator_not_null i)
    ⟩

lemma DemAux_well_defined (i : Fin n) : ∀ (p q : PolyFraction' n),
    p ≈ q → ((mk ∘ DemAux' i) p) = ((mk ∘ DemAux' i) q) := by
  intro p q h
  simp only [Function.comp_apply, DemAux', SwapVariables, renameEquiv_apply, mk_eq]
  rw[← equiv_r] at h
  change p.numerator * q.denominator = q.numerator * p.denominator at h
  let S : MvPolynomial (Fin (n + 1)) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (n + 1)) ℂ :=
    SwapVariables (Fin.castSucc i) (Fin.succ i)
  let delta : MvPolynomial (Fin (n + 1)) ℂ := X (Fin.castSucc i) - X (Fin.succ i)
  have h_swap : S p.numerator * S q.denominator = S q.numerator * S p.denominator := by
    simpa [S, map_mul] using congrArg S h
  calc
    (p.numerator * S p.denominator - S p.numerator * p.denominator) *
        (q.denominator * S q.denominator * delta) =
      (p.numerator * q.denominator) * (S p.denominator * S q.denominator * delta) -
        (S p.numerator * S q.denominator) * (p.denominator * q.denominator * delta) := by
        ring_nf
    _ = p.denominator * S p.denominator * delta *
        (q.numerator * S q.denominator - S q.numerator * q.denominator) := by
        rw [h, h_swap]
        ring_nf

/-- The auxiliary Demazure operator on quotient polynomial fractions. -/
def DemAux (i : Fin n) (p : PolyFraction n) : PolyFraction n :=
  Quotient.lift (mk ∘ (DemAux' i)) (DemAux_well_defined i) p

/- This definition is equivalent to the direct one on the polynomial ring-/
lemma demazure_definitions_equivalent' : ∀ i : Fin n, ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  mk (DemAux' i (to_frac p)) = mk' (DemazureFun i p) := by
  intro i p
  simp only [mk', mk_eq, mul_one]
  simp only [DemAux', to_frac, SwapVariables, renameEquiv_apply, map_one, mul_one, one_mul]
  have h : DemazureDenominator i * ((DemazureNumerator i p) /ₘ (DemazureDenominator i)) =
      DemazureNumerator i p := demazure_division_exact' i p
  apply (SwapVariables (Fin.castSucc i) (0 : Fin (n + 1))).injective
  apply (MvPolynomial.finSuccEquiv ℂ n).injective
  change DemazureNumerator i p = (MvPolynomial.finSuccEquiv ℂ n)
    ((SwapVariables (Fin.castSucc i) 0)
      ((X (Fin.castSucc i) - X (Fin.succ i)) * DemazureFun i p))
  rw[← h]
  simp only [SwapVariables, renameEquiv_apply, map_mul, map_sub, rename_X,
    Equiv.swap_apply_left, ne_eq, fin_succ_ne_fin_castSucc i, not_false_eq_true,
    Fin.succ_ne_zero, Equiv.swap_apply_of_ne_of_ne]
  rw [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  have h3 : DemazureDenominator i = Polynomial.X - Polynomial.C (X i) := by
    simp [DemazureDenominator]
  rw[← h3]
  rw[← poly_mul_cancel (demazure_denominator_ne_zero i)]
  simp only [DemazureFun, SwapVariables, renameEquiv_apply, rename_rename]
  rw [show (⇑(Equiv.swap (Fin.castSucc i) 0) ∘ ⇑(Equiv.swap (Fin.castSucc i) 0)) =
      id by
    funext k
    simp]
  simp

lemma demazure_definitions_equivalent : ∀ i : Fin n, ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  DemAux i (mk' p) = mk' (DemazureFun i p) := by
  intro i p
  rw[mk']
  simp only [DemAux]
  rw[lift_r]
  rw[← demazure_definitions_equivalent' i p]
  rfl

/- We can prove equalities in the ring of polynomials by reducing to the polynomial fraction case.
This sets the strategy for proving properties of the Demazure operator:

Prove them for DemAux (in DemazureAuxRelations.lean) and then use these lemmas and
the equivalence of both operators
to get the result for Demazure (in DemazureRelations.lean).-/
lemma eq_zero_of_mk'_zero {p : MvPolynomial (Fin (n + 1)) ℂ} : mk' p = zero ↔ p = 0 := by
  constructor
  · intro h
    simpa [mk', zero] using h
  · intro h
    simp[h, mk', zero]

lemma eq_of_eq_mk' {p q : MvPolynomial (Fin (n + 1)) ℂ} : mk' p = mk' q ↔ p = q := by
  constructor
  · intro h
    simpa [mk'] using h
  · intro h
    simp[h]


/- Some lemmas for interplay between mk and add -/
@[simp]
lemma simp_add {p q : PolyFraction n} : p + q = add p q := rfl

lemma mk_add {p q : PolyFraction' n} :  ((mk p) : PolyFraction n) + mk q = mk (p + q) := by
  have h1 : p+q = add' p q := by rfl
  have h2 : mk p + mk q = add (mk p) (mk q) := by rfl
  simp[add, add_mk, add', h1, h2]

lemma mk'_add : ∀ (p q : MvPolynomial (Fin (n + 1)) ℂ), mk' (p + q) = mk' p + mk' q := by
  simp[mk', add, add_mk, add']

@[simp]
lemma simp_mul' {p q : PolyFraction' n} :
    p * q = ⟨p.numerator * q.numerator, p.denominator * q.denominator,
      mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero⟩ := rfl

@[simp]
lemma simp_mul {p q : PolyFraction n} : p * q = mul p q := rfl

lemma mk_mul {p q : PolyFraction' n} :  ((mk p) : PolyFraction n) * mk q = mk (p * q) := by
  have h1 : p*q = mul' p q := by rfl
  have h2 : mk p * mk q = mul (mk p) (mk q) := by rfl
  simp[mul, mul_mk, mul']

lemma mk'_mul {p q : MvPolynomial (Fin (n + 1)) ℂ} :  mk' p * mk' q = mk' (p * q) := by
  simp[mk', mul_mk, mul', mul]

end Demazure

end
