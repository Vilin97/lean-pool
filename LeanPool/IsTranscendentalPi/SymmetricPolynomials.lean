/-
Copyright (c) 2026 James Huang, Samuël Borza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Huang, Samuël Borza
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Symmetric polynomials

Multisets `{b₀, …, bₙ₋₁}` attached to maps `b : Fin n → α` and symmetric-function
machinery feeding the algebraic estimates of Niven's proof.
-/

open Polynomial
open Multiset

open scoped Polynomial
open scoped BigOperators

/-- The multiset `{b₀, …, bₙ₋₁}` attached to `b : Fin n → α`. -/
def valuesFin {α : Type*} {n : ℕ} (b : Fin n → α) : Multiset α :=
  (Finset.univ : Finset (Fin n)).val.map b

/-- Every multiset can be indexed by a map `a : Fin n → α`. -/
lemma exists_valuesFin_eq_multiset {α : Type*} (s : Multiset α) :
    ∃ (n : ℕ) (a : Fin n → α), s = valuesFin a := by
  refine Quotient.inductionOn s ?_
  intro l
  refine ⟨l.length, l.get, ?_⟩
  simp [valuesFin, Fin.univ_val_map]

/-- The roots of a polynomial can be listed as a valuesFin `a₀, …, aₙ₋₁`. -/
lemma exists_valuesFin_eq_aroots (P : ℚ[X]) :
    ∃ (n : ℕ) (a : Fin n → ℂ), P.aroots ℂ = valuesFin a := by
  simp [exists_valuesFin_eq_multiset]

/-- For a monic polynomial with roots `b₀, …, bₙ₋₁`, its `k`-th coefficient is written
with an elementary symmetric polynomial in the roots. -/
lemma coeff_eq_esymm_of_roots
    {R S : Type*} [CommRing R] [Field S] [Algebra R S] [IsAlgClosed S]
    {n : ℕ} (B : Polynomial R) (b : Fin n → S)
    (hmonic : B.Monic) (hroots : B.aroots S = valuesFin b)
    {k : ℕ} (hk : k ≤ n) :
    algebraMap R S (B.coeff k)
      = MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) b
          (((-1) ^ (n - k)) * MvPolynomial.esymm (Fin n) ℤ (n - k)) := by
  let p : Polynomial S := B.map (algebraMap R S)
  have hsplit : p.Splits := by simpa [p] using IsAlgClosed.splits p
  have hdeg : p.natDegree = n := by
    rw [hsplit.natDegree_eq_card_roots]
    simp [p, hroots, valuesFin]
  have hlead : p.leadingCoeff = 1 := by
    simpa [p] using (Monic.map (algebraMap R S) hmonic).leadingCoeff
  rw [← Polynomial.coeff_map]
  calc
    _ = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) := by
      exact Polynomial.coeff_eq_esymm_roots_of_splits hsplit (hdeg ▸ hk)
    _ = (-1) ^ (n - k) * (valuesFin b).esymm (n - k) := by
      simp [hdeg, hlead, p, hroots]
    _ = _ := by simp [valuesFin, MvPolynomial.aeval_esymm_eq_multiset_esymm]

/-- If `P` is symmetric, then `P(b₀, …, bₙ₋₁)` can be rewritten as a polynomial expression in
the coefficients of the monic polynomial with roots `b₀, …, bₙ₋₁`. -/
lemma symmetric_poly_at_roots_eq_poly_of_esymm
    {R S : Type*} [CommRing R] [Field S] [Algebra R S] [IsAlgClosed S]
    {n : ℕ} (B : R[X]) (a : Fin n → S)
    (hmonic : B.Monic) (hroots : B.aroots S = valuesFin a)
    (P : MvPolynomial (Fin n) ℤ) (hP : MvPolynomial.IsSymmetric P) :
    ∃ Q : MvPolynomial (Fin n) ℤ,
      MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) a P
        = algebraMap R S (MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := R)
              (fun i : Fin n => (-1) ^ (i.1 + 1) * B.coeff (n - (i.1 + 1))) Q) := by
  obtain ⟨Q, hQ⟩ :=
    (MvPolynomial.esymmAlgHom_fin_surjective (R := ℤ) (m := n) (n := n) le_rfl) ⟨P, hP⟩
  refine ⟨Q, ?_⟩
  apply_fun (fun p : MvPolynomial.symmetricSubalgebra (Fin n) ℤ =>
    MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) a p.1) at hQ
  rw [MvPolynomial.esymmAlgHom_apply] at hQ
  rw [← hQ, MvPolynomial.comp_aeval_apply]
  rw [← MvPolynomial.aeval_algebraMap_apply
    (R := ℤ) (A := R) (B := S)
    (x := fun i : Fin n => (-1) ^ (i.1 + 1) * B.coeff (n - (i.1 + 1))) (p := Q)]
  congr with i
  simpa [tsub_tsub_cancel_of_le (Nat.succ_le_of_lt i.2), ← mul_assoc, ← pow_add] using
    congrArg (fun z : S => (-1 : S) ^ (i.1 + 1) * z)
    ((coeff_eq_esymm_of_roots
      (B := B) (b := a) hmonic hroots (k := n - (i.1 + 1)) (Nat.sub_le _ _)).symm)

/-- If `P` is symmetric, then `P(b₀, …, bₙ₋₁) ∈ R` if `b₀, …, bₙ₋₁` are
the roots of a monic polynomial over `R`. -/
lemma symmetric_poly_at_roots
    {R S : Type*} [CommRing R] [Field S] [Algebra R S] [IsAlgClosed S]
    {n : ℕ} (B : R[X]) (a : Fin n → S)
    (hmonic : B.Monic) (hroots : B.aroots S = valuesFin a)
    (P : MvPolynomial (Fin n) ℤ) (hP : MvPolynomial.IsSymmetric P) :
    ∃ z : R, MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := S) a P = algebraMap R S z := by
  obtain ⟨Q, hQ⟩ := symmetric_poly_at_roots_eq_poly_of_esymm (B := B) (a := a) hmonic hroots P hP
  exact ⟨MvPolynomial.aeval (σ := Fin n) (R := ℤ) (S₁ := R)
    (fun i : Fin n => (-1) ^ (i.1 + 1) * B.coeff (n - (i.1 + 1))) Q, hQ⟩
