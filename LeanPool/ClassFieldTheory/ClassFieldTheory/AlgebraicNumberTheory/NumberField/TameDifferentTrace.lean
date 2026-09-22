/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.Ideal.Int
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Trace.Basic
/-!
# A trace witness bounds a primary factor of the different

For a coprime factorization of q times the integer ring, the Chinese
remainder idempotent (1, 0) has trace equal to the dimension of the first
factor. If that factor has norm q^m and q does not divide m, its trace is
nonzero modulo q. Mathlib's trace-dual criterion then shows that the first
factor cannot divide the different. The factor need not be prime.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace AlgebraicNumberTheory.Discriminant

/-- A primary factor whose residue dimension is prime to q cannot divide
an entire additional power into the different. -/
theorem not_dvd_differentIdeal_of_coprime_norm_exponent
    (L : Type*) [Field L] [NumberField L]
    (q m : ℕ) (hq : q.Prime)
    (R Q : Ideal (𝓞 L)) (hRQ : IsCoprime R Q)
    (hMul : R * Q = (Ideal.span {(q : ℤ)}).map (algebraMap ℤ (𝓞 L)))
    (hNorm : R.absNorm = q ^ m) (hm : ¬ q ∣ m) :
    ¬ R ∣ differentIdeal ℤ (𝓞 L) := by
  classical
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  let : Fact q.Prime := ⟨hq⟩
  let : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  let : Algebra (ℤ ⧸ p) (𝓞 L ⧸ R) :=
    Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hMul]
      exact Ideal.mul_le_left)
  let : Algebra (ℤ ⧸ p) (𝓞 L ⧸ Q) :=
    Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hMul]
      exact Ideal.mul_le_right)
  have : IsScalarTower ℤ (ℤ ⧸ p) (𝓞 L ⧸ R) := .of_algebraMap_eq' rfl
  have : IsScalarTower ℤ (ℤ ⧸ p) (𝓞 L ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (ℤ ⧸ p) (𝓞 L ⧸ R) :=
    Module.Finite.of_restrictScalars_finite ℤ (ℤ ⧸ p) (𝓞 L ⧸ R)
  have : Module.Finite (ℤ ⧸ p) (𝓞 L ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite ℤ (ℤ ⧸ p) (𝓞 L ⧸ Q)
  have hpCard : Nat.card (ℤ ⧸ p) = q := Int.card_ideal_quot q
  have hRCard : Nat.card (𝓞 L ⧸ R) = q ^ m := by
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hNorm
  have hDim : Module.finrank (ℤ ⧸ p) (𝓞 L ⧸ R) = m := by
    apply Nat.pow_right_injective hq.two_le
    have hCard := Module.natCard_eq_pow_finrank (K := ℤ ⧸ p) (V := 𝓞 L ⧸ R)
    rw [hpCard, hRCard] at hCard
    exact hCard.symm
  have hCast : (m : ℤ ⧸ p) ≠ 0 := by
    intro h
    have hz : (m : ZMod q) = 0 := by
      simpa using congrArg (Int.quotientSpanNatEquivZMod q) h
    exact hm ((ZMod.natCast_eq_zero_iff m q).mp hz)
  let e : (𝓞 L ⧸ p.map (algebraMap ℤ (𝓞 L))) ≃ₐ[ℤ ⧸ p]
      ((𝓞 L ⧸ R) × (𝓞 L ⧸ Q)) :=
    { __ := (Ideal.quotEquivOfEq hMul.symm).trans
        (Ideal.quotientMulEquivQuotientProd R Q hRQ)
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (1, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem ℤ R Q hMul x ?_ ?_
  · have h := congr((e $hx).2)
    simp? at h
    change Ideal.Quotient.mk Q x = 0 at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  · rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← Algebra.trace_quotient_eq_of_isDedekindDomain, hx,
      Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    have ht : Algebra.trace (ℤ ⧸ p) (𝓞 L ⧸ R) 1 = (m : ℤ ⧸ p) := by
      simpa only [map_one, nsmul_one, hDim] using
        (Algebra.trace_algebraMap (R := ℤ ⧸ p) (S := 𝓞 L ⧸ R) (1 : ℤ ⧸ p))
    change Algebra.trace (ℤ ⧸ p) (𝓞 L ⧸ R) 1 +
      Algebra.trace (ℤ ⧸ p) (𝓞 L ⧸ Q) 0 ≠ 0
    rw [ht, map_zero, add_zero]
    exact hCast

end AlgebraicNumberTheory.Discriminant
