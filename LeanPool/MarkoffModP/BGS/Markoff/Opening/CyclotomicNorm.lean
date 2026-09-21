/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Opening.CyclotomicDefect
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# The norm and reduction bridge in the cyclotomic opening

This module connects the already formalized archimedean estimate for the symmetric cyclotomic
defect to the arithmetic norm used in the opening argument.  It also records the exact ideal
theoretic step turning vanishing modulo a prime above `p` into divisibility of the integer norm
by `p`.

The construction of simultaneous compatible lifts and of the prime ideal realizing their
finite-field reduction is deliberately not assumed here.  Those are the remaining inputs needed
before `prime_dvd_integerNorm_of_quotient_eq_zero` can be applied to the defect.
-/

open scoped NumberField

namespace BGS.Markoff

/-- If every complex embedding of a number-field element has norm at most `B`, then its rational
field norm has norm at most `B` to the field degree. -/
theorem algebraNorm_norm_le_pow_of_embeddings
    {K : Type*} [Field K] [NumberField K]
    (x : K) (B : ℝ) (hB : ∀ σ : K →+* ℂ, ‖σ x‖ ≤ B) :
    ‖Algebra.norm ℚ x‖ ≤ B ^ Module.finrank ℚ K := by
  classical
  calc
    ‖Algebra.norm ℚ x‖ = ‖((Algebra.norm ℚ x : ℚ) : ℝ)‖ := by
      exact (Rat.norm_cast_real _).symm
    _ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := Real.norm_eq_abs _
    _ = ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ x)‖ := by
      change |((Algebra.norm ℚ x : ℚ) : ℝ)| = ‖((Algebra.norm ℚ x : ℚ) : ℂ)‖
      rw [Complex.norm_ratCast]
    _ = ‖∏ σ : K →ₐ[ℚ] ℂ, σ x‖ := by rw [Algebra.norm_eq_prod_embeddings]
    _ ≤ ∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _σ : K →ₐ[ℚ] ℂ, B := by
      exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun σ _ ↦ hB σ)
    _ = B ^ Module.finrank ℚ K := by simp [AlgHom.card]

/-- Integral version of `algebraNorm_norm_le_pow_of_embeddings`, with an integer-valued bound. -/
theorem integerNorm_natAbs_le_pow_of_embeddings
    {K : Type*} [Field K] [NumberField K]
    (x : 𝓞 K) (B : ℕ) (hB : ∀ σ : K →+* ℂ, ‖σ (x : K)‖ ≤ B) :
    (Algebra.norm ℤ x).natAbs ≤ B ^ Module.finrank ℚ K := by
  rw [← Nat.cast_le (α := ℝ), Nat.cast_natAbs, Int.cast_abs]
  have h := algebraNorm_norm_le_pow_of_embeddings (x : K) (B : ℝ) hB
  rw [← Algebra.coe_norm_int] at h
  rw [← Rat.norm_cast_real, Real.norm_eq_abs] at h
  simpa only [Rat.cast_intCast, Int.cast_abs, Rat.cast_natCast, Nat.cast_pow] using h

/-- A nonzero algebraic integer has a nonzero, hence positive-natural-absolute, integer norm. -/
theorem integerNorm_natAbs_pos
    {K : Type*} [Field K] [NumberField K] {x : 𝓞 K} (hx : x ≠ 0) :
    0 < (Algebra.norm ℤ x).natAbs := by
  rw [Int.natAbs_pos]
  exact Algebra.norm_ne_zero_iff.mpr hx

/-- If an algebraic integer lies in an ideal above the rational ideal `(p)`, then `p` divides its
integer norm.  Primality is not needed for this algebraic implication; it is needed when the ideal
above `p` is constructed. -/
theorem prime_dvd_integerNorm_of_mem_idealAbove
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (p : ℕ) (x : 𝓞 K)
    (hP : P.under ℤ = Ideal.span {(p : ℤ)}) (hx : x ∈ P) :
    (p : ℤ) ∣ Algebra.norm ℤ x := by
  have h_under : p ∣ Ideal.absNorm P := by
    have h := Int.absNorm_under_dvd_absNorm P
    rw [hP, Ideal.absNorm_span_singleton] at h
    simpa using h
  exact (Int.natCast_dvd_natCast.mpr h_under).trans (Ideal.absNorm_dvd_norm_of_mem hx)

/-- Quotient-map form of `prime_dvd_integerNorm_of_mem_idealAbove`, matching the reduction step in
the paper: reduction of `x` to zero modulo a prime above `p` forces `p ∣ N(x)`. -/
theorem prime_dvd_integerNorm_of_quotient_eq_zero
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (p : ℕ) (x : 𝓞 K)
    (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hx : Ideal.Quotient.mk P x = 0) :
    (p : ℤ) ∣ Algebra.norm ℤ x := by
  apply prime_dvd_integerNorm_of_mem_idealAbove P p x hP
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

/-- If a nonzero algebraic integer reduces to zero modulo an ideal above `(p)`, then `p` is at
most the natural absolute value of its integer norm. -/
theorem modulus_le_integerNorm_natAbs_of_quotient_eq_zero
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) (p : ℕ) (x : 𝓞 K)
    (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hx : Ideal.Quotient.mk P x = 0) (hxne : x ≠ 0) :
    p ≤ (Algebra.norm ℤ x).natAbs := by
  apply Nat.le_of_dvd (integerNorm_natAbs_pos hxne)
  change (p : ℤ).natAbs ∣ (Algebra.norm ℤ x).natAbs
  rw [Int.natAbs_dvd_natAbs]
  simpa using prime_dvd_integerNorm_of_quotient_eq_zero P p x hP hx

/-- Reciprocal trace preserves integrality when both the eigenvalue and its inverse are integral. -/
theorem isIntegral_cyclotomicTrace
    {K : Type*} [Field K] {z : K}
    (hz : IsIntegral ℤ z) (hzinv : IsIntegral ℤ z⁻¹) :
    IsIntegral ℤ (cyclotomicTrace z) := by
  exact hz.add hzinv

/-- The symmetric defect is integral when the three reciprocal traces are integral. -/
theorem isIntegral_cyclotomicDefect
    {K : Type*} [Field K] {z₁ z₂ z₃ : K}
    (hz₁ : IsIntegral ℤ z₁) (hz₁inv : IsIntegral ℤ z₁⁻¹)
    (hz₂ : IsIntegral ℤ z₂) (hz₂inv : IsIntegral ℤ z₂⁻¹)
    (hz₃ : IsIntegral ℤ z₃) (hz₃inv : IsIntegral ℤ z₃⁻¹) :
    IsIntegral ℤ (cyclotomicDefect z₁ z₂ z₃) := by
  have h₁ := isIntegral_cyclotomicTrace hz₁ hz₁inv
  have h₂ := isIntegral_cyclotomicTrace hz₂ hz₂inv
  have h₃ := isIntegral_cyclotomicTrace hz₃ hz₃inv
  exact ((h₁.pow 2).add (h₂.pow 2) |>.add (h₃.pow 2)).sub ((h₁.mul h₂).mul h₃)

/-- The cyclotomic defect of three primitive roots of positive orders is an algebraic integer. -/
theorem isIntegral_cyclotomicDefect_of_primitiveRoots
    {K : Type*} [Field K] {z₁ z₂ z₃ : K} {l₁ l₂ l₃ : ℕ}
    (hz₁ : IsPrimitiveRoot z₁ l₁) (hl₁ : 0 < l₁)
    (hz₂ : IsPrimitiveRoot z₂ l₂) (hl₂ : 0 < l₂)
    (hz₃ : IsPrimitiveRoot z₃ l₃) (hl₃ : 0 < l₃) :
    IsIntegral ℤ (cyclotomicDefect z₁ z₂ z₃) := by
  exact BGS.Markoff.isIntegral_cyclotomicDefect
    (hz₁.isIntegral hl₁) (hz₁.inv.isIntegral hl₁)
    (hz₂.isIntegral hl₂) (hz₂.inv.isIntegral hl₂)
    (hz₃.isIntegral hl₃) (hz₃.inv.isIntegral hl₃)

/-- The exact archimedean norm conclusion needed in the opening: the integer norm of a
cyclotomic defect is bounded by `20 ^ φ(n)`. -/
theorem cyclotomicDefect_integerNorm_natAbs_le_twenty_pow_totient
    {K : Type*} [Field K] [NumberField K]
    {n l₁ l₂ l₃ : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    {z₁ z₂ z₃ : K}
    (hz₁ : IsPrimitiveRoot z₁ l₁) (hl₁ : 0 < l₁)
    (hz₂ : IsPrimitiveRoot z₂ l₂) (hl₂ : 0 < l₂)
    (hz₃ : IsPrimitiveRoot z₃ l₃) (hl₃ : 0 < l₃) :
    let η : 𝓞 K := ⟨cyclotomicDefect z₁ z₂ z₃,
      isIntegral_cyclotomicDefect_of_primitiveRoots hz₁ hl₁ hz₂ hl₂ hz₃ hl₃⟩
    (Algebra.norm ℤ η).natAbs ≤ 20 ^ n.totient := by
  dsimp only
  rw [← IsCyclotomicExtension.Rat.finrank n K]
  apply integerNorm_natAbs_le_pow_of_embeddings
  intro σ
  simpa [cyclotomicDefect, cyclotomicTrace] using
    norm_cyclotomicDefect_le_twenty
      ((hz₁.map_of_injective σ.injective).norm'_eq_one hl₁.ne')
      ((hz₂.map_of_injective σ.injective).norm'_eq_one hl₂.ne')
      ((hz₃.map_of_injective σ.injective).norm'_eq_one hl₃.ne')

/-- A nonzero cyclotomic defect has positive natural absolute integer norm. -/
theorem cyclotomicDefect_integerNorm_natAbs_pos
    {K : Type*} [Field K] [NumberField K]
    {z₁ z₂ z₃ : K} {l₁ l₂ l₃ : ℕ}
    (hz₁ : IsPrimitiveRoot z₁ l₁) (hl₁ : 0 < l₁)
    (hz₂ : IsPrimitiveRoot z₂ l₂) (hl₂ : 0 < l₂)
    (hz₃ : IsPrimitiveRoot z₃ l₃) (hl₃ : 0 < l₃)
    (hη : cyclotomicDefect z₁ z₂ z₃ ≠ 0) :
    let η : 𝓞 K := ⟨cyclotomicDefect z₁ z₂ z₃,
      isIntegral_cyclotomicDefect_of_primitiveRoots hz₁ hl₁ hz₂ hl₂ hz₃ hl₃⟩
    0 < (Algebra.norm ℤ η).natAbs := by
  dsimp only
  apply integerNorm_natAbs_pos
  intro hzero
  apply hη
  exact congrArg (fun x : 𝓞 K ↦ (x : K)) hzero

/-- The completed norm-and-reduction implication: if the nonzero cyclotomic defect reduces to zero
at an ideal above `(p)`, then `p ≤ 20 ^ φ(n)`.  Constructing the compatible reduction data is the
remaining opening problem, not an assumption hidden in this theorem. -/
theorem modulus_le_twenty_pow_totient_of_cyclotomicDefect_reduction
    {K : Type*} [Field K] [NumberField K]
    {n l₁ l₂ l₃ : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    {z₁ z₂ z₃ : K}
    (hz₁ : IsPrimitiveRoot z₁ l₁) (hl₁ : 0 < l₁)
    (hz₂ : IsPrimitiveRoot z₂ l₂) (hl₂ : 0 < l₂)
    (hz₃ : IsPrimitiveRoot z₃ l₃) (hl₃ : 0 < l₃)
    (P : Ideal (𝓞 K)) (p : ℕ)
    (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (hη : cyclotomicDefect z₁ z₂ z₃ ≠ 0)
    (hred : let η : 𝓞 K := ⟨cyclotomicDefect z₁ z₂ z₃,
      isIntegral_cyclotomicDefect_of_primitiveRoots hz₁ hl₁ hz₂ hl₂ hz₃ hl₃⟩
      Ideal.Quotient.mk P η = 0) :
    p ≤ 20 ^ n.totient := by
  let η : 𝓞 K := ⟨cyclotomicDefect z₁ z₂ z₃,
    isIntegral_cyclotomicDefect_of_primitiveRoots hz₁ hl₁ hz₂ hl₂ hz₃ hl₃⟩
  have hηne : η ≠ 0 := by
    intro hzero
    apply hη
    exact congrArg (fun x : 𝓞 K ↦ (x : K)) hzero
  have hp_le : p ≤ (Algebra.norm ℤ η).natAbs :=
    modulus_le_integerNorm_natAbs_of_quotient_eq_zero P p η hP (by simpa [η] using hred) hηne
  exact hp_le.trans <| by
    simpa [η] using
      cyclotomicDefect_integerNorm_natAbs_le_twenty_pow_totient
        hz₁ hl₁ hz₂ hl₂ hz₃ hl₃

end BGS.Markoff
