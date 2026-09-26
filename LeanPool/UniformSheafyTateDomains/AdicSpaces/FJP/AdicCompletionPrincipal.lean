/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Noetherianity of the adic completion at a principal ideal

Let `R` be a commutative ring and `a : R`. We construct the canonical ring homomorphism

* `AdicCompletion.ofPowerSeries a : R⟦X⟧ →+* AdicCompletion (Ideal.span {a}) R`

sending `X` to `a`: on the `n`-th component it evaluates the truncation of a power series
below degree `n` at `a`, modulo `(a) ^ n`.  This map is always surjective
(`AdicCompletion.ofPowerSeries_surjective`): a compatible sequence of residues can be
telescoped into the coefficients of a preimage power series.

Since `R⟦X⟧` is Noetherian whenever `R` is, we deduce the main result:

* `AdicCompletion.isNoetherianRing_span_singleton`: if `R` is a Noetherian commutative ring,
  then the `(a)`-adic completion `AdicCompletion (Ideal.span {a}) R` is Noetherian, and
* `AdicCompletion.isNoetherianRing_of_isPrincipal`: the same for the completion at any
  principal ideal.

This is the principal-ideal case of the classical fact that the `I`-adic completion of a
Noetherian ring is Noetherian.
-/

@[expose] public section

suppress_compilation

open PowerSeries

open scoped Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- If two polynomials agree in all coefficients below `n`, then their values at `a` are
congruent modulo `(a) ^ n`. -/
theorem eval_sub_eval_mem_span_singleton_pow {n : ℕ} {p q : R[X]}
    (h : ∀ d < n, p.coeff d = q.coeff d) (a : R) :
    p.eval a - q.eval a ∈ Ideal.span {a} ^ n := by
  obtain ⟨u, hu⟩ := (X_pow_dvd_iff (f := p - q)).mpr fun d hd ↦ by
    rw [coeff_sub, h d hd, sub_self]
  rw [← eval_sub, hu, eval_mul, eval_pow, eval_X, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

end Polynomial

namespace AdicCompletion

variable {R : Type*} [CommRing R] (a : R)

/-- Evaluation of the truncation below degree `n` of a power series at `a`, as a ring
homomorphism `R⟦X⟧ →+* R ⧸ (a) ^ n`.  This is the `n`-th component of
`AdicCompletion.ofPowerSeries`. -/
def truncEvalMk (n : ℕ) : R⟦X⟧ →+* R ⧸ Ideal.span {a} ^ n where
  toFun f := Ideal.Quotient.mk _ ((trunc n f).eval a)
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {a} ^ n)),
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa using
      Polynomial.eval_sub_eval_mem_span_singleton_pow (p := trunc n (1 : R⟦X⟧)) (q := 1)
        (fun d hd ↦ by simp [coeff_trunc, hd, coeff_one, Polynomial.coeff_one]) a
  map_mul' f g := by
    rw [← map_mul (Ideal.Quotient.mk (Ideal.span {a} ^ n)),
      Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← Polynomial.eval_mul]
    exact Polynomial.eval_sub_eval_mem_span_singleton_pow
      (fun d hd ↦ by
        rw [coeff_trunc, ite_eq_left hd, coeff_mul_eq_coeff_trunc_mul_trunc f g hd,
          ← Polynomial.coe_mul, Polynomial.coeff_coe]) a
  map_zero' := by simp
  map_add' f g := by simp

@[simp]
theorem truncEvalMk_apply (n : ℕ) (f : R⟦X⟧) :
    truncEvalMk a n f = Ideal.Quotient.mk (Ideal.span {a} ^ n) ((trunc n f).eval a) :=
  rfl

theorem factorPow_comp_truncEvalMk {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {a}) hmn).comp (truncEvalMk a n) =
      truncEvalMk a m := by
  ext f
  rw [RingHom.comp_apply, truncEvalMk_apply, truncEvalMk_apply, Ideal.Quotient.factor_mk,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Polynomial.eval_sub_eval_mem_span_singleton_pow
    (fun d hd ↦ by simp [coeff_trunc, hd, hd.trans_le hmn]) a

/-- The canonical ring homomorphism from `R⟦X⟧` to the `(a)`-adic completion of `R`, sending
`X` to `a`: on the `n`-th component it evaluates the truncation below degree `n` at `a`,
modulo `(a) ^ n`.  It is surjective; see `AdicCompletion.ofPowerSeries_surjective`. -/
def ofPowerSeries : R⟦X⟧ →+* AdicCompletion (Ideal.span {a}) R :=
  liftRingHom (Ideal.span {a}) (truncEvalMk a) fun hmn ↦ factorPow_comp_truncEvalMk a hmn

@[simp]
theorem evalₐ_ofPowerSeries (n : ℕ) (f : R⟦X⟧) :
    evalₐ (Ideal.span {a}) n (ofPowerSeries a f) =
      Ideal.Quotient.mk (Ideal.span {a} ^ n) ((trunc n f).eval a) :=
  evalₐ_liftRingHom _ _ _ n f

@[simp]
theorem ofPowerSeries_C (r : R) :
    ofPowerSeries a (C r) = of (Ideal.span {a}) R r := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_ofPowerSeries, evalₐ_of, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simpa using
    Polynomial.eval_sub_eval_mem_span_singleton_pow (p := trunc n (C r))
      (q := Polynomial.C r)
      (fun d hd ↦ by simp [coeff_trunc, hd, coeff_C, Polynomial.coeff_C]) a

@[simp]
theorem ofPowerSeries_X :
    ofPowerSeries a X = of (Ideal.span {a}) R a := by
  refine ext_evalₐ fun n ↦ ?_
  rw [evalₐ_ofPowerSeries, evalₐ_of, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simpa using
    Polynomial.eval_sub_eval_mem_span_singleton_pow (p := trunc n (X : R⟦X⟧))
      (q := Polynomial.X)
      (fun d hd ↦ by simp [coeff_trunc, hd, coeff_X, Polynomial.coeff_X, eq_comm]) a

/-- The ring homomorphism `R⟦X⟧ →+* AdicCompletion (Ideal.span {a}) R` is surjective: given a
compatible sequence of residues `r`, the successive differences `r (k + 1) - r k` are
divisible by `a ^ k`, and the resulting quotients telescope into the coefficients of a
preimage power series. -/
theorem ofPowerSeries_surjective : Function.Surjective (ofPowerSeries a) := by
  intro x
  refine induction_on (p := fun y ↦ ∃ g, ofPowerSeries a g = y) (Ideal.span {a}) R x
    fun r ↦ ?_
  -- Extract the successive differences: `r (k + 1) - r k = a ^ k * c k`.
  have key : ∀ k : ℕ, ∃ c : R, r.val (k + 1) - r.val k = a ^ k * c := by
    intro k
    have h := SModEq.sub_mem.mp (r.property (Nat.le_succ k))
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨-c, by linear_combination -hc⟩
  choose c hc using key
  refine ⟨C (r.val 0) + PowerSeries.mk c, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_ofPowerSeries, evalₐ_mk]
  rcases n with - | n
  · rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simp
  -- The partial sums telescope to the given residues.
  have hsum : ∀ m : ℕ,
      (trunc (m + 1) (C (r.val 0) + PowerSeries.mk c)).eval a = r.val (m + 1) := by
    intro m
    induction m with
    | zero =>
      rw [trunc_one_left]
      simp only [map_add, coeff_zero_C, coeff_mk, Polynomial.eval_add, Polynomial.eval_C]
      linear_combination -hc 0
    | succ m ih =>
      rw [trunc_succ, Polynomial.eval_add, ih, Polynomial.eval_monomial]
      simp only [map_add, coeff_C, Nat.succ_ne_zero, ite_false, coeff_mk, zero_add]
      linear_combination -hc (m + 1)
  rw [hsum n]

/-- The `(a)`-adic completion of a Noetherian commutative ring is Noetherian: it is a
quotient of the power series ring `R⟦X⟧`.

This is the principal-ideal case of the fact that the adic completion of a Noetherian ring
at any ideal is Noetherian. -/
theorem isNoetherianRing_span_singleton (R : Type*) [CommRing R] [IsNoetherianRing R]
    (a : R) : IsNoetherianRing (AdicCompletion (Ideal.span {a}) R) :=
  isNoetherianRing_of_surjective R⟦X⟧ _ (ofPowerSeries a) (ofPowerSeries_surjective a)

/-- The adic completion of a Noetherian commutative ring at a principal ideal is
Noetherian. -/
theorem isNoetherianRing_of_isPrincipal {R : Type*} [CommRing R] [IsNoetherianRing R]
    {I : Ideal R} (hI : I.IsPrincipal) : IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨a, rfl⟩ := hI
  exact isNoetherianRing_span_singleton R a

end AdicCompletion
