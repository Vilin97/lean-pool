/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# q-Pochhammer symbols as formal power series

This file reformulates the q-Pochhammer symbols and the Jacobi triple product
identity in the ring of formal power series `A⟦q⟧`, where `A = ℂ[z, z⁻¹]`
is the ring of Laurent polynomials.

## Key idea

The variable `q` is the formal power series indeterminate `X`, while `z` lives in
the coefficient ring `A = LaurentPolynomial ℂ`. The q-Pochhammer symbol
`(a; q)_∞ = ∏_{k ≥ 0} (1 - a qᵏ)` is a well-defined element of `A⟦X⟧`
because the factors converge to `1` in the `X`-adic (pi) topology — no analytic
convergence hypotheses are needed.

## Main definitions

* `QSeries.FormalPowerSeries.qPochhammer`    — Finite q-Pochhammer `(a; X)_n` in `R⟦X⟧`.
* `QSeries.FormalPowerSeries.qPochhammerInf` — Infinite q-Pochhammer `(a; X)_∞` in `R⟦X⟧`
  (via `tprod`).

## Main results

* `QSeries.FormalPowerSeries.multipliable_one_sub_mul_pow` — The infinite product is multipliable.
* `QSeries.FormalPowerSeries.qPochhammerInf_eq_one_sub_mul`  — `(a; X)_∞ = (1 - a) · (aX; X)_∞`.
* `QSeries.FormalPowerSeries.qPochhammerInf_eq_mk`     — Coefficient-wise characterisation.
* `QSeries.FormalPowerSeries.jacobiTripleProduct` — The Jacobi triple product in `A⟦X⟧`
  (proved in `QSeries.FPSAlgebra`).
-/

public section

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace QSeries.FormalPowerSeries

section Finite

variable {R : Type*} [CommRing R]

/-- **Finite q-Pochhammer symbol** in `R⟦X⟧`.
`(a; X)_n = ∏_{k=0}^{n-1} (1 - a · X^k)` where `a ∈ R⟦X⟧`. -/
@[expose] def qPochhammer (a : R⟦X⟧) (n : ℕ) : R⟦X⟧ :=
  ∏ k ∈ range n, (1 - a * X ^ k)

/-- The empty finite q-Pochhammer product `(a; X)_0 = 1`. -/
@[simp]
theorem qPochhammer_zero (a : R⟦X⟧) : qPochhammer a 0 = 1 := by
  simp [qPochhammer]

/-- The recurrence `(a; X)_{n+1} = (a; X)_n * (1 - a X^n)`. -/
theorem qPochhammer_succ (a : R⟦X⟧) (n : ℕ) :
    qPochhammer a (n + 1) = qPochhammer a n * (1 - a * X ^ n) := by
  simp [qPochhammer, prod_range_succ]

/-- The shift identity `(a; X)_{n+1} = (1 - a) * (aX; X)_n`. -/
theorem qPochhammer_succ_eq_one_sub_mul (a : R⟦X⟧) (n : ℕ) :
    qPochhammer a (n + 1) = (1 - a) * qPochhammer (a * X) n := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih => rw [qPochhammer_succ, ih, qPochhammer_succ]; ring

end Finite

section Stabilisation

variable {R : Type*} [CommRing R]

/-- For `d < n`, the `d`-th coefficient of `(a; X)_{n+1}` equals that of `(a; X)_n`. -/
theorem coeff_qPochhammer_succ (a : R⟦X⟧) {d n : ℕ} (hdn : d < n) :
    coeff d (qPochhammer a (n + 1)) = coeff d (qPochhammer a n) := by
  rw [qPochhammer_succ, mul_sub, mul_one, map_sub, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', ite_eq_right hdn.not_ge, sub_zero]

/-- For `N ≥ M > d`, the `d`-th coefficient of `(a; X)_N` equals that of `(a; X)_M`. -/
theorem coeff_qPochhammer_eq_of_le (a : R⟦X⟧) {d M N : ℕ}
    (hM : d < M) (hN : M ≤ N) :
    coeff d (qPochhammer a N) = coeff d (qPochhammer a M) := by
  induction hN with
  | refl => rfl
  | step hN ih =>
      convert coeff_qPochhammer_succ a (lt_of_lt_of_le hM hN) using 1
      exact ih.symm

end Stabilisation

section Infinite

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

omit [DiscreteTopology R] in
/-- The infinite product `∏_{k ≥ 0} (1 - a X^k)` is multipliable in `R⟦X⟧`. -/
theorem multipliable_one_sub_mul_pow (a : R⟦X⟧) :
    Multipliable (fun k : ℕ => 1 - a * X ^ k) := by
  have hord : ∀ k : ℕ, (k : ℕ∞) ≤ (-(a * X ^ k) : R⟦X⟧).order := fun k =>
    PowerSeries.le_order _ _ fun i hi => by
      have hik : i < k := by exact_mod_cast hi
      rw [map_neg, PowerSeries.coeff_mul_X_pow', ite_eq_right hik.not_ge, neg_zero]
  simp only [sub_eq_add_neg]
  refine WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top R
    (ENat.tendsto_nhds_top_iff_natCast_lt.2 fun n => Filter.eventually_atTop.2 ⟨n + 1, ?_⟩)
  exact fun k hk => lt_of_lt_of_le (by exact_mod_cast hk) (hord k)

/-- **Infinite q-Pochhammer symbol** `(a; X)_∞ = ∏_{k ≥ 0} (1 - a · X^k)`.
Well-defined in `R⟦X⟧` with the pi topology. -/
@[expose] def qPochhammerInf (a : R⟦X⟧) : R⟦X⟧ :=
  ∏' k : ℕ, (1 - a * X ^ k)

/-- The `d`-th coefficient of `(a; X)_∞` equals the `d`-th coefficient of `(a; X)_{d+1}`. -/
theorem coeff_qPochhammerInf (a : R⟦X⟧) (d : ℕ) :
    coeff d (qPochhammerInf a) = coeff d (qPochhammer a (d + 1)) := by
  have h_limit : Filter.Tendsto (fun n => coeff d (qPochhammer a n)) Filter.atTop
      (nhds (coeff d (qPochhammerInf a))) :=
    ((WithPiTopology.continuous_coeff R d).tendsto _).comp
      (multipliable_one_sub_mul_pow a).hasProd.tendsto_prod_nat
  refine tendsto_nhds_unique h_limit (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact (coeff_qPochhammer_eq_of_le a (Nat.lt_succ_self _) hn).symm

/-- **Coefficient-wise definition.** -/
theorem qPochhammerInf_eq_mk (a : R⟦X⟧) :
    qPochhammerInf a = mk fun d => coeff d (qPochhammer a (d + 1)) := by
  ext d; rw [coeff_mk, coeff_qPochhammerInf]

/-- If the constant coefficient of `a` is zero, then that of `(a; X)_∞` is `1`. -/
theorem coeff_zero_qPochhammerInf (a : R⟦X⟧) (ha : coeff 0 a = 0) :
    coeff 0 (qPochhammerInf a) = 1 := by
  rw [coeff_qPochhammerInf, qPochhammer_succ, qPochhammer_zero]
  simp [-coeff_zero_eq_constantCoeff, ha]

/-- The recursion `(a; X)_∞ = (1 - a) * (aX; X)_∞`. -/
theorem qPochhammerInf_eq_one_sub_mul (a : R⟦X⟧) :
    qPochhammerInf a = (1 - a) * qPochhammerInf (a * X) := by
  -- The shifted partial products converge to `(aX; X)_∞`.
  have h_shift : Filter.Tendsto (fun n => ∏ k ∈ range n, (1 - a * X ^ (k + 1))) Filter.atTop
      (nhds (qPochhammerInf (a * X))) :=
    (multipliable_one_sub_mul_pow (a * X)).hasProd.tendsto_prod_nat.congr
      fun n => prod_congr rfl fun k _ => by ring
  -- The partial products of `(a; X)_∞`, reindexed, converge to `(a; X)_∞`.
  have h_all : Filter.Tendsto (fun n => ∏ k ∈ range (n + 1), (1 - a * X ^ k)) Filter.atTop
      (nhds (qPochhammerInf a)) :=
    (multipliable_one_sub_mul_pow a).hasProd.tendsto_prod_nat.comp (Filter.tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique h_all ?_
  have hsplit : ∀ n : ℕ, ∏ k ∈ range (n + 1), (1 - a * X ^ k)
      = (1 - a) * ∏ k ∈ range n, (1 - a * X ^ (k + 1)) := fun n => by
    rw [prod_range_succ', pow_zero, mul_one, mul_comm]
  simp_rw [hsplit]
  exact tendsto_const_nhds.mul h_shift

/-- `(a; X)_∞` is a unit in `R⟦X⟧` whenever `1 - coeff 0 a` is a unit in `R`. -/
theorem isUnit_qPochhammerInf (a : R⟦X⟧) (ha : IsUnit (1 - coeff 0 a : R)) :
    IsUnit (qPochhammerInf a) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
    coeff_qPochhammerInf, qPochhammer_succ, qPochhammer_zero, one_mul, pow_zero, mul_one]
  simpa using ha

end Infinite

section JTP

local notation "A" => LaurentPolynomial ℂ

/-- The discrete topology on `LaurentPolynomial ℂ`, the coefficient ring of the formal-power-series
Jacobi triple product. It is all the `X`-adic arguments below require.

This is `scoped` deliberately: a *global* instance would silently equip Mathlib's
`LaurentPolynomial ℂ` with a discrete topology for every downstream import, which is not this
library's decision to make. Consumers opt in with `open scoped QSeries.FormalPowerSeries`. -/
scoped instance instTopologicalSpaceLaurentPolyComplex : TopologicalSpace A := ⊥

/-- The topology on `LaurentPolynomial ℂ` from the scoped instance above is discrete. -/
scoped instance instDiscreteTopologyLaurentPolyComplex : DiscreteTopology A := ⟨rfl⟩

local notation "PS" => (PowerSeries.C : A →+* A⟦X⟧)

/-- `z = T(1)` viewed as a constant power series in `A⟦X⟧`. -/
abbrev laurentZ : A⟦X⟧ := PS (LaurentPolynomial.T 1)

/-- `z⁻¹ = T(-1)` viewed as a constant power series in `A⟦X⟧`. -/
abbrev laurentZInv : A⟦X⟧ := PS (LaurentPolynomial.T (-1))

/-- `(q; q)_∞` in `A⟦X⟧`. -/
@[expose] def qPochhammerInfX : A⟦X⟧ := qPochhammerInf X

/-- `(-z; q)_∞` in `A⟦X⟧`. -/
@[expose] def qPochhammerInfNegZ : A⟦X⟧ := qPochhammerInf (-laurentZ)

/-- `(-q/z; q)_∞` in `A⟦X⟧`. -/
@[expose] def qPochhammerInfNegXMulZInv : A⟦X⟧ := qPochhammerInf (-X * laurentZInv)

/-- The **Jacobi triple product** (LHS) as an element of `A⟦X⟧`. -/
@[expose] def jacobiProd : A⟦X⟧ := qPochhammerInfX * qPochhammerInfNegZ * qPochhammerInfNegXMulZInv

/-- The **bilateral theta series** (RHS). -/
@[expose] def jacobiBilateral : A⟦X⟧ :=
  (∑' n : ℕ, PS (LaurentPolynomial.T (n : ℤ)) * X ^ n.choose 2) +
  (∑' m : ℕ, PS (LaurentPolynomial.T (-(↑m + 1))) * X ^ (m + 2).choose 2)

end JTP

end QSeries.FormalPowerSeries

end
