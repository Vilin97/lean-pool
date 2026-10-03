/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Interior
public import LeanPool.Sendov.Boundary

/-!
# Sendov's conjecture and the Phelps–Rodriguez conjecture

> Let `n ≥ 2` and let `p` be a degree `n` polynomial with all zeroes in the closed unit disk.
> Then for every zero `a` of `p` there is a critical point `ζ` of `p` with `‖ζ - a‖ ≤ 1`
> (Sendov), and in fact with `‖ζ - a‖ < 1` unless `‖a‖ = 1` and `p` is a scalar multiple of
> `zⁿ - aⁿ` (Phelps–Rodriguez).

Everything mathematical is already done: this file only removes the normalization `a ∈ [0,1)`
by rotating the variable.  Writing `a = ω r` with `‖ω‖ = 1` and `r = ‖a‖`, the polynomial
`p(ωz)` has the same degree, still has all its zeroes in the closed unit disk, and vanishes at
the *real* point `r`.  Its critical points are the `ω⁻¹ζ`, and `‖ω⁻¹ζ - r‖ = ‖ζ - a‖`, so the
conclusion transports back unchanged.

Three cases, by the position of `a`:

* `a = 0`: `Sendov.sendov_center`;
* `0 < ‖a‖ < 1`: `Sendov.sendov_interior_real` after rotating;
* `‖a‖ = 1`: `Sendov.rubinstein_one` after rotating, whose extremal polynomial `c(zⁿ - 1)`
  rotates back to `c ω⁻ⁿ (zⁿ - aⁿ)`.

## Main statements

* `Sendov.phelps_rodriguez`: the Phelps–Rodriguez conjecture;
* `Sendov.sendov`: Sendov's conjecture.
-/

public section

namespace Sendov

open Polynomial

/-! ### Rotating the variable -/

/-- `p(ωz)`. -/
noncomputable def rotate (ω : ℂ) (p : ℂ[X]) : ℂ[X] := p.comp (C ω * X)

@[simp] lemma eval_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (rotate ω p).eval x = p.eval (ω * x) := by
  simp [rotate, eval_comp]

lemma natDegree_rotate {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) :
    (rotate ω p).natDegree = p.natDegree := by
  rw [rotate, natDegree_comp, natDegree_C_mul hω, natDegree_X, mul_one]

lemma derivative_rotate (ω : ℂ) (p : ℂ[X]) :
    derivative (rotate ω p) = C ω * rotate ω (derivative p) := by
  simp only [rotate, derivative_comp, derivative_mul, derivative_C, derivative_X, zero_mul,
    mul_one, zero_add]

lemma eval_derivative_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (derivative (rotate ω p)).eval x = ω * (derivative p).eval (ω * x) := by
  rw [derivative_rotate, eval_mul, eval_C, eval_rotate]

/-- Rotating is undone by rotating back. -/
lemma rotate_rotate_inv {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) : rotate ω⁻¹ (rotate ω p) = p := by
  have h : (C ω * X : ℂ[X]).comp (C ω⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hω, C_1, one_mul]
  rw [rotate, rotate, comp_assoc, h, comp_X]

lemma roots_rotate {ω : ℂ} (hω : ‖ω‖ = 1) {p : ℂ[X]} (hp : p ≠ 0)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) : ∀ w ∈ (rotate ω p).roots, ‖w‖ ≤ 1 := by
  intro w hw
  have hev : p.eval (ω * w) = 0 := by
    have := (mem_roots'.1 hw).2
    rwa [IsRoot, eval_rotate] at this
  have hmem : ω * w ∈ p.roots := mem_roots'.2 ⟨hp, hev⟩
  have := hroots _ hmem
  rwa [norm_mul, hω, one_mul] at this

/-! ### The Phelps–Rodriguez conjecture -/

/-- **The Phelps–Rodriguez conjecture.**  Every zero `a` of a degree `n ≥ 2` polynomial with all
zeroes in the closed unit disk has a critical point strictly within distance `1`, unless `a` is
on the unit circle and `p` is a scalar multiple of `zⁿ - aⁿ`. -/
theorem phelps_rodriguez {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧ p = C c * (X ^ n - C (a ^ n))) := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨ζ, hζ, hlt⟩ := sendov_center hn hdeg hroots hpa
    exact Or.inl ⟨ζ, hζ, by simpa using hlt⟩
  -- the rotation `a = ω r`
  have hr0 : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hr1 : ‖a‖ ≤ 1 := hroots a (mem_roots'.2 ⟨hp0, hpa⟩)
  have hrC : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hr0
  obtain ⟨ω, hωdef⟩ : ∃ w : ℂ, w = a / ((‖a‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hωne : ω ≠ 0 := by
    rw [hωdef]
    exact div_ne_zero ha0 hrC
  have hωnorm : ‖ω‖ = 1 := by
    rw [hωdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr0),
      div_self (ne_of_gt hr0)]
  have hωr : ω * ((‖a‖ : ℝ) : ℂ) = a := by
    rw [hωdef, div_mul_cancel₀ _ hrC]
  -- the rotated polynomial
  have hdeg' : (rotate ω p).natDegree = n := by rw [natDegree_rotate hωne, hdeg]
  have hroots' := roots_rotate hωnorm hp0 hroots
  have hpr : (rotate ω p).eval ((‖a‖ : ℝ) : ℂ) = 0 := by rw [eval_rotate, hωr, hpa]
  -- transporting a strict witness back
  have htransport : ∀ ζ : ℂ, (derivative (rotate ω p)).eval ζ = 0 →
      ‖ζ - ((‖a‖ : ℝ) : ℂ)‖ < 1 → ∃ ξ : ℂ, (derivative p).eval ξ = 0 ∧ ‖ξ - a‖ < 1 := by
    intro ζ hζ hlt
    refine ⟨ω * ζ, ?_, ?_⟩
    · rw [eval_derivative_rotate] at hζ
      exact (mul_eq_zero.1 hζ).resolve_left hωne
    · have : ω * ζ - a = ω * (ζ - ((‖a‖ : ℝ) : ℂ)) := by rw [mul_sub, hωr]
      rw [this, norm_mul, hωnorm, one_mul]
      exact hlt
  rcases lt_or_eq_of_le hr1 with hlt1 | heq1
  · -- the interior case
    obtain ⟨ζ, hζ, hd⟩ :=
      sendov_interior_real hn hdeg' hroots' (le_of_lt hr0) hlt1 hpr
    exact Or.inl (htransport ζ hζ hd)
  · -- the boundary case: `a = ω`
    have hone : ((‖a‖ : ℝ) : ℂ) = 1 := by rw [heq1]; norm_num
    have haω : a = ω := by rw [← hωr, hone, mul_one]
    have hpr1 : (rotate ω p).eval 1 = 0 := by rwa [hone] at hpr
    rcases rubinstein_one hn hdeg' hroots' hpr1 with ⟨ζ, hζ, hd⟩ | hext
    · exact Or.inl (htransport ζ hζ (by rw [hone]; exact hd))
    -- the extremal case, rotated back
    obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = (rotate ω p).leadingCoeff := ⟨_, rfl⟩
    have hcne : c ≠ 0 := by
      rw [hcdef]
      refine leadingCoeff_ne_zero.2 ?_
      intro h
      rw [h, natDegree_zero] at hdeg'
      omega
    refine Or.inr ⟨heq1, c * ω⁻¹ ^ n,
      mul_ne_zero hcne (pow_ne_zero _ (inv_ne_zero hωne)), ?_⟩
    have hext' : rotate ω p = C c * (X ^ n - 1) := by rw [hcdef]; exact hext
    have hcomp : rotate ω⁻¹ (C c * (X ^ n - 1)) = C c * (C (ω⁻¹ ^ n) * X ^ n - 1) := by
      simp only [rotate, mul_comp, sub_comp, pow_comp, C_comp, X_comp, one_comp, mul_pow,
        ← C_pow]
    have h1 : (C (ω⁻¹ ^ n) * C (ω ^ n) : ℂ[X]) = 1 := by
      rw [← C_mul, ← mul_pow, inv_mul_cancel₀ hωne, one_pow, C_1]
    have hgoal : rotate ω⁻¹ (rotate ω p) = C (c * ω⁻¹ ^ n) * (X ^ n - C (a ^ n)) := by
      rw [hext', hcomp, haω, C_mul]
      linear_combination (C c) * h1
    exact (rotate_rotate_inv hωne p).symm.trans hgoal

/-! ### Sendov's conjecture -/

/-- **Sendov's conjecture.**  Every zero of a degree `n ≥ 2` polynomial with all zeroes in the
closed unit disk has a critical point within distance `1`. -/
theorem sendov {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 := by
  rcases phelps_rodriguez hn hdeg hroots hpa with ⟨ζ, hζ, hlt⟩ | ⟨hnorm, c, hc, hext⟩
  · exact ⟨ζ, hζ, le_of_lt hlt⟩
  -- the extremal polynomial `c(zⁿ - aⁿ)` has its only critical point at the origin, at
  -- distance exactly `‖a‖ = 1`
  refine ⟨0, ?_, by simpa using le_of_eq hnorm⟩
  rw [hext, derivative_C_mul, derivative_sub, derivative_X_pow, derivative_C]
  simp [zero_pow (by omega : n - 1 ≠ 0)]

end Sendov

/-!
## The statements of record

Upstream states both theorems a second time, in the Mathlib-only form that its comparator
configuration checks: the degree hypothesis is `2 ≤ p.natDegree` rather than a separate `n`,
and the disk hypothesis quantifies over all of `ℂ` rather than over `Polynomial.roots`.  Each
is a thin bridge to the theorem above; both differences are bookkeeping only, and the
hypotheses here are the weaker pair, so these conclusions are the stronger claims.
-/

namespace SendovConjecture

open Polynomial

/-- **Sendov's conjecture**, in the Mathlib-only form of the upstream statement of record:
proved by `Sendov.sendov`. -/
theorem sendov {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ ≤ 1 :=
  Sendov.sendov (n := p.natDegree) hdeg rfl (fun w hw => hzeroes w (mem_roots'.1 hw).2) hpa

/-- **The Phelps–Rodriguez conjecture**, in the Mathlib-only form of the upstream statement
of record: proved by `Sendov.phelps_rodriguez`. -/
theorem phelps_rodriguez {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree)
    (hzeroes : ∀ w : ℂ, p.eval w = 0 → ‖w‖ ≤ 1) {a : ℂ} (hpa : p.eval a = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - a‖ < 1)
      ∨ (‖a‖ = 1 ∧ ∃ c : ℂ, c ≠ 0 ∧
          p = C c * (X ^ p.natDegree - C (a ^ p.natDegree))) :=
  Sendov.phelps_rodriguez (n := p.natDegree) hdeg rfl
    (fun w hw => hzeroes w (mem_roots'.1 hw).2) hpa

end SendovConjecture
