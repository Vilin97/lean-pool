/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Basic definitions for the Chudnovsky formula project

Shared definitions for the formalization of Milla's proof of the Chudnovsky formula
(arXiv:1809.00533v6), targeting Mathlib's `proof_wanted chudnovskySum_eq_pi_inv`.

We define, on top of Mathlib's `UpperHalfPlane`, `PeriodPair`, `E₄`, `E₆` and `E2`:

* `Chudnovsky.Lτ` : the period pair `(1, τ)` for `τ : ℍ`, giving the lattice `ℤ + ℤτ`;
* `Chudnovsky.q` : the nome `q = exp (2πiτ)` (Mathlib's `Periodic.qParam 1`);
* `Chudnovsky.J` : Klein's `J`-invariant `E₄³ / (E₄³ - E₆²)`;
* `Chudnovsky.E₂star` : the non-holomorphic Eisenstein series `E₂*(τ) = E₂(τ) - 3/(π Im τ)`;
* `Chudnovsky.s₂` : Ramanujan's function `s₂ = (E₄/E₆)·E₂*`;
* `Chudnovsky.τ₁₆₃`, `Chudnovsky.τ₈` : the CM points `(1+i√163)/2` and `i√2`.

Following the plan in `PLAN.md`, `J` is defined directly in terms of Eisenstein series; the
lattice-theoretic description `g₂³/Δ` becomes a lemma (proved in `Fourier.lean`).
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries

open scoped Real ComplexOrder

/-- The period pair `(1, τ)` generating the lattice `L_τ = ℤ + ℤτ` for `τ` in the upper
half-plane. -/
def Lτ (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := (LinearIndependent.pair_iff' one_ne_zero).mpr fun a ha ↦ by
    have h := congrArg Complex.im ha
    simp only [Complex.smul_im, Complex.one_im, smul_zero, coe_im] at h
    exact τ.im_pos.ne' h.symm

@[simp] lemma Lτ_ω₁ (τ : ℍ) : (Lτ τ).ω₁ = 1 := rfl

@[simp] lemma Lτ_ω₂ (τ : ℍ) : (Lτ τ).ω₂ = τ := rfl

/-- The nome `q = exp (2πiτ)`, as Mathlib's `Periodic.qParam` with period `1`. -/
def q (τ : ℍ) : ℂ := Function.Periodic.qParam 1 τ

lemma q_eq (τ : ℍ) : q τ = Complex.exp (2 * π * Complex.I * τ) := by
  simp [q, Function.Periodic.qParam]

lemma norm_q (τ : ℍ) : ‖q τ‖ = Real.exp (-(2 * π * τ.im)) := by
  rw [q, Function.Periodic.norm_qParam]
  simp [coe_im]

lemma norm_q_lt_one (τ : ℍ) : ‖q τ‖ < 1 := by
  rw [norm_q, Real.exp_lt_one_iff, neg_lt_zero]
  positivity

/-- Klein's `J`-invariant, defined via Eisenstein series: `J = E₄³ / (E₄³ - E₆²)`.
The classical lattice description `J = g₂³ / Δ` is proved in `Fourier.lean`. -/
def J (τ : ℍ) : ℂ := E₄ τ ^ 3 / (E₄ τ ^ 3 - E₆ τ ^ 2)

/-- The denominator of `J` never vanishes: `E₄³ - E₆² = 1728·Δ` and `Δ ≠ 0`. -/
lemma E₄_cube_sub_E₆_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 := by
  have h := discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hΔ := discriminant_ne_zero τ
  intro hc
  rw [hc] at h
  simp only [zero_div] at h
  exact hΔ h

lemma E₄_cube_sub_E₆_sq_eq_discriminant (τ : ℍ) :
    E₄ τ ^ 3 - E₆ τ ^ 2 = 1728 * discriminant τ := by
  rw [discriminant_eq_E₄_cube_sub_E₆_sq τ]
  ring

/-- `1728·J = E₄³/Δ`. -/
lemma mul_J_eq (τ : ℍ) : 1728 * J τ = E₄ τ ^ 3 / discriminant τ := by
  have hΔ := discriminant_ne_zero τ
  rw [J, E₄_cube_sub_E₆_sq_eq_discriminant]
  field_simp

/-- The non-holomorphic (quasi-modular) Eisenstein series
`E₂*(τ) = E₂(τ) - 3 / (π · Im τ)`. -/
def E₂star (τ : ℍ) : ℂ := E2 τ - 3 / (π * τ.im)

/-- Ramanujan's function `s₂(τ) = (E₄(τ)/E₆(τ)) · E₂*(τ)`. -/
def s₂ (τ : ℍ) : ℂ := E₄ τ / E₆ τ * E₂star τ

/-- The CM point `τ₁₆₃ = (1 + i√163)/2` of discriminant `-163`. -/
def τ₁₆₃ : ℍ := ⟨⟨1 / 2, Real.sqrt 163 / 2⟩,
  div_pos (Real.sqrt_pos.mpr (by norm_num)) two_pos⟩

lemma τ₁₆₃_re : (τ₁₆₃ : ℂ).re = 1 / 2 := rfl

@[simp] lemma τ₁₆₃_im : τ₁₆₃.im = Real.sqrt 163 / 2 := rfl

/-- The CM point `τ₈ = i√2` of discriminant `-8`, used for the branch-of-square-root
argument in the Main Theorem. -/
def τ₈ : ℍ := ⟨⟨0, Real.sqrt 2⟩, Real.sqrt_pos.mpr (by norm_num)⟩

lemma τ₈_re : (τ₈ : ℂ).re = 0 := rfl

@[simp] lemma τ₈_im : τ₈.im = Real.sqrt 2 := rfl

/-- All estimates in the paper hold on the region `Im τ > 1.25`. -/
def Region : Set ℍ := {τ : ℍ | 5 / 4 < τ.im}

lemma τ₁₆₃_mem_Region : τ₁₆₃ ∈ Region := by
  simp only [Region, Set.mem_setOf_eq, τ₁₆₃_im]
  nlinarith [Real.sq_sqrt (by norm_num : (163 : ℝ) ≥ 0).le, Real.sqrt_nonneg (163 : ℝ)]

lemma τ₈_mem_Region : τ₈ ∈ Region := by
  simp only [Region, Set.mem_setOf_eq, τ₈_im]
  nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0).le, Real.sqrt_nonneg (2 : ℝ)]

end Chudnovsky
