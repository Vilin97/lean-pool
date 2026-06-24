/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Distribution.TemperateGrowth
import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.HermiteFunctions

/-!
# Schwartz Hermite Expansion (1D)

Prove that for D = ℝ, F = ℝ, the Hermite expansion
  f = ∑' n, cₙ(f) · ψₙ
converges in the Schwartz topology, implying the `schwartz_hermite_expansion` axiom.

## Proof outline

1. **Basis**: ψₙ = hermiteFunction n, lifted to SchwartzMap ℝ ℝ
2. **Coefficients**: cₙ(f) = ∫ f(x) ψₙ(x) dx (a CLM on 𝓢)
3. **Harmonic oscillator eigenvalue**: -ψₙ'' + x²ψₙ = (2n+1)ψₙ
   (Follows from `mul_x_hermiteFunction` and `deriv_hermiteFunction`)
4. **Integration by parts**: ∫ Hf · ψₙ = (2n+1) ∫ f · ψₙ
5. **Coefficient decay**: |cₙ(f)| ≤ C·(2n+1)⁻ᵏ · p_q(f) for any k
6. **Schwartz convergence**: ∑ cₙ(f)ψₙ converges in each seminorm
   (Uses decay + `hermiteFunction_seminorm_bound`)
7. **Identify limit**: The Schwartz limit equals f (by L² uniqueness
   via `hermiteFunction_complete`)
8. **Expansion identity**: For any CLM T : 𝓢 →L[ℝ] H, continuity gives
   T(f) = ∑ cₙ(f) T(ψₙ)

## Dependencies

Several lemmas in HermiteFunctions.lean are currently `private` and need
to be exported:
- `mul_x_hermiteFunction` (raising/lowering identity)
- `deriv_hermiteFunction` (derivative identity)
- `hermiteFunction_contDiff` (smoothness)
-/

open MeasureTheory Real SchwartzMap
open scoped BigOperators

noncomputable section

/-! ## Section 1: The 1D Schwartz Hermite Basis -/

/-- The n-th Hermite function as a Schwartz map. Uses `Classical.choose` on
    `hermiteFunction_schwartz n`.
-/
def schwartzHermiteBasis1D (n : ℕ) : SchwartzMap ℝ ℝ :=
  Classical.choose (hermiteFunction_schwartz n)

/-- The Schwartz map agrees with `hermiteFunction n` pointwise. -/
theorem schwartzHermiteBasis1D_apply (n : ℕ) (x : ℝ) :
    schwartzHermiteBasis1D n x = hermiteFunction n x :=
  Classical.choose_spec (hermiteFunction_schwartz n) x

/-- Coercion: the underlying function of the Schwartz map is hermiteFunction n. -/
theorem schwartzHermiteBasis1D_coe (n : ℕ) :
    ⇑(schwartzHermiteBasis1D n) = hermiteFunction n := funext (schwartzHermiteBasis1D_apply n)

/-! ## Section 2: The 1D Hermite Coefficients -/

/-- The n-th Hermite coefficient of a Schwartz function f:
    cₙ(f) = ∫ f(x) ψₙ(x) dx.
-/
def hermiteCoeff1D (n : ℕ) (f : SchwartzMap ℝ ℝ) : ℝ :=
  ∫ x, f x * hermiteFunction n x

/-- The Hermite coefficient is the L² inner product with ψₙ. -/
theorem hermiteCoeff1D_eq_integral (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    hermiteCoeff1D n f = ∫ x, f x * hermiteFunction n x := rfl

/-- Hermite coefficients are linear in f. -/
theorem hermiteCoeff1D_linear (n : ℕ) :
    IsLinearMap ℝ (hermiteCoeff1D n) where
  map_add := by
    intro f g
    simp only [hermiteCoeff1D]
    rw [show (fun x => (f + g) x * hermiteFunction n x) =
        fun x => f x * hermiteFunction n x + g x * hermiteFunction n x from by
      ext x; simp [add_mul]]
    exact integral_add
      ((f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n))
      ((g.memLp 2 volume).integrable_mul (hermiteFunction_memLp n))
  map_smul := by
    intro c f
    simp only [hermiteCoeff1D]
    rw [show (fun x => (c • f) x * hermiteFunction n x) =
        fun x => c * (f x * hermiteFunction n x) from by
      ext x; simp [smul_eq_mul, mul_assoc]]
    exact integral_const_mul c _

/-! ## Section 3: Harmonic Oscillator Eigenvalue

The harmonic oscillator H = -d²/dx² + x² satisfies Hψₙ = (2n+1)ψₙ.
This follows from combining:
- `mul_x_hermiteFunction`: x·ψₙ = √((n+1)/2)·ψ_{n+1} + √(n/2)·ψ_{n-1}
- `deriv_hermiteFunction`: ψₙ' = √(n/2)·ψ_{n-1} - √((n+1)/2)·ψ_{n+1}

Computing x²ψₙ (apply mul_x twice) and ψₙ'' (apply deriv twice), then
subtracting gives -ψₙ'' + x²ψₙ = (2n+1)ψₙ.

NOTE: Currently blocked because `mul_x_hermiteFunction` and
`deriv_hermiteFunction` are `private` in HermiteFunctions.lean.
-/

/-- The harmonic oscillator eigenvalue equation:
    -ψₙ''(x) + x² ψₙ(x) = (2n+1) ψₙ(x).
-/
-- Helper: differentiability of hermiteFunction
private theorem hermiteFunction_differentiable (k : ℕ) : Differentiable ℝ (hermiteFunction k) :=
  (hermiteFunction_contDiff k 1).differentiable_one

-- Helper: second derivative of hermiteFunction
private theorem deriv2_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (deriv (hermiteFunction n)) x =
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑(n - 1) : ℝ) / 2) *
      hermiteFunction (n - 1 - 1) x -
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction n x -
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction n x +
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 2) : ℝ) / 2) *
      hermiteFunction (n + 2) x := by
  have hderiv_eq : deriv (hermiteFunction n) =
      fun y => Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) y -
               Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) y := by
    ext y; exact deriv_hermiteFunction n y
  set a := Real.sqrt ((↑n : ℝ) / 2)
  set b := Real.sqrt ((↑(n + 1) : ℝ) / 2)
  have hfn_eq : (fun y => a * hermiteFunction (n - 1) y - b * hermiteFunction (n + 1) y) =
      (fun y => a * hermiteFunction (n - 1) y) - (fun y => b * hermiteFunction (n + 1) y) := by
    ext y; simp [Pi.sub_apply]
  rw [hderiv_eq, hfn_eq]
  rw [deriv_sub
        ((hermiteFunction_differentiable _).differentiableAt.const_mul _)
        ((hermiteFunction_differentiable _).differentiableAt.const_mul _)]
  simp only [deriv_const_mul_field]
  rw [deriv_hermiteFunction (n - 1) x, deriv_hermiteFunction (n + 1) x]
  rw [show n + 1 - 1 = n from Nat.succ_sub_one n, show n + 1 + 1 = n + 2 from rfl]
  -- The term (n - 1) + 1 from deriv_hermiteFunction (n-1) doesn't simplify to n
  -- when n = 0. Case split:
  cases n with
  | zero =>
    simp only [a, b, Nat.cast_zero, zero_div, Real.sqrt_zero, zero_mul, neg_zero, zero_sub,
               zero_add, Nat.zero_sub]
    ring
  | succ m =>
    rw [show m + 1 - 1 = m from Nat.succ_sub_one m]
    ring

-- Helper: x^2 * hermiteFunction expanded via mul_x_hermiteFunction twice.
-- The ψ_{n-1+1} term equals ψ_n when n ≥ 1 and the coefficient vanishes when n = 0,
-- so we handle the two cases separately.
private theorem x_sq_mul_hermiteFunction (n : ℕ) (x : ℝ) :
    x ^ 2 * hermiteFunction n x =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 2) : ℝ) / 2) *
      hermiteFunction (n + 2) x +
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction n x +
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction n x +
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑(n - 1) : ℝ) / 2) *
      hermiteFunction (n - 1 - 1) x := by
  have hx2 : x ^ 2 * hermiteFunction n x = x * (x * hermiteFunction n x) := by ring
  rw [hx2, mul_x_hermiteFunction n x]
  have hdist : x * (Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
      Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x) =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * (x * hermiteFunction (n + 1) x) +
    Real.sqrt ((↑n : ℝ) / 2) * (x * hermiteFunction (n - 1) x) := by ring
  rw [hdist, mul_x_hermiteFunction (n + 1) x, mul_x_hermiteFunction (n - 1) x]
  rw [show n + 1 - 1 = n from Nat.succ_sub_one n, show n + 1 + 1 = n + 2 from rfl]
  -- The problematic term: √(n/2) * √((n-1+1)/2) * ψ_{n-1+1}
  -- When n = 0: √(0/2) = 0 so both sides have 0 for this term
  -- When n ≥ 1: n-1+1 = n so this is √(n/2) * √(n/2) * ψ_n
  cases n with
  | zero =>
    simp [Real.sqrt_zero]
    ring
  | succ m =>
    rw [show m + 1 - 1 = m from Nat.succ_sub_one m, show m + 1 = m + 1 from rfl]
    ring

theorem hermiteFunction_harmonic_oscillator_eigenvalue (n : ℕ) (x : ℝ) :
    -(iteratedDeriv 2 (hermiteFunction n) x) + x ^ 2 * hermiteFunction n x =
    (2 * ↑n + 1) * hermiteFunction n x := by
  -- Convert iteratedDeriv 2 to deriv (deriv ...)
  have hiter : iteratedDeriv 2 (hermiteFunction n) x = deriv (deriv (hermiteFunction n)) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hiter, deriv2_hermiteFunction, x_sq_mul_hermiteFunction]
  -- Now the ψ_{n+2} and ψ_{n-1-1} terms cancel, leaving coefficient calculation on ψ_n
  -- √(n/2)^2 + √((n+1)/2)^2 + √((n+1)/2)^2 + √(n/2)^2
  -- equals n/2 + (n+1)/2 + (n+1)/2 + n/2 = 2n+1.
  have hsq_np1 :
      Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 1) : ℝ) / 2) =
        (↑(n + 1) : ℝ) / 2 :=
    Real.mul_self_sqrt (by positivity)
  have hsq_n : Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑n : ℝ) / 2) = (↑n : ℝ) / 2 :=
    Real.mul_self_sqrt (by positivity)
  rw [hsq_np1, hsq_n]
  push_cast
  ring

/-! ## Section 4: Integration by Parts

For Schwartz functions f, integration by parts twice gives:
  ∫ f''·g = ∫ f·g''
(boundary terms vanish since f, g ∈ 𝓢 decay faster than any polynomial).

Combined with the eigenvalue equation, this yields:
  ∫ (-f'' + x²f) · ψₙ = (2n+1) ∫ f · ψₙ

i.e., cₙ(Hf) = (2n+1) · cₙ(f).
-/

/-- Integration by parts: ∫ f'' g = ∫ f g'' for Schwartz functions. -/
theorem schwartz_integration_by_parts_twice
    (f g : SchwartzMap ℝ ℝ) :
    ∫ x, iteratedDeriv 2 f x * g x = ∫ x, f x * iteratedDeriv 2 g x := by
  -- Unfold iteratedDeriv 2 to deriv ∘ deriv
  have hf2 : ∀ x, iteratedDeriv 2 (⇑f) x = deriv (deriv (⇑f)) x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have hg2 : ∀ x, iteratedDeriv 2 (⇑g) x = deriv (deriv (⇑g)) x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  simp_rw [hf2, hg2]
  -- Key: deriv (⇑f) = ⇑(derivCLM ℝ ℝ f) as functions
  have hf' : deriv (⇑f) = ⇑(derivCLM ℝ ℝ f) := by ext x; simp [derivCLM_apply]
  have hg' : deriv (⇑g) = ⇑(derivCLM ℝ ℝ g) := by ext x; simp [derivCLM_apply]
  -- Rewrite second derivatives using derivCLM
  rw [hf', hg']
  -- Now LHS = ∫ x, deriv (⇑(derivCLM ℝ ℝ f)) x * g x
  -- and RHS = ∫ x, f x * deriv (⇑(derivCLM ℝ ℝ g)) x
  -- Apply IBP to LHS: ∫ (derivCLM f)' * g = -∫ (derivCLM f) * g'
  -- i.e., ∫ deriv(derivCLM f) * g = -∫ (derivCLM f) * deriv(g)
  have ibp1 := integral_mul_deriv_eq_neg_deriv_mul (derivCLM ℝ ℝ f) g
  -- ibp1 : ∫ (derivCLM f) x * deriv g x = -∫ deriv(derivCLM f) x * g x
  -- So ∫ deriv(derivCLM f) x * g x = -∫ (derivCLM f) x * deriv g x
  have lhs_eq : ∫ x, deriv (⇑(derivCLM ℝ ℝ f)) x * g x =
      -(∫ x, (derivCLM ℝ ℝ f) x * deriv (⇑g) x) := by linarith
  -- Apply IBP to RHS: ∫ f * (derivCLM g)' = -∫ f' * (derivCLM g)
  -- i.e., ∫ f * deriv(derivCLM g) = -∫ deriv(f) * (derivCLM g)
  have ibp2 := integral_mul_deriv_eq_neg_deriv_mul f (derivCLM ℝ ℝ g)
  -- ibp2 : ∫ f x * deriv(derivCLM g) x = -∫ deriv(f) x * (derivCLM g) x
  -- Rewrite (derivCLM f) and deriv(f) and (derivCLM g) and deriv(g)
  -- using derivCLM_apply
  simp only [derivCLM_apply] at ibp1 ibp2 lhs_eq ⊢
  -- Now lhs_eq : LHS = -(∫ deriv f x * deriv g x)
  -- ibp2 : RHS = -(∫ deriv f x * deriv g x)
  linarith

/-- The harmonic oscillator is symmetric on Schwartz space:
    ∫ Hf · ψₙ = (2n+1) ∫ f · ψₙ.
-/
theorem hermiteCoeff_harmonic_oscillator (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    ∫ x, (-(iteratedDeriv 2 f x) + x ^ 2 * f x) * hermiteFunction n x =
    (2 * ↑n + 1) * hermiteCoeff1D n f := by
  set ψ := schwartzHermiteBasis1D n
  have hψ_coe : ⇑ψ = hermiteFunction n := schwartzHermiteBasis1D_coe n
  have hψ_apply : ∀ x, ψ x = hermiteFunction n x := schwartzHermiteBasis1D_apply n
  -- Schwartz second derivatives
  set f'' : SchwartzMap ℝ ℝ := derivCLM ℝ ℝ (derivCLM ℝ ℝ f)
  set ψ'' : SchwartzMap ℝ ℝ := derivCLM ℝ ℝ (derivCLM ℝ ℝ ψ)
  -- Relate iteratedDeriv 2 to derivCLM^2 at function level
  have hf''_coe : ⇑f'' = deriv (deriv ⇑f) := by
    have h1 : ⇑(derivCLM ℝ ℝ f) = deriv ⇑f := funext (derivCLM_apply (𝕜 := ℝ) f)
    ext x; show f'' x = deriv (deriv ⇑f) x
    change (derivCLM ℝ ℝ (derivCLM ℝ ℝ f)) x = _
    rw [derivCLM_apply (𝕜 := ℝ), h1]
  have hψ''_coe : ⇑ψ'' = deriv (deriv ⇑ψ) := by
    have h1 : ⇑(derivCLM ℝ ℝ ψ) = deriv ⇑ψ := funext (derivCLM_apply (𝕜 := ℝ) ψ)
    ext x; show ψ'' x = deriv (deriv ⇑ψ) x
    change (derivCLM ℝ ℝ (derivCLM ℝ ℝ ψ)) x = _
    rw [derivCLM_apply (𝕜 := ℝ), h1]
  -- Pointwise equalities
  have hf''_eq : ∀ x, iteratedDeriv 2 (⇑f) x = f'' x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_zero]; exact (congrFun hf''_coe x).symm
  have hψ''_iter : ∀ x, iteratedDeriv 2 (hermiteFunction n) x = ψ'' x := by
    intro x; rw [show hermiteFunction n = ⇑ψ from hψ_coe.symm]
    rw [iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_zero]; exact (congrFun hψ''_coe x).symm
  -- Integrability
  have hint_f''ψ : Integrable (fun x => iteratedDeriv 2 (⇑f) x * hermiteFunction n x) :=
    ((f''.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)).congr
      (by filter_upwards with x; change f'' x * hermiteFunction n x = _; rw [← hf''_eq])
  have hint_fψ'' : Integrable (fun x => f x * iteratedDeriv 2 (hermiteFunction n) x) :=
    ((f.memLp 2 volume).integrable_mul (ψ''.memLp 2 volume)).congr
      (by filter_upwards with x; change f x * ψ'' x = _; rw [← hψ''_iter])
  have hint_fψ : Integrable (fun x => f x * hermiteFunction n x) := by
    rw [show (fun x => f x * hermiteFunction n x) = (⇑f * hermiteFunction n) from rfl]
    exact (f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)
  have hint_x2fψ : Integrable (fun x => x ^ 2 * f x * hermiteFunction n x) := by
    have heigen : ∀ x, x ^ 2 * f x * hermiteFunction n x =
        (2 * ↑n + 1) * (f x * hermiteFunction n x) +
          f x * iteratedDeriv 2 (hermiteFunction n) x := by
      intro x
      have h := hermiteFunction_harmonic_oscillator_eigenvalue n x
      have : x ^ 2 * hermiteFunction n x =
          (2 * ↑n + 1) * hermiteFunction n x +
            iteratedDeriv 2 (hermiteFunction n) x := by
        linarith
      calc x ^ 2 * f x * hermiteFunction n x
          = f x * (x ^ 2 * hermiteFunction n x) := by ring
        _ = f x * ((2 * ↑n + 1) * hermiteFunction n x +
              iteratedDeriv 2 (hermiteFunction n) x) := by
            rw [this]
        _ = (2 * ↑n + 1) * (f x * hermiteFunction n x) +
            f x * iteratedDeriv 2 (hermiteFunction n) x := by ring
    simp_rw [heigen]; exact (hint_fψ.const_mul _).add hint_fψ''
  -- Step 1: Rewrite integrand using eigenvalue equation and factor
  -- (-f''(x) + x²f(x)) * ψₙ(x) = f(x) * ((2n+1)ψₙ(x)) + (f(x)*ψₙ''(x) - f''(x)*ψₙ(x))
  -- The second part integrates to 0 by IBP.
  -- Strategy: directly show the integral equals the target
  -- IBP: ∫ f''·ψₙ = ∫ f·ψₙ''
  have hibp : ∫ x, iteratedDeriv 2 (⇑f) x * hermiteFunction n x =
      ∫ x, f x * iteratedDeriv 2 (hermiteFunction n) x := by
    have h := schwartz_integration_by_parts_twice f ψ
    simp only [hψ_coe] at h; exact h
  -- Eigenvalue decomposition of x²·f·ψₙ
  have heigen : ∀ x, x ^ 2 * f x * hermiteFunction n x =
      (2 * ↑n + 1) * (f x * hermiteFunction n x) +
      f x * iteratedDeriv 2 (hermiteFunction n) x := by
    intro x
    have h := hermiteFunction_harmonic_oscillator_eigenvalue n x
    have hx2 : x ^ 2 * hermiteFunction n x =
        (2 * ↑n + 1) * hermiteFunction n x +
          iteratedDeriv 2 (hermiteFunction n) x := by
      linarith
    calc x ^ 2 * f x * hermiteFunction n x
        = f x * (x ^ 2 * hermiteFunction n x) := by ring
      _ = f x * ((2 * ↑n + 1) * hermiteFunction n x +
            iteratedDeriv 2 (hermiteFunction n) x) := by
          rw [hx2]
      _ = _ := by ring
  -- Rewrite full integrand
  have h_integrand : ∀ x, (-(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x) * hermiteFunction n x =
      (2 * ↑n + 1) * (f x * hermiteFunction n x) +
      (f x * iteratedDeriv 2 (hermiteFunction n) x -
        iteratedDeriv 2 (⇑f) x * hermiteFunction n x) := by
    intro x
    have h1 := heigen x
    -- Expand and simplify: both sides equal -f''·ψ + (2n+1)·f·ψ + f·ψ''
    have hlhs : (-(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x) * hermiteFunction n x =
        -(iteratedDeriv 2 (⇑f) x * hermiteFunction n x) +
          x ^ 2 * f x * hermiteFunction n x := by
      ring
    rw [hlhs, h1]; ring
  simp_rw [h_integrand]
  -- Split: ∫ (a + b) = ∫ a + ∫ b
  have hint_main := hint_fψ.const_mul (2 * ↑n + 1)
  have hint_diff : Integrable (fun x => f x * iteratedDeriv 2 (hermiteFunction n) x -
      iteratedDeriv 2 (⇑f) x * hermiteFunction n x) := hint_fψ''.sub hint_f''ψ
  rw [integral_add hint_main hint_diff, integral_const_mul, integral_sub hint_fψ'' hint_f''ψ]
  -- Goal: (2n+1) * ∫ f·ψₙ + (∫ f·ψₙ'' - ∫ f''·ψₙ) = (2n+1) * hermiteCoeff1D n f
  -- By IBP: ∫ f''·ψₙ = ∫ f·ψₙ'', so the second term is 0
  rw [hibp]; unfold hermiteCoeff1D; linarith

/-! ## Section 5: Coefficient Decay

By iterating the harmonic oscillator identity k times:
  cₙ(f) = (2n+1)⁻ᵏ · cₙ(Hᵏf)

Combined with Cauchy-Schwarz:
  |cₙ(f)| ≤ (2n+1)⁻ᵏ · ‖Hᵏf‖_{L²}

And the Schwartz seminorm bound:
  ‖Hᵏf‖_{L²} ≤ C · p_q(f)  for some q depending on k

This gives super-polynomial decay of Hermite coefficients.
-/

/-- **Coefficient decay**: Hermite coefficients of Schwartz functions
    decay faster than any polynomial.
    For any k, there exist C > 0 and seminorm index q such that
    |cₙ(f)| · (1+n)^k ≤ C · p_q(f) for all f ∈ 𝓢 and n ∈ ℕ.
-/
-- Helper: Cauchy-Schwarz for integrals
private lemma cauchy_schwarz_integral (f g : ℝ → ℝ) (hf : Integrable (fun x => f x ^ 2))
    (hg : Integrable (fun x => g x ^ 2)) (hfg : Integrable (fun x => f x * g x)) :
    |∫ x, f x * g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  -- Set notation
  set A := ∫ x, f x ^ 2 with hA_def
  set B := ∫ x, g x ^ 2 with hB_def
  set C := ∫ x, f x * g x with hC_def
  have hA_nn : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  have hB_nn : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  -- Key: for all t, 0 ≤ ∫ (f + tg)² = A + 2tC + t²B
  have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B := by
    intro t
    have hint : Integrable (fun x => (f x + t * g x) ^ 2) := by
      have h1 : (fun x => (f x + t * g x) ^ 2) =
          fun x => f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) := by
        ext x; ring
      rw [h1]; exact hf.add ((hfg.const_mul _).add (hg.const_mul _))
    have h0 : (0 : ℝ) ≤ ∫ x, (f x + t * g x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    have heq : ∫ x, (f x + t * g x) ^ 2 = A + 2 * t * C + t ^ 2 * B := by
      have hint1 : Integrable (fun x => 2 * t * (f x * g x)) := hfg.const_mul _
      have hint2 : Integrable (fun x => t ^ 2 * (g x ^ 2)) := hg.const_mul _
      have h_sq : ∫ x, (f x + t * g x) ^ 2 =
          ∫ x, f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) := by
        congr 1; ext x; ring
      have h_s1 : ∫ x, f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) =
          (∫ x, f x ^ 2) + ∫ x, (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) :=
        integral_add hf (hint1.add hint2)
      have h_s2 : ∫ x, (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) =
          (∫ x, 2 * t * (f x * g x)) + ∫ x, t ^ 2 * (g x ^ 2) :=
        integral_add hint1 hint2
      rw [h_sq, h_s1, h_s2, integral_const_mul, integral_const_mul]; ring
    linarith
  -- Case split on B
  by_cases hB : B = 0
  · -- B = 0 implies g² =ᵐ 0, hence g =ᵐ 0, hence C = 0
    have hg2_ae : (fun x => g x ^ 2) =ᵐ[MeasureTheory.volume] 0 := by
      rwa [← integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg (g x))) hg]
    have hC0 : C = 0 := by
      have : (fun x => f x * g x) =ᵐ[MeasureTheory.volume] (fun _ => 0) := by
        filter_upwards [hg2_ae] with x hx
        simp only [Pi.zero_apply] at hx
        have := sq_eq_zero_iff.mp hx
        rw [this, mul_zero]
      rw [hC_def, integral_congr_ae this, integral_zero]
    simp [hC0, hB, abs_zero]
  · -- B > 0: substitute t = -C/B
    have hB_pos : 0 < B := lt_of_le_of_ne hB_nn (Ne.symm hB)
    have h := hquad (-C / B)
    have hsimp : A + 2 * (-C / B) * C + (-C / B) ^ 2 * B = A - C ^ 2 / B := by field_simp; ring
    rw [hsimp] at h
    have hCsq : C ^ 2 ≤ A * B := by
      have h1 : C ^ 2 / B ≤ A := by linarith
      calc C ^ 2 = C ^ 2 / B * B := by field_simp
        _ ≤ A * B := mul_le_mul_of_nonneg_right h1 hB_pos.le
    -- |C| = √(C²) ≤ √(AB) = √A · √B
    calc |C| = Real.sqrt (C ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hCsq
      _ = Real.sqrt A * Real.sqrt B := by rw [Real.sqrt_mul hA_nn]

-- Cauchy-Schwarz bound: |∫ f·ψₙ| ≤ √(∫ f²)
private lemma abs_hermiteCoeff1D_le_sqrt_integral_sq (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    |hermiteCoeff1D n f| ≤ Real.sqrt (∫ x, f x ^ 2) := by
  unfold hermiteCoeff1D
  have hint : Integrable (fun x => f x * hermiteFunction n x) :=
    (f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)
  have hf2 : Integrable (fun x => f x ^ 2) :=
    ((f.memLp 2 volume).integrable_mul (f.memLp 2 volume)).congr
      (by filter_upwards with x; change f x * f x = f x ^ 2; ring)
  have hψ2 : Integrable (fun x => hermiteFunction n x ^ 2) := by
    exact ((hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp n)).congr (by
      filter_upwards with x
      change hermiteFunction n x * hermiteFunction n x = hermiteFunction n x ^ 2
      ring)
  have horth : ∫ x, hermiteFunction n x ^ 2 = 1 := by
    simpa only [pow_two, ite_true] using hermiteFunction_orthonormal n n
  calc |∫ x, f x * hermiteFunction n x|
      ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, hermiteFunction n x ^ 2) :=
        cauchy_schwarz_integral f (hermiteFunction n) hf2 hψ2 hint
    _ = Real.sqrt (∫ x, f x ^ 2) := by rw [horth, Real.sqrt_one, mul_one]

-- x² has temperate growth (needed for smulLeftCLM)
private lemma hasTemperateGrowth_x_sq :
    Function.HasTemperateGrowth (fun x : ℝ => x ^ 2) := by
  have : (fun x : ℝ => x ^ 2) = fun x => x * x := by ext; ring
  rw [this]; exact Function.HasTemperateGrowth.id'.mul .id'

-- The harmonic oscillator H = -d²/dx² + x² as a CLM on Schwartz space
private def harmonicOscillator : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ) :=
  -(derivCLM ℝ ℝ ∘L derivCLM ℝ ℝ) + smulLeftCLM ℝ (fun x : ℝ => x ^ 2)

-- Pointwise: (H f)(x) = -f''(x) + x²f(x)
private lemma harmonicOscillator_apply (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    harmonicOscillator f x = -(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x := by
  simp only [harmonicOscillator, add_apply, neg_apply,
    ContinuousLinearMap.comp_apply]
  -- SchwartzMap add_apply/neg_apply and derivCLM_apply are rfl; use change to make pointwise
  change -(deriv (deriv (⇑f)) x) + (smulLeftCLM ℝ (fun x : ℝ => x ^ 2) f) x =
    -(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x
  rw [smulLeftCLM_apply_apply hasTemperateGrowth_x_sq, smul_eq_mul]
  congr 1
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]

-- Coefficient identity: cₙ(H f) = (2n+1) cₙ(f)
private lemma hermiteCoeff1D_harmonicOscillator (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    hermiteCoeff1D n (harmonicOscillator f) = (2 * ↑n + 1) * hermiteCoeff1D n f := by
  unfold hermiteCoeff1D
  have : (fun x => harmonicOscillator f x * hermiteFunction n x) =
      fun x => (-(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x) * hermiteFunction n x := by
    ext x; rw [harmonicOscillator_apply]
  rw [this]; exact hermiteCoeff_harmonic_oscillator n f

-- Iteration: cₙ(H^m f) = (2n+1)^m cₙ(f)
private lemma hermiteCoeff1D_harmonicOscillator_pow :
    ∀ (m n : ℕ) (f : SchwartzMap ℝ ℝ),
    hermiteCoeff1D n ((harmonicOscillator ^ m) f) =
      (2 * ↑n + 1) ^ m * hermiteCoeff1D n f := by
  intro m; induction m with
  | zero => intro n f; simp
  | succ k ih =>
    intro n f
    rw [pow_succ, mul_apply_eq_comp, ih n (harmonicOscillator f),
      hermiteCoeff1D_harmonicOscillator, pow_succ]; ring

-- L² norm ≤ sup-seminorms for Schwartz functions
private lemma schwartz_l2_le_sup_seminorm :
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      Real.sqrt (∫ x, (f x) ^ 2) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by
  -- Pointwise bound: (1+‖x‖) * ‖f x‖ ≤ 2S where S = sup-seminorm over Iic (1,0)
  -- Then (f x)² ≤ 4S²·(1+‖x‖)⁻² and √(∫ f²) ≤ 2S·√(∫ (1+‖x‖)⁻²)
  have h_int : Integrable (fun x : ℝ => (1 + ‖x‖) ^ ((-2) : ℝ)) volume :=
    integrable_one_add_norm (by
      rw [show Module.finrank ℝ ℝ = 1 from Module.finrank_self ℝ]; norm_num)
  have hI_nn : 0 ≤ ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ) :=
    integral_nonneg (fun x => rpow_nonneg (by positivity) _)
  refine ⟨(1, 0), 2 * Real.sqrt (∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ)) + 1,
    by linarith [Real.sqrt_nonneg (∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ))], fun f => ?_⟩
  set S := (Finset.Iic (1, 0)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f
  have hS_nn : (0 : ℝ) ≤ S := apply_nonneg _ _
  -- Integrability of f²
  have hint_f2 : Integrable (fun x => (f x) ^ 2) volume :=
    ((f.memLp 2 volume).integrable_mul (f.memLp 2 volume)).congr
      (by filter_upwards with x; change f x * f x = f x ^ 2; ring)
  -- Pointwise bound: (f x)² ≤ 4S² * (1+‖x‖)^(-2)
  have h_pw : ∀ x : ℝ, (f x) ^ 2 ≤ 4 * S ^ 2 * (1 + ‖x‖) ^ ((-2) : ℝ) := by
    intro x
    have hx_pos : (0 : ℝ) < 1 + ‖x‖ := by positivity
    have h := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (1, 0))
      (k := 1) (n := 0) le_rfl le_rfl f x
    simp only [pow_one, norm_iteratedFDeriv_zero] at h
    -- h : (1 + ‖x‖) * ‖f x‖ ≤ 2 * S (definitionally)
    -- Convert rpow to regular pow
    have h_rpow_eq : (1 + ‖x‖) ^ ((-2) : ℝ) = ((1 + ‖x‖) ^ 2)⁻¹ := by
      have : (-2 : ℝ) = -(↑(2 : ℕ) : ℝ) := by norm_num
      rw [this, rpow_neg hx_pos.le, rpow_natCast]
    rw [h_rpow_eq]
    -- Goal: (f x)^2 ≤ 4 * S^2 * ((1+‖x‖)^2)⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (show (0 : ℝ) < (1 + ‖x‖) ^ 2 from by positivity)]
    -- Goal: (f x)^2 * (1+‖x‖)^2 ≤ 4 * S^2
    have h_eq : (f x) ^ 2 * (1 + ‖x‖) ^ 2 = ((1 + ‖x‖) * ‖f x‖) ^ 2 := by
      rw [mul_pow, mul_comm ((1 + ‖x‖) ^ 2)]; congr 1
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_eq]
    calc ((1 + ‖x‖) * ‖f x‖) ^ 2 ≤ (2 * S) ^ 2 :=
          sq_le_sq' (by nlinarith [norm_nonneg (f x)]) (by linarith)
      _ = 4 * S ^ 2 := by ring
  -- Integrate the bound
  have h_integral : ∫ x, (f x) ^ 2 ≤
      4 * S ^ 2 * ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ) :=
    calc ∫ x, (f x) ^ 2
        ≤ ∫ x, 4 * S ^ 2 * (1 + ‖x‖) ^ ((-2) : ℝ) :=
          integral_mono hint_f2 (h_int.const_mul _) h_pw
      _ = 4 * S ^ 2 * ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ) := integral_const_mul _ _
  -- Take sqrt
  set I := ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ)
  calc Real.sqrt (∫ x, (f x) ^ 2)
      ≤ Real.sqrt (4 * S ^ 2 * I) := Real.sqrt_le_sqrt h_integral
    _ = Real.sqrt (4 * S ^ 2) * Real.sqrt I := Real.sqrt_mul (by positivity) I
    _ = 2 * S * Real.sqrt I := by
        rw [show (4 : ℝ) * S ^ 2 = (2 * S) ^ 2 from by ring,
          Real.sqrt_sq (by linarith)]
    _ ≤ (2 * Real.sqrt I + 1) * S := by nlinarith [Real.sqrt_nonneg I]

-- Helper: a single seminorm of T f is bounded by finitely many seminorms of f
private lemma clm_single_seminorm_bound (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ))
    (k l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : NNReal), C ≠ 0 ∧
      (SchwartzMap.seminorm ℝ k l).comp T.toLinearMap ≤
        C • s.sup (schwartzSeminormFamily ℝ ℝ ℝ) := by
  have hws := schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ)
  set q := (SchwartzMap.seminorm ℝ k l).comp T.toLinearMap
  have hq : Continuous q := by
    change Continuous (fun f => SchwartzMap.seminorm ℝ k l (T f))
    exact (hws.continuous_seminorm (k, l)).comp T.continuous
  exact Seminorm.bound_of_continuous hws q hq

-- Helper: for any finite set of index pairs, the sup of seminorms of T f is bounded
private lemma clm_finset_sup_seminorm_bound
    (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ)) :
    ∀ (S : Finset (ℕ × ℕ)),
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      S.sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) (T f) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by
  intro S
  induction S using Finset.induction with
  | empty =>
    exact ⟨(0, 0), 1, one_pos, fun f => by simp⟩
  | @insert a s ha ih =>
    obtain ⟨q_s, C_s, hC_s, h_s⟩ := ih
    obtain ⟨s_a, C_a, hC_a, hle_a⟩ := clm_single_seminorm_bound T a.1 a.2
    -- Local abbreviation to help type inference
    let snf : ℕ × ℕ → Seminorm ℝ (SchwartzMap ℝ ℝ) :=
      fun p => SchwartzMap.seminorm ℝ p.1 p.2
    -- Convert the bound from clm_single_seminorm_bound
    have h_a : ∀ f : SchwartzMap ℝ ℝ, SchwartzMap.seminorm ℝ a.1 a.2 (T f) ≤
        (C_a : ℝ) * s_a.sup snf f := fun f => by
      have := hle_a f
      simp only [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def] at this
      exact this
    -- Take q large enough
    set q₁ := max q_s.1 (s_a.sup Prod.fst)
    set q₂ := max q_s.2 (s_a.sup Prod.snd)
    refine ⟨(q₁, q₂), max C_s (C_a : ℝ) + 1, by positivity, fun f => ?_⟩
    haveI : SMulCommClass ℝ ℝ (SchwartzMap ℝ ℝ) :=
      ⟨fun r s f => by rw [← mul_smul, ← mul_smul, mul_comm]⟩
    rw [Finset.sup_insert]
    apply sup_le
    · -- Bound for the new element
      have hsub_a : s_a.sup snf ≤ (Finset.Iic (q₁, q₂)).sup snf := by
        apply Finset.sup_le; intro ⟨i, j⟩ hij
        apply Finset.le_sup (f := snf)
        simp only [Finset.mem_Iic, Prod.le_def]
        exact ⟨le_trans (Finset.le_sup (f := Prod.fst) hij) (le_max_right _ _),
               le_trans (Finset.le_sup (f := Prod.snd) hij) (le_max_right _ _)⟩
      calc snf a (T f)
          ≤ (C_a : ℝ) * s_a.sup snf f := h_a f
        _ ≤ (C_a : ℝ) * (Finset.Iic (q₁, q₂)).sup snf f :=
            mul_le_mul_of_nonneg_left (hsub_a f) (NNReal.coe_nonneg C_a)
        _ ≤ (max C_s (C_a : ℝ) + 1) * (Finset.Iic (q₁, q₂)).sup snf f := by
            gcongr; linarith [le_max_right C_s (C_a : ℝ)]
    · -- Bound for the rest (from IH)
      have hsub_s : (Finset.Iic q_s).sup snf ≤ (Finset.Iic (q₁, q₂)).sup snf := by
        apply Finset.sup_le; intro ⟨i, j⟩ hij
        apply Finset.le_sup (f := snf)
        simp only [Finset.mem_Iic, Prod.le_def] at hij ⊢
        exact ⟨le_trans hij.1 (le_max_left _ _), le_trans hij.2 (le_max_left _ _)⟩
      calc s.sup snf (T f)
          ≤ C_s * (Finset.Iic q_s).sup snf f := h_s f
        _ ≤ C_s * (Finset.Iic (q₁, q₂)).sup snf f :=
            mul_le_mul_of_nonneg_left (hsub_s f) (le_of_lt hC_s)
        _ ≤ (max C_s (C_a : ℝ) + 1) * (Finset.Iic (q₁, q₂)).sup snf f := by
            gcongr; linarith [le_max_left C_s (C_a : ℝ)]

-- Helper: sup-seminorms of T f bounded by sup-seminorms of f (single step, Iic version)
private lemma clm_sup_seminorm_bound (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ))
    (q₀ : ℕ × ℕ) :
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) (T f) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f :=
  clm_finset_sup_seminorm_bound T (Finset.Iic q₀)

-- sup-seminorms of T^m f bounded by sup-seminorms of f (for any CLM T)
private lemma pow_clm_sup_seminorm_bound (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ))
    (m : ℕ) (q₀ : ℕ × ℕ) :
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) ((T ^ m) f) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by
  induction m with
  | zero =>
    exact ⟨q₀, 1, one_pos, fun f => by simp⟩
  | succ k ih =>
    obtain ⟨q_k, C_k, hC_k, h_k⟩ := ih
    obtain ⟨q_T, C_T, hC_T, h_T⟩ := clm_sup_seminorm_bound T q_k
    refine ⟨q_T, C_k * C_T, by positivity, fun f => ?_⟩
    -- T^(k+1) f = T^k (T f)
    rw [pow_succ, mul_apply_eq_comp]
    calc (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) ((T ^ k) (T f))
        ≤ C_k * (Finset.Iic q_k).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) (T f) :=
          h_k (T f)
      _ ≤ C_k * (C_T * (Finset.Iic q_T).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f) :=
          by gcongr; exact h_T f
      _ = C_k * C_T * (Finset.Iic q_T).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by ring

theorem hermiteCoeff1D_decay :
    ∀ k : ℝ, ∃ (C : ℝ) (q : ℕ × ℕ), 0 < C ∧
      ∀ (f : SchwartzMap ℝ ℝ) (n : ℕ),
        |hermiteCoeff1D n f| * (1 + (n : ℝ)) ^ k ≤
          C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  intro k
  -- Get L² ≤ sup-seminorm bound
  obtain ⟨q₀, C₀, hC₀_pos, h_l2⟩ := schwartz_l2_le_sup_seminorm
  -- Choose m ≥ k (natural number)
  set m := ⌈max k 0⌉₊ with hm_def
  -- Get CLM seminorm bound for harmonicOscillator^m
  obtain ⟨q_H, C_H, hC_H_pos, h_H⟩ := pow_clm_sup_seminorm_bound harmonicOscillator m q₀
  refine ⟨C₀ * C_H, q_H, by positivity, fun f n => ?_⟩
  -- Key bound: |cₙ(f)| ≤ (2n+1)^{-m} · √(∫ (H^m f)²)
  -- and this is at most (2n+1)^{-m} · C₀ · C_H · sup(f).
  have h_cs := abs_hermiteCoeff1D_le_sqrt_integral_sq n ((harmonicOscillator ^ m) f)
  have h_l2' := h_l2 ((harmonicOscillator ^ m) f)
  have h_H' := h_H f
  -- From iteration: |cₙ(f)| * (2n+1)^m = |cₙ(H^m f)|
  have h_iter : |hermiteCoeff1D n f| * (2 * ↑n + 1) ^ m =
      |hermiteCoeff1D n ((harmonicOscillator ^ m) f)| := by
    rw [hermiteCoeff1D_harmonicOscillator_pow, abs_mul,
      abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * ↑n + 1) m), mul_comm]
  -- Bound (1+n)^k ≤ (2n+1)^m
  have h_rpow_le : (1 + (n : ℝ)) ^ k ≤ (2 * ↑n + 1) ^ m := by
    have h1 : (1 : ℝ) ≤ 1 + ↑n := le_add_of_nonneg_right (Nat.cast_nonneg n)
    calc (1 + (n : ℝ)) ^ k
        ≤ (1 + ↑n) ^ (↑m : ℝ) :=
          rpow_le_rpow_of_exponent_le h1
            (le_trans (le_max_left k 0) (Nat.le_ceil (max k 0)))
      _ = (1 + ↑n) ^ m := by rw [rpow_natCast]
      _ ≤ (2 * ↑n + 1) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith) m
  -- Combine the exponent comparison and coefficient bound.
  calc |hermiteCoeff1D n f| * (1 + ↑n) ^ k
      ≤ |hermiteCoeff1D n f| * (2 * ↑n + 1) ^ m :=
        mul_le_mul_of_nonneg_left h_rpow_le (abs_nonneg _)
    _ = |hermiteCoeff1D n ((harmonicOscillator ^ m) f)| := h_iter
    _ ≤ Real.sqrt (∫ x, ((harmonicOscillator ^ m) f x) ^ 2) := h_cs
    _ ≤ C₀ * (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2)
          ((harmonicOscillator ^ m) f) := h_l2'
    _ ≤ C₀ * (C_H * (Finset.Iic q_H).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f) :=
        by exact mul_le_mul_of_nonneg_left h_H' hC₀_pos.le
    _ = C₀ * C_H * (Finset.Iic q_H).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by ring

/-! ## Section 6: Schwartz Convergence

The Hermite expansion converges absolutely in each Schwartz seminorm:
  ∑ₙ |cₙ(f)| · p_{k,l}(ψₙ) < ∞

This uses:
- `hermiteCoeff1D_decay`: |cₙ(f)| ≤ C(1+n)⁻ˢ · p_q(f) for any s
- `hermiteFunction_seminorm_bound`: p_{k,l}(ψₙ) ≤ C'(1+n)^σ
- Choose s > σ + 1: ∑ (1+n)^{σ-s} < ∞
-/

/-- The Hermite expansion converges absolutely in each Schwartz seminorm. -/
theorem hermite_expansion_seminorm_summable (f : SchwartzMap ℝ ℝ) (k l : ℕ) :
    Summable (fun n => |hermiteCoeff1D n f| *
      SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)) := by
  -- Get seminorm bound: p_{k,l}(ψₙ) ≤ C_h * (1+n)^s
  obtain ⟨C_h, s, hC_h_pos, _, h_sem⟩ := hermiteFunction_seminorm_bound k l
  -- Get coefficient decay: |cₙ| * (1+n)^{s+2} ≤ C_d * sup_seminorms(f)
  obtain ⟨C_d, q, hC_d_pos, h_dec⟩ := hermiteCoeff1D_decay (s + 2)
  -- rpow identity: (1+n)^s = (1+n)^{s+2} * (1+n)^{-2}
  have h_rpow : ∀ n : ℕ, (1 + (n : ℝ)) ^ s =
      (1 + (n : ℝ)) ^ (s + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n; rw [← rpow_add (by positivity : (0 : ℝ) < 1 + (n : ℝ))]; congr 1; ring
  set S := (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  set K := C_h * C_d * S with hK_def
  -- Bound each term by K * (1+n)^{-2}
  have h_bound : ∀ n : ℕ, |hermiteCoeff1D n f| *
      SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) ≤
      K * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    have h_z_nn : (0 : ℝ) ≤ (1 + (n : ℝ)) ^ ((-2) : ℝ) := rpow_nonneg (by positivity) _
    calc |hermiteCoeff1D n f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)
        ≤ |hermiteCoeff1D n f| * (C_h * (1 + ↑n) ^ s) :=
          mul_le_mul_of_nonneg_left (h_sem n) (abs_nonneg _)
      _ = C_h * (|hermiteCoeff1D n f| * (1 + ↑n) ^ (s + 2)) * (1 + ↑n) ^ ((-2) : ℝ) := by
          rw [h_rpow n]; ring
      _ ≤ C_h * (C_d * S) * (1 + ↑n) ^ ((-2) : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (h_dec f n) hC_h_pos.le) h_z_nn
      _ = K * (1 + ↑n) ^ ((-2) : ℝ) := by rw [hK_def]; ring
  -- Summability of K * (1+n)^{-2} by p-series (shifted)
  have h_sum : Summable (fun n : ℕ => K * (1 + (n : ℝ)) ^ ((-2) : ℝ)) := by
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by change ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    exact h1.const_smul K
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    h_bound h_sum

/-- The Hermite expansion ∑ cₙ(f) ψₙ converges in each Schwartz seminorm. -/
theorem hermite_expansion_schwartz_seminorm_summable (f : SchwartzMap ℝ ℝ) (k l : ℕ) :
    Summable (fun n => SchwartzMap.seminorm ℝ k l
      (hermiteCoeff1D n f • schwartzHermiteBasis1D n)) := by
  -- seminorm(c • ψ) = |c| * seminorm(ψ) by seminorm homogeneity
  simp_rw [map_smul_eq_mul, Real.norm_eq_abs]
  exact hermite_expansion_seminorm_summable f k l

/-! ## Section 7: Identify the Limit

The Schwartz series ∑ cₙ(f) ψₙ converges to some g ∈ 𝓢.
Since g = f in L² (by `hermiteFunction_complete` and orthonormal expansion),
and both are continuous, g = f everywhere.
-/

/-- The Hermite expansion of a Schwartz function converges in L² to f.
    This follows from `hermiteFunction_orthonormal` and `hermiteFunction_complete`.
-/
-- Helper: integrability of f * ψₙ
private lemma schwartz_mul_hermite_integrable (f : SchwartzMap ℝ ℝ) (n : ℕ) :
    Integrable (fun x => f x * hermiteFunction n x) volume :=
  (f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)

-- Helper: integrability of ψₙ * ψₘ
private lemma hermite_mul_hermite_integrable (n m : ℕ) :
    Integrable (fun x => hermiteFunction n x * hermiteFunction m x) volume :=
  (hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp m)

-- Helper: integrability of (partial sum) * ψₘ
private lemma partial_sum_mul_hermite_integrable (f : SchwartzMap ℝ ℝ) (N m : ℕ) :
    Integrable (fun x => (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x) volume := by
  simp_rw [Finset.sum_mul]
  apply integrable_finsetSum
  intro n _
  exact ((hermite_mul_hermite_integrable n m).const_mul _).congr
    (by filter_upwards with x; ring)

-- Helper: the orthogonality identity ∫ (∑ cₙψₙ) * ψₘ = cₘ for m < N
private lemma partial_sum_inner_hermite (f : SchwartzMap ℝ ℝ) (N m : ℕ) (hm : m < N) :
    ∫ x, (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x =
    hermiteCoeff1D m f := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun n _ => by
    exact ((hermite_mul_hermite_integrable n m).const_mul _).congr
      (by filter_upwards with x; ring))]
  simp_rw [show ∀ n, (fun x => hermiteCoeff1D n f * hermiteFunction n x * hermiteFunction m x) =
    (fun x => hermiteCoeff1D n f * (hermiteFunction n x * hermiteFunction m x)) from
    by intro n; ext x; ring]
  simp_rw [integral_const_mul, hermiteFunction_orthonormal]
  simp only [Finset.sum_ite_eq', Finset.mem_range.mpr hm, ite_true, mul_one,
    mul_ite, mul_zero]

-- Helper: the L² norm of the partial sum: ∫ (∑ cₙψₙ)² = ∑ cₙ²
private lemma partial_sum_l2_norm_sq (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∫ x, (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) ^ 2 =
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 := by
  -- Rewrite integrand: (∑ cₙψₙ)² = ∑ₘ cₘ · ((∑ cₙψₙ) · ψₘ)
  have h1 : ∫ x, (∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x) ^ 2 =
      ∫ x, ∑ m ∈ Finset.range N, hermiteCoeff1D m f *
        ((∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x) *
          hermiteFunction m x) := by
    congr 1; ext x; simp only [sq, Finset.mul_sum]; congr 1; ext m; ring
  rw [h1, integral_finsetSum _ (fun m _ =>
    (partial_sum_mul_hermite_integrable f N m).const_mul _)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [partial_sum_inner_hermite f N m (Finset.mem_range.mp hm), sq]

-- Helper: the cross term ∫ f * (∑ cₙψₙ) = ∑ cₙ²
private lemma cross_term_integral (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∫ x, f x * (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) =
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun n _ =>
    ((schwartz_mul_hermite_integrable f n).const_mul (hermiteCoeff1D n f)).congr
      (by filter_upwards with x; ring))]
  congr 1; ext n
  rw [show (fun x => f x * (hermiteCoeff1D n f * hermiteFunction n x)) =
    fun x => hermiteCoeff1D n f * (f x * hermiteFunction n x) from by ext x; ring,
    integral_const_mul]; unfold hermiteCoeff1D; ring

-- Bessel's identity: ∫ (f - ∑ cₙψₙ)² = ∫ f² - ∑ cₙ²
private lemma bessel_identity (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∫ x, (f x - ∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) ^ 2 =
    (∫ x, (f x) ^ 2) - ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 := by
  set S := fun x => ∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x
  -- Integrability facts
  have hint_f2 : Integrable (fun x => (f x) ^ 2) volume :=
    ((f.memLp 2 volume).integrable_mul (f.memLp 2 volume)).congr
      (by filter_upwards with x; change f x * f x = f x ^ 2; ring)
  have hint_S_memLp : MemLp S 2 volume := by
    apply memLp_finsetSum; intro n _; exact (hermiteFunction_memLp n).const_mul _
  have hint_fS : Integrable (fun x => f x * S x) volume :=
    (f.memLp 2 volume).integrable_mul hint_S_memLp
  have hint_S2 : Integrable (fun x => (S x) ^ 2) volume :=
    (hint_S_memLp.integrable_mul hint_S_memLp).congr
      (by filter_upwards with x; change S x * S x = S x ^ 2; ring)
  have hint_neg2fS : Integrable (fun x => -2 * (f x * S x)) volume :=
    hint_fS.const_mul (-2)
  -- Expand and compute
  calc ∫ x, (f x - S x) ^ 2
      = ∫ x, (f x ^ 2 + (-2 * (f x * S x) + S x ^ 2)) := by congr 1; ext x; ring
    _ = (∫ x, f x ^ 2) + ∫ x, (-2 * (f x * S x) + S x ^ 2) :=
        integral_add hint_f2 (hint_neg2fS.add hint_S2)
    _ = (∫ x, f x ^ 2) + ((∫ x, -2 * (f x * S x)) + ∫ x, S x ^ 2) :=
        by rw [integral_add hint_neg2fS hint_S2]
    _ = (∫ x, f x ^ 2) + (-2 * (∫ x, f x * S x) + ∫ x, S x ^ 2) := by rw [integral_const_mul]
    _ = (∫ x, f x ^ 2) + (-2 * ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 +
        ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2) := by
        rw [cross_term_integral, partial_sum_l2_norm_sq]
    _ = _ := by ring

-- Helper: Bessel's inequality
private lemma bessel_inequality (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 ≤ ∫ x, (f x) ^ 2 := by
  have h := bessel_identity f N
  have hnn : 0 ≤ ∫ x, (f x - ∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

-- Helper: summability of hermiteCoeff squares (Bessel's inequality)
private lemma hermiteCoeff_sq_summable (f : SchwartzMap ℝ ℝ) :
    Summable (fun n => hermiteCoeff1D n f ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (fun u => by
    calc ∑ x ∈ u, hermiteCoeff1D x f ^ 2
        ≤ ∑ n ∈ Finset.range (u.sup id + 1), hermiteCoeff1D n f ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_range]
            exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
          · intros; exact sq_nonneg _
      _ ≤ ∫ x, (f x) ^ 2 := bessel_inequality f _)

-- Helper: the Hermite series ∑ cₙ ψₙ(x) converges absolutely at every point.
private lemma hermite_series_summable_pointwise (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Summable (fun n => hermiteCoeff1D n f * hermiteFunction n x) := by
  apply Summable.of_norm_bounded (g := fun n => |hermiteCoeff1D n f| *
    SchwartzMap.seminorm ℝ 0 0 (schwartzHermiteBasis1D n))
  · exact hermite_expansion_seminorm_summable f 0 0
  · intro n
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h := SchwartzMap.le_seminorm ℝ 0 0 (schwartzHermiteBasis1D n) x
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
    rwa [schwartzHermiteBasis1D_apply, Real.norm_eq_abs] at h

-- Helper: |cₙ(f)| is summable (super-polynomial decay ⇒ summable)
private lemma hermiteCoeff_abs_summable (f : SchwartzMap ℝ ℝ) :
    Summable (fun n => |hermiteCoeff1D n f|) := by
  obtain ⟨C, q, hC, h_dec⟩ := hermiteCoeff1D_decay 2
  set S := (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  -- Bound: |cₙ| ≤ C * S * (1+n)^{-2}
  have h_bound : ∀ n : ℕ, |hermiteCoeff1D n f| ≤ C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    have h1n_pos : (0 : ℝ) < 1 + ↑n := by positivity
    have h := h_dec f n
    -- h : |cₙ| * (1+n)^(2:ℝ) ≤ C * S
    have h2_pos : (0 : ℝ) < (1 + (↑n : ℝ)) ^ (2 : ℝ) := rpow_pos_of_pos h1n_pos 2
    have hle : |hermiteCoeff1D n f| ≤ C * S / (1 + (↑n : ℝ)) ^ (2 : ℝ) :=
      (le_div_iff₀ h2_pos).mpr h
    rw [div_eq_mul_inv, ← rpow_neg h1n_pos.le] at hle; exact hle
  -- ∑ (1+n)^{-2} < ∞ (shifted p-series)
  have h_sum : Summable (fun n : ℕ => C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ)) := by
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by change ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    exact h1.const_smul (C * S)
  exact .of_nonneg_of_le (fun n => abs_nonneg _) h_bound h_sum

-- Helper: the pointwise tsum ∑' cₙψₙ is in L²
-- Proof: by Fatou's lemma. S_N² → (∑'cₙψₙ)² pointwise, and
-- ∫S_N² = ∑_{n<N} cₙ² ≤ ∫f².
private lemma hermite_series_memLp (f : SchwartzMap ℝ ℝ) :
    MemLp (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) 2 volume := by
  -- Define partial sums S_N(x) = ∑_{n<N} cₙ ψₙ(x)
  set S : ℕ → ℝ → ℝ := fun N x =>
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x with hS_def
  -- Partial sums are in L²
  have hS_memLp : ∀ N, MemLp (S N) 2 volume := fun N => by
    apply memLp_finsetSum; intro n _; exact (hermiteFunction_memLp n).const_mul _
  -- Partial sums converge pointwise to the tsum
  have hS_tendsto : ∀ x, Filter.Tendsto (fun N => S N x) Filter.atTop
      (nhds (∑' n, hermiteCoeff1D n f * hermiteFunction n x)) := fun x =>
    (hermite_series_summable_pointwise f x).hasSum.tendsto_sum_nat
  -- AEStronglyMeasurable for the tsum (limit of measurable functions)
  have h_aesm : AEStronglyMeasurable
      (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) volume :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun N => (hS_memLp N).aestronglyMeasurable)
      (ae_of_all _ hS_tendsto)
  -- Split: MemLp = AEStronglyMeasurable ∧ eLpNorm < ∞
  refine ⟨h_aesm, ?_⟩
  -- Use Fatou for eLpNorm: eLpNorm(limit) ≤ liminf eLpNorm(S_N)
  -- Then bound liminf by eLpNorm(f) using Bessel inequality
  apply lt_of_le_of_lt
  -- Step 1: Fatou gives eLpNorm(tsum) ≤ liminf eLpNorm(S_N)
  · exact Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun N => (hS_memLp N).aestronglyMeasurable) _ (ae_of_all _ hS_tendsto)
  -- Step 2: liminf eLpNorm(S_N) ≤ eLpNorm(f) < ∞
  -- Helper: convert ∫⁻ ‖g‖ₑ^(ENNReal.toReal 2) to ENNReal.ofReal (∫ g^2)
  have h_lintegral_sq : ∀ (g : ℝ → ℝ) (hg : Integrable (fun x => g x ^ 2) volume),
      ∫⁻ x, ‖g x‖ₑ ^ ENNReal.toReal 2 ∂volume =
        ENNReal.ofReal (∫ x, g x ^ 2 ∂volume) := by
    intro g hg
    have h_nn : 0 ≤ᵐ[volume] (fun x => g x ^ 2) := ae_of_all _ (fun x => sq_nonneg _)
    simp only [ENNReal.toReal_ofNat]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
    simp_rw [ENNReal.rpow_natCast]
    rw [show (fun x => ‖g x‖ₑ ^ 2) = (fun x => ENNReal.ofReal (g x ^ 2)) from by
      ext x; rw [← enorm_pow, enorm_eq_ofReal (sq_nonneg _)]]
    rw [← ofReal_integral_eq_lintegral_ofReal hg h_nn]
  -- Helper: eLpNorm(S_N) ≤ eLpNorm(f) for all N
  have h_eLpNorm_le : ∀ N, eLpNorm (S N) 2 volume ≤ eLpNorm f 2 volume := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    rw [h_lintegral_sq (S N) (hS_memLp N).integrable_sq,
        h_lintegral_sq f (f.memLp 2 volume).integrable_sq]
    exact ENNReal.ofReal_le_ofReal (by rw [partial_sum_l2_norm_sq]; exact bessel_inequality f N)
  apply lt_of_le_of_lt
  · apply Filter.liminf_le_of_frequently_le'
    exact Filter.Frequently.of_forall (fun N => h_eLpNorm_le N)
  · exact (f.memLp 2 volume).2

-- Helper: integral of tsum · ψₘ equals tsum of integrals
-- Uses integral_tsum with dominated convergence
private lemma integral_tsum_mul_hermite (f : SchwartzMap ℝ ℝ) (m : ℕ) :
    ∫ x, (∑' n, hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x =
    ∑' n, ∫ x, hermiteCoeff1D n f * hermiteFunction n x * hermiteFunction m x := by
  -- Step 1: (∑' cₙψₙ) * ψₘ = ∑' cₙψₙψₘ using tsum_mul_right
  conv_lhs => rw [show (fun x => (∑' n, hermiteCoeff1D n f * hermiteFunction n x) *
      hermiteFunction m x) = fun x => ∑' n, (hermiteCoeff1D n f *
      hermiteFunction n x * hermiteFunction m x) from by
    ext x; rw [← tsum_mul_right]]
  -- Step 2: interchange ∫ and ∑' using integral_tsum
  rw [integral_tsum
    -- AEStronglyMeasurable for each term
    (fun n => ((hermite_mul_hermite_integrable n m).const_mul _).congr
      (by filter_upwards with x; ring) |>.aestronglyMeasurable)
    -- Sum of lintegrals is finite
    (by
      -- Strategy: bound ∫⁻ ‖cₙψₙψₘ‖₊ using integrability, then sum
      -- Each cₙ * ψₙ * ψₘ is integrable
      have h_int : ∀ n, Integrable (fun a => hermiteCoeff1D n f *
          hermiteFunction n a * hermiteFunction m a) volume :=
        fun n => ((hermite_mul_hermite_integrable n m).const_mul _).congr
          (by filter_upwards with x; ring)
      -- Summable |cₙ| in NNReal
      have h_summable_nn : Summable (fun n => ‖hermiteCoeff1D n f‖₊) := by
        rw [← NNReal.summable_coe]
        exact (hermiteCoeff_abs_summable f).congr
          (fun n => by simp [coe_nnnorm, Real.norm_eq_abs])
      -- Helper: ∫ ψₖ² = 1 (from orthonormality)
      have hψ_sq : ∀ k, ∫ x, hermiteFunction k x ^ 2 = 1 := fun k => by
        simpa only [pow_two, ite_true] using hermiteFunction_orthonormal k k
      -- Helper: integrability of ψₖ²
      have hψ_sq_int : ∀ k, Integrable (fun x => hermiteFunction k x ^ 2) := fun k =>
        ((hermiteFunction_memLp k).integrable_mul (hermiteFunction_memLp k)).congr
          (by filter_upwards with x; change hermiteFunction k x * hermiteFunction k x = _; ring)
      -- Helper: ∫ |ψₙ * ψₘ| ≤ 1 by AM-GM + orthonormality
      have h_ψψ_norm_le : ∀ n, ∫ a, |hermiteFunction n a * hermiteFunction m a| ≤ 1 := by
        intro n
        calc ∫ a, |hermiteFunction n a * hermiteFunction m a|
            = ∫ a, |hermiteFunction n a| * |hermiteFunction m a| := by
              congr 1; ext a; exact abs_mul _ _
          _ ≤ ∫ a, ((hermiteFunction n a ^ 2 + hermiteFunction m a ^ 2) / 2) := by
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _))
                ((hψ_sq_int n).add (hψ_sq_int m) |>.div_const 2)
              exact Filter.Eventually.of_forall fun a => by
                simp only [Pi.add_apply]
                have h := two_mul_le_add_sq |hermiteFunction n a| |hermiteFunction m a|
                rw [sq_abs, sq_abs] at h
                linarith
          _ = 1 := by
              rw [integral_div, integral_add (hψ_sq_int n) (hψ_sq_int m), hψ_sq n, hψ_sq m]
              norm_num
      -- Each ∫⁻ ‖cₙψₙψₘ‖₊ ≤ ‖cₙ‖₊
      have h_bound : ∀ n, ∫⁻ a, ‖hermiteCoeff1D n f * hermiteFunction n a *
          hermiteFunction m a‖ₑ ≤ ↑‖hermiteCoeff1D n f‖₊ := by
        intro n
        -- ‖x‖ₑ = ↑‖x‖₊ for normed types
        change ∫⁻ a, ↑‖hermiteCoeff1D n f * hermiteFunction n a *
            hermiteFunction m a‖₊ ≤ ↑‖hermiteCoeff1D n f‖₊
        -- Factor out constant: ‖c * (ψₙ * ψₘ)‖₊ = ‖c‖₊ * ‖ψₙ * ψₘ‖₊
        conv_lhs => arg 2; ext a; rw [mul_assoc, nnnorm_mul, ENNReal.coe_mul]
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        suffices h : ∫⁻ a, ↑‖hermiteFunction n a * hermiteFunction m a‖₊ ≤ 1 by
          calc ↑‖hermiteCoeff1D n f‖₊ * ∫⁻ a, ↑‖hermiteFunction n a *
                  hermiteFunction m a‖₊
              ≤ ↑‖hermiteCoeff1D n f‖₊ * 1 := by gcongr
            _ = ↑‖hermiteCoeff1D n f‖₊ := mul_one _
        -- Show ∫⁻ ‖ψₙ * ψₘ‖₊ ≤ 1
        -- ↑‖x‖₊ = ‖x‖ₑ = ENNReal.ofReal ‖x‖ for normed types
        -- Use hasFiniteIntegral / lintegral bound
        -- Bound ∫⁻ ↑‖ψₙ * ψₘ‖₊ by converting through integral
        have hint := hermite_mul_hermite_integrable n m
        -- ∫⁻ ‖f‖₊ = ENNReal.ofReal (∫ ‖f‖) for integrable f
        -- We have ∫ ‖ψₙ * ψₘ‖ = ∫ |ψₙ * ψₘ| ≤ 1
        calc ∫⁻ a, ↑‖hermiteFunction n a * hermiteFunction m a‖₊
            = ∫⁻ a, ENNReal.ofReal ‖hermiteFunction n a * hermiteFunction m a‖ := by
              congr 1; ext a; exact (ofReal_norm _).symm
          _ = ENNReal.ofReal (∫ a, ‖hermiteFunction n a * hermiteFunction m a‖) := by
              exact (ofReal_integral_eq_lintegral_ofReal hint.norm
                (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm
          _ ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal (h_ψψ_norm_le n)
          _ = 1 := ENNReal.ofReal_one
      -- Sum the bound: ∑' ‖cₙ‖₊ < ⊤
      apply ne_top_of_le_ne_top
        (ENNReal.tsum_coe_ne_top_iff_summable.mpr h_summable_nn)
      exact ENNReal.tsum_le_tsum h_bound)]

-- The Hermite series converges to f a.e. (key lemma, uses hermiteFunction_complete)
private lemma hermite_series_eq_f_ae (f : SchwartzMap ℝ ℝ) :
    (fun x => f x - ∑' n, hermiteCoeff1D n f * hermiteFunction n x) =ᵐ[volume] 0 := by
  apply hermiteFunction_complete
  · -- MemLp (f - ∑' cₙψₙ) 2
    exact (f.memLp 2 volume).sub (hermite_series_memLp f)
  · -- ∀ m, ∫ (f - ∑' cₙψₙ) · ψₘ = 0
    intro m
    have hint_fψ := schwartz_mul_hermite_integrable f m
    have hint_Sψ : Integrable (fun x => (∑' n, hermiteCoeff1D n f *
        hermiteFunction n x) * hermiteFunction m x) volume :=
      (hermite_series_memLp f).integrable_mul (hermiteFunction_memLp m)
    rw [show (fun x => (f x - ∑' n, hermiteCoeff1D n f * hermiteFunction n x) *
        hermiteFunction m x) = fun x => f x * hermiteFunction m x -
        (∑' n, hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x from by
      ext x; ring]
    rw [integral_sub hint_fψ hint_Sψ, integral_tsum_mul_hermite]
    -- ∑' cₙ · ∫ ψₙ·ψₘ = cₘ (by orthonormality)
    simp_rw [show ∀ n, (fun x => hermiteCoeff1D n f * hermiteFunction n x *
        hermiteFunction m x) = fun x => hermiteCoeff1D n f *
        (hermiteFunction n x * hermiteFunction m x) from by intro n; ext x; ring]
    simp_rw [integral_const_mul, hermiteFunction_orthonormal]
    simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq]
    unfold hermiteCoeff1D; ring

-- Parseval's identity: ∫ f² = ∑' cₙ²
-- Uses hermite_series_eq_f_ae + Fatou's lemma for ≤ direction.
private lemma parseval_identity (f : SchwartzMap ℝ ℝ) :
    ∫ x, (f x) ^ 2 = ∑' n, hermiteCoeff1D n f ^ 2 := by
  apply le_antisymm
  · -- ≤ direction: ∫f² ≤ ∑' cₙ²
    -- By hermite_series_eq_f_ae, f = ∑'cₙψₙ a.e.
    -- So ∫f² = ∫(∑'cₙψₙ)² ≤ liminf ∫S_N² = ∑'cₙ² (Fatou)
    have hae := hermite_series_eq_f_ae f
    -- f² = (∑'cₙψₙ)² a.e.
    have h_sq_ae : (fun x => (f x) ^ 2) =ᵐ[volume]
        (fun x => (∑' n, hermiteCoeff1D n f * hermiteFunction n x) ^ 2) := by
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply, sub_eq_zero] at hx; rw [hx]
    rw [integral_congr_ae h_sq_ae]
    -- Now use Fatou: ∫(∑'cₙψₙ)² = ∫ lim S_N² ≤ liminf ∫ S_N² = ∑'cₙ²
    -- Define partial sums
    set c := fun n => hermiteCoeff1D n f
    set ψ := hermiteFunction
    set T := fun x => ∑' n, c n * ψ n x with hT_def
    set S : ℕ → ℝ → ℝ := fun N x =>
      ∑ n ∈ Finset.range N, c n * ψ n x with hS_def
    -- Key facts
    have hS_sq_eq : ∀ N, ∫ x, (S N x) ^ 2 =
        ∑ n ∈ Finset.range N, c n ^ 2 := partial_sum_l2_norm_sq f
    have hS_tendsto : ∀ x, Filter.Tendsto (fun N => S N x) Filter.atTop (nhds (T x)) :=
      fun x => (hermite_series_summable_pointwise f x).hasSum.tendsto_sum_nat
    have hc_summable := hermiteCoeff_sq_summable f
    -- Step 1: ∀ N, ∫ S_N² = ∑_{n<N} cₙ² ≤ ∑' cₙ²
    have h_le_tsum : ∀ N, ∫ x, (S N x) ^ 2 ≤ ∑' n, c n ^ 2 := by
      intro N
      rw [hS_sq_eq]
      exact hc_summable.sum_le_tsum _ (fun _ _ => sq_nonneg _)
    -- Step 2: Use Fatou via lintegral
    -- Convert Bochner integral to lintegral for nonneg functions
    have hT_sq_nn : 0 ≤ᵐ[volume] (fun x => (T x) ^ 2) :=
      ae_of_all _ (fun x => sq_nonneg _)
    have hT_sq_int : Integrable (fun x => (T x) ^ 2) volume :=
      ((hermite_series_memLp f).integrable_mul (hermite_series_memLp f)).congr
        (by filter_upwards with x; change T x * T x = T x ^ 2; ring)
    have hS_sq_int : ∀ N, Integrable (fun x => (S N x) ^ 2) volume := by
      intro N
      have hSmemLp : MemLp (S N) 2 volume := by
        apply memLp_finsetSum; intro n _; exact (hermiteFunction_memLp n).const_mul _
      exact (hSmemLp.integrable_mul hSmemLp).congr
        (by filter_upwards with x; change S N x * S N x = S N x ^ 2; ring)
    have hT_sq_aesm : AEStronglyMeasurable (fun x => (T x) ^ 2) volume :=
      hT_sq_int.aestronglyMeasurable
    -- Convert: ∫ T² = toReal (∫⁻ ofReal T²)
    rw [integral_eq_lintegral_of_nonneg_ae hT_sq_nn hT_sq_aesm]
    -- Suffices to show ∫⁻ ofReal T² ≤ ofReal (∑' cₙ²), then apply toReal
    apply ENNReal.toReal_le_of_le_ofReal (tsum_nonneg (fun n => sq_nonneg (c n)))
    -- Now: ∫⁻ ofReal T(x)² ≤ ofReal (∑' cₙ²)
    -- Step: rewrite as lintegral via ofReal_integral
    calc ∫⁻ x, ENNReal.ofReal ((T x) ^ 2) ∂volume
        = ∫⁻ x,
            Filter.liminf (fun N => ENNReal.ofReal ((S N x) ^ 2)) Filter.atTop
            ∂volume := by
          congr 1; ext x
          exact (Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal
            ((Filter.Tendsto.pow (hS_tendsto x) 2)))).symm
      _ ≤ Filter.liminf
            (fun N => ∫⁻ x, ENNReal.ofReal ((S N x) ^ 2) ∂volume) Filter.atTop := by
          apply lintegral_liminf_le'
          intro N
          exact (hS_sq_int N).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ = Filter.liminf
            (fun N => ENNReal.ofReal (∫ x, (S N x) ^ 2 ∂volume)) Filter.atTop := by
          congr 1; ext N
          exact (ofReal_integral_eq_lintegral_ofReal (hS_sq_int N)
            (ae_of_all _ (fun x => sq_nonneg _))).symm
      _ = Filter.liminf (fun N => ENNReal.ofReal
            (∑ n ∈ Finset.range N, c n ^ 2)) Filter.atTop := by
          congr 1; ext N; rw [hS_sq_eq]
      _ = ENNReal.ofReal (∑' n, c n ^ 2) := by
          exact Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal
            hc_summable.hasSum.tendsto_sum_nat)
  · -- ≥ direction: ∑' cₙ² ≤ integral f² (Bessel inequality in the limit)
    exact le_of_tendsto'
      (hermiteCoeff_sq_summable f).hasSum.tendsto_sum_nat
      (fun N => bessel_inequality f N)

theorem hermite_expansion_l2_convergence (f : SchwartzMap ℝ ℝ) :
    Filter.Tendsto
      (fun N => ∫ x, (f x - ∑ n ∈ Finset.range N,
        hermiteCoeff1D n f * hermiteFunction n x) ^ 2)
      Filter.atTop (nhds 0) := by
  simp_rw [bessel_identity f]
  have hparseval := parseval_identity f
  have htend := (hermiteCoeff_sq_summable f).hasSum.tendsto_sum_nat
  rw [show (0 : ℝ) = (∫ x, (f x) ^ 2) - ∑' n, hermiteCoeff1D n f ^ 2 from by
    rw [hparseval]; ring]
  exact Filter.Tendsto.sub tendsto_const_nhds htend

/-! ## Section 8: The 1D Expansion Theorem

Combining Schwartz convergence with limit identification:
for any CLM T : 𝓢(ℝ,ℝ) →L[ℝ] H,
  ⟨w, T(f)⟩ = ∑' n, cₙ(f) · ⟨w, T(ψₙ)⟩
-/

-- Helper: the norm bound for each term ψₙ(x) by p_{0,0} seminorm
private lemma hermiteFunction_norm_le_seminorm (n : ℕ) (x : ℝ) :
    |hermiteFunction n x| ≤ SchwartzMap.seminorm ℝ 0 0 (schwartzHermiteBasis1D n) := by
  have h := SchwartzMap.le_seminorm ℝ 0 0 (schwartzHermiteBasis1D n) x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
  rwa [schwartzHermiteBasis1D_apply, Real.norm_eq_abs] at h

-- Helper: iteratedFDeriv of schwartzHermiteBasis1D equals that of hermiteFunction
private lemma iteratedFDeriv_schwartzHermiteBasis1D_eq (n k : ℕ) (x : ℝ) :
    iteratedFDeriv ℝ k (⇑(schwartzHermiteBasis1D n)) x =
    iteratedFDeriv ℝ k (hermiteFunction n) x :=
  congr_arg (iteratedFDeriv ℝ k · x) (schwartzHermiteBasis1D_coe n)

-- Helper: uniform bound on iteratedFDeriv of cₙ * ψₙ by |cₙ| * p_{0,k}(ψₙ)
private lemma hermite_term_iteratedFDeriv_bound (f : SchwartzMap ℝ ℝ) (k n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => hermiteCoeff1D n f * hermiteFunction n y) x‖ ≤
    |hermiteCoeff1D n f| * SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n) := by
  have hsm : iteratedFDeriv ℝ k (fun y => hermiteCoeff1D n f * hermiteFunction n y) x =
      hermiteCoeff1D n f • iteratedFDeriv ℝ k (hermiteFunction n) x := by
    rw [show (fun y => hermiteCoeff1D n f * hermiteFunction n y) =
      (fun y => hermiteCoeff1D n f • hermiteFunction n y) from by ext; simp [smul_eq_mul]]
    exact iteratedFDeriv_const_smul_apply'
      ((hermiteFunction_contDiff n k).contDiffAt)
  rw [hsm, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by
    have h := SchwartzMap.le_seminorm ℝ 0 k (schwartzHermiteBasis1D n) x
    simp only [pow_zero, one_mul] at h
    rwa [iteratedFDeriv_schwartzHermiteBasis1D_eq] at h) (abs_nonneg _)

-- Helper: summability of the uniform bounds
private lemma hermite_term_bound_summable (f : SchwartzMap ℝ ℝ) (k : ℕ) :
    Summable (fun n => |hermiteCoeff1D n f| *
      SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n)) :=
  hermite_expansion_seminorm_summable f 0 k

-- Helper: f(x) = ∑' cₙ ψₙ(x) for ALL x (not just a.e.)
private lemma hermite_series_eq_f_everywhere (f : SchwartzMap ℝ ℝ) :
    ∀ x, f x = ∑' n, hermiteCoeff1D n f * hermiteFunction n x := by
  have hae := hermite_series_eq_f_ae f
  have h_cont : Continuous (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) :=
    continuous_tsum
      (fun n => continuous_const.mul (hermiteFunction_contDiff n 0).continuous)
      (hermite_term_bound_summable f 0)
      (fun n x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hermiteFunction_norm_le_seminorm n x) (abs_nonneg _))
  have hae' : (⇑f) =ᵐ[volume]
      (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) := by
    filter_upwards [hae] with y hy
    simp only [Pi.zero_apply, sub_eq_zero] at hy; exact hy
  exact congr_fun ((f.continuous.ae_eq_iff_eq volume h_cont).mp hae')

-- Helper: termwise differentiation of the Hermite series
private lemma hermite_series_iteratedFDeriv (f : SchwartzMap ℝ ℝ) (l : ℕ) (x : ℝ) :
    iteratedFDeriv ℝ l (fun y => ∑' n, hermiteCoeff1D n f * hermiteFunction n y) x =
    ∑' n, iteratedFDeriv ℝ l (fun y => hermiteCoeff1D n f * hermiteFunction n y) x := by
  apply iteratedFDeriv_tsum_apply (N := ⊤)
      (v := fun k n =>
        |hermiteCoeff1D n f| *
          SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n))
  · intro n; exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
  · intro k _; exact hermite_term_bound_summable f k
  · intro k n y _; exact hermite_term_iteratedFDeriv_bound f k n y
  · exact le_top

/-- **Schwartz seminorm tail bound**: for any finite set s controlling the vanishing
    of the coefficient-seminorm series, the Schwartz seminorm of the Hermite expansion
    remainder f - ∑_{i∈s} cᵢ·ψᵢ is bounded.

    Proof:
    1. f(x) = ∑' cₙ ψₙ(x) everywhere [hermite_series_eq_f_everywhere]
    2. Termwise differentiation:
       D^l(f)(x) = ∑' cₙ · D^l(ψₙ)(x) [hermite_series_iteratedFDeriv].
       So r = f - ∑_{i∈s} cᵢψᵢ satisfies
       D^l(r)(x) = ∑'_{i∉s} cᵢ D^l(ψᵢ)(x).
    3. For each x:
       ‖x‖^k · ‖D^l(r)(x)‖ ≤
       ∑'_{i∉s} |cᵢ| · ‖x‖^k · ‖D^l(ψᵢ)(x)‖.
    4. Bound by ∑'_{i∉s} |cᵢ| · p_{k,l}(ψᵢ) ≤ ε (from vanishing condition).
-/
private lemma schwartz_seminorm_remainder_le (f : SchwartzMap ℝ ℝ) (k l : ℕ)
    (s : Finset ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (h_vanish : ∀ t : Finset ℕ, Disjoint t s →
      ∑ i ∈ t, |hermiteCoeff1D i f| *
        SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D i) ≤ ε) :
    SchwartzMap.seminorm ℝ k l
      (f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i) ≤ ε := by
  -- Reduce to pointwise bound: ∀ x, |x|^k * ‖iteratedDeriv l (remainder) x‖ ≤ ε
  apply SchwartzMap.seminorm_le_bound' ℝ k l _ hε
  intro x
  -- Let r denote the remainder Schwartz function
  set r := f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i with hr_def
  -- Abbreviation for the n-th term as a plain function
  let g : ℕ → ℝ → ℝ := fun n y => hermiteCoeff1D n f * hermiteFunction n y
  -- Summability of iteratedFDeriv values
  have h_summ_iFD : Summable (fun n => iteratedFDeriv ℝ l (g n) x) := by
    apply Summable.of_norm_bounded
      (g := fun n => |hermiteCoeff1D n f| *
        SchwartzMap.seminorm ℝ 0 l (schwartzHermiteBasis1D n))
    · exact hermite_term_bound_summable f l
    · intro n; exact hermite_term_iteratedFDeriv_bound f l n x
  -- Step 1: iteratedFDeriv of f = ∑' iteratedFDeriv(gₙ)
  have h_iFD_f : iteratedFDeriv ℝ l (⇑f) x = ∑' n, iteratedFDeriv ℝ l (g n) x := by
    have hf_eq : ⇑f = fun y => ∑' n, g n y := funext (hermite_series_eq_f_everywhere f)
    rw [hf_eq]; exact hermite_series_iteratedFDeriv f l x
  -- Step 2: coercion of finite Schwartz sum = pointwise finite sum
  have hsum_coe : ∀ y, (∑ i ∈ s,
    hermiteCoeff1D i f • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
      ∑ i ∈ s, g i y := by
    intro y
    have : ∀ (t : Finset ℕ), (∑ i ∈ t,
      hermiteCoeff1D i f • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
        ∑ i ∈ t, g i y := by
      intro t; induction t using Finset.cons_induction with
      | empty => simp
      | cons a t' ha ih => simp [smul_eq_mul,
          schwartzHermiteBasis1D_apply, g]
    exact this s
  -- Step 3: iteratedFDeriv of the finite sum = ∑_{i∈s} iteratedFDeriv(gᵢ)
  have h_iFD_sum : iteratedFDeriv ℝ l
      (⇑(∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ)) x =
      ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
    have hcoe :
        ⇑((∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i :
          SchwartzMap ℝ ℝ)) =
          fun y => ∑ i ∈ s, g i y := funext hsum_coe
    rw [hcoe]
    have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
      (fun i _ => (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
    -- h_eq : iteratedFDeriv ℝ l (∑ j ∈ s, g j ·) = ∑ j ∈ s, iteratedFDeriv ℝ l (g j)
    have := congr_fun h_eq x
    simpa only [Finset.sum_apply] using this
  -- Step 4: iteratedFDeriv of r = ∑'_{i∉s} iteratedFDeriv(gₙ)
  have h_iFD_r : iteratedFDeriv ℝ l (⇑r) x =
      ∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x := by
    have hf_cd : ContDiff ℝ l (⇑f) := (f.smooth l).of_le le_rfl
    have hg_cd : ContDiff ℝ l (fun y => ∑ i ∈ s, g i y) :=
      ContDiff.sum (fun i _ =>
        (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
    -- ⇑r = ⇑f - (finite sum function)
    have hcoe_r : (⇑r : ℝ → ℝ) = fun y => f y - ∑ i ∈ s, g i y := by
      ext y; simp only [hr_def, sub_apply]
      exact congrArg (f y - ·) (hsum_coe y)
    rw [hcoe_r]
    -- Compute iteratedFDeriv of (f - sum) via iteratedFDeriv_add + iteratedFDeriv_neg
    set h_sum := fun y => ∑ i ∈ s, g i y with h_sum_def
    have h_neg_cd : ContDiff ℝ l (-h_sum) := hg_cd.neg
    -- (fun y => f y - h_sum y) = ⇑f + (-h_sum) as Pi functions
    have h_rw : (fun y => f y - h_sum y) = ⇑f + (-h_sum) := by ext; simp [sub_eq_add_neg]
    rw [h_rw, iteratedFDeriv_add hf_cd h_neg_cd, Pi.add_apply,
      iteratedFDeriv_neg, Pi.neg_apply, h_iFD_f]
    -- iteratedFDeriv of h_sum
    have h_iFD_h : iteratedFDeriv ℝ l h_sum x = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
      rw [h_sum_def]
      have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
        (fun i _ => (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
      -- h_eq : iteratedFDeriv ℝ l (∑ j ∈ s, g j ·) = ∑ j ∈ s, iteratedFDeriv ℝ l (g j)
      calc iteratedFDeriv ℝ l (fun y => ∑ i ∈ s, g i y) x
          = (∑ j ∈ s, iteratedFDeriv ℝ l (g j)) x := congr_fun h_eq x
        _ = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := Finset.sum_apply x s _
    rw [h_iFD_h, ← h_summ_iFD.sum_add_tsum_compl (s := s)]
    abel
  -- Step 5: Bound |x|^k * ‖iteratedDeriv l r x‖
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm, h_iFD_r]
  -- Summability of norms on complement
  have h_norm_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
      ‖iteratedFDeriv ℝ l (g ↑i) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun ⟨n, _⟩ => hermite_term_iteratedFDeriv_bound f l n x)
      ((hermite_term_bound_summable f l).subtype _)
  -- Summability of the seminorm bounds on complement
  have h_sem_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
      |hermiteCoeff1D (↑i) f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D (↑i))) :=
    (hermite_expansion_seminorm_summable f k l).subtype _
  -- Key pointwise bound: |x|^k * ‖iteratedFDeriv l (gₙ) x‖ ≤ |cₙ| * p_{k,l}(ψₙ)
  have h_ptwise : ∀ (i : ↥(↑s : Set ℕ)ᶜ),
      |x| ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖ ≤
      |hermiteCoeff1D (↑i) f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D (↑i)) := by
    intro ⟨n, _⟩
    -- Rewrite g n as the coercion of cₙ • ψₙ
    have hg_eq : g n = ⇑(hermiteCoeff1D n f • schwartzHermiteBasis1D n) := by
      ext y; simp [g, smul_eq_mul, schwartzHermiteBasis1D_apply]
    rw [hg_eq]
    -- le_seminorm gives: ‖x‖^k * ‖iteratedFDeriv‖ ≤ p_{k,l}(c • ψ)
    -- For ℝ, ‖x‖ = |x| via Real.norm_eq_abs
    have h_bound := SchwartzMap.le_seminorm ℝ k l
      (hermiteCoeff1D n f • schwartzHermiteBasis1D n) x
    rw [Real.norm_eq_abs] at h_bound
    calc |x| ^ k * ‖iteratedFDeriv ℝ l
            (⇑(hermiteCoeff1D n f • schwartzHermiteBasis1D n)) x‖
        ≤ SchwartzMap.seminorm ℝ k l
            (hermiteCoeff1D n f • schwartzHermiteBasis1D n) := h_bound
      _ = |hermiteCoeff1D n f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
  -- Chain: |x|^k * ‖tsum‖ ≤ tsum of bounds ≤ ε
  calc |x| ^ k * ‖∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x‖
      ≤ |x| ^ k * ∑' (i : ↥(↑s : Set ℕ)ᶜ), ‖iteratedFDeriv ℝ l (g ↑i) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
          (pow_nonneg (abs_nonneg x) k)
    _ = ∑' (i : ↥(↑s : Set ℕ)ᶜ), (|x| ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖) := by rw [tsum_mul_left]
    _ ≤ ∑' (i : ↥(↑s : Set ℕ)ᶜ),
          (|hermiteCoeff1D (↑i) f| *
            SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D (↑i))) :=
        (h_norm_summ.mul_left _).tsum_le_tsum h_ptwise h_sem_summ
    _ ≤ ε := by
        apply h_sem_summ.tsum_le_of_sum_le
        intro t
        -- t is a Finset over sᶜ; map to Finset ℕ disjoint from s
        set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
        have h_disj : Disjoint t' s := by
          rw [Finset.disjoint_left]
          intro n hn hn_s
          rw [Finset.mem_map] at hn
          obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
          exact hm hn_s
        have h_le := h_vanish t' h_disj
        rwa [ht'_def, Finset.sum_map] at h_le

lemma schwartz_hermite_hasSum (f : SchwartzMap ℝ ℝ) :
    HasSum (fun n => hermiteCoeff1D n f • schwartzHermiteBasis1D n) f := by
  rw [HasSum]
  change Filter.Tendsto _ Filter.atTop _
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ f]
  intro ⟨k, l⟩ ε hε
  have h_sem := hermite_expansion_seminorm_summable f k l
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp h_sem (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs => ?_⟩
  rw [show (∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i) - f =
    -(f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i) from by abel,
    map_neg_eq_map]
  -- Chain: seminorm ≤ ε/2 < ε
  calc SchwartzMap.seminorm ℝ k l
        (f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i)
      ≤ ε / 2 := by
        apply schwartz_seminorm_remainder_le f k l s (half_pos hε).le
        intro t ht
        have h_disj : Disjoint t s₀ := Disjoint.mono_right hs ht
        have := hs₀ t h_disj
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
          mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at this
        exact le_of_lt this
    _ < ε := half_lt_self hε

theorem schwartz_hermite_expansion_1D :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
       (T : (SchwartzMap ℝ ℝ) →L[ℝ] H) (f : SchwartzMap ℝ ℝ) (w : H),
       @inner ℝ H _ w (T f) =
         ∑' n, hermiteCoeff1D n f * @inner ℝ H _ w (T (schwartzHermiteBasis1D n)) := by
  intro H _ _ _ T f w
  -- Apply CLM T to Schwartz HasSum
  have h_T := (schwartz_hermite_hasSum f).map T T.continuous
  simp only [Function.comp_def, map_smul] at h_T
  -- Apply inner product ⟪w, ·⟫ (continuous linear functional)
  have h_inner := h_T.map (innerSL ℝ w) (innerSL ℝ w).continuous
  simp only [Function.comp_def, innerSL_apply_apply, real_inner_smul_right] at h_inner
  exact h_inner.tsum_eq.symm

end
