/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.PrimePowerExpansion
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouExponentialInversion

/-!
# Regularized Prime Power Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain MeasureTheory Real

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime power location used in the Odlyzko-bound argument. -/
noncomputable def primePowerLocation
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℝ :=
  (e + 1 : ℕ) * Real.log (primeIdealNorm K P)

/-- A regularized prime power poitou weight used in the Odlyzko-bound argument. -/
noncomputable def regularizedPrimePowerPoitouWeight
    (y δ : ℝ) (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℝ :=
  Real.log (primeIdealNorm K P) *
    poitouKernel (regularizedScaledTartar y δ)
      (primePowerLocation K P e) *
    Real.exp (-(primePowerLocation K P e) / 2)

theorem regularizedPrimePowerPoitouWeight_nonneg
    (y δ : ℝ)
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    0 ≤ regularizedPrimePowerPoitouWeight K y δ P e := by
  unfold regularizedPrimePowerPoitouWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Real.log_nonneg (by
        exact_mod_cast (Nat.le_of_lt (one_lt_primeIdealNorm K P)))
    · unfold poitouKernel
      exact div_nonneg
        (regularizedScaledTartar_nonneg y δ _)
        (Real.cosh_pos _).le
  · exact (Real.exp_pos _).le

theorem integral_poitouTransform_regularized_mul_primePowerLogTerm
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ)
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        primePowerLogTerm K P e (σ + t * I)) =
      ((2 * Real.pi *
        regularizedPrimePowerPoitouWeight K y δ P e : ℝ) : ℂ) := by
  simp_rw [primePowerLogTerm_eq_log_mul_cexp_neg]
  rw [show
      (fun t : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          ((Real.log (primeIdealNorm K P) : ℂ) *
            Complex.exp
              (-(((e + 1 : ℕ) : ℝ) *
                Real.log (primeIdealNorm K P)) * (σ + t * I)))) =
        fun t : ℝ ↦
          (Real.log (primeIdealNorm K P) : ℂ) *
            (poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
              Complex.exp
                (-(((e + 1 : ℕ) : ℝ) *
                  Real.log (primeIdealNorm K P)) * (σ + t * I))) by
    grind,
    integral_const_mul]
  have h :=
    integral_poitouTransform_regularized_mul_exp_neg
      hδ y σ ((e + 1 : ℕ) * Real.log (primeIdealNorm K P))
  have hinner :
      (∫ t : ℝ,
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          Complex.exp
            (-(((e + 1 : ℕ) : ℝ) *
              Real.log (primeIdealNorm K P)) * (σ + t * I))) =
        2 * Real.pi *
          (poitouKernel (regularizedScaledTartar y δ)
            (((e + 1 : ℕ) : ℝ) *
              Real.log (primeIdealNorm K P)) : ℂ) *
          Complex.exp
            (-((((e + 1 : ℕ) : ℝ) *
              Real.log (primeIdealNorm K P))) / 2) := by simp_all
  rw [hinner]
  unfold regularizedPrimePowerPoitouWeight primePowerLocation
  push_cast
  ring

end NumberField.Odlyzko
