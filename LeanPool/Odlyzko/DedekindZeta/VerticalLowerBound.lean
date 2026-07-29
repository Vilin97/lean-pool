/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealEulerProduct
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealSummability
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Vertical Lower Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A dedekind zeta inverse vertical majorant used in the Odlyzko-bound argument. -/
noncomputable def dedekindZetaInverseVerticalMajorant : ℝ :=
  Real.exp <| ∑' P : HeightOneSpectrum (𝓞 K),
    (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ))

lemma one_le_dedekindZetaInverseVerticalMajorant :
    1 ≤ dedekindZetaInverseVerticalMajorant K := by
  rw [dedekindZetaInverseVerticalMajorant]
  exact Real.one_le_exp <| tsum_nonneg
    (fun _ ↦ Real.rpow_nonneg (by positivity) _)

private lemma norm_one_sub_inverseNormPower_two_add_mul_I_le
    (P : HeightOneSpectrum (𝓞 K)) (t : ℝ) :
    ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖ ≤
      1 + (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ)) := by
  calc
    ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖
        ≤ ‖(1 : ℂ)‖ +
            ‖-inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖ :=
      norm_add_le _ _
    _ = 1 + (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ)) := by
      rw [norm_one, norm_neg, norm_inverseNormPower _ (Nat.zero_lt_of_lt
        (one_lt_primeIdealNorm K P))]
      simp

private lemma multipliable_one_sub_inverseNormPower_two_add_mul_I (t : ℝ) :
    Multipliable (fun P : HeightOneSpectrum (𝓞 K) ↦
      1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)) := by
  have hnorm :
      Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
        ‖-inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖) := by
    simpa [norm_inverseNormPower, Nat.zero_lt_of_lt (one_lt_primeIdealNorm K _)] using
      (summable_primeIdealNorm_rpow K (show (1 : ℝ) < 2 by norm_num))
  have h := multipliable_one_add_of_summable (R := ℂ) hnorm
  grind

private lemma one_sub_inverseNormPower_two_add_mul_I_hasProd (t : ℝ) :
    HasProd
      (fun P : HeightOneSpectrum (𝓞 K) ↦
        1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I))
      (NumberField.dedekindZeta K (2 + t * Complex.I))⁻¹ := by
  let s : ℂ := 2 + t * Complex.I
  have hs : 1 < s.re := by simp [s]
  have hf := multipliable_primeIdealFactor K hs
  have hg := multipliable_one_sub_inverseNormPower_two_add_mul_I K t
  have hmul := hf.tprod_mul hg
  have hzeta :
      ∏' P : HeightOneSpectrum (𝓞 K), primeIdealFactor K P s =
        NumberField.dedekindZeta K s :=
    dedekindZeta_primeIdeal_eulerProduct_tprod K hs
  have hleft :
      ∏' P : HeightOneSpectrum (𝓞 K),
        primeIdealFactor K P s *
          (1 + -inverseNormPower (primeIdealNorm K P) s) = 1 := by
    have hfactor : ∀ P : HeightOneSpectrum (𝓞 K),
        primeIdealFactor K P s *
          (1 + -inverseNormPower (primeIdealNorm K P) s) = 1 := by
      intro P
      rw [primeIdealFactor, localFactor]
      exact inv_mul_cancel₀ <| by
        simpa [sub_eq_add_neg] using one_sub_inverseNormPower_ne_zero
          (one_lt_primeIdealNorm K P) (zero_lt_one.trans hs)
    simp only [hfactor, tprod_one]
  rw [hleft, hzeta] at hmul
  have htprod :
      ∏' P : HeightOneSpectrum (𝓞 K),
        (1 + -inverseNormPower (primeIdealNorm K P) s) =
          (NumberField.dedekindZeta K s)⁻¹ := by grind
  rw [← htprod]
  exact hg.hasProd

theorem norm_inv_dedekindZeta_two_add_mul_I_le (t : ℝ) :
    ‖(NumberField.dedekindZeta K (2 + t * Complex.I))⁻¹‖ ≤
      dedekindZetaInverseVerticalMajorant K := by
  have hzeta :
      HasProd
        (fun P : HeightOneSpectrum (𝓞 K) ↦
          ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖)
        ‖(NumberField.dedekindZeta K (2 + t * Complex.I))⁻¹‖ := by
    exact (one_sub_inverseNormPower_two_add_mul_I_hasProd K t).norm
  apply hasProd_le_of_prod_le hzeta
  intro S
  calc
    ∏ P ∈ S,
        ‖1 + -inverseNormPower (primeIdealNorm K P) (2 + t * Complex.I)‖ ≤
        ∏ P ∈ S, (1 + (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ))) := by
      exact Finset.prod_le_prod
        (fun _ _ ↦ norm_nonneg _)
        (fun P _ ↦ norm_one_sub_inverseNormPower_two_add_mul_I_le K P t)
    _ ≤ Real.exp (∑ P ∈ S, (primeIdealNorm K P : ℝ) ^ (-(2 : ℝ))) :=
      Real.prod_one_add_le_exp_sum S
        (fun _ ↦ Real.rpow_nonneg (by positivity) _)
    _ ≤ dedekindZetaInverseVerticalMajorant K := by
      rw [dedekindZetaInverseVerticalMajorant]
      exact Real.exp_le_exp.mpr <|
        (summable_primeIdealNorm_rpow K (by norm_num)).sum_le_tsum S
          (fun _ _ ↦ Real.rpow_nonneg (by positivity) _)

theorem one_le_dedekindZetaInverseVerticalMajorant_mul_norm (t : ℝ) :
    1 ≤ dedekindZetaInverseVerticalMajorant K *
      ‖NumberField.dedekindZeta K (2 + t * Complex.I)‖ := by
  have hs : 1 < (2 + t * Complex.I : ℂ).re := by simp
  have hzeta : NumberField.dedekindZeta K (2 + t * Complex.I) ≠ 0 := by
    rw [← dedekindZeta_primeIdeal_eulerProduct_tprod K hs]
    exact tprod_primeIdealFactor_ne_zero K hs
  have h := mul_le_mul_of_nonneg_right
    (norm_inv_dedekindZeta_two_add_mul_I_le K t)
    (norm_nonneg (NumberField.dedekindZeta K (2 + t * Complex.I)))
  simp_all

end NumberField.Odlyzko
