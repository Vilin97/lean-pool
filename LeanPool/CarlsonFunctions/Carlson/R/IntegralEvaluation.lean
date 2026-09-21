/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Evaluation of Euler-type integrals by Carlson R-functions

This file is the home for the general integral evaluations of [Carl77, Section 8.1].  We
first use the unit-interval parameterization; oriented complex line-segment versions can be
derived from it without building phase choices into the basic definition.
-/

open Complex MeasureTheory ProbabilityTheory
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The Euler-type unit-interval integral underlying Carlson's Formula 8.1-1. -/
def carlsonEulerSegmentIntegral (a a' : ℂ) (b p q : ι → ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioo 0 1,
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
      ∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i)

/-- Componentwise endpoint ratio used in Carlson's finite-segment evaluation. -/
def carlsonEndpointRatio (p q : ι → ℂ) : ι → ℂ :=
  fun i => q i / p i

/-- The principal logarithms used to factor an affine endpoint segment are compatible.

This is the exact branch condition needed for
`((1-u) * p i + u * q i) ^ c = (p i) ^ c * ((1-u) + u * q i / p i) ^ c`.
It cannot in general be replaced by nonvanishing of the segment. -/
def CompatibleCarlsonSegmentLogs (p q : ι → ℂ) : Prop :=
  ∀ i u, u ∈ Set.Ioo (0 : ℝ) 1 →
    log ((1 - u : ℂ) * p i + (u : ℂ) * q i) =
      log (p i) + log ((1 - u : ℂ) + (u : ℂ) * (q i / p i))

/-- Carlson's Formula 8.1-1 in unit-interval form, with the principal-log compatibility
hypothesis needed to extract the endpoint powers. -/
theorem carlsonEulerSegmentIntegral_eq_rIntegral
    {a a' : ℂ} {b p q : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hp : ∀ i, p i ≠ 0)
    (hsegment : ∀ i, ∀ u : ℝ, u ∈ Set.Icc 0 1 →
      (1 - u : ℂ) * p i + (u : ℂ) * q i ≠ 0)
    (hlog : CompatibleCarlsonSegmentLogs p q)
    (hratio : carlsonEndpointRatio p q ∈ carlsonRVariableDomain) :
    carlsonEulerSegmentIntegral a a' b p q =
      betaIntegral a a' * (∏ i, (p i) ^ (-b i)) *
        carlsonRIntegral (-a) b (carlsonEndpointRatio p q) := by
  let P : ℂ := ∏ i, (p i) ^ (-b i)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
          ∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i) =
        P * ((u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
          ∏ i, ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i)) := by
    have hfactor (i : ι) :
        (1 - u : ℂ) * p i + (u : ℂ) * q i =
          p i * ((1 - u : ℂ) + (u : ℂ) * (q i / p i)) := by
      field_simp [hp i]
    have hpow (i : ι) :
        ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i) =
          (p i) ^ (-b i) *
            ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i) := by
      change ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i) =
        (p i) ^ (-b i) * ((1 - u : ℂ) + (u : ℂ) * (q i / p i)) ^ (-b i)
      have haff : (1 - u : ℂ) * p i + (u : ℂ) * q i ≠ 0 :=
        hsegment i u ⟨hu.1.le, hu.2.le⟩
      have hnorm : (1 - u : ℂ) + (u : ℂ) * (q i / p i) ≠ 0 := by
        intro hz
        apply haff
        rw [hfactor i, hz, mul_zero]
      rw [cpow_def_of_ne_zero haff, cpow_def_of_ne_zero (hp i),
        cpow_def_of_ne_zero hnorm, hlog i u hu, add_mul, exp_add]
    have hprod :
        (∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i)) =
          P * ∏ i,
            ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i) := by
      calc
        _ = ∏ i, (p i) ^ (-b i) *
            ((1 - u : ℂ) + (u : ℂ) * carlsonEndpointRatio p q i) ^ (-b i) := by
              apply Finset.prod_congr rfl
              intro i _
              exact hpow i
        _ = _ := by rw [Finset.prod_mul_distrib]
    rw [hprod]
    ring
  unfold carlsonEulerSegmentIntegral
  calc
    (∫ u : ℝ in Set.Ioo 0 1,
        (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
          ∏ i, ((1 - u : ℂ) * p i + (u : ℂ) * q i) ^ (-b i)) =
      P * carlsonRUnitIntervalIntegral a a' b (carlsonEndpointRatio p q) := by
        rw [carlsonRUnitIntervalIntegral, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        exact hpoint u hu
    _ = betaIntegral a a' * (∏ i, (p i) ^ (-b i)) *
        carlsonRIntegral (-a) b (carlsonEndpointRatio p q) := by
      rw [carlsonRUnitIntervalIntegral_eq ha ha' hsum hb hratio]
      dsimp only [P]
      ring

/-- The ray integral underlying Carlson's Formulas 8.1-2 and 8.1-3.  The choice of endpoint
values `p` and ray directions `w` accommodates either orientation. -/
def carlsonEulerRayIntegral (a : ℂ) (b p w : ι → ℂ) : ℂ :=
  ∫ s : ℝ in Set.Ioi 0,
    (s : ℂ) ^ (a - 1) * ∏ i, (p i + (s : ℂ) * w i) ^ (-b i)

/-- The principal logarithms used to factor a Carlson ray are compatible. -/
def CompatibleCarlsonRayLogs (p w : ι → ℂ) : Prop :=
  ∀ i (s : ℝ), 0 < s →
    log (p i + (s : ℂ) * w i) =
      log (w i) + log (p i / w i + (s : ℂ))

/-- Carlson's Formulas 8.1-2 and 8.1-3, with the principal-log compatibility hypothesis
needed to extract the ray-direction powers. -/
theorem carlsonEulerRayIntegral_eq_rIntegral
    {a a' : ℂ} {b p w : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i) (hb : b ∈ mvBetaConvergent)
    (hw : ∀ i, w i ≠ 0)
    (hray : ∀ i, ∀ s : ℝ, 0 ≤ s → p i + (s : ℂ) * w i ≠ 0)
    (hlog : CompatibleCarlsonRayLogs p w)
    (hvars : (fun i => p i / w i) ∈ carlsonRVariableDomain) :
    carlsonEulerRayIntegral a b p w =
      betaIntegral a a' * (∏ i, (w i) ^ (-b i)) *
        carlsonRIntegral (-a') b (fun i => p i / w i) := by
  let W : ℂ := ∏ i, (w i) ^ (-b i)
  have hpoint (s : ℝ) (hs : s ∈ Set.Ioi (0 : ℝ)) :
      (s : ℂ) ^ (a - 1) * ∏ i, (p i + (s : ℂ) * w i) ^ (-b i) =
        W * ((s : ℂ) ^ (a - 1) *
          ∏ i, (p i / w i + (s : ℂ)) ^ (-b i)) := by
    have hfactor (i : ι) :
        p i + (s : ℂ) * w i = w i * (p i / w i + (s : ℂ)) := by
      field_simp [hw i]
    have hpow (i : ι) :
        (p i + (s : ℂ) * w i) ^ (-b i) =
          (w i) ^ (-b i) * (p i / w i + (s : ℂ)) ^ (-b i) := by
      have haff : p i + (s : ℂ) * w i ≠ 0 := hray i s hs.le
      have hnorm : p i / w i + (s : ℂ) ≠ 0 := by
        intro hz
        apply haff
        rw [hfactor i, hz, mul_zero]
      rw [cpow_def_of_ne_zero haff, cpow_def_of_ne_zero (hw i),
        cpow_def_of_ne_zero hnorm, hlog i s hs, add_mul, exp_add]
    have hprod :
        (∏ i, (p i + (s : ℂ) * w i) ^ (-b i)) =
          W * ∏ i, (p i / w i + (s : ℂ)) ^ (-b i) := by
      calc
        _ = ∏ i, (w i) ^ (-b i) * (p i / w i + (s : ℂ)) ^ (-b i) := by
              apply Finset.prod_congr rfl
              intro i _
              exact hpow i
        _ = _ := by rw [Finset.prod_mul_distrib]
    rw [hprod]
    ring
  unfold carlsonEulerRayIntegral
  calc
    (∫ s : ℝ in Set.Ioi 0,
        (s : ℂ) ^ (a - 1) * ∏ i, (p i + (s : ℂ) * w i) ^ (-b i)) =
      W * carlsonRPositiveRayIntegral a b (fun i => p i / w i) := by
        rw [carlsonRPositiveRayIntegral, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        exact hpoint s hs
    _ = betaIntegral a a' * (∏ i, (w i) ^ (-b i)) *
        carlsonRIntegral (-a') b (fun i => p i / w i) := by
      rw [carlsonRPositiveRayIntegral_eq ha ha' hsum hb hvars]
      dsimp only [W]
      ring

end DirichletTransform
end CarlsonR
