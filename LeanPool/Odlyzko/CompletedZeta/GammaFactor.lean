/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.Defs
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex

namespace NumberField.Odlyzko

/-- A complex place gamma factor used in the Odlyzko-bound argument. -/
def CompletedZeta.complexPlaceGammaFactor (s : ℂ) : ℂ :=
  Complex.Gammaℂ s / 2

theorem complexPlaceGammaFactor_eq (s : ℂ) :
    CompletedZeta.complexPlaceGammaFactor s = (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s := by
  rw [CompletedZeta.complexPlaceGammaFactor, Complex.Gammaℂ_def]
  ring

theorem complexPlaceGammaFactor_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    CompletedZeta.complexPlaceGammaFactor s ≠ 0 := by
  rw [complexPlaceGammaFactor_eq]
  exact mul_ne_zero
    (cpow_ne_zero_iff.mpr <| Or.inl <| mul_ne_zero two_ne_zero <|
      ofReal_ne_zero.mpr Real.pi_ne_zero)
    (Complex.Gamma_ne_zero_of_re_pos hs)

theorem differentiableAt_complexPlaceGammaFactor_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ CompletedZeta.complexPlaceGammaFactor s := by
  rw [show CompletedZeta.complexPlaceGammaFactor =
      fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z by
    funext z
    exact complexPlaceGammaFactor_eq z]
  apply DifferentiableAt.mul
  · exact differentiableAt_id.neg.const_cpow <|
      Or.inl <| mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  · exact Complex.differentiableAt_Gamma s fun n h ↦ by
      have : 0 < (-n : ℂ).re := h ▸ hs
      simp only [neg_re, natCast_re, neg_pos] at this
      grind

theorem logDeriv_const_cpow_neg {c : ℂ} (hc : c ≠ 0) (s : ℂ) :
    logDeriv (fun z : ℂ ↦ c ^ (-z)) s = -Complex.log c := by
  rw [logDeriv_apply]
  have hderiv :
      deriv (fun z : ℂ ↦ c ^ (-z)) s =
        Complex.log c * deriv (fun z : ℂ ↦ -z) s * c ^ (-s) :=
    Complex.deriv_const_cpow (f := fun z : ℂ ↦ -z) (x := s) (by fun_prop) c
  rw [hderiv]
  have hneg : deriv (fun z : ℂ ↦ -z) s = -1 :=
    (hasDerivAt_id s).neg.deriv
  rw [hneg]
  have hpow : c ^ (-s) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hc)
  grind

theorem logDeriv_complexPlaceGammaFactor_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    logDeriv CompletedZeta.complexPlaceGammaFactor s =
      Complex.digamma s - Complex.log (2 * (Real.pi : ℂ)) := by
  rw [show CompletedZeta.complexPlaceGammaFactor =
      fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z by
    funext z
    exact complexPlaceGammaFactor_eq z]
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hgammaDiff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s fun n h ↦ by
      have hn : 0 < (-n : ℂ).re := h ▸ hs
      simp only [neg_re, natCast_re, neg_pos] at hn
      grind
  have hmul := logDeriv_mul
    (f := fun z : ℂ ↦ (2 * (Real.pi : ℂ)) ^ (-z))
    (g := Complex.Gamma) s
    (cpow_ne_zero_iff.mpr <| Or.inl hbase)
    (Complex.Gamma_ne_zero_of_re_pos hs)
    ((show DifferentiableAt ℂ (fun z : ℂ ↦ -z) s by fun_prop).const_cpow <| Or.inl hbase)
    hgammaDiff
  rw [hmul,
    logDeriv_const_cpow_neg (mul_ne_zero two_ne_zero <|
      ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.digamma_def]
  ring

end NumberField.Odlyzko
